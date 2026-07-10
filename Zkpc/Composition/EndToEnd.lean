import Zkpc.Core.Composition
import Zkpc.Fleet.T6
import Zkpc.Network.Credential
import Zkpc.Refund.Safety
import Zkpc.Games.T7
import Zkpc.Games.FrameDeferred
import Zkpc.Games.Calibration

/-!
# Synchronized end-to-end composition

This module supplies the product transition system that is deliberately not
present in the component developments.  A composed execution is one labelled
trace, not a tuple of independently chosen reachable states.

The flat mode has three lanes (`Core`, `Fleet`, and `Network`).  Admission is
one atomic three-lane transition; reconciliation/slashing is one atomic
Core--Fleet transition; payee settlement is one atomic Core--Network
transition; and time advances in all three lanes at once.  In particular,
`Core.accept`, `Core.slash`, `Core.sweepOne`, `Fleet.accept`, and
`Network.accept` have no asynchronous escape hatch.

The refund mode synchronizes refund-chain admission with portable-network
admission.  Close and network settlement remain separate labelled protocol
phases because the refund machine nets an entire channel at close whereas the
network machine settles individual events.  They nevertheless occur on the
same trace, and the completion predicate requires both phases to have
finished.

Every cross-lane identification absent from the frozen component models is a
field of `FlatLink`/`RefundLink` and every use is witnessed in an admission or
alignment certificate.  No new trusted declaration identifies messages, nullifiers,
recipients, credentials, or clocks.
-/

open OracleSpec OracleComp

namespace Zkpc.Composition

/-! ## Generic labelled traces -/

/-- A finite, chronologically labelled trace for an arbitrary step relation. -/
inductive LTrace {S L : Type} (Step : S → L → S → Prop) :
    S → List L → S → Prop
  | nil (s : S) : LTrace Step s [] s
  | cons {s t u : S} {label : L} {labels : List L} :
      Step s label t → LTrace Step t labels u →
        LTrace Step s (label :: labels) u

namespace LTrace

/-- Concatenate two traces whose boundary states agree. -/
theorem append {S L : Type} {Step : S → L → S → Prop}
    {s t u : S} {xs ys : List L}
    (h₁ : LTrace Step s xs t) (h₂ : LTrace Step t ys u) :
    LTrace Step s (xs ++ ys) u := by
  induction h₁ with
  | nil => exact h₂
  | cons hstep htail ih => exact .cons hstep (ih h₂)

/-- Regard one labelled transition as a singleton trace. -/
theorem single {S L : Type} {Step : S → L → S → Prop}
    {s t : S} {label : L} (h : Step s label t) :
    LTrace Step s [label] t :=
  .cons h (.nil t)

end LTrace

/-! ## Flat Core--Fleet--Network product -/

/-- The lanes of the flat product. -/
inductive FlatLane
  | core
  | fleet
  | network
deriving DecidableEq

/-- Product state of the flat channel, distributed fleet, and portable
network accounting machines. -/
structure FlatState (N : ℕ) (F M P Recipient Nf Payload : Type) where
  core : Core.St F M
  fleet : Fleet.FSt N P
  network : Network.St Recipient Nf Payload

namespace FlatState

/-- Fully parameterized Core projection (the raw structure projector erases
the unrelated lane parameters, which makes them awkward to infer in records). -/
abbrev coreSt {N : ℕ} {F M P Recipient Nf Payload : Type}
    (s : FlatState N F M P Recipient Nf Payload) : Core.St F M :=
  @FlatState.core N F M P Recipient Nf Payload s

/-- Fully parameterized Fleet projection. -/
abbrev fleetSt {N : ℕ} {F M P Recipient Nf Payload : Type}
    (s : FlatState N F M P Recipient Nf Payload) : Fleet.FSt N P :=
  @FlatState.fleet N F M P Recipient Nf Payload s

/-- Fully parameterized Network projection. -/
abbrev networkSt {N : ℕ} {F M P Recipient Nf Payload : Type}
    (s : FlatState N F M P Recipient Nf Payload) :
    Network.St Recipient Nf Payload :=
  @FlatState.network N F M P Recipient Nf Payload s

end FlatState

/-- The uniquely aligned initial product state. -/
def FlatState.init (N : ℕ) (F M P Recipient Nf Payload : Type) (D : ℕ) :
    FlatState N F M P Recipient Nf Payload :=
  ⟨Core.init, Fleet.finit, Network.init D⟩

/-- Explicit application-level identifications used to relate the three
frozen component alphabets.  The relations are data, not assumptions in the
kernel environment. -/
structure FlatLink (N : ℕ) (F M P Recipient Nf Payload : Type) where
  nfOf : F → ℕ → Nf
  recipientOf : Fin N → Recipient
  coreFleetPayload : M → P → Prop
  coreNetworkPayload : M → Payload → Prop

/-- Core actions that really are local to the channel lane.  Admission,
identity slashing, sweeping, and ticking are intentionally absent: their only
composed constructors are synchronized ones below. -/
inductive CoreLocal {F M : Type} : Core.Act F M → Prop
  | openCh (k : F) : CoreLocal (.openCh k)
  | emitHonest (k : F) (m : M) : CoreLocal (.emitHonest k m)
  | emitAdv (k : F) (i : ℕ) (m : M) : CoreLocal (.emitAdv k i m)
  | payerClose (k : F) (U : Finset ℕ) : CoreLocal (.payerClose k U)
  | closeDispute (k : F) (i : ℕ) (m : M) :
      CoreLocal (.closeDispute k i m)
  | settleClose (k : F) : CoreLocal (.settleClose k)
  | settleVoid (k : F) : CoreLocal (.settleVoid k)

/-- Labels expose which logical protocol event occurred. -/
inductive FlatLabel (N : ℕ) (F M P Recipient Nf Payload : Type)
  | core (a : Core.Act F M)
  | tick
  | redeem (k : F) (i : ℕ) (m : M) (gateway : Fin N) (payload : P)
      (ticket : Network.Credential.Ticket F Recipient Nf Payload)
  | reconcile (k : F) (i : ℕ) (m m' : M)
  | settle (k : F) (i : ℕ) (m : M)
      (event : Network.Event Recipient Nf Payload)

/-- Active lanes of each flat label. -/
def FlatLabel.lanes {N : ℕ} {F M P Recipient Nf Payload : Type} :
    FlatLabel N F M P Recipient Nf Payload → List FlatLane
  | .core _ => [.core]
  | .tick => [.core, .fleet, .network]
  | .redeem _ _ _ _ _ _ => [.core, .fleet, .network]
  | .reconcile _ _ _ _ => [.core, .fleet]
  | .settle _ _ _ _ => [.core, .network]

section Flat

variable {N : ℕ} {F M P Recipient Nf Payload : Type}
variable [Field F] [DecidableEq F] [DecidableEq M] [DecidableEq P]
variable [DecidableEq Recipient] [DecidableEq Nf] [DecidableEq Payload]
variable {C D τ b Te : ℕ} {honest : F → Prop}

/-- Core successor of one synchronized admission. -/
def flatCoreAcceptNext (s : Core.St F M) (k : F) (i : ℕ) (m : M) :
    Core.St F M :=
  { s with acc := insert (k, i, m) s.acc }

/-- Fleet successor of the same synchronized admission. -/
def flatFleetAcceptNext (s : Fleet.FSt N P) (g : Fin N) (i : ℕ) (p : P) :
    Fleet.FSt N P :=
  ⟨s.clock, insert (Fleet.Ev.mk s.clock g i (g, p)) s.log, s.slashed⟩

/-- Network successor of the same synchronized admission. -/
def flatNetworkAcceptNext (s : Network.St Recipient Nf Payload)
    (event : Network.Event Recipient Nf Payload) :
    Network.St Recipient Nf Payload :=
  { s with accepted := insert event s.accepted }

/-- Core successor of synchronized identity slashing. -/
def flatCoreSlashNext (s : Core.St F M) (k : F) : Core.St F M :=
  { s with slashedAt := Function.update s.slashedAt k (some s.clock) }

/-- Fleet successor of synchronized identity slashing. -/
def flatFleetSlashNext (s : Fleet.FSt N P) : Fleet.FSt N P :=
  { s with slashed := some s.clock }

/-- Core successor of synchronized payee settlement. -/
def flatCoreSettleNext (C : ℕ) (s : Core.St F M) (k : F) (i : ℕ) :
    Core.St F M :=
  { s with swept := insert (k, i) s.swept, paidGw := s.paidGw + C }

/-- Network successor of synchronized payee settlement. -/
def flatNetworkSettleNext (s : Network.St Recipient Nf Payload)
    (event : Network.Event Recipient Nf Payload) :
    Network.St Recipient Nf Payload :=
  { s with settled := insert event s.settled,
           totalPaid := s.totalPaid + event.value }

/-- A proof-bearing synchronized admission.  Besides the three actual step
proofs, it carries concrete proof verification and every cross-lane field
identification used by the composition. -/
structure FlatAdmissionCert
    (H : Crypto.LinearSigma.ChallengeOracle F)
    (encode : Network.Credential.Encode F Recipient Nf Payload)
    (link : FlatLink N F M P Recipient Nf Payload)
    (s : FlatState N F M P Recipient Nf Payload) where
  key : F
  index : ℕ
  message : M
  gateway : Fin N
  fleetPayload : P
  ticket : Network.Credential.Ticket F Recipient Nf Payload
  verified : Network.Credential.WellFormed H encode ticket
  value_eq : ticket.value = C
  nf_eq : ticket.nf = link.nfOf key index
  recipient_eq : ticket.recipient = link.recipientOf gateway
  fleet_payload : link.coreFleetPayload message fleetPayload
  network_payload : link.coreNetworkPayload message ticket.payload
  coreStep : Core.Step C D τ honest s.coreSt (.accept key index message)
      (flatCoreAcceptNext s.coreSt key index message)
  fleetStep : Fleet.FStep C D b Te s.fleetSt
      (flatFleetAcceptNext s.fleetSt gateway index fleetPayload)
  networkStep : Network.Step s.networkSt (.accept ticket.event)
      (flatNetworkAcceptNext s.networkSt ticket.event)

/-- State produced by a synchronized admission certificate. -/
def FlatAdmissionCert.next
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {s : FlatState N F M P Recipient Nf Payload}
    (cert : FlatAdmissionCert (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link s) :
      FlatState N F M P Recipient Nf Payload :=
  ⟨flatCoreAcceptNext s.coreSt cert.key cert.index cert.message,
    flatFleetAcceptNext s.fleetSt cert.gateway cert.index cert.fleetPayload,
    flatNetworkAcceptNext s.networkSt cert.ticket.event⟩

/-- Proof-bearing alignment for a detected cross-gateway conflict.  The
certificate explicitly relates the fleet evidence to the two Core messages
and requires both slash steps, at an aligned clock, to fire atomically. -/
structure FlatReconcileCert
    (link : FlatLink N F M P Recipient Nf Payload)
    (s : FlatState N F M P Recipient Nf Payload) where
  key : F
  index : ℕ
  message : M
  message' : M
  event : Fleet.Ev N P
  event' : Fleet.Ev N P
  event_mem : event ∈ s.fleetSt.log
  event'_mem : event' ∈ s.fleetSt.log
  conflict : Fleet.Conflict event event'
  event_index : event.idx = index
  event'_index : event'.idx = index
  event_message : link.coreFleetPayload message event.msg.2
  event'_message : link.coreFleetPayload message' event'.msg.2
  clock_eq : s.coreSt.clock = s.fleetSt.clock
  coreStep : Core.Step C D τ honest s.coreSt
      (.slash key index message message')
      (flatCoreSlashNext s.coreSt key)
  fleetStep : Fleet.FStep C D b Te s.fleetSt
      (flatFleetSlashNext s.fleetSt)

/-- State produced by an aligned Core--Fleet reconciliation. -/
def FlatReconcileCert.next
    {link : FlatLink N F M P Recipient Nf Payload}
    {s : FlatState N F M P Recipient Nf Payload}
    (cert : FlatReconcileCert (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) link s) :
      FlatState N F M P Recipient Nf Payload :=
  ⟨flatCoreSlashNext s.coreSt cert.key,
    flatFleetSlashNext s.fleetSt, s.networkSt⟩

/-- Proof-bearing alignment of a Core sweep with settlement of the same
logical payment event in the portable network. -/
structure FlatSettlementCert
    (link : FlatLink N F M P Recipient Nf Payload)
    (s : FlatState N F M P Recipient Nf Payload) where
  key : F
  index : ℕ
  message : M
  event : Network.Event Recipient Nf Payload
  value_eq : event.value = C
  nf_eq : event.nf = link.nfOf key index
  payload_eq : link.coreNetworkPayload message event.payload
  coreStep : Core.Step C D τ honest s.coreSt (.sweepOne key index message)
      (flatCoreSettleNext C s.coreSt key index)
  networkStep : Network.Step s.networkSt (.settle event)
      (flatNetworkSettleNext s.networkSt event)

/-- State produced by a synchronized payee settlement. -/
def FlatSettlementCert.next
    {link : FlatLink N F M P Recipient Nf Payload}
    {s : FlatState N F M P Recipient Nf Payload}
    (cert : FlatSettlementCert (C := C) (D := D) (τ := τ)
      (honest := honest) link s) :
      FlatState N F M P Recipient Nf Payload :=
  ⟨flatCoreSettleNext C s.coreSt cert.key cert.index, s.fleetSt,
    flatNetworkSettleNext s.networkSt cert.event⟩

/-- The synchronized flat product transition relation. -/
inductive FlatStep
    (H : Crypto.LinearSigma.ChallengeOracle F)
    (encode : Network.Credential.Encode F Recipient Nf Payload)
    (link : FlatLink N F M P Recipient Nf Payload) :
    FlatState N F M P Recipient Nf Payload →
      FlatLabel N F M P Recipient Nf Payload →
      FlatState N F M P Recipient Nf Payload → Prop
  | core {s : FlatState N F M P Recipient Nf Payload}
      {a : Core.Act F M} {core' : Core.St F M}
      (isLocal : CoreLocal a)
      (step : Core.Step C D τ honest s.coreSt a core') :
      FlatStep H encode link s (.core a) { s with core := core' }
  | tick (s : FlatState N F M P Recipient Nf Payload) :
      FlatStep H encode link s .tick
        ⟨{ (s.coreSt) with clock := s.coreSt.clock + 1 },
          { (s.fleetSt) with clock := s.fleetSt.clock + 1 },
          { (s.networkSt) with clock := s.networkSt.clock + 1 }⟩
  | redeem {s : FlatState N F M P Recipient Nf Payload}
      (cert : FlatAdmissionCert (C := C) (D := D) (τ := τ) (b := b)
        (Te := Te) (honest := honest) H encode link s) :
      FlatStep H encode link s
        (.redeem cert.key cert.index cert.message cert.gateway
          cert.fleetPayload cert.ticket) cert.next
  | reconcile {s : FlatState N F M P Recipient Nf Payload}
      (cert : FlatReconcileCert (C := C) (D := D) (τ := τ) (b := b)
        (Te := Te) (honest := honest) link s) :
      FlatStep H encode link s
        (.reconcile cert.key cert.index cert.message cert.message') cert.next
  | settle {s : FlatState N F M P Recipient Nf Payload}
      (cert : FlatSettlementCert (C := C) (D := D) (τ := τ)
        (honest := honest) link s) :
      FlatStep H encode link s
        (.settle cert.key cert.index cert.message cert.event) cert.next

/-- All clocks in a flat product state denote the same logical time. -/
def FlatClockAligned (s : FlatState N F M P Recipient Nf Payload) : Prop :=
  s.coreSt.clock = s.fleetSt.clock ∧
    s.coreSt.clock = s.networkSt.clock

/-- Core payee accounting and portable-network settlement accounting denote
the same money on a synchronized flat execution. -/
def FlatPaymentAligned (s : FlatState N F M P Recipient Nf Payload) : Prop :=
  s.coreSt.paidGw = s.networkSt.totalPaid

omit [Field F] in
/-- A permitted Core-local action does not advance time. -/
theorem CoreLocal.step_clock_eq {s t : Core.St F M} {a : Core.Act F M}
    (hlocal : CoreLocal a) (hstep : Core.Step C D τ honest s a t) :
    t.clock = s.clock := by
  cases hstep <;> cases hlocal <;> rfl

omit [Field F] in
/-- A permitted Core-local action cannot change payee settlement. -/
theorem CoreLocal.step_paidGw_eq {s t : Core.St F M} {a : Core.Act F M}
    (hlocal : CoreLocal a) (hstep : Core.Step C D τ honest s a t) :
    t.paidGw = s.paidGw := by
  cases hstep <;> cases hlocal <;> rfl

/-- Every synchronized flat transition preserves clock alignment. -/
theorem FlatStep.preserves_clockAlignment
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {s t : FlatState N F M P Recipient Nf Payload}
    {label : FlatLabel N F M P Recipient Nf Payload}
    (hstep : FlatStep (C := C) (D := D) (τ := τ) (b := b) (Te := Te)
      (honest := honest) H encode link s label t)
    (haligned : FlatClockAligned s) : FlatClockAligned t := by
  cases hstep with
  | core hlocal hcore =>
      constructor
      · change _ = s.fleetSt.clock
        rw [CoreLocal.step_clock_eq hlocal hcore]
        exact haligned.1
      · change _ = s.networkSt.clock
        rw [CoreLocal.step_clock_eq hlocal hcore]
        exact haligned.2
  | tick =>
      exact ⟨congrArg (· + 1) haligned.1, congrArg (· + 1) haligned.2⟩
  | redeem cert =>
      simpa [FlatClockAligned, FlatAdmissionCert.next, flatCoreAcceptNext,
        flatFleetAcceptNext, flatNetworkAcceptNext] using haligned
  | reconcile cert =>
      simpa [FlatClockAligned, FlatReconcileCert.next, flatCoreSlashNext,
        flatFleetSlashNext] using haligned
  | settle cert =>
      simpa [FlatClockAligned, FlatSettlementCert.next, flatCoreSettleNext,
        flatNetworkSettleNext] using haligned

/-- Every synchronized flat transition preserves cross-lane payment
accounting. -/
theorem FlatStep.preserves_paymentAlignment
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {s t : FlatState N F M P Recipient Nf Payload}
    {label : FlatLabel N F M P Recipient Nf Payload}
    (hstep : FlatStep (C := C) (D := D) (τ := τ) (b := b) (Te := Te)
      (honest := honest) H encode link s label t)
    (haligned : FlatPaymentAligned s) : FlatPaymentAligned t := by
  cases hstep with
  | core hlocal hcore =>
      change _ = s.networkSt.totalPaid
      rw [CoreLocal.step_paidGw_eq hlocal hcore]
      exact haligned
  | tick => exact haligned
  | redeem cert =>
      simpa [FlatPaymentAligned, FlatAdmissionCert.next, flatCoreAcceptNext,
        flatNetworkAcceptNext] using haligned
  | reconcile cert =>
      simpa [FlatPaymentAligned, FlatReconcileCert.next, flatCoreSlashNext]
        using haligned
  | settle cert =>
      simpa [FlatPaymentAligned, FlatSettlementCert.next,
        flatCoreSettleNext, flatNetworkSettleNext, cert.value_eq] using
        congrArg (· + C) haligned

/-! ### Flat trace projections -/

/-- Project any composed trace to Core reachability, starting from an
arbitrary already-reachable Core source.  Inactive Core lanes stutter in the
induction; active lanes contribute the step stored in their certificate. -/
theorem flatTrace_coreReach
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {s t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link) s labels t)
    (hreach : Core.Reach C D τ honest s.coreSt) :
    Core.Reach C D τ honest t.coreSt := by
  induction htrace with
  | nil => exact hreach
  | cons hstep _ ih =>
      apply ih
      cases hstep with
      | core _ step => exact Core.Reach.step hreach step
      | tick => exact Core.Reach.step hreach (Core.Step.tick _)
      | redeem cert => exact Core.Reach.step hreach cert.coreStep
      | reconcile cert => exact Core.Reach.step hreach cert.coreStep
      | settle cert => exact Core.Reach.step hreach cert.coreStep

/-- Project a composed trace to Fleet reachability. -/
theorem flatTrace_fleetReach
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {s t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link) s labels t)
    (hreach : Fleet.FReach C D b Te s.fleetSt) :
    Fleet.FReach C D b Te t.fleetSt := by
  induction htrace with
  | nil => exact hreach
  | cons hstep _ ih =>
      apply ih
      cases hstep with
      | core _ _ => exact hreach
      | tick => exact Fleet.FReach.step hreach (Fleet.FStep.tick _)
      | redeem cert => exact Fleet.FReach.step hreach cert.fleetStep
      | reconcile cert => exact Fleet.FReach.step hreach cert.fleetStep
      | settle _ => exact hreach

/-- Project a composed trace to portable-network reachability. -/
theorem flatTrace_networkReach
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {s t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link) s labels t)
    (hreach : Network.Reach D s.networkSt) :
    Network.Reach D t.networkSt := by
  induction htrace with
  | nil => exact hreach
  | cons hstep _ ih =>
      apply ih
      cases hstep with
      | core _ _ => exact hreach
      | tick => exact Network.Reach.step hreach (Network.Step.tick _)
      | redeem cert => exact Network.Reach.step hreach cert.networkStep
      | reconcile _ => exact hreach
      | settle cert => exact Network.Reach.step hreach cert.networkStep

/-- Core projection of a trace from the synchronized initial state. -/
theorem flatTrace_coreProjection
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link)
      (FlatState.init N F M P Recipient Nf Payload D) labels t) :
    Core.Reach C D τ honest t.coreSt :=
  flatTrace_coreReach htrace Core.Reach.init

/-- Fleet projection of a trace from the synchronized initial state. -/
theorem flatTrace_fleetProjection
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link)
      (FlatState.init N F M P Recipient Nf Payload D) labels t) :
    Fleet.FReach C D b Te t.fleetSt :=
  flatTrace_fleetReach htrace Fleet.FReach.init

/-- Network projection of a trace from the synchronized initial state. -/
theorem flatTrace_networkProjection
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link)
      (FlatState.init N F M P Recipient Nf Payload D) labels t) :
    Network.Reach D t.networkSt :=
  flatTrace_networkReach htrace Network.Reach.init

/-- Transport clock alignment across an arbitrary flat trace. -/
theorem flatTrace_clockAlignmentFrom
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {s t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link) s labels t)
    (haligned : FlatClockAligned s) : FlatClockAligned t := by
  induction htrace with
  | nil => exact haligned
  | cons hstep _ ih =>
      exact ih (hstep.preserves_clockAlignment haligned)

/-- Clock alignment is an invariant of every flat trace from the product
initial state. -/
theorem flatTrace_clockAlignment
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link)
      (FlatState.init N F M P Recipient Nf Payload D) labels t) :
    FlatClockAligned t :=
  flatTrace_clockAlignmentFrom htrace ⟨rfl, rfl⟩

/-- Transport cross-lane payment accounting across an arbitrary flat trace. -/
theorem flatTrace_paymentAlignmentFrom
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {s t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link) s labels t)
    (haligned : FlatPaymentAligned s) : FlatPaymentAligned t := by
  induction htrace with
  | nil => exact haligned
  | cons hstep _ ih =>
      exact ih (hstep.preserves_paymentAlignment haligned)

/-- Core and network payment totals agree on every flat trace from the
synchronized initial state. -/
theorem flatTrace_paymentAlignment
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {t : FlatState N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link)
      (FlatState.init N F M P Recipient Nf Payload D) labels t) :
    FlatPaymentAligned t :=
  flatTrace_paymentAlignmentFrom htrace rfl

/-! ### Flat completion -/

/-- At least one proof-bearing synchronized admission occurred. -/
def FlatAdmissionOccurred
    (labels : List (FlatLabel N F M P Recipient Nf Payload)) : Prop :=
  ∃ label ∈ labels, match label with
    | .redeem _ _ _ _ _ _ => True
    | _ => False

/-- The target payer posted a close on this trace. -/
def FlatCloseOccurred (key : F)
    (labels : List (FlatLabel N F M P Recipient Nf Payload)) : Prop :=
  ∃ label ∈ labels, match label with
    | .core (.payerClose key' _) => key' = key
    | _ => False

/-- Automatic close settlement for the target payer occurred on this trace. -/
def FlatCloseSettlementOccurred (key : F)
    (labels : List (FlatLabel N F M P Recipient Nf Payload)) : Prop :=
  ∃ label ∈ labels, match label with
    | .core (.settleClose key') => key' = key
    | _ => False

/-- At least one aligned Core--Network payee settlement occurred. -/
def FlatPaymentSettlementOccurred
    (labels : List (FlatLabel N F M P Recipient Nf Payload)) : Prop :=
  ∃ label ∈ labels, match label with
    | .settle _ _ _ _ => True
    | _ => False

/-- Terminal predicate for a genuinely complete flat execution.  The label
requirements rule out declaring an asynchronous tuple (or the initial state)
complete; the final-state requirements close both settlement surfaces and
carry the honest-fleet reconciliation guarantee explicitly. -/
structure FlatComplete (L : ℕ) (key : F)
    (labels : List (FlatLabel N F M P Recipient Nf Payload))
    (s : FlatState N F M P Recipient Nf Payload) : Prop where
  admitted : FlatAdmissionOccurred labels
  closePosted : FlatCloseOccurred key labels
  closeSettledStep : FlatCloseSettlementOccurred key labels
  paymentSettledStep : FlatPaymentSettlementOccurred labels
  closeSettled : s.coreSt.closeSettled key = true
  networkSettled : s.networkSt.settled = s.networkSt.accepted
  fleetReconciled : Fleet.FleetFair L s.fleetSt

end Flat

/-! ## Refund--Network product -/

/-- Lanes of the refund product. -/
inductive RefundLane
  | refund
  | network
deriving DecidableEq

/-- Product state of one refund-bearing channel and portable accounting. -/
structure RefundState (Rep Recipient Nf Payload : Type) where
  refund : Refund.St Rep
  network : Network.St Recipient Nf Payload

namespace RefundState

/-- Fully parameterized refund-lane projection. -/
abbrev refundSt {Rep Recipient Nf Payload : Type}
    (s : RefundState Rep Recipient Nf Payload) : Refund.St Rep :=
  @RefundState.refund Rep Recipient Nf Payload s

/-- Fully parameterized network-lane projection. -/
abbrev networkSt {Rep Recipient Nf Payload : Type}
    (s : RefundState Rep Recipient Nf Payload) :
    Network.St Recipient Nf Payload :=
  @RefundState.network Rep Recipient Nf Payload s

end RefundState

/-- Initial refund product state. -/
def RefundState.init (Rep Recipient Nf Payload : Type) (r0 : Rep) (D : ℕ) :
    RefundState Rep Recipient Nf Payload :=
  ⟨Refund.St.init r0, Network.init D⟩

/-- Explicit application identifications for refund admission. -/
structure RefundLink (Rep Recipient Nf Payload : Type) where
  nfOf : ℕ → Nf
  payload : ℕ → Rep → Payload → Prop

/-- Refund product labels.  Admission is synchronized; close and per-event
network settlement are separate phases on the same labelled trace. -/
inductive RefundLabel (F Rep Recipient Nf Payload : Type)
  | redeem (cost : ℕ) (newRep : Rep)
      (ticket : Network.Credential.Ticket F Recipient Nf Payload)
  | close
  | forceClose
  | settle (event : Network.Event Recipient Nf Payload)
  | tick

/-- Active lanes of each refund label. -/
def RefundLabel.lanes {F Rep Recipient Nf Payload : Type} :
    RefundLabel F Rep Recipient Nf Payload → List RefundLane
  | .redeem _ _ _ => [.refund, .network]
  | .close => [.refund]
  | .forceClose => [.refund]
  | .settle _ => [.network]
  | .tick => [.network]

section Refund

variable {F Rep Recipient Nf Payload : Type}
variable [Field F] [DecidableEq F] [DecidableEq Recipient]
variable [DecidableEq Nf] [DecidableEq Payload]
variable {Cmax D : ℕ}

/-- Refund successor of synchronized acceptance. -/
def refundAcceptNext (Cmax : ℕ) (s : Refund.St Rep) (cost : ℕ)
    (newRep : Rep) : Refund.St Rep :=
  { s with idx := s.idx + 1, R := s.R + (Cmax - cost),
           sumc := s.sumc + cost, rep := newRep }

/-- Network successor of synchronized refund admission. -/
def refundNetworkAcceptNext (s : Network.St Recipient Nf Payload)
    (event : Network.Event Recipient Nf Payload) :
    Network.St Recipient Nf Payload :=
  { s with accepted := insert event s.accepted }

/-- Cooperative refund-close successor. -/
def refundCloseNext (Cmax D : ℕ) (s : Refund.St Rep) : Refund.St Rep :=
  { s with closed := true, settled := true,
           payerPay := (D + s.R) - s.idx * Cmax,
           payeePay := s.idx * Cmax - s.R }

/-- Force-close/fund-slash successor. -/
def refundForceCloseNext (D : ℕ) (s : Refund.St Rep) : Refund.St Rep :=
  { s with closed := true, settled := true, slashed := true,
           payerPay := 0, payeePay := D }

/-- Network successor of per-event settlement. -/
def refundNetworkSettleNext (s : Network.St Recipient Nf Payload)
    (event : Network.Event Recipient Nf Payload) :
    Network.St Recipient Nf Payload :=
  { s with settled := insert event s.settled,
           totalPaid := s.totalPaid + event.value }

/-- Proof-bearing synchronized refund/network admission. -/
structure RefundAdmissionCert
    (H : Crypto.LinearSigma.ChallengeOracle F)
    (encode : Network.Credential.Encode F Recipient Nf Payload)
    (link : RefundLink Rep Recipient Nf Payload)
    (s : RefundState Rep Recipient Nf Payload) where
  cost : ℕ
  newRep : Rep
  ticket : Network.Credential.Ticket F Recipient Nf Payload
  verified : Network.Credential.WellFormed H encode ticket
  value_eq : ticket.value = cost
  nf_eq : ticket.nf = link.nfOf s.refundSt.idx
  payload_eq : link.payload cost newRep ticket.payload
  refundStep : Refund.Step Cmax D s.refundSt (.accept cost newRep)
      (refundAcceptNext Cmax s.refundSt cost newRep)
  networkStep : Network.Step s.networkSt (.accept ticket.event)
      (refundNetworkAcceptNext s.networkSt ticket.event)

/-- State produced by synchronized refund admission. -/
def RefundAdmissionCert.next
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {s : RefundState Rep Recipient Nf Payload}
    (cert : RefundAdmissionCert (Cmax := Cmax) (D := D) H encode link s) :
    RefundState Rep Recipient Nf Payload :=
  ⟨refundAcceptNext Cmax s.refundSt cert.cost cert.newRep,
    refundNetworkAcceptNext s.networkSt cert.ticket.event⟩

/-- The synchronized refund product transition relation.  There is no
refund-only acceptance constructor. -/
inductive RefundStep
    (H : Crypto.LinearSigma.ChallengeOracle F)
    (encode : Network.Credential.Encode F Recipient Nf Payload)
    (link : RefundLink Rep Recipient Nf Payload) :
    RefundState Rep Recipient Nf Payload →
      RefundLabel F Rep Recipient Nf Payload →
      RefundState Rep Recipient Nf Payload → Prop
  | redeem {s : RefundState Rep Recipient Nf Payload}
      (cert : RefundAdmissionCert (Cmax := Cmax) (D := D) H encode link s) :
      RefundStep H encode link s (.redeem cert.cost cert.newRep cert.ticket)
        cert.next
  | close {s : RefundState Rep Recipient Nf Payload}
      (step : Refund.Step Cmax D s.refundSt .close
        (refundCloseNext Cmax D s.refundSt)) :
      RefundStep H encode link s .close
        ⟨refundCloseNext Cmax D s.refundSt, s.networkSt⟩
  | forceClose {s : RefundState Rep Recipient Nf Payload}
      (step : Refund.Step Cmax D s.refundSt .forceClose
        (refundForceCloseNext D s.refundSt)) :
      RefundStep H encode link s .forceClose
        ⟨refundForceCloseNext D s.refundSt, s.networkSt⟩
  | settle {s : RefundState Rep Recipient Nf Payload}
      (event : Network.Event Recipient Nf Payload)
      (step : Network.Step s.networkSt (.settle event)
        (refundNetworkSettleNext s.networkSt event)) :
      RefundStep H encode link s (.settle event)
        ⟨s.refundSt, refundNetworkSettleNext s.networkSt event⟩
  | tick (s : RefundState Rep Recipient Nf Payload) :
      RefundStep H encode link s .tick
        ⟨s.refundSt, { (s.networkSt) with clock := s.networkSt.clock + 1 }⟩

/-- The refund machine's accumulated accepted cost equals the value of the
portable events admitted by the same synchronized trace. -/
def RefundValueAligned (s : RefundState Rep Recipient Nf Payload) : Prop :=
  s.refundSt.sumc = Network.valueSum s.networkSt.accepted

/-- Every refund-product step preserves accepted-value alignment. -/
theorem RefundStep.preserves_valueAlignment
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {s t : RefundState Rep Recipient Nf Payload}
    {label : RefundLabel F Rep Recipient Nf Payload}
    (hstep : RefundStep (Cmax := Cmax) (D := D) H encode link s label t)
    (haligned : RefundValueAligned s) : RefundValueAligned t := by
  cases hstep with
  | redeem cert =>
      have hnotmem : cert.ticket.event ∉ s.networkSt.accepted := by
        intro hmem
        cases cert.networkStep with
        | accept _ _ hfresh => exact (hfresh cert.ticket.event hmem) rfl
      simpa [RefundValueAligned, RefundAdmissionCert.next,
        refundAcceptNext, refundNetworkAcceptNext, Network.valueSum,
        Finset.sum_insert hnotmem, cert.value_eq] using
        congrArg (· + cert.cost) haligned
  | close _ => simpa [RefundValueAligned, refundCloseNext] using haligned
  | forceClose _ =>
      simpa [RefundValueAligned, refundForceCloseNext] using haligned
  | settle _ _ =>
      simpa [RefundValueAligned, refundNetworkSettleNext] using haligned
  | tick => exact haligned

/-! ### Refund trace projections -/

/-- Project a refund product trace to the refund machine. -/
theorem refundTrace_refundReach
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {s t : RefundState Rep Recipient Nf Payload}
    {labels : List (RefundLabel F Rep Recipient Nf Payload)}
    {r0 : Rep}
    (htrace : LTrace (RefundStep (Cmax := Cmax) (D := D) H encode link)
      s labels t)
    (hreach : Refund.Reach Rep Cmax D r0 s.refundSt) :
    Refund.Reach Rep Cmax D r0 t.refundSt := by
  induction htrace with
  | nil => exact hreach
  | cons hstep _ ih =>
      apply ih
      cases hstep with
      | redeem cert => exact Refund.Reach.step hreach cert.refundStep
      | close step => exact Refund.Reach.step hreach step
      | forceClose step => exact Refund.Reach.step hreach step
      | settle _ _ => exact hreach
      | tick => exact hreach

/-- Project a refund product trace to portable-network reachability. -/
theorem refundTrace_networkReach
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {s t : RefundState Rep Recipient Nf Payload}
    {labels : List (RefundLabel F Rep Recipient Nf Payload)}
    (htrace : LTrace (RefundStep (Cmax := Cmax) (D := D) H encode link)
      s labels t)
    (hreach : Network.Reach D s.networkSt) :
    Network.Reach D t.networkSt := by
  induction htrace with
  | nil => exact hreach
  | cons hstep _ ih =>
      apply ih
      cases hstep with
      | redeem cert => exact Network.Reach.step hreach cert.networkStep
      | close _ => exact hreach
      | forceClose _ => exact hreach
      | settle _ step => exact Network.Reach.step hreach step
      | tick => exact Network.Reach.step hreach (Network.Step.tick _)

/-- Refund projection from the synchronized initial state. -/
theorem refundTrace_refundProjection
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {t : RefundState Rep Recipient Nf Payload}
    {labels : List (RefundLabel F Rep Recipient Nf Payload)} {r0 : Rep}
    (htrace : LTrace (RefundStep (Cmax := Cmax) (D := D) H encode link)
      (RefundState.init Rep Recipient Nf Payload r0 D) labels t) :
    Refund.Reach Rep Cmax D r0 t.refundSt :=
  refundTrace_refundReach htrace Refund.Reach.init

/-- Network projection from the synchronized refund initial state. -/
theorem refundTrace_networkProjection
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {t : RefundState Rep Recipient Nf Payload}
    {labels : List (RefundLabel F Rep Recipient Nf Payload)} {r0 : Rep}
    (htrace : LTrace (RefundStep (Cmax := Cmax) (D := D) H encode link)
      (RefundState.init Rep Recipient Nf Payload r0 D) labels t) :
    Network.Reach D t.networkSt :=
  refundTrace_networkReach htrace Network.Reach.init

/-- Transport accepted-value alignment across an arbitrary refund trace. -/
theorem refundTrace_valueAlignmentFrom
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {s t : RefundState Rep Recipient Nf Payload}
    {labels : List (RefundLabel F Rep Recipient Nf Payload)}
    (htrace : LTrace (RefundStep (Cmax := Cmax) (D := D) H encode link)
      s labels t)
    (haligned : RefundValueAligned s) : RefundValueAligned t := by
  induction htrace with
  | nil => exact haligned
  | cons hstep _ ih => exact ih (hstep.preserves_valueAlignment haligned)

/-- Accepted refund costs and portable admitted value agree on every trace
from the synchronized initial state. -/
theorem refundTrace_valueAlignment
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {t : RefundState Rep Recipient Nf Payload}
    {labels : List (RefundLabel F Rep Recipient Nf Payload)} {r0 : Rep}
    (htrace : LTrace (RefundStep (Cmax := Cmax) (D := D) H encode link)
      (RefundState.init Rep Recipient Nf Payload r0 D) labels t) :
    RefundValueAligned t := by
  apply refundTrace_valueAlignmentFrom htrace
  simp [RefundValueAligned, RefundState.init, Refund.St.init,
    Network.init, Network.valueSum]

/-! ### Refund completion -/

def RefundAdmissionOccurred
    (labels : List (RefundLabel F Rep Recipient Nf Payload)) : Prop :=
  ∃ label ∈ labels, match label with
    | .redeem _ _ _ => True
    | _ => False

def RefundTerminalCloseOccurred
    (labels : List (RefundLabel F Rep Recipient Nf Payload)) : Prop :=
  ∃ label ∈ labels, match label with
    | .close => True
    | .forceClose => True
    | _ => False

def RefundPaymentSettlementOccurred
    (labels : List (RefundLabel F Rep Recipient Nf Payload)) : Prop :=
  ∃ label ∈ labels, match label with
    | .settle _ => True
    | _ => False

/-- Terminal predicate for a complete refund execution on one trace. -/
structure RefundComplete
    (labels : List (RefundLabel F Rep Recipient Nf Payload))
    (s : RefundState Rep Recipient Nf Payload) : Prop where
  admitted : RefundAdmissionOccurred labels
  closeOccurred : RefundTerminalCloseOccurred labels
  paymentSettledStep : RefundPaymentSettlementOccurred labels
  refundSettled : s.refundSt.settled = true
  networkSettled : s.networkSt.settled = s.networkSt.accepted

end Refund

/-! ## Operational and scheme-level guarantee records -/

section FlatGuarantees

variable {N : ℕ} {F M P Recipient Nf Payload : Type}
variable [Field F] [DecidableEq F] [DecidableEq M] [DecidableEq P]
variable [DecidableEq Recipient] [DecidableEq Nf] [DecidableEq Payload]
variable {C D τ b Te L : ℕ} {honest : F → Prop}

/-- Safety facts transported from all three flat component machines. -/
structure FlatOperationalSafety (key : F)
    (s : FlatState N F M P Recipient Nf Payload) : Prop where
  coreReach : Core.Reach C D τ honest s.coreSt
  fleetReach : Fleet.FReach C D b Te s.fleetSt
  networkReach : Network.Reach D s.networkSt
  clocksAligned : FlatClockAligned s
  noOverspend : ∀ key' : F, s.coreSt.valueOf key' C ≤ D
  payeeExact : s.coreSt.paidGw = C * s.coreSt.swept.card
  payeeNetworkAligned : s.coreSt.paidGw = s.networkSt.totalPaid
  allAcceptedValuePaid :
    s.coreSt.paidGw = Network.valueSum s.networkSt.accepted
  payerFloor : s.coreSt.paidPayer key + s.coreSt.emittedCnt key * C = D
  payerFloorEq : s.coreSt.paidPayer key = D - s.coreSt.emittedCnt key * C
  honestUnslashed : s.coreSt.slashedAt key = none
  fleetPricedDivergence :
    s.fleetSt.acceptedValue C ≤
      D / C * C + N * b * (Fleet.ceilDiv L Te + 1) * C
  networkNoOverspend : s.networkSt.totalPaid ≤ D
  networkGlobalDedup : Network.NfUnique s.networkSt.accepted

/-- Operational safety plus a realized, non-vacuous completion witness on
the very same labelled trace. -/
structure FlatOperationalGuarantees (key : F)
    (labels : List (FlatLabel N F M P Recipient Nf Payload))
    (s : FlatState N F M P Recipient Nf Payload) : Prop where
  safety : FlatOperationalSafety (C := C) (D := D) (τ := τ) (b := b)
    (Te := Te) (L := L) (honest := honest) key s
  liveness : FlatComplete L key labels s

/-- Assemble all operational flat guarantees from one composed trace. -/
theorem flatOperational_of_trace
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    {s : FlatState N F M P Recipient Nf Payload} {key : F}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link)
      (FlatState.init N F M P Recipient Nf Payload D) labels s)
    (hkey : honest key) (hTe : 0 < Te)
    (hcomplete : FlatComplete L key labels s) :
    FlatOperationalGuarantees (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (L := L) (honest := honest) key labels s := by
  have hcore := flatTrace_coreProjection htrace
  have hfleet := flatTrace_fleetProjection htrace
  have hnetwork := flatTrace_networkProjection htrace
  have hclocks := flatTrace_clockAlignment htrace
  have hpayments := flatTrace_paymentAlignment htrace
  have hpaidValue := (Network.reach_inv hnetwork).paid_eq
  have hallAccepted :
      s.coreSt.paidGw = Network.valueSum s.networkSt.accepted := by
    calc
      s.coreSt.paidGw = s.networkSt.totalPaid := hpayments
      _ = Network.valueSum s.networkSt.settled := hpaidValue
      _ = Network.valueSum s.networkSt.accepted :=
        congrArg Network.valueSum hcomplete.networkSettled
  have hfloor := Core.T3_settled_amount hcore key hkey hcomplete.closeSettled
  refine ⟨?_, hcomplete⟩
  exact
    { coreReach := hcore
      fleetReach := hfleet
      networkReach := hnetwork
      clocksAligned := hclocks
      noOverspend := fun key' => Core.T1_no_overspend hcore key'
      payeeExact := Core.T2_paid_exact hcore
      payeeNetworkAligned := hpayments
      allAcceptedValuePaid := hallAccepted
      payerFloor := hfloor.1
      payerFloorEq := hfloor.2
      honestUnslashed := Core.honest_never_slashed hcore key hkey
      fleetPricedDivergence :=
        Fleet.T6_priced_divergence hfleet hTe hcomplete.fleetReconciled
      networkNoOverspend := Network.no_overspend hnetwork
      networkGlobalDedup := Network.global_dedup hnetwork }

end FlatGuarantees

section RefundGuarantees

variable {F Rep Recipient Nf Payload : Type}
variable [Field F] [DecidableEq F] [DecidableEq Recipient]
variable [DecidableEq Nf] [DecidableEq Payload]
variable {Cmax D : ℕ}

/-- Safety facts transported from both refund component machines. -/
structure RefundOperationalSafety (r0 : Rep)
    (s : RefundState Rep Recipient Nf Payload) : Prop where
  refundReach : Refund.Reach Rep Cmax D r0 s.refundSt
  networkReach : Network.Reach D s.networkSt
  refundNoOverspend : s.refundSt.sumc ≤ D
  settlementConservation : s.refundSt.payerPay + s.refundSt.payeePay = D
  cooperativeFloor : s.refundSt.slashed = false →
    s.refundSt.payerPay + s.refundSt.sumc = D
  acceptedValueCharged :
    Network.valueSum s.networkSt.accepted = s.refundSt.sumc
  allAcceptedValuePaid : s.networkSt.totalPaid = s.refundSt.sumc
  networkNoOverspend : s.networkSt.totalPaid ≤ D
  networkGlobalDedup : Network.NfUnique s.networkSt.accepted

/-- Refund operational safety plus a realized two-lane completion witness. -/
structure RefundOperationalGuarantees (r0 : Rep)
    (labels : List (RefundLabel F Rep Recipient Nf Payload))
    (s : RefundState Rep Recipient Nf Payload) : Prop where
  safety : RefundOperationalSafety (Cmax := Cmax) (D := D) r0 s
  liveness : RefundComplete labels s

/-- Assemble all operational refund guarantees from one composed trace. -/
theorem refundOperational_of_trace
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {labels : List (RefundLabel F Rep Recipient Nf Payload)}
    {s : RefundState Rep Recipient Nf Payload} {r0 : Rep}
    (htrace : LTrace (RefundStep (Cmax := Cmax) (D := D) H encode link)
      (RefundState.init Rep Recipient Nf Payload r0 D) labels s)
    (hcomplete : RefundComplete labels s) :
    RefundOperationalGuarantees (Cmax := Cmax) (D := D) r0 labels s := by
  have hrefund := refundTrace_refundProjection htrace
  have hnetwork := refundTrace_networkProjection htrace
  have hvalues := refundTrace_valueAlignment htrace
  have hpaidValue := (Network.reach_inv hnetwork).paid_eq
  have hallAccepted : s.networkSt.totalPaid = s.refundSt.sumc := by
    calc
      s.networkSt.totalPaid = Network.valueSum s.networkSt.settled := hpaidValue
      _ = Network.valueSum s.networkSt.accepted :=
        congrArg Network.valueSum hcomplete.networkSettled
      _ = s.refundSt.sumc := hvalues.symm
  refine ⟨?_, hcomplete⟩
  exact
    { refundReach := hrefund
      networkReach := hnetwork
      refundNoOverspend := Refund.T1_B_no_overspend hrefund
      settlementConservation := Refund.conservation hrefund hcomplete.refundSettled
      cooperativeFloor := fun hns =>
        Refund.T3_B_floor hrefund hcomplete.refundSettled hns
      acceptedValueCharged := hvalues.symm
      allAcceptedValuePaid := hallAccepted
      networkNoOverspend := Network.no_overspend hnetwork
      networkGlobalDedup := Network.global_dedup hnetwork }

end RefundGuarantees

section SchemeGuarantees

variable {F GameMessage : Type}
variable [Field F] [DecidableEq F] [SampleableType F] [Fintype F]
variable [DecidableEq GameMessage]

/-- A proof object for the concrete query-budgeted T7 statement.  Any new
handler-coupling premise enters by constructing this record. -/
structure T7Certificate (mclose : GameMessage)
    (A : F → OracleComp (Games.frameSpec F GameMessage) (Games.Evidence F))
    (qb : Games.FrameQueryBounds A) : Prop where
  bound : Games.frameWinProb mclose A ≤
    ((qb.total + 1 : ℕ) : ENNReal) * (Fintype.card F : ENNReal)⁻¹

/-- The corrected secret-averaged deferred-sampling socket constructs the
scheme-level T7 certificate without adding any trusted declaration. -/
theorem T7Certificate.ofAveraged (mclose : GameMessage)
    (A : F → OracleComp (Games.frameSpec F GameMessage) (Games.Evidence F))
    (qb : Games.FrameQueryBounds A)
    (certificate : Games.FrameDeferredSamplingAvg mclose A qb) :
    T7Certificate mclose A qb :=
  ⟨Games.T7_frame_query_bound_avg mclose A qb certificate⟩

/-- Unified end-to-end guarantee record.  `Operational` is instantiated by
one of the trace-derived records above; T4 and T7 remain scheme-level game
claims, so the symbolic transition systems cannot silently discharge a
cryptographic premise. -/
structure EndToEndGuarantee (Operational : Prop) (scheme : Games.UnlinkScheme)
    (mclose : GameMessage)
    (A : F → OracleComp (Games.frameSpec F GameMessage) (Games.Evidence F))
    (qb : Games.FrameQueryBounds A) : Prop where
  operational : Operational
  t4 : ∀ adversary : Games.UnlinkAdversary scheme,
    Games.unlinkAdvantage scheme adversary = 0
  t7 : T7Certificate mclose A qb

end SchemeGuarantees

section EndToEndAssembly

variable {N : ℕ} {F M P Recipient Nf Payload : Type}
variable [Field F] [DecidableEq F] [SampleableType F] [Fintype F]
variable [DecidableEq M] [DecidableEq P] [DecidableEq Recipient]
variable [DecidableEq Nf] [DecidableEq Payload]
variable {C D τ b Te L : ℕ} {honest : F → Prop}

/-- Complete flat theorem: one synchronized operational trace, the verified
Fiat--Shamir T4 theorem, and an explicit T7 proof certificate. -/
theorem flat_endToEnd
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : FlatLink N F M P Recipient Nf Payload}
    {labels : List (FlatLabel N F M P Recipient Nf Payload)}
    {s : FlatState N F M P Recipient Nf Payload} {key : F}
    {mclose : M}
    {A : F → OracleComp (Games.frameSpec F M) (Games.Evidence F)}
    {qb : Games.FrameQueryBounds A}
    (htrace : LTrace (FlatStep (C := C) (D := D) (τ := τ) (b := b)
      (Te := Te) (honest := honest) H encode link)
      (FlatState.init N F M P Recipient Nf Payload D) labels s)
    (hkey : honest key) (hTe : 0 < Te)
    (hcomplete : FlatComplete L key labels s)
    (t7 : T7Certificate mclose A qb) :
    EndToEndGuarantee
      (FlatOperationalGuarantees (C := C) (D := D) (τ := τ) (b := b)
        (Te := Te) (L := L) (honest := honest) key labels s)
      (Games.fsFlatInstance (F := F) (D / C)) mclose A qb := by
  refine ⟨flatOperational_of_trace htrace hkey hTe hcomplete, ?_, t7⟩
  exact fun adversary => Games.T4_fsFlat_unlinkability (D / C) adversary

variable {Rep GameMessage : Type} [SampleableType Rep]
variable [DecidableEq GameMessage]
variable {Cmax : ℕ}

/-- Complete refund theorem: one synchronized Refund--Network trace, the
patched B-rerandomized T4 theorem, and an explicit T7 proof certificate. -/
theorem refund_endToEnd
    {H : Crypto.LinearSigma.ChallengeOracle F}
    {encode : Network.Credential.Encode F Recipient Nf Payload}
    {link : RefundLink Rep Recipient Nf Payload}
    {labels : List (RefundLabel F Rep Recipient Nf Payload)}
    {s : RefundState Rep Recipient Nf Payload} {r0 : Rep}
    {mclose : GameMessage}
    {A : F → OracleComp (Games.frameSpec F GameMessage) (Games.Evidence F)}
    {qb : Games.FrameQueryBounds A}
    (htrace : LTrace (RefundStep (Cmax := Cmax) (D := D) H encode link)
      (RefundState.init Rep Recipient Nf Payload r0 D) labels s)
    (hcomplete : RefundComplete labels s)
    (t7 : T7Certificate mclose A qb) :
    EndToEndGuarantee
      (RefundOperationalGuarantees (Cmax := Cmax) (D := D) r0 labels s)
      (Games.bRerand Rep Cmax D) mclose A qb := by
  refine ⟨refundOperational_of_trace htrace hcomplete, ?_, t7⟩
  exact fun adversary =>
    Games.unlinkAdvantage_bRerand_eq_zero Rep Cmax D adversary

end EndToEndAssembly

end Zkpc.Composition
