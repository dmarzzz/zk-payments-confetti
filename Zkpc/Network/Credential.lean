import Zkpc.Network.State
import Zkpc.Crypto.LinearSigma

/-!
# Concrete proof-bearing portable network tickets

A ticket binds its recipient, global nullifier, value, and payload into the
public line coordinate, and carries a Fiat--Shamir proof for the corresponding
RLN statement. Verification is performed before the ticket is translated into
the shared-deposit accounting event. The refinement theorem connects a valid,
fresh credential redemption directly to `Network.Step.accept`.
-/

namespace Zkpc.Network.Credential

open Zkpc.Crypto.LinearSigma

variable {F Recipient Nf Payload : Type}
variable [Field F] [DecidableEq F]
variable [DecidableEq Recipient] [DecidableEq Nf] [DecidableEq Payload]

/-- Application encoding committed into the proof statement. -/
abbrev Encode (F Recipient Nf Payload : Type) :=
  Recipient → Nf → ℕ → Payload → F

/-- Portable recipient-directed credential. -/
structure Ticket (F Recipient Nf Payload : Type) where
  recipient : Recipient
  nf : Nf
  value : ℕ
  payload : Payload
  statement : Statement F
  proof : FSProof F

/-- Accounting event carried by a ticket. -/
def Ticket.event (t : Ticket F Recipient Nf Payload) :
    Network.Event Recipient Nf Payload :=
  ⟨t.recipient, t.nf, t.value, t.payload⟩

/-- Verification binds all application fields into the line coordinate and
checks the concrete Fiat--Shamir proof. -/
def WellFormed (H : ChallengeOracle F) (encode : Encode F Recipient Nf Payload)
    (t : Ticket F Recipient Nf Payload) : Prop :=
  t.statement.x = nonzeroX (encode t.recipient t.nf t.value t.payload) ∧
  FSVerify H t.statement t.proof

instance (H : ChallengeOracle F) (encode : Encode F Recipient Nf Payload)
    (t : Ticket F Recipient Nf Payload) : Decidable (WellFormed H encode t) := by
  unfold WellFormed FSVerify Verify fsTranscript
  infer_instance

/-- Construct an honestly proved portable ticket from an RLN line witness. -/
def issue (H : ChallengeOracle F) (encode : Encode F Recipient Nf Payload)
    (recipient : Recipient) (nf : Nf) (value : ℕ) (payload : Payload)
    (w : Witness F) (r : Randomness F) : Ticket F Recipient Nf Payload :=
  let x := nonzeroX (encode recipient nf value payload)
  let st : Statement F := ⟨x, w.k + w.a * x⟩
  ⟨recipient, nf, value, payload, st, fsProve H st w r⟩

/-- Honest issuance always verifies. -/
theorem issue_wellFormed (H : ChallengeOracle F)
    (encode : Encode F Recipient Nf Payload)
    (recipient : Recipient) (nf : Nf) (value : ℕ) (payload : Payload)
    (w : Witness F) (r : Randomness F) :
    WellFormed H encode (issue H encode recipient nf value payload w r) := by
  refine ⟨rfl, fs_completeness H _ w r ?_⟩
  rfl

/-- Verify and register a credential in the portable-deposit network. -/
def redeem (H : ChallengeOracle F) (encode : Encode F Recipient Nf Payload)
    (s : Network.St Recipient Nf Payload)
    (t : Ticket F Recipient Nf Payload) :
    Option (Network.St Recipient Nf Payload) :=
  if WellFormed H encode t then Network.execAccept s t.event else none

/-- Successful credential redemption is exactly a network admission step. -/
theorem redeem_refines (H : ChallengeOracle F)
    (encode : Encode F Recipient Nf Payload)
    (s : Network.St Recipient Nf Payload)
    (t : Ticket F Recipient Nf Payload)
    (hvalid : WellFormed H encode t)
    (hfresh : ∀ old ∈ s.accepted, old.nf ≠ t.nf) :
    ∃ s', redeem H encode s t = some s' ∧
      Network.Step s (.accept t.event) s' := by
  rw [redeem, if_pos hvalid]
  exact Network.execAccept_refines s t.event hfresh

/-- A nullifier already admitted for any recipient is rejected globally,
including an attempted replay directed at a different recipient. -/
theorem redeem_rejects_global_replay (H : ChallengeOracle F)
    (encode : Encode F Recipient Nf Payload)
    (s : Network.St Recipient Nf Payload)
    (t : Ticket F Recipient Nf Payload)
    (old : Network.Event Recipient Nf Payload) (hold : old ∈ s.accepted)
    (hnf : old.nf = t.nf) :
    redeem H encode s t = none := by
  have hnotfresh : ¬ (∀ e ∈ s.accepted, e.nf ≠ t.event.nf) := by
    intro hfresh
    exact hfresh old hold hnf
  unfold redeem
  split
  · simp [Network.execAccept, hnotfresh]
  · rfl

/-- End-to-end portable payment composition: a verified fresh credential is
registered, settled once, remains within the shared deposit, and produces a
state reachable by the network transition system. -/
theorem credential_payment_end_to_end (H : ChallengeOracle F)
    (encode : Encode F Recipient Nf Payload) (D : ℕ)
    (s : Network.St Recipient Nf Payload) (hreach : Network.Reach D s)
    (t : Ticket F Recipient Nf Payload) (hvalid : WellFormed H encode t)
    (hfresh : ∀ old ∈ s.accepted, old.nf ≠ t.nf)
    (hbudget : s.totalPaid + t.value ≤ s.deposit) :
    ∃ s₁ s₂,
      redeem H encode s t = some s₁ ∧
      Network.execSettle s₁ t.event = some s₂ ∧
      Network.Reach D s₂ ∧ s₂.totalPaid ≤ D := by
  obtain ⟨s₁, hredeem, hadmit⟩ := redeem_refines H encode s t hvalid hfresh
  have hreach₁ : Network.Reach D s₁ := Network.Reach.step hreach hadmit
  have haccepted : t.event ∈ s₁.accepted := by
    cases hadmit
    simp [Ticket.event]
  have hunpaid : t.event ∉ s₁.settled := by
    cases hadmit
    intro hsettled
    have hold : t.event ∈ s.accepted := (Network.reach_inv hreach).settled_sub hsettled
    exact hfresh t.event hold rfl
  have hbudget₁ : s₁.totalPaid + t.event.value ≤ s₁.deposit := by
    cases hadmit
    exact hbudget
  obtain ⟨s₂, hsettle, hstep₂⟩ :=
    Network.execSettle_refines s₁ t.event haccepted hunpaid hbudget₁
  have hreach₂ : Network.Reach D s₂ := Network.Reach.step hreach₁ hstep₂
  exact ⟨s₁, s₂, hredeem, hsettle, hreach₂, Network.no_overspend hreach₂⟩

end Zkpc.Network.Credential

#print axioms Zkpc.Network.Credential.issue_wellFormed
#print axioms Zkpc.Network.Credential.redeem_refines
#print axioms Zkpc.Network.Credential.redeem_rejects_global_replay
#print axioms Zkpc.Network.Credential.credential_payment_end_to_end
