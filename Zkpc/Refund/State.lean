import Mathlib.Data.Finset.Card

/-!
# Refund-variant (instantiation B) symbolic settlement machine (tasks H1/H2/H4; Spec.md §4, §2 MC18/MC20)

The single-channel transition system for instantiation B's **close-time
netting** (Spec.md MC18): a refund-bearing channel settles exactly once, at
close, with the two settlement caps and the conserving payer/payee split.
This is the B analogue of `Zkpc.Core.State` (the flat-ticket machine), scoped
to what tasks H1/H2/H4 need: the certified refund chain `(R, n)`, the B
solvency inequality `(i+1)·C_max ≤ D + R`, and the MC18 settlement arithmetic
`((D+R) − j·C_max)` payer / `(j·C_max − R)` payee.

## Symbolic identifications (Spec.md §4, §5)

- The certified object is the pair `(R, n)` in the clear (Spec.md §4: "the
  payer tracks `(R, n)` in plaintext; no honest algorithm ever decrypts").
  `St.idx` is the certified count `n` (= next spend index, contiguous by
  construction, MC20/rev-6); `St.R` is the certified refund total. Per accept,
  the payee declares actual cost `c ≤ C_max` and the chain grows by the refund
  `C_max − c` and increments the count (Spec.md §4). Knowledge soundness /
  EUF-CMA are the `accept` guard: an accepted spend *is* one whose receipt was
  honestly issued to this channel.
- **Chain tag binding (MC7) = per-channel receipt structure (H1).** `St.R`
  is a per-machine (per-channel) field: there is no channel-to-channel receipt
  transport in the model, so cross-channel splicing (the rev-1 blocking
  finding the tag `H_tag(k)` excludes) is structurally impossible here. The
  tag is the identity of "this channel's `R`".

## The E(R) representation is a parameter the safety layer ignores (H2)

The machine is generic over the ciphertext representation type `Rep` of the
certified total (Spec.md §4: B-static presents `ct` bit-identically, B-rerand
presents a re-randomization). The settlement/solvency logic reads only the
plaintext `R : ℕ` and `n : ℕ`; the representation `rep : Rep` is threaded but
**never guarded on**. So "both representations compile" (H2) is the single
statement that every theorem below holds for *every* `Rep` — a
representation-generic machine, instantiable at B-static's and B-rerand's
representation types alike.

## GATE-NOTE register

* **GATE-NOTE (single channel).** Stated for one channel (`N = 1`, Spec.md
  §4). T1-B/T3-B/conservation are per-channel statements; the fleet layer
  (`Zkpc.Fleet`) composes channels and is out of scope for H1/H2/H4.
* **GATE-NOTE (upgrade sub-window not modeled — one round only).** The
  machine models a *single* close round: the honest closer presents its
  latest receipt at the true count `n`. The rev-7/8 receipt-withholding
  **upgrade sub-window cascade** (a stale close disputed, the withheld
  receipt published, the payer re-closing one count higher — Spec.md §2, T2-B
  "up to one round per understated count") is NOT modeled: there is one
  `close` action, guarded to be at the certified count. The honest-payer case
  Spec.md T5 bounds at one round, so the single-round model is faithful for
  the honest closer whose floor T3-B protects; the multi-round adversarial
  cascade against a *stale* close is the deferred follow-up.
* **GATE-NOTE (force-close forfeit = fund-slash path).** `forceClose` models
  Spec.md MC18's force-close-with-forfeit for a silent/abandoned channel and,
  equivalently, the rev-10 F9-1b fund-slash settlement (a failed upgrade
  whose `k`-gated per-nullifier claims cannot run): the payee takes the whole
  deposit `D`, the payer nothing. It settles the channel (conserving `D`) and
  marks it slashed, which is exactly the path task H5 cites.
-/

namespace Zkpc.Refund

variable {Rep : Type}

/-- Single B channel state (Spec.md §4). `idx` is the certified count `n`
(= next spend index), `R` the certified refund total, `sumc` the running
`Σ c_ℓ` of accepted declared costs, `rep` the opaque `E(R)` representation
(H2: never inspected). The settlement bookkeeping (`payerPay`, `payeePay`,
`closed`, `settled`, `slashed`) records the MC18 close outcome. -/
structure St (Rep : Type) where
  /-- certified count `n` = next spend index (contiguous, MC20) -/
  idx : ℕ
  /-- certified refund total `R = Σ (C_max − c_ℓ)` -/
  R : ℕ
  /-- running total of accepted declared costs `Σ c_ℓ` -/
  sumc : ℕ
  /-- opaque `E(R)` ciphertext representation (H2: threaded, never guarded) -/
  rep : Rep
  /-- channel has closed (no more spends) -/
  closed : Bool
  /-- channel has settled once (MC18: settles exactly once) -/
  settled : Bool
  /-- channel settled by a slash/forfeit path (force-close), not cooperatively -/
  slashed : Bool
  /-- cumulative payer settlement -/
  payerPay : ℕ
  /-- cumulative payee settlement -/
  payeePay : ℕ

/-- Genesis state at `Open` (Spec.md §2): certified count and refund zero,
carrying the genesis representation `r0`. -/
def St.init (r0 : Rep) : St Rep :=
  ⟨0, 0, 0, r0, false, false, false, 0, 0⟩

/-- Transition labels (Spec.md §4/§2, B). -/
inductive Act (Rep : Type)
  /-- payee accepts a spend, declares actual cost `c`, issues the incremented
  receipt (new representation `r'`); the certified `(R, n)` grows -/
  | accept (c : ℕ) (r' : Rep)
  /-- payer closes cooperatively at the certified count `n` (MC18 netting) -/
  | close
  /-- payee force-closes a silent/abandoned channel with forfeit (MC18;
  fund-slash path, rev-10 F9-1b) -/
  | forceClose

/-- The B step relation (Spec.md §4 spend/§2 MC18 close). Parameters: the
per-spend cap `C_max` and the deposit `D`. Guards are the semantic content of
`R_spend^B` / `R_close^B`. -/
inductive Step (Cmax D : ℕ) : St Rep → Act Rep → St Rep → Prop
  /-- Accept a spend at the certified count `n = idx` (contiguity by
  construction, MC20), declared cost `c ≤ C_max`, under B solvency
  `(idx+1)·C_max ≤ D + R` (Spec.md §4). The certified total grows by the
  refund `C_max − c` and the count by one; the new representation `r'` is the
  payee's incremented ciphertext (H2: unconstrained). -/
  | accept (s : St Rep) (c : ℕ) (r' : Rep)
      (hlive : s.closed = false)
      (hc : c ≤ Cmax)
      (hsolv : (s.idx + 1) * Cmax ≤ D + s.R) :
      Step Cmax D s (.accept c r')
        { s with idx := s.idx + 1, R := s.R + (Cmax - c),
                 sumc := s.sumc + c, rep := r' }
  /-- Cooperative close at the certified count `j = idx` (Spec.md MC18): the
  two caps `R ≤ j·C_max` and `j·C_max ≤ D + R` hold by the reachable
  invariant; payouts are `(D+R) − j·C_max` (payer) and `j·C_max − R` (payee,
  `= Σ c_ℓ`). Settles once. -/
  | close (s : St Rep)
      (hlive : s.closed = false) :
      Step Cmax D s .close
        { s with closed := true, settled := true,
                 payerPay := (D + s.R) - s.idx * Cmax,
                 payeePay := s.idx * Cmax - s.R }
  /-- Force-close with forfeit (Spec.md MC18; the fund-slash path): the payee
  takes the whole deposit `D`, the payer nothing; the channel is marked
  slashed and settled. -/
  | forceClose (s : St Rep)
      (hlive : s.closed = false) :
      Step Cmax D s .forceClose
        { s with closed := true, settled := true, slashed := true,
                 payerPay := 0, payeePay := D }

/-- Reachability from genesis under the B step relation. -/
inductive Reach (Rep : Type) (Cmax D : ℕ) (r0 : Rep) : St Rep → Prop
  | init : Reach Rep Cmax D r0 (St.init r0)
  | step {s s' : St Rep} {a : Act Rep} :
      Reach Rep Cmax D r0 s → Step Cmax D s a s' → Reach Rep Cmax D r0 s'

end Zkpc.Refund
