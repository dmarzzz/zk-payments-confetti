import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Zkpc.Spec.Object

/-!
# Flat-ticket symbolic state machine (task D1; Spec.md §2–§3, instantiation A, N = 1)

The single-gateway transition system over which T1–T3 and T5 are stated.
Fleet state (per-gateway spent sets, lag, budgets) lives in `Zkpc.Fleet`
(task G1); rate budgets are deliberately absent here — they only *restrict*
the adversary, so proving T1–T3 without them is strictly stronger.

## Symbolic identifications (Spec.md §5, `Zkpc.Assumptions` table)

- A nullifier *is* its preimage pair `(k, i)`: collision-freeness of the
  domain-separated hash family is absorbed by construction (assumption 3).
- An accepted ticket *is* its extracted witness `(k, i, m)`: knowledge
  soundness is the `accept` guard (assumption 1). Forged proofs do not
  exist in the model.
- Signals for a secret `k` enter `sigs` only through payer actions:
  honest payers via `emitHonest` (protocol-following, MC2), adversarial
  payers via `emitAdv` (arbitrary, including deliberate double-signs).
  That the adversary cannot mint signals for secrets it does not hold is
  the symbolic form of `single_signal_hiding`; the game layer (T7) proves
  the probabilistic statement backing it.

## Time and the ledger

`clock` advances by the `tick` action; the idealized ledger's `Δ`-inclusion
is folded to instantaneous inclusion at the action's clock value, and T5 is
stated against the machine clock with the window `τ` explicit (Spec.md T5's
`t + Δ + τ` bound; the `Δ` re-enters as prose when interpreting machine
time). Window settlement is an always-enabled internal action from expiry
on; liveness statements carry the explicit fairness hypothesis that enabled
settlement is eventually taken.
-/

namespace Zkpc.Core

open Finset

variable (K M : Type) [DecidableEq K] [DecidableEq M]

/-- Machine state, single honest gateway (Spec.md §2). `K` is the secret
sort (symbolic: the secret is the channel identity), `M` the message sort.
The distinguished close message is a designated constant of `M` supplied to
the actions that need it. -/
structure St where
  /-- global machine clock -/
  clock : ℕ
  /-- open channels, by secret (symbolically `cm ≡ k`) -/
  opened : Finset K
  /-- slashed channels, with slash (window-open) time -/
  slashedAt : K → Option ℕ
  /-- payer-closes: `(k, declared index j, inclusion time)`; at most one per `k` -/
  closedAt : K → Option (ℕ × ℕ)
  /-- next index of each protocol-following payer (MC2: emission consumes) -/
  emittedCnt : K → ℕ
  /-- all emitted signals `(k, i, m)` — honest and adversarial -/
  sigs : Finset (K × ℕ × M)
  /-- the gateway's accepted spent set (Spec.md §2 Redeem, accept branch) -/
  acc : Finset (K × ℕ × M)
  /-- ledger `RedeemedNF`: swept nullifiers `(k, i)` (MC16 dedup) -/
  swept : Finset (K × ℕ)
  /-- cumulative payer settlements -/
  paidPayer : K → ℕ
  /-- cumulative gateway sweep revenue -/
  paidGw : ℕ
  /-- whether the close of `k` has settled (window expired and paid) -/
  closeSettled : K → Bool

variable {K M}

namespace St

/-- The accepted tickets attributed (by extractor, symbolically: first
component) to secret `k`. -/
def accOf (s : St K M) (k : K) : Finset (K × ℕ × M) :=
  s.acc.filter (fun t => t.1 = k)

/-- Attributed accepted value for `k` at flat price `C` (Spec.md T1). -/
def valueOf (s : St K M) (k : K) (C : ℕ) : ℕ :=
  C * (s.accOf k).card

/-- A channel is live: open, unslashed, unclosed. -/
def live (s : St K M) (k : K) : Prop :=
  k ∈ s.opened ∧ s.slashedAt k = none ∧ s.closedAt k = none

instance (s : St K M) (k : K) : Decidable (s.live k) := by
  unfold live; infer_instance

end St

/-- Initial state. -/
def init : St K M where
  clock := 0
  opened := ∅
  slashedAt := fun _ => none
  closedAt := fun _ => none
  emittedCnt := fun _ => 0
  sigs := ∅
  acc := ∅
  swept := ∅
  paidPayer := fun _ => 0
  paidGw := 0
  closeSettled := fun _ => false

variable (K M)

/-- Transition labels. `honest : K → Prop` marks protocol-following payers;
`mclose : M` is the distinguished close message (Spec.md §2 Close). -/
inductive Act
  /-- time passes -/
  | tick
  /-- `Open` (Spec.md §2): register `k`, escrow `D` -/
  | openCh (k : K)
  /-- protocol-following emission at the payer's next index (MC2) -/
  | emitHonest (k : K) (m : M)
  /-- adversarial emission: any signal for a secret the adversary holds -/
  | emitAdv (k : K) (i : ℕ) (m : M)
  /-- `Redeem` accept branch (checks of Spec.md §2; knowledge soundness as guard) -/
  | accept (k : K) (i : ℕ) (m : M)
  /-- `Dispute` on a conflicting pair (permissionless; two existing signals) -/
  | slash (k : K) (i : ℕ) (m m' : M)
  /-- payer close-as-final-spend at declared index `j` (MC1) -/
  | payerClose (k : K) (j : ℕ)
  /-- ledger settlement of an expired close window (automatic contract logic) -/
  | settleClose (k : K)
  /-- gateway sweep of one accepted, unswept tuple (MC16: gateway-only) -/
  | sweepOne (k : K) (i : ℕ) (m : M)

variable {K M}

/-- The step relation. Parameters: flat price `C`, deposit `D`, window `τ`,
the honest-payer predicate, and the distinguished close message.

Guards are the semantic content of Spec.md §2's checks; every guard is
annotated with its Spec.md source. -/
inductive Step (C D τ : ℕ) (honest : K → Prop) (mclose : M) :
    St K M → Act K M → St K M → Prop
  | tick (s : St K M) :
      Step C D τ honest mclose s .tick { s with clock := s.clock + 1 }
  | openCh (s : St K M) (k : K)
      (hnew : k ∉ s.opened) :
      Step C D τ honest mclose s (.openCh k) { s with opened := insert k s.opened }
  | emitHonest (s : St K M) (k : K) (m : M)
      (hh : honest k)
      (hlive : s.live k)
      (hm : m ≠ mclose)
      -- solvency at the next index (Spec.md §3, R_spend conjunct 2);
      -- an honest payer only emits while solvent (`Spend` returns ⊥ otherwise)
      (hsolv : (s.emittedCnt k + 1) * C ≤ D) :
      Step C D τ honest mclose s (.emitHonest k m)
        { s with sigs := insert (k, s.emittedCnt k, m) s.sigs
                 emittedCnt := Function.update s.emittedCnt k (s.emittedCnt k + 1) }
  | emitAdv (s : St K M) (k : K) (i : ℕ) (m : M)
      -- the adversary holds only adversarial secrets (symbolic single_signal_hiding)
      (hadv : ¬ honest k) :
      Step C D τ honest mclose s (.emitAdv k i m)
        { s with sigs := insert (k, i, m) s.sigs }
  | accept (s : St K M) (k : K) (i : ℕ) (m : M)
      -- the ticket exists: knowledge soundness (assumption 1) — an accepted
      -- proof has an extracted witness, i.e. an emitted signal
      (hsig : (k, i, m) ∈ s.sigs)
      (hm : m ≠ mclose)
      -- check 2: root current — channel open and unslashed and unclosed
      (hlive : s.live k)
      -- R_spend conjunct 2: solvency (Spec.md §3)
      (hsolv : (i + 1) * C ≤ D)
      -- check 6: nullifier (k, i) fresh at this gateway
      (hfresh : ∀ m', (k, i, m') ∉ s.acc) :
      Step C D τ honest mclose s (.accept k i m)
        { s with acc := insert (k, i, m) s.acc }
  | slash (s : St K M) (k : K) (i : ℕ) (m m' : M)
      -- Dispute validation (Spec.md §2): two well-formed signals on the
      -- same (k, i) with different messages; the line algebra recovers k
      (h1 : (k, i, m) ∈ s.sigs) (h2 : (k, i, m') ∈ s.sigs) (hne : m ≠ m')
      (hopen : k ∈ s.opened) (hns : s.slashedAt k = none) :
      Step C D τ honest mclose s (.slash k i m m')
        { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
  | payerClose (s : St K M) (k : K) (j : ℕ)
      (hlive : s.live k)
      -- the close signal at declared index j on m_close (MC1); honest
      -- closers use j = emittedCnt k, dishonest may declare anything —
      -- understatement collides with an existing signal and is slashable
      (hj : honest k → j = s.emittedCnt k) :
      Step C D τ honest mclose s (.payerClose k j)
        { s with sigs := insert (k, j, mclose) s.sigs
                 closedAt := Function.update s.closedAt k (some (j, s.clock)) }
  | settleClose (s : St K M) (k : K) (j t : ℕ)
      (hc : s.closedAt k = some (j, t))
      -- window τ expired, channel not slashed during it (Spec.md §2 Close:
      -- settlement automatic at expiry)
      (hexp : t + τ ≤ s.clock)
      (hns : s.slashedAt k = none)
      (hnotYet : s.closeSettled k = false) :
      Step C D τ honest mclose s (.settleClose k)
        { s with paidPayer := Function.update s.paidPayer k (s.paidPayer k + (D - j * C))
                 closeSettled := Function.update s.closeSettled k true }
  | sweepOne (s : St K M) (k : K) (i : ℕ) (m : M)
      -- MC16: only the (single, honest) gateway sweeps, only its accepted
      -- tuples, deduped by nullifier on the ledger
      (hacc : (k, i, m) ∈ s.acc)
      (hdedup : (k, i) ∉ s.swept)
      -- post-slash sweeps only inside the priority window (MC4)
      (hwin : ∀ ts, s.slashedAt k = some ts → s.clock ≤ ts + τ) :
      Step C D τ honest mclose s (.sweepOne k i m)
        { s with swept := insert (k, i) s.swept
                 paidGw := s.paidGw + C }

/-- Reachability from `init` under the step relation. -/
inductive Reach (C D τ : ℕ) (honest : K → Prop) (mclose : M) : St K M → Prop
  | init : Reach C D τ honest mclose init
  | step {s s' : St K M} {a : Act K M} :
      Reach C D τ honest mclose s → Step C D τ honest mclose s a s' →
      Reach C D τ honest mclose s'

end Zkpc.Core
