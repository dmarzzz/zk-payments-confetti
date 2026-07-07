import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Zkpc.Spec.Object

/-!
# Flat-ticket symbolic state machine (task D1; Spec.md rev-7 §2–§3, instantiation A, N = 1)

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

## Close semantics (MC20, rev-7: "close-by-unused-enumeration")

There is **no close signal**. A payer closes by publishing the set `U` of
its claimed-unused indices' nullifiers — symbolically, the index set
itself (a nullifier *is* `(k, i)` and the closing `k` is public at close).
`π_close` well-formedness (each `nf ∈ U` is `H_nf(H_a(k, i))` for a
distinct `i < cap := ⌊D/C⌋`) is the `payerClose` guards; an honest closer
enumerates exactly its unused indices `{i | emittedCnt ≤ i < cap}`.
Settlement at window expiry pays `C·|U| + (D − cap·C)` and thereafter
bars every `nf ∈ U` from sweeps (the rev-6 sweep bar — `sweepOne`'s
`hbar` guard). The bar is **two-sided** (rev-7 F7-2, rev-8): settlement
itself first checks `U` against the already-swept nullifiers — any
overlap is a proven-false claim, and the close is voided and slashed
instead of settling (`settleVoid`; `settleClose`'s `hswbar` guard). The
two sides together conserve the pool in both orderings: swept-then-close
voids, close-then-settled bars. A false unused-claim (an index actually
accepted) is additionally disputable within the window by bit-match
against the accepting gateway's pre-close checkpoint (`closeDispute`),
voiding the close and slashing.

**Checkpoint modeling note (MC19/MC20):** in this honest-single-gateway
machine every entry of `acc` predates any given close (the `accept` guard
requires the channel live, i.e. unclosed), so `acc` *is* the pre-close
checkpoint and `closeDispute` matches directly against it. Checkpoint
*cadence* — the fleet-facing staleness lever of Spec.md §2 — has no
content at `N = 1` with an always-current checkpoint; it enters with the
fleet model (task G1).

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
sort (symbolically the secret is the channel identity), `M` the message
sort. -/
structure St where
  /-- global machine clock -/
  clock : ℕ
  /-- open channels, by secret (symbolically `cm ≡ k`) -/
  opened : Finset K
  /-- slashed channels, with slash (window-open) time -/
  slashedAt : K → Option ℕ
  /-- payer-closes (MC20): `(k, claimed-unused index set U, inclusion time)`;
  at most one per `k` -/
  closedAt : K → Option (Finset ℕ × ℕ)
  /-- next index of each protocol-following payer (MC2: emission consumes) -/
  emittedCnt : K → ℕ
  /-- all emitted signals `(k, i, m)` — honest and adversarial -/
  sigs : Finset (K × ℕ × M)
  /-- the gateway's accepted spent set (Spec.md §2 Redeem, accept branch);
  also the pre-close checkpoint (see the header note) -/
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

/-- The MC20 sweep bar (Spec.md §2 Close A, rev-6 blocking find): nullifier
`(k, i)` was recorded as claimed-unused in a *settled* close of `k`, so the
ledger refuses to sweep it — a refunded nullifier is never also paid as
sweep revenue, and the commingled pool conserves. -/
def sweepBarred (s : St K M) (k : K) (i : ℕ) : Prop :=
  ∃ U t, s.closedAt k = some (U, t) ∧ s.closeSettled k = true ∧ i ∈ U

instance (s : St K M) (k : K) (i : ℕ) : Decidable (s.sweepBarred k i) := by
  unfold sweepBarred
  cases hc : s.closedAt k with
  | none => exact isFalse (by rintro ⟨U, t, h, -, -⟩; exact nomatch h)
  | some p =>
    refine decidable_of_iff (s.closeSettled k = true ∧ i ∈ p.1)
      ⟨fun h => ⟨p.1, p.2, rfl, h.1, h.2⟩, ?_⟩
    rintro ⟨U, t, h, h1, h2⟩
    obtain rfl := Option.some.inj h
    exact ⟨h1, h2⟩

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

/-- Transition labels. `honest : K → Prop` marks protocol-following payers.
There is no distinguished close message: under MC20 (rev-7) a close emits
no signal at all, only the unused-index enumeration `U`. -/
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
  /-- payer close-by-unused-enumeration at claimed-unused index set `U` (MC20) -/
  | payerClose (k : K) (U : Finset ℕ)
  /-- MC20 close-dispute: a registered gateway disproves an unused-claim by
  bit-match of an accepted ticket against the claimed set `U` -/
  | closeDispute (k : K) (i : ℕ) (m : M)
  /-- ledger settlement of an expired close window (automatic contract logic) -/
  | settleClose (k : K)
  /-- ledger voiding of an expired close whose claimed set overlaps the
  swept nullifiers — the settlement-time side of the two-sided bar
  (rev-7 F7-2): proven-false claim, slash instead of payout -/
  | settleVoid (k : K)
  /-- gateway sweep of one accepted, unswept, unbarred tuple (MC16 + MC20 bar) -/
  | sweepOne (k : K) (i : ℕ) (m : M)

variable {K M}

/-- The step relation. Parameters: flat price `C`, deposit `D`, window `τ`,
and the honest-payer predicate.

Guards are the semantic content of Spec.md §2's checks; every guard is
annotated with its Spec.md source. -/
inductive Step (C D τ : ℕ) (honest : K → Prop) :
    St K M → Act K M → St K M → Prop
  | tick (s : St K M) :
      Step C D τ honest s .tick { s with clock := s.clock + 1 }
  | openCh (s : St K M) (k : K)
      (hnew : k ∉ s.opened) :
      Step C D τ honest s (.openCh k) { s with opened := insert k s.opened }
  | emitHonest (s : St K M) (k : K) (m : M)
      (hh : honest k)
      (hlive : s.live k)
      -- solvency at the next index (Spec.md §3, R_spend conjunct 2);
      -- an honest payer only emits while solvent (`Spend` returns ⊥ otherwise)
      (hsolv : (s.emittedCnt k + 1) * C ≤ D) :
      Step C D τ honest s (.emitHonest k m)
        { s with sigs := insert (k, s.emittedCnt k, m) s.sigs
                 emittedCnt := Function.update s.emittedCnt k (s.emittedCnt k + 1) }
  | emitAdv (s : St K M) (k : K) (i : ℕ) (m : M)
      -- the adversary holds only adversarial secrets (symbolic single_signal_hiding)
      (hadv : ¬ honest k) :
      Step C D τ honest s (.emitAdv k i m)
        { s with sigs := insert (k, i, m) s.sigs }
  | accept (s : St K M) (k : K) (i : ℕ) (m : M)
      -- the ticket exists: knowledge soundness (assumption 1) — an accepted
      -- proof has an extracted witness, i.e. an emitted signal
      (hsig : (k, i, m) ∈ s.sigs)
      -- check 2: root current — channel open and unslashed and unclosed
      (hlive : s.live k)
      -- R_spend conjunct 2: solvency (Spec.md §3)
      (hsolv : (i + 1) * C ≤ D)
      -- check 6: nullifier (k, i) fresh at this gateway
      (hfresh : ∀ m', (k, i, m') ∉ s.acc) :
      Step C D τ honest s (.accept k i m)
        { s with acc := insert (k, i, m) s.acc }
  | slash (s : St K M) (k : K) (i : ℕ) (m m' : M)
      -- Dispute validation (Spec.md §2): two well-formed signals on the
      -- same (k, i) with different messages; the line algebra recovers k
      (h1 : (k, i, m) ∈ s.sigs) (h2 : (k, i, m') ∈ s.sigs) (hne : m ≠ m')
      (hopen : k ∈ s.opened) (hns : s.slashedAt k = none) :
      Step C D τ honest s (.slash k i m m')
        { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
  | payerClose (s : St K M) (k : K) (U : Finset ℕ)
      (hlive : s.live k)
      -- π_close well-formedness (MC20): each claimed-unused nullifier sits
      -- at a distinct index below cap = ⌊D/C⌋ (distinctness is `U : Finset`)
      (hUlt : ∀ i ∈ U, i < D / C)
      -- an honest closer enumerates exactly its unused indices
      -- {i | emittedCnt ≤ i < cap}; a dishonest closer claims anything —
      -- a false claim (used index in U) is `closeDispute`-able, an
      -- under-claim only donates (Spec.md §2 Close A)
      (hUeq : honest k →
        U = (Finset.range (D / C)).filter (fun i => s.emittedCnt k ≤ i)) :
      Step C D τ honest s (.payerClose k U)
        { s with closedAt := Function.update s.closedAt k (some (U, s.clock)) }
  | closeDispute (s : St K M) (k : K) (i : ℕ) (m : M) (U : Finset ℕ) (t : ℕ)
      -- MC20 window dispute: an index claimed unused ...
      (hc : s.closedAt k = some (U, t))
      (hiU : i ∈ U)
      -- ... is bit-matched against an acceptance in the pre-close
      -- checkpoint (= `acc` here; see the header checkpoint note) ...
      (hacc : (k, i, m) ∈ s.acc)
      -- ... within the close window, before settlement
      (hwin : s.clock ≤ t + τ)
      (hnotYet : s.closeSettled k = false) :
      -- effect: the channel freezes — the false claim voids the close
      -- (settleClose's no-slash guard now blocks settlement forever) and
      -- the channel is slashed (Spec.md §2 Close A, window branch (a))
      Step C D τ honest s (.closeDispute k i m)
        { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
  | settleClose (s : St K M) (k : K) (U : Finset ℕ) (t : ℕ)
      (hc : s.closedAt k = some (U, t))
      -- window τ expired, close not voided by a dispute (Spec.md §2 Close:
      -- settlement automatic at expiry)
      (hexp : t + τ ≤ s.clock)
      (hns : s.slashedAt k = none)
      -- settlement-time bar check (rev-7 F7-2, two-sided bar): no claimed
      -- index was already swept — else the claim is proven false and the
      -- close voids instead (`settleVoid`)
      (hswbar : ∀ i ∈ U, (k, i) ∉ s.swept)
      (hnotYet : s.closeSettled k = false) :
      -- MC20 payout: C per proven-unused index plus the sub-ticket residue
      -- D − cap·C; on the honest path |U| = cap − j and this is D − j·C
      Step C D τ honest s (.settleClose k)
        { s with paidPayer := Function.update s.paidPayer k
                   (s.paidPayer k + (C * U.card + (D - (D / C) * C)))
                 closeSettled := Function.update s.closeSettled k true }
  | settleVoid (s : St K M) (k : K) (U : Finset ℕ) (t : ℕ)
      (hc : s.closedAt k = some (U, t))
      -- the check happens at settlement time (same timing as settleClose)
      (hexp : t + τ ≤ s.clock)
      (hns : s.slashedAt k = none)
      (hnotYet : s.closeSettled k = false)
      -- the overlap: a claimed-unused nullifier was already swept, so the
      -- claim is proven false on the ledger's own records (rev-7 F7-2)
      (hover : ∃ i ∈ U, (k, i) ∈ s.swept) :
      -- effect: void + slash, no payout (settleClose's hns guard then
      -- blocks settlement forever)
      Step C D τ honest s (.settleVoid k)
        { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
  | sweepOne (s : St K M) (k : K) (i : ℕ) (m : M)
      -- MC16: only the (single, honest) gateway sweeps, only its accepted
      -- tuples, deduped by nullifier on the ledger
      (hacc : (k, i, m) ∈ s.acc)
      (hdedup : (k, i) ∉ s.swept)
      -- post-slash sweeps only inside the priority window (MC4)
      (hwin : ∀ ts, s.slashedAt k = some ts → s.clock ≤ ts + τ)
      -- MC20 sweep bar: nullifiers refunded by a settled close are not
      -- sweepable (rev-6: else a false unused-claim uncaught by a stale
      -- checkpoint is paid twice and the pool bears it)
      (hbar : ¬ s.sweepBarred k i) :
      Step C D τ honest s (.sweepOne k i m)
        { s with swept := insert (k, i) s.swept
                 paidGw := s.paidGw + C }

/-- Reachability from `init` under the step relation. -/
inductive Reach (C D τ : ℕ) (honest : K → Prop) : St K M → Prop
  | init : Reach C D τ honest init
  | step {s s' : St K M} {a : Act K M} :
      Reach C D τ honest s → Step C D τ honest s a s' →
      Reach C D τ honest s'

end Zkpc.Core
