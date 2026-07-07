import Zkpc.Core.T1

/-!
# T3 — Payer balance security (task D4; Spec.md §7 T3, flat ticket)

Spec.md T3 has two clauses against a malicious-payee adversary:

* **The floor:** an honest payer with deposit `D` that emitted `j` spend
  tickets recovers `D − j·C` via `Close` and the elapse of the dispute
  window. Here: `payer_pay_inv` (settlement pays exactly once and exactly
  the close formula), `settleClose_enabled` (the settlement step is
  available from window expiry on, with the no-slash guard discharged by
  `honest_never_slashed`), and `T3_settled_amount` (the settled amount is
  `D − j·C` with `j` the payer's emission count — stated additively,
  `paid + j·C = D`, so no ℕ-truncation ambiguity).
* **No framing:** no adversary produces `Dispute` evidence that slashes an
  honest payer. In the symbolic model this is `honest_never_slashed`
  (Zkpc.Core.T1); the probabilistic complement is T7's FRAME game.

`T3_payer_balance_security` bundles both clauses. The path from "enabled"
to "taken" — that the always-enabled settlement actually fires — is T5
(`Zkpc.Core.T5`), per Spec.md's rev-1 de-circularization (T2/T3 own the
amounts, T5 owns the deadline).

GATE-NOTE (deltas between Spec.md T3 and these statements):
1. *"At least" vs "exactly".* Spec.md says the payer recovers *at least*
   `D − j·C`. The flat machine has exactly one payer income event
   (`settleClose`, guarded to fire once), so we prove the stronger
   equality `paidPayer k + j·C = D`. "At least" would be the faithful
   reading if other income paths existed; here equality implies it.
2. *`j` = emitted count.* Spec.md's floor is stated against *emitted*
   tickets (MC2: emission is the authorization event). The machine forces
   an honest closer to declare `j = emittedCnt k` (guard `hj` of
   `payerClose`), and `HonestSig` carries `closedAt = some (j, t) →
   j = emittedCnt k` forward (the counter freezes at close, since honest
   emission requires a live channel). So "emitted `j` tickets" and "the
   declared close index" coincide for honest payers — the off-by-one audit
   of Spec.md T3 scope note (iii): the close signal occupies index `j` and
   is not charged.
3. *Refund variant.* This file is instantiation A only (flat price); the
   `D − j·C_max + R` clause of T3-B is task H4, out of scope here.
4. *Timing.* As in T2/T5, the ledger's `Δ` is folded to instantaneous
   inclusion at the action's machine time (State.lean header).
-/

namespace Zkpc.Core

open Finset

variable {K M : Type} [DecidableEq K] [DecidableEq M]
variable {C D τ : ℕ} {honest : K → Prop} {mclose : M}

/-- Payer-settlement invariant (Spec.md §2 Close, payer side):
(1) before its close window has settled, a payer has been paid nothing;
(2) once settled, it has been paid exactly `D − j·C` for its recorded
    close index `j` — the automatic-settlement formula, paid exactly once
    (the `closeSettled` guard);
(3) an honest payer's emission counter never outruns solvency:
    `emittedCnt·C ≤ D` (the `Spend` guard, R_spend conjunct 2). -/
def PayerPay (C D : ℕ) (honest : K → Prop) (s : St K M) : Prop :=
  (∀ k, s.closeSettled k = false → s.paidPayer k = 0) ∧
  (∀ k, s.closeSettled k = true →
    ∃ j t, s.closedAt k = some (j, t) ∧ s.paidPayer k = D - j * C) ∧
  (∀ k, honest k → s.emittedCnt k * C ≤ D)

/-- The payer-settlement invariant holds at every reachable state. -/
theorem payer_pay_inv {s : St K M} (h : Reach C D τ honest mclose s) :
    PayerPay C D honest s := by
  induction h with
  | init =>
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [Zkpc.Core.init]
  | step hprev hstep ih =>
    obtain ⟨hZero, hSettled, hSolv⟩ := ih
    cases hstep with
    | tick => exact ⟨hZero, hSettled, hSolv⟩
    | openCh k hnew => exact ⟨hZero, hSettled, hSolv⟩
    | emitAdv k i m hadv => exact ⟨hZero, hSettled, hSolv⟩
    | accept k i m hsig hm hlive hsolv hfresh => exact ⟨hZero, hSettled, hSolv⟩
    | slash k i m m' h1 h2 hne hopen hns => exact ⟨hZero, hSettled, hSolv⟩
    | sweepOne k i m hacc hdedup hwin => exact ⟨hZero, hSettled, hSolv⟩
    | emitHonest k m hh hlive hm hsolv =>
      refine ⟨hZero, hSettled, ?_⟩
      intro k' hh'
      rcases eq_or_ne k' k with rfl | hkk
      · simpa [Function.update_apply] using hsolv
      · simpa [Function.update_apply, hkk] using hSolv k' hh'
    | payerClose k j hlive hj =>
      obtain ⟨hop, hsl, hcl⟩ := hlive
      refine ⟨hZero, ?_, hSolv⟩
      intro k' hset
      rcases eq_or_ne k' k with rfl | hkk
      · obtain ⟨j', t', hct, -⟩ := hSettled k' hset
        rw [hcl] at hct
        simp at hct
      · obtain ⟨j', t', hct, hpay⟩ := hSettled k' hset
        exact ⟨j', t', by simpa [Function.update_apply, hkk] using hct, hpay⟩
    | settleClose k j t hc hexp hns hnotYet =>
      refine ⟨?_, ?_, hSolv⟩
      · intro k' hset
        rcases eq_or_ne k' k with rfl | hkk
        · simp [Function.update_apply] at hset
        · simp only [Function.update_apply, if_neg hkk] at hset ⊢
          exact hZero k' hset
      · intro k' hset
        rcases eq_or_ne k' k with rfl | hkk
        · exact ⟨j, t, hc, by simp [Function.update_apply, hZero k' hnotYet]⟩
        · simp only [Function.update_apply, if_neg hkk] at hset ⊢
          exact hSettled k' hset

/-- **T3 enabledness (Spec.md §7 T3 with §2 Close; T5 feeds on this).**
For an honest payer that closed at declared index `j` at time `t`, the
automatic ledger settlement (`settleClose`) is enabled at every reachable
state with `clock ≥ t + τ` in which it has not yet fired. The no-slash
guard is discharged by `honest_never_slashed` — no adversary ever produces
`Dispute` evidence against an honest payer (T3 second clause), so the
window always expires unslashed for it. -/
theorem settleClose_enabled {s : St K M}
    (h : Reach C D τ honest mclose s) (k : K) (hk : honest k)
    {j t : ℕ} (hc : s.closedAt k = some (j, t))
    (hexp : t + τ ≤ s.clock) (hnotYet : s.closeSettled k = false) :
    Step C D τ honest mclose s (.settleClose k)
      { s with
        paidPayer := Function.update s.paidPayer k (s.paidPayer k + (D - j * C))
        closeSettled := Function.update s.closeSettled k true } :=
  Step.settleClose s k j t hc hexp (honest_never_slashed h k hk) hnotYet

/-- **T3 settled amount (Spec.md §7 T3, the floor).** In any reachable
state in which an honest payer's close has settled, it has been paid
exactly `D − j·C` where `j = emittedCnt k` is the number of spend tickets
it emitted (emission = authorization, MC2; the close signal at index `j`
is not charged, Spec.md T3 scope note (iii)). Stated additively —
`paid + j·C = D` — so the ℕ subtraction is exact, using the honest
solvency invariant `j·C ≤ D`. -/
theorem T3_settled_amount {s : St K M}
    (h : Reach C D τ honest mclose s) (k : K) (hk : honest k)
    (hset : s.closeSettled k = true) :
    s.paidPayer k + s.emittedCnt k * C = D ∧
    s.paidPayer k = D - s.emittedCnt k * C := by
  obtain ⟨-, hSettled, hSolv⟩ := payer_pay_inv h
  obtain ⟨-, -, hCloseIdx, -, -⟩ := (reach_inv h).2
  obtain ⟨j, t, hct, hpay⟩ := hSettled k hset
  have hje : j = s.emittedCnt k := hCloseIdx k j t hk hct
  subst hje
  have hle : s.emittedCnt k * C ≤ D := hSolv k hk
  exact ⟨by rw [hpay]; omega, hpay⟩

/-- **T3 — Payer balance security, bundled (Spec.md §7 T3, flat).**
Against any adversary controlling the payee, all other payers, and the
scheduler, at every reachable state, for every honest payer `k`:

1. *(no framing)* `k` is never slashed — this is `honest_never_slashed`
   (Zkpc.Core.T1), the symbolic form of the FRAME game with all `N`
   gateways corrupted, cited here as Spec.md directs;
2. *(solvency of the floor)* its emitted value never exceeds the deposit,
   `emittedCnt·C ≤ D`;
3. *(the floor)* once its close settles — and `settleClose_enabled` plus
   T5 guarantee it always can settle after emitting its close and letting
   the window elapse — it has recovered exactly `D − j·C` for its `j`
   emitted spends: `paidPayer k + emittedCnt k · C = D`. -/
theorem T3_payer_balance_security {s : St K M}
    (h : Reach C D τ honest mclose s) (k : K) (hk : honest k) :
    s.slashedAt k = none ∧
    s.emittedCnt k * C ≤ D ∧
    (s.closeSettled k = true →
      s.paidPayer k + s.emittedCnt k * C = D) :=
  ⟨honest_never_slashed h k hk, (payer_pay_inv h).2.2 k hk,
    fun hset => (T3_settled_amount h k hk hset).1⟩

end Zkpc.Core
