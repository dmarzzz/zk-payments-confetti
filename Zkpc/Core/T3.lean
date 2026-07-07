import Mathlib.Order.Interval.Finset.Nat
import Zkpc.Core.T1

/-!
# T3 — Payer balance security (task D4; Spec.md rev-7 §7 T3, flat ticket)

Spec.md T3 has two clauses against a malicious-payee adversary:

* **The floor:** an honest payer with deposit `D` that emitted `j` spend
  tickets recovers `D − j·C` via `Close` and the elapse of the dispute
  window. Under MC20 (rev-7) the close enumerates the unused indices and
  settlement pays `C·|U| + (D − cap·C)` with `cap = ⌊D/C⌋`; for an honest
  closer `|U| = cap − j` and the payout is exactly `D − j·C` — the ℕ
  arithmetic is `close_payout_arith`, using `j ≤ cap` from the honest
  solvency invariant. Here: `payer_pay_inv` (settlement pays exactly once
  and exactly the MC20 formula), `settleClose_enabled` (the settlement
  step is available from window expiry on, with the no-slash guard
  discharged by `honest_never_slashed`), and `T3_settled_amount` (the
  settled amount is `D − j·C` with `j` the payer's emission count —
  stated additively, `paid + j·C = D`, so no ℕ-truncation ambiguity).
* **No framing:** no adversary produces evidence that slashes an honest
  payer — neither `Dispute` (a conflicting signal pair cannot exist:
  `honest_never_slashed`, Zkpc.Core.T1) nor the MC20 `closeDispute` (an
  honest close claims only genuinely-unused indices, so no acceptance
  bit-matches it: `honest_close_undisputable`, Zkpc.Core.T1). Under MC20
  the close emits no signal, so closing opens no evidence surface. The
  probabilistic complement is T7's FRAME game.

`T3_payer_balance_security` bundles all clauses. The path from "enabled"
to "taken" — that the always-enabled settlement actually fires — is T5
(`Zkpc.Core.T5`), per Spec.md's rev-1 de-circularization (T2/T3 own the
amounts, T5 owns the deadline).

GATE-NOTE (deltas between Spec.md T3 and these statements):
1. *"At least" vs "exactly".* Spec.md says the payer recovers *at least*
   `D − j·C`. The flat machine has exactly one payer income event
   (`settleClose`, guarded to fire once), so we prove the stronger
   equality `paidPayer k + j·C = D`. "At least" would be the faithful
   reading if other income paths existed; here equality implies it.
2. *`j` = emitted count; the close charges no index.* Spec.md's floor is
   stated against *emitted* tickets (MC2: emission is the authorization
   event). The machine forces an honest closer to enumerate exactly
   `{i | emittedCnt ≤ i < cap}` (guard `hUeq` of `payerClose`), and
   `HonestSig` carries that set forward (the counter freezes at close,
   since honest emission requires a live channel). Under MC20 the close
   emits no signal and occupies no index, so the payout is over the `j`
   spends at indices `0..j−1` via `|U| = cap − j` — Spec.md T3 scope
   note (iii), rev-7 wording.
3. *Refund variant.* This file is instantiation A only (flat price); the
   `D − j·C_max + R` clause of T3-B is task H4, out of scope here.
4. *Timing.* As in T2/T5, the ledger's `Δ` is folded to instantaneous
   inclusion at the action's machine time (State.lean header).
-/

namespace Zkpc.Core

open Finset

variable {K M : Type} [DecidableEq K] [DecidableEq M]
variable {C D τ : ℕ} {honest : K → Prop}

/-- **The MC20 close-payout identity (Spec.md §2 Close A: "for an honest
closer with `j` emitted indices, `|U| = cap − j` and the payout is
exactly `D − j·C`").** For `j·C ≤ D` and `U` the honest enumeration
`{i | j ≤ i < ⌊D/C⌋}`:
`C·|U| + (D − ⌊D/C⌋·C) = D − j·C` — refund per unused index plus the
sub-ticket residue equals the pre-MC20 floor. Exact in ℕ. -/
theorem close_payout_arith (C D j : ℕ) (hj : j * C ≤ D) :
    C * (((Finset.range (D / C)).filter (fun i => j ≤ i)).card)
      + (D - D / C * C) = D - j * C := by
  have hfilter : (Finset.range (D / C)).filter (fun i => j ≤ i)
      = Finset.Ico j (D / C) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact and_comm
  rw [hfilter, Nat.card_Ico]
  rcases Nat.eq_zero_or_pos C with hC | hC
  · subst hC
    simp
  · have hcap : D / C * C ≤ D := Nat.div_mul_le_self D C
    have hjcap : j ≤ D / C := (Nat.le_div_iff_mul_le hC).mpr hj
    have hsum : C * (D / C - j) + C * j = C * (D / C) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hjcap]
    have hc1 : C * (D / C) = D / C * C := Nat.mul_comm _ _
    have hc2 : C * j = j * C := Nat.mul_comm _ _
    omega

/-- Payer-settlement invariant (Spec.md §2 Close A, payer side, MC20):
(1) before its close window has settled, a payer has been paid nothing;
(2) once settled, it has been paid exactly `C·|U| + (D − cap·C)` for its
    recorded claimed-unused set `U` — the automatic-settlement formula,
    paid exactly once (the `closeSettled` guard);
(3) an honest payer's emission counter never outruns solvency:
    `emittedCnt·C ≤ D` (the `Spend` guard, R_spend conjunct 2). -/
def PayerPay (C D : ℕ) (honest : K → Prop) (s : St K M) : Prop :=
  (∀ k, s.closeSettled k = false → s.paidPayer k = 0) ∧
  (∀ k, s.closeSettled k = true →
    ∃ U t, s.closedAt k = some (U, t) ∧
      s.paidPayer k = C * U.card + (D - D / C * C)) ∧
  (∀ k, honest k → s.emittedCnt k * C ≤ D)

/-- The payer-settlement invariant holds at every reachable state. -/
theorem payer_pay_inv {s : St K M} (h : Reach C D τ honest s) :
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
    | accept k i m hsig hlive hsolv hfresh => exact ⟨hZero, hSettled, hSolv⟩
    | slash k i m m' h1 h2 hne hopen hns => exact ⟨hZero, hSettled, hSolv⟩
    | closeDispute k i m U t hc hiU hacc hwin hnotYet =>
      exact ⟨hZero, hSettled, hSolv⟩
    | settleVoid k U t hc hexp hns hnotYet hover => exact ⟨hZero, hSettled, hSolv⟩
    | sweepOne k i m hacc hdedup hwin hbar => exact ⟨hZero, hSettled, hSolv⟩
    | emitHonest k m hh hlive hsolv =>
      refine ⟨hZero, hSettled, ?_⟩
      intro k' hh'
      rcases eq_or_ne k' k with rfl | hkk
      · simpa [Function.update_apply] using hsolv
      · simpa [Function.update_apply, hkk] using hSolv k' hh'
    | payerClose k U hlive hUlt hUeq =>
      obtain ⟨hop, hsl, hcl⟩ := hlive
      refine ⟨hZero, ?_, hSolv⟩
      intro k' hset
      rcases eq_or_ne k' k with rfl | hkk
      · obtain ⟨U', t', hct, -⟩ := hSettled k' hset
        rw [hcl] at hct
        simp at hct
      · obtain ⟨U', t', hct, hpay⟩ := hSettled k' hset
        exact ⟨U', t', by simpa [Function.update_apply, hkk] using hct, hpay⟩
    | settleClose k U t hc hexp hns hswbar hnotYet =>
      refine ⟨?_, ?_, hSolv⟩
      · intro k' hset
        rcases eq_or_ne k' k with rfl | hkk
        · simp [Function.update_apply] at hset
        · simp only [Function.update_apply, if_neg hkk] at hset ⊢
          exact hZero k' hset
      · intro k' hset
        rcases eq_or_ne k' k with rfl | hkk
        · exact ⟨U, t, hc, by simp [Function.update_apply, hZero k' hnotYet]⟩
        · simp only [Function.update_apply, if_neg hkk] at hset ⊢
          exact hSettled k' hset

/-- **T3 enabledness (Spec.md §7 T3 with §2 Close; T5 feeds on this).**
For an honest payer that closed with claimed-unused set `U` at time `t`,
the automatic ledger settlement (`settleClose`) is enabled at every
reachable state with `clock ≥ t + τ` in which it has not yet fired. The
no-slash guard is discharged by `honest_never_slashed` — no adversary
produces `Dispute` evidence against an honest payer, and no acceptance
bit-matches its claimed set (`honest_close_undisputable`), so the window
always expires unslashed and unvoided for it — and the rev-8
settlement-time bar check by `honest_settleVoid_never` (an honest `U`
never overlaps the swept nullifiers, so the `settleVoid` branch never
fires against it). -/
theorem settleClose_enabled {s : St K M}
    (h : Reach C D τ honest s) (k : K) (hk : honest k)
    {U : Finset ℕ} {t : ℕ} (hc : s.closedAt k = some (U, t))
    (hexp : t + τ ≤ s.clock) (hnotYet : s.closeSettled k = false) :
    Step C D τ honest s (.settleClose k)
      { s with
        paidPayer := Function.update s.paidPayer k
          (s.paidPayer k + (C * U.card + (D - D / C * C)))
        closeSettled := Function.update s.closeSettled k true } :=
  Step.settleClose s k U t hc hexp (honest_never_slashed h k hk)
    (honest_settleVoid_never h k hk hc) hnotYet

/-- **T3 settled amount (Spec.md §7 T3, the floor).** In any reachable
state in which an honest payer's close has settled, it has been paid
exactly `D − j·C` where `j = emittedCnt k` is the number of spend tickets
it emitted (emission = authorization, MC2): its recorded claimed set is
exactly the honest enumeration, so `C·|U| + (D − cap·C) = D − j·C` by
`close_payout_arith`. Stated additively — `paid + j·C = D` — so the ℕ
subtraction is exact, using the honest solvency invariant `j·C ≤ D`. -/
theorem T3_settled_amount {s : St K M}
    (h : Reach C D τ honest s) (k : K) (hk : honest k)
    (hset : s.closeSettled k = true) :
    s.paidPayer k + s.emittedCnt k * C = D ∧
    s.paidPayer k = D - s.emittedCnt k * C := by
  obtain ⟨-, hSettled, hSolv⟩ := payer_pay_inv h
  obtain ⟨U, t, hct, hpay⟩ := hSettled k hset
  have hU := (reach_inv h).2.2.2.1 k U t hk hct
  subst hU
  have hle : s.emittedCnt k * C ≤ D := hSolv k hk
  rw [close_payout_arith C D (s.emittedCnt k) hle] at hpay
  exact ⟨by rw [hpay]; omega, hpay⟩

/-- **T3 — Payer balance security, bundled (Spec.md §7 T3, flat, rev-7).**
Against any adversary controlling the payee, all other payers, and the
scheduler, at every reachable state, for every honest payer `k`:

1. *(no framing, `Dispute`)* `k` is never slashed — `honest_never_slashed`
   (Zkpc.Core.T1), the symbolic form of the FRAME game with all `N`
   gateways corrupted, cited here as Spec.md directs;
2. *(no framing, MC20 `closeDispute`)* no acceptance ever bit-matches
   `k`'s claimed-unused set — `honest_close_undisputable` — so its close
   is never voided;
3. *(solvency of the floor)* its emitted value never exceeds the deposit,
   `emittedCnt·C ≤ D`;
4. *(the floor)* once its close settles — and `settleClose_enabled` plus
   T5 guarantee it always can settle after closing and letting the window
   elapse — it has recovered exactly `D − j·C` for its `j` emitted
   spends: `paidPayer k + emittedCnt k · C = D`. -/
theorem T3_payer_balance_security {s : St K M}
    (h : Reach C D τ honest s) (k : K) (hk : honest k) :
    s.slashedAt k = none ∧
    (∀ (U : Finset ℕ) (t i : ℕ) (m : M),
      s.closedAt k = some (U, t) → i ∈ U → (k, i, m) ∉ s.acc) ∧
    s.emittedCnt k * C ≤ D ∧
    (s.closeSettled k = true →
      s.paidPayer k + s.emittedCnt k * C = D) :=
  ⟨honest_never_slashed h k hk,
   fun _U _t _i _m hc hiU => honest_close_undisputable h k hk hc hiU,
   (payer_pay_inv h).2.2 k hk,
   fun hset => (T3_settled_amount h k hk hset).1⟩

end Zkpc.Core
