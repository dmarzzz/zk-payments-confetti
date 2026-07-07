import Zkpc.Core.T3

/-!
# T5 — Closure liveness (task I1; Spec.md §7 T5)

Payer-close half of T5: an honest payer that initiated `Close` at machine
time `t` is settled its T3 amount once the window `τ` elapses —
settlement is *automatic at expiry* (Spec.md §2 Close), needs no second
transaction, and no counterparty behavior can delay or alter it.

Decomposition (matching Spec.md's statement):
* `settleClose_enabled` (Zkpc.Core.T3) — from `clock ≥ t + τ` on, the
  settlement action is enabled; the no-slash guard is `honest_never_slashed`
  (T3's exculpability clause, exactly as Spec.md T5 cites it).
* `settleClose_stable` — enabledness is *never revoked*: every step other
  than the settlement itself preserves it (garbage submissions, disputes,
  sweeps, other closes — nothing an adversary schedules can disable it).
* `reach_tick_add` / `tick_progress` — time always passes: from any
  reachable state the clock reaches any bound with all other components
  untouched, so window expiry is always reachable.
* `T5_payer_close_liveness` — the bundle: a settling continuation exists,
  reaching `closeSettled = true` and payout `D − j·C` at machine time
  `max(now, t + τ)` exactly.

The payee half of Spec.md T5 ("a sweep submitted at `t` is paid by
`t + Δ`, no window") is part of T2's collectability: `sweepOne_enabled`
and `T2_collectable` (Zkpc.Core.T2) show sweeps enabled and settling with
no ticks at all.

**Fairness hypothesis (stated per State.lean's header, made explicit
here):** the machine cannot force internal actions to occur, so liveness
is proved as (a) a constructive settling continuation from every reachable
state, plus (b) persistence — the settlement stays enabled under every
other action. Under the idealized ledger's guarantee that enabled contract
logic is eventually executed (weak fairness for the `settleClose` and
`tick` actions — Spec.md §5's "contract logic executes exactly as
specified", automatic window settlement included), every execution
settles: a weakly-fair run cannot avoid an action that (b) keeps
continuously enabled. The adversary controls scheduling but not the
ledger's own automatic actions.

GATE-NOTE (deltas between Spec.md T5 and these statements):
1. *`Δ` folded to zero.* Spec.md's bound is `t + Δ + τ` with `Δ` the
   ledger inclusion delay. The machine includes actions instantly at their
   clock value (State.lean header), so the bound here is machine-time
   `t + τ`, with `t` the recorded inclusion time of the close;
   `T5_payer_close_liveness` pins the settling state's clock to
   `max(now, t + τ)` — the "exactly, no `O(·)` slack" clause of Spec.md T5.
   `Δ` re-enters as prose when interpreting machine time.
2. *"Cannot extend these bounds"* is rendered as `settleClose_stable`
   (no step disables the settlement or changes its payout fields) rather
   than as a quantification over adversarial transaction contents — the
   machine's action alphabet *is* the adversary's transaction surface, so
   quantifying over steps covers it.
3. *negl(λ) caveat.* Spec.md excepts a negligible-probability event
   (forged `Dispute` evidence). The symbolic machine has no probability;
   that event does not exist in the model (`honest_never_slashed` is
   exact), and the probabilistic residue lives in T7's game layer, as for
   T3.
-/

namespace Zkpc.Core

variable {K M : Type} [DecidableEq K] [DecidableEq M]
variable {C D τ : ℕ} {honest : K → Prop} {mclose : M}

/-- Time can always pass: `n` ticks from any reachable state reach the
same state with the clock advanced by `n` and every other component
unchanged. -/
theorem reach_tick_add {s : St K M} (h : Reach C D τ honest mclose s)
    (n : ℕ) :
    Reach C D τ honest mclose { s with clock := s.clock + n } := by
  induction n with
  | zero => exact h
  | succ n ih => exact Reach.step ih (Step.tick _)

/-- **T5 tick progress.** From any reachable state, a state with
`clock ≥ T` (any bound `T`) is reachable by ticks alone, all
non-clock components untouched. Window expiry is therefore always
reachable; no adversary controls the passage of time. -/
theorem tick_progress {s : St K M} (h : Reach C D τ honest mclose s)
    (T : ℕ) :
    ∃ s' : St K M, Reach C D τ honest mclose s' ∧ T ≤ s'.clock ∧
      s' = { s with clock := s.clock + (T - s.clock) } := by
  refine ⟨{ s with clock := s.clock + (T - s.clock) },
    reach_tick_add h _, ?_, rfl⟩
  show T ≤ s.clock + (T - s.clock)
  omega

/-- **T5 persistence ("counterparty silence, garbage submissions, and
concurrent disputes cannot extend these bounds", Spec.md §7 T5).** Once
the settlement of an honest payer's expired close window is enabled, every
step other than that settlement itself preserves its enabledness: the
close record is immutable, the clock never decreases, no adversary
produces a slash against an honest payer (`honest_never_slashed` supplies
the guard separately), and only the settlement itself flips
`closeSettled`. With `settleClose_enabled` this makes the settlement
*continuously* enabled from expiry until taken — the shape weak fairness
needs. -/
theorem settleClose_stable {s s' : St K M} {a : Act K M}
    (hstep : Step C D τ honest mclose s a s')
    (k : K) {j t : ℕ}
    (hc : s.closedAt k = some (j, t)) (hexp : t + τ ≤ s.clock)
    (hnotYet : s.closeSettled k = false) (hna : a ≠ .settleClose k) :
    s'.closedAt k = some (j, t) ∧ t + τ ≤ s'.clock ∧
      s'.closeSettled k = false := by
  cases hstep with
  | tick => exact ⟨hc, Nat.le_succ_of_le hexp, hnotYet⟩
  | openCh k' hnew => exact ⟨hc, hexp, hnotYet⟩
  | emitHonest k' m hh hlive hm hsolv => exact ⟨hc, hexp, hnotYet⟩
  | emitAdv k' i m hadv => exact ⟨hc, hexp, hnotYet⟩
  | accept k' i m hsig hm hlive hsolv hfresh => exact ⟨hc, hexp, hnotYet⟩
  | slash k' i m m' h1 h2 hne hopen hns => exact ⟨hc, hexp, hnotYet⟩
  | payerClose k' j' hlive hj =>
    rcases eq_or_ne k' k with rfl | hkk
    · exact absurd hc (by rw [hlive.2.2]; simp)
    · refine ⟨?_, hexp, hnotYet⟩
      simpa [Function.update_apply, Ne.symm hkk] using hc
  | settleClose k' j' t' hc' hexp' hns' hnotYet' =>
    have hkk : k' ≠ k := fun hkkeq => hna (by rw [hkkeq])
    refine ⟨hc, hexp, ?_⟩
    simpa [Function.update_apply, Ne.symm hkk] using hnotYet
  | sweepOne k' i m hacc hdedup hwin => exact ⟨hc, hexp, hnotYet⟩

/-- **T5 — Closure liveness, payer close (Spec.md §7 T5).** An honest
payer whose close was included at machine time `t` (window `τ`, not yet
settled) reaches, from any reachable state and against any adversary
scheduling, a state in which its close *has* settled:

* at machine time exactly `max(now, t + τ)` — settlement fires the moment
  the window expires, with no slack (Spec.md: "settled ... by
  `t + Δ + τ` exactly"; GATE-NOTE 1 for the `Δ` folding);
* with payout exactly its T3 floor `D − j·C`, stated additively as
  `paid + j·C = D` via the honest solvency invariant.

The continuation consists of ticks (always enabled) followed by the
automatic settlement (enabled by `settleClose_enabled`, kept enabled by
`settleClose_stable`); under the idealized ledger's fairness — enabled
contract logic eventually executes (see the file header) — every
execution contains it. No counterparty transaction is involved anywhere:
counterparty silence is harmless, and `honest_never_slashed` bars the
only transaction kind (`Dispute`) that could touch the window. -/
theorem T5_payer_close_liveness {s : St K M}
    (h : Reach C D τ honest mclose s) (k : K) (hk : honest k)
    {j t : ℕ} (hc : s.closedAt k = some (j, t))
    (hnotYet : s.closeSettled k = false) :
    ∃ s', Reach C D τ honest mclose s' ∧
      s'.clock = max s.clock (t + τ) ∧
      s'.closeSettled k = true ∧
      s'.paidPayer k = D - j * C ∧
      s'.paidPayer k + j * C = D := by
  -- the honest close index is the emission count, and it is solvent
  obtain ⟨-, -, hCloseIdx, -, -⟩ := (reach_inv h).2
  have hje : j = s.emittedCnt k := hCloseIdx k j t hk hc
  have hjC : j * C ≤ D := by
    rw [hje]; exact (payer_pay_inv h).2.2 k hk
  -- tick to window expiry
  have h₁ : Reach C D τ honest mclose
      { s with clock := s.clock + (t + τ - s.clock) } :=
    reach_tick_add h _
  have hzero : s.paidPayer k = 0 := (payer_pay_inv h₁).1 k hnotYet
  -- the automatic settlement, enabled at expiry (no-slash via T3)
  have hstep := Step.settleClose (C := C) (D := D) (τ := τ)
    (honest := honest) (mclose := mclose)
    { s with clock := s.clock + (t + τ - s.clock) } k j t hc
    (by show t + τ ≤ s.clock + (t + τ - s.clock); omega)
    (honest_never_slashed h₁ k hk) hnotYet
  refine ⟨_, Reach.step h₁ hstep, ?_, ?_, ?_, ?_⟩
  · show s.clock + (t + τ - s.clock) = max s.clock (t + τ)
    omega
  · show Function.update s.closeSettled k true k = true
    simp [Function.update_apply]
  · show Function.update s.paidPayer k (s.paidPayer k + (D - j * C)) k
      = D - j * C
    simp [Function.update_apply, hzero]
  · show Function.update s.paidPayer k (s.paidPayer k + (D - j * C)) k
      + j * C = D
    rw [Function.update_self, hzero]
    omega

end Zkpc.Core
