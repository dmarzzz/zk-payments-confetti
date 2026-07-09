import Zkpc.Core.Flat

/-!
# Flat object-to-ledger forward refinement

`Core.Flat.flatScheme` supplies executable algorithm bodies, while
`Core.State.Step` is the transition system used by the safety and liveness
proofs.  This module proves that the state-changing success paths of the
object API are exactly concrete ledger transitions.  The results remove the
previous reliance on parallel, manually compared definitions.

The payer's private counter is related to the ledger's `emittedCnt`.  Spend
first updates the private state and its corresponding ledger emission step;
Open, payer Close, and identity Dispute directly return the same ledger state
as their `Step` constructor.  Automatic close-window transitions remain
ledger-internal by design and are already the subject of T2/T3/T5.
-/

namespace Zkpc.Core.Flat

open Zkpc.Spec Zkpc.Core

variable {F Pl : Type} [Field F] [DecidableEq F] [DecidableEq Pl]

/-- Open succeeds exactly on a fresh commitment and returns the state produced
by the symbolic `openCh` transition. -/
theorem open_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (hnew : k ∉ s.opened) :
    ∃ s',
      (flatScheme F Pl).open' pp k s =
        some (((k, 0, none), s')) ∧
      Step pp.C pp.D pp.tau honest s (.openCh k) s' := by
  let s' : St F (Msg Pl) := { s with opened := insert k s.opened }
  refine ⟨s', ?_, ?_⟩
  · simp [flatScheme, hnew, s']
  · exact Step.openCh s k hnew

/-- An honest executable Spend at the ledger's current counter is simulated
by one `emitHonest` transition and advances the private counter to match the
new ledger counter. -/
theorem spend_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (last : Option (F × ℕ × Msg Pl))
    (m : Msg Pl) (hh : honest k) (hlive : s.live k)
    (hsolv : (s.emittedCnt k + 1) * pp.C ≤ pp.D) :
    ∃ s' ticket payer',
      (flatScheme F Pl).spend pp (k, s.emittedCnt k, last) m =
        some (ticket, payer') ∧
      Step pp.C pp.D pp.tau honest s (.emitHonest k m) s' ∧
      ticket = (k, s.emittedCnt k, m) ∧
      payer'.1 = k ∧ payer'.2.1 = s'.emittedCnt k := by
  let ticket : F × ℕ × Msg Pl := (k, s.emittedCnt k, m)
  let payer' : F × ℕ × Option (F × ℕ × Msg Pl) :=
    (k, s.emittedCnt k + 1, some ticket)
  let s' : St F (Msg Pl) :=
    { s with sigs := insert ticket s.sigs
             emittedCnt := Function.update s.emittedCnt k (s.emittedCnt k + 1) }
  refine ⟨s', ticket, payer', ?_, ?_, rfl, rfl, ?_⟩
  · simp [flatScheme, hsolv, ticket, payer']
  · exact Step.emitHonest s k m hh hlive hsolv
  · simp [payer', s']

/-- On a fresh nullifier, executable `Redeem` accepts exactly when the
symbolic machine can take its knowledge-sound `accept` transition. -/
theorem redeem_accept_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (i : ℕ) (m : Msg Pl)
    (hsig : (k, i, m) ∈ s.sigs) (hlive : s.live k)
    (hsolv : (i + 1) * pp.C ≤ pp.D)
    (hfresh : ∀ m', (k, i, m') ∉ s.acc) :
    ∃ s',
      (flatScheme F Pl).redeem pp () s.acc s (k, i, m) =
        (.accept, s'.acc, none) ∧
      Step pp.C pp.D pp.tau honest s (.accept k i m) s' := by
  let s' : St F (Msg Pl) := { s with acc := insert (k, i, m) s.acc }
  refine ⟨s', ?_, ?_⟩
  · have hnotmem : (k, i, m) ∉ s.acc := hfresh m
    have hempty :
        (s.acc.filter (fun u => u.1 = k ∧ u.2.1 = i)).toList = [] := by
      rw [Finset.toList_eq_nil]
      exact Finset.filter_eq_empty_iff.mpr (by
        intro u hu hki
        rcases u with ⟨ku, iu, mu⟩
        simp only at hki ⊢
        rcases hki with ⟨rfl, rfl⟩
        exact hfresh mu hu)
    simp [flatScheme, hlive, hsolv, hnotmem, hempty, s']
  · exact Step.accept s k i m hsig hlive hsolv hfresh

/-- The executable honest payer-close enumerates exactly the unused suffix and
returns precisely the ledger state of `Step.payerClose`. -/
theorem payerClose_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (j : ℕ)
    (last : Option (F × ℕ × Msg Pl)) (hh : honest k)
    (hlive : s.live k) (hcount : j = s.emittedCnt k) :
    ∃ s' U,
      (flatScheme F Pl).payerClose pp (k, j, last) s = some s' ∧
      Step pp.C pp.D pp.tau honest s (.payerClose k U) s' ∧
      U = (Finset.range (pp.D / pp.C)).filter (fun i => j ≤ i) := by
  let U := (Finset.range (pp.D / pp.C)).filter (fun i => j ≤ i)
  let s' : St F (Msg Pl) :=
    { s with closedAt := Function.update s.closedAt k (some (U, s.clock)) }
  refine ⟨s', U, ?_, ?_, rfl⟩
  · have hopen : k ∈ s.opened := hlive.1
    simp [flatScheme, St.live, hopen, hlive.2.1, hlive.2.2, U, s']
  · apply Step.payerClose s k U hlive
    · intro i hi
      exact (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    · intro _
      subst j
      rfl

/-- A valid executable identity dispute returns exactly the state of the
symbolic slash transition. -/
theorem dispute_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (i : ℕ) (m m' : Msg Pl)
    (h1 : (k, i, m) ∈ s.sigs) (h2 : (k, i, m') ∈ s.sigs)
    (hne : m ≠ m') (hopen : k ∈ s.opened)
    (hns : s.slashedAt k = none) :
    ∃ s',
      (flatScheme F Pl).dispute pp (k, i, m, m') s = some s' ∧
      Step pp.C pp.D pp.tau honest s (.slash k i m m') s' := by
  let s' : St F (Msg Pl) :=
    { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
  refine ⟨s', ?_, ?_⟩
  · simp [flatScheme, h1, h2, hne, hopen, hns, s']
  · exact Step.slash s k i m m' h1 h2 hne hopen hns

/-! ## Automatic MC20 window drivers -/

/-- Execute a close-window challenge against an accepted ticket claimed
unused by the payer. -/
def execCloseDispute (pp : Params) (s : St F (Msg Pl))
    (k : F) (i : ℕ) (m : Msg Pl) : Option (St F (Msg Pl)) :=
  match s.closedAt k with
  | none => none
  | some (U, t) =>
      if i ∈ U ∧ (k, i, m) ∈ s.acc ∧ s.clock ≤ t + pp.tau ∧
          s.closeSettled k = false then
        some { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
      else none

/-- Execute successful close settlement after expiry and the two-sided sweep
bar check. -/
def execSettleClose (pp : Params) (s : St F (Msg Pl)) (k : F) :
    Option (St F (Msg Pl)) :=
  match s.closedAt k with
  | none => none
  | some (U, t) =>
      if t + pp.tau ≤ s.clock ∧ s.slashedAt k = none ∧
          (∀ i ∈ U, (k, i) ∉ s.swept) ∧ s.closeSettled k = false then
        some { s with paidPayer := Function.update s.paidPayer k
                  (s.paidPayer k + (pp.C * U.card + (pp.D - (pp.D / pp.C) * pp.C)))
                      closeSettled := Function.update s.closeSettled k true }
      else none

/-- Execute settlement-time voiding when a claimed-unused nullifier was
already swept. -/
def execSettleVoid (pp : Params) (s : St F (Msg Pl)) (k : F) :
    Option (St F (Msg Pl)) :=
  match s.closedAt k with
  | none => none
  | some (U, t) =>
      if t + pp.tau ≤ s.clock ∧ s.slashedAt k = none ∧
          s.closeSettled k = false ∧ (∃ i ∈ U, (k, i) ∈ s.swept) then
        some { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
      else none

/-- The executable close challenge is exactly `Step.closeDispute`. -/
theorem execCloseDispute_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (i : ℕ) (m : Msg Pl)
    (U : Finset ℕ) (t : ℕ) (hc : s.closedAt k = some (U, t))
    (hiU : i ∈ U) (hacc : (k, i, m) ∈ s.acc)
    (hwin : s.clock ≤ t + pp.tau) (hnotYet : s.closeSettled k = false) :
    ∃ s', execCloseDispute pp s k i m = some s' ∧
      Step pp.C pp.D pp.tau honest s (.closeDispute k i m) s' := by
  let s' : St F (Msg Pl) :=
    { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
  refine ⟨s', ?_, Step.closeDispute s k i m U t hc hiU hacc hwin hnotYet⟩
  simp [execCloseDispute, hc, hiU, hacc, hwin, hnotYet, s']

/-- The executable successful settlement is exactly `Step.settleClose`. -/
theorem execSettleClose_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (U : Finset ℕ) (t : ℕ)
    (hc : s.closedAt k = some (U, t)) (hexp : t + pp.tau ≤ s.clock)
    (hns : s.slashedAt k = none) (hswbar : ∀ i ∈ U, (k, i) ∉ s.swept)
    (hnotYet : s.closeSettled k = false) :
    ∃ s', execSettleClose pp s k = some s' ∧
      Step pp.C pp.D pp.tau honest s (.settleClose k) s' := by
  let s' : St F (Msg Pl) :=
    { s with paidPayer := Function.update s.paidPayer k
        (s.paidPayer k + (pp.C * U.card + (pp.D - (pp.D / pp.C) * pp.C)))
             closeSettled := Function.update s.closeSettled k true }
  refine ⟨s', ?_, Step.settleClose s k U t hc hexp hns hswbar hnotYet⟩
  simp [execSettleClose, hc, hexp, hns, hswbar, hnotYet, s']

/-- The executable settlement-time void is exactly `Step.settleVoid`. -/
theorem execSettleVoid_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (U : Finset ℕ) (t : ℕ)
    (hc : s.closedAt k = some (U, t)) (hexp : t + pp.tau ≤ s.clock)
    (hns : s.slashedAt k = none) (hnotYet : s.closeSettled k = false)
    (hover : ∃ i ∈ U, (k, i) ∈ s.swept) :
    ∃ s', execSettleVoid pp s k = some s' ∧
      Step pp.C pp.D pp.tau honest s (.settleVoid k) s' := by
  let s' : St F (Msg Pl) :=
    { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
  refine ⟨s', ?_, Step.settleVoid s k U t hc hexp hns hnotYet hover⟩
  simp [execSettleVoid, hc, hexp, hns, hnotYet, hover, s']

/-- Sweeping a singleton eligible tuple is exactly one `sweepOne` ledger
transition, the base case of the implementation's list fold. -/
theorem sweep_single_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (i : ℕ) (m : Msg Pl)
    (hacc : (k, i, m) ∈ s.acc) (hdedup : (k, i) ∉ s.swept)
    (hwin : sweepOpen pp.tau s k) (hbar : ¬ s.sweepBarred k i) :
    ∃ s',
      (flatScheme F Pl).sweep pp () [(k, i, m)] s = s' ∧
      Step pp.C pp.D pp.tau honest s (.sweepOne k i m) s' := by
  let s' : St F (Msg Pl) :=
    { s with swept := insert (k, i) s.swept
             paidGw := s.paidGw + pp.C }
  refine ⟨s', ?_, ?_⟩
  · simp [flatScheme, hacc, hdedup, hwin, hbar, s']
  · exact Step.sweepOne s k i m hacc hdedup hwin hbar

/-- Reflexive-transitive symbolic meaning of the executable sweep fold.
Eligible entries take one `sweepOne` step; rejected, duplicate, expired, or
barred entries leave the ledger unchanged, exactly as the implementation
specifies. -/
inductive SweepTrace (pp : Params) (honest : F → Prop) :
    St F (Msg Pl) → List (F × ℕ × Msg Pl) → St F (Msg Pl) → Prop
  | nil (s) : SweepTrace pp honest s [] s
  | skip (s) (u : F × ℕ × Msg Pl) (us) (s')
      (hineligible : ¬ (u ∈ s.acc ∧ (u.1, u.2.1) ∉ s.swept ∧
        sweepOpen pp.tau s u.1 ∧ ¬ s.sweepBarred u.1 u.2.1))
      (tail : SweepTrace pp honest s us s') :
      SweepTrace pp honest s (u :: us) s'
  | take (s) (k : F) (i : ℕ) (m : Msg Pl) (us) (s')
      (hacc : (k, i, m) ∈ s.acc) (hdedup : (k, i) ∉ s.swept)
      (hwin : sweepOpen pp.tau s k) (hbar : ¬ s.sweepBarred k i)
      (tail : SweepTrace pp honest
        { s with swept := insert (k, i) s.swept
                 paidGw := s.paidGw + pp.C } us s') :
      SweepTrace pp honest s ((k, i, m) :: us) s'

/-- Every call of the arbitrary-list executable sweep produces a symbolic
trace, including its no-op decisions for ineligible list entries. -/
theorem sweep_refines_trace (pp : Params) (honest : F → Prop)
    (tuples : List (F × ℕ × Msg Pl)) (s : St F (Msg Pl)) :
    SweepTrace pp honest s tuples
      ((flatScheme F Pl).sweep pp () tuples s) := by
  induction tuples generalizing s with
  | nil => exact SweepTrace.nil s
  | cons u us ih =>
      rcases u with ⟨k, i, m⟩
      by_cases helig : (k, i, m) ∈ s.acc ∧ (k, i) ∉ s.swept ∧
          sweepOpen pp.tau s k ∧ ¬ s.sweepBarred k i
      · rcases helig with ⟨hacc, hdedup, hwin, hbar⟩
        apply SweepTrace.take s k i m us _ hacc hdedup hwin hbar
        simpa [flatScheme, hacc, hdedup, hwin, hbar] using
          (ih { s with swept := insert (k, i) s.swept
                       paidGw := s.paidGw + pp.C })
      · apply SweepTrace.skip s (k, i, m) us _ helig
        simpa [flatScheme, helig] using ih s

/-- A concrete sweep trace from a reachable ledger ends in another reachable
ledger, so the full list implementation inherits every reachability
invariant, not merely the singleton success case. -/
theorem SweepTrace.reachable (pp : Params) (honest : F → Prop)
    {s s' : St F (Msg Pl)} {tuples : List (F × ℕ × Msg Pl)}
    (htrace : SweepTrace pp honest s tuples s')
    (hreach : Reach pp.C pp.D pp.tau honest s) :
    Reach pp.C pp.D pp.tau honest s' := by
  induction htrace with
  | nil => exact hreach
  | skip _ _ _ _ _ _ ih => exact ih hreach
  | take s k i m us s' hacc hdedup hwin hbar tail ih =>
      exact ih (Reach.step hreach
        (Step.sweepOne s k i m hacc hdedup hwin hbar))

/-- End-to-end reachability theorem for the executable arbitrary-list sweep. -/
theorem sweep_preserves_reachability (pp : Params) (honest : F → Prop)
    (tuples : List (F × ℕ × Msg Pl)) (s : St F (Msg Pl))
    (hreach : Reach pp.C pp.D pp.tau honest s) :
    Reach pp.C pp.D pp.tau honest
      ((flatScheme F Pl).sweep pp () tuples s) :=
  (sweep_refines_trace pp honest tuples s).reachable pp honest hreach

/-- A sequence of successful refined object calls yields ordinary concrete
reachability, so all existing T1--T5 invariants apply to the executable API
trace. -/
theorem refined_steps_reachable (pp : Params) (honest : F → Prop)
    {s : St F (Msg Pl)} (h : Reach pp.C pp.D pp.tau honest s)
    {s' : St F (Msg Pl)} {a : Act F (Msg Pl)}
    (hstep : Step pp.C pp.D pp.tau honest s a s') :
    Reach pp.C pp.D pp.tau honest s' :=
  Reach.step h hstep

end Zkpc.Core.Flat

#print axioms Zkpc.Core.Flat.open_refines_step
#print axioms Zkpc.Core.Flat.spend_refines_step
#print axioms Zkpc.Core.Flat.redeem_accept_refines_step
#print axioms Zkpc.Core.Flat.payerClose_refines_step
#print axioms Zkpc.Core.Flat.dispute_refines_step
#print axioms Zkpc.Core.Flat.execCloseDispute_refines_step
#print axioms Zkpc.Core.Flat.execSettleClose_refines_step
#print axioms Zkpc.Core.Flat.execSettleVoid_refines_step
#print axioms Zkpc.Core.Flat.sweep_single_refines_step
#print axioms Zkpc.Core.Flat.sweep_refines_trace
#print axioms Zkpc.Core.Flat.SweepTrace.reachable
#print axioms Zkpc.Core.Flat.sweep_preserves_reachability
#print axioms Zkpc.Core.Flat.refined_steps_reachable
