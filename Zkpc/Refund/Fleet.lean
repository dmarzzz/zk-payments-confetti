import Zkpc.Refund.Safety
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Refund-channel fleet composition

This module lifts the representation-generic instantiation-B settlement
machine from one channel to a finite fleet. A fleet step advances exactly one
channel; all other channels are unchanged. The component projection theorem
then transports the single-channel safety results and aggregates them.
-/

namespace Zkpc.Refund

open scoped BigOperators

variable {I Rep : Type} [DecidableEq I]

/-- A finite collection of independent refund-bearing channels. -/
abbrev FleetSt (I Rep : Type) := I → St Rep

/-- One interleaved fleet step updates exactly one channel. -/
inductive FleetStep (Cmax D : ℕ) : FleetSt I Rep → FleetSt I Rep → Prop
  | channel (s : FleetSt I Rep) (i : I) (a : Act Rep) (s' : St Rep)
      (hstep : Step Cmax D (s i) a s') :
      FleetStep Cmax D s (Function.update s i s')

/-- Fleet reachability from independently initialized channels. -/
inductive FleetReach (Cmax D : ℕ) (r0 : I → Rep) : FleetSt I Rep → Prop
  | init : FleetReach Cmax D r0 (fun i => St.init (r0 i))
  | step {s s' : FleetSt I Rep} :
      FleetReach Cmax D r0 s → FleetStep Cmax D s s' →
        FleetReach Cmax D r0 s'

/-- Every channel projection of a reachable fleet state is reachable in the
single-channel machine from its own genesis representation. -/
theorem FleetReach.component {Cmax D : ℕ} {r0 : I → Rep}
    {s : FleetSt I Rep} (h : FleetReach Cmax D r0 s) (i : I) :
    Reach Rep Cmax D (r0 i) (s i) := by
  induction h with
  | init => exact Reach.init
  | @step s s' hreach hstep ih =>
    cases hstep with
    | channel j a sj hsj =>
      by_cases hij : i = j
      · subst i
        rw [Function.update_self]
        exact Reach.step ih hsj
      · rw [Function.update_of_ne hij]
        exact ih

section Finite

variable [Fintype I]

/-- Fleet-wide accepted cost is at most one deposit per channel. -/
theorem fleet_no_overspend {Cmax D : ℕ} {r0 : I → Rep}
    {s : FleetSt I Rep} (h : FleetReach Cmax D r0 s) :
    (∑ i, (s i).sumc) ≤ Fintype.card I * D := by
  calc
    (∑ i, (s i).sumc) ≤ ∑ _i : I, D :=
      Finset.sum_le_sum fun i _ => T1_B_no_overspend (h.component i)
    _ = Fintype.card I * D := by simp

/-- If every channel has settled, aggregate payer and payee payouts conserve
exactly the fleet's total locked deposit. -/
theorem fleet_conservation {Cmax D : ℕ} {r0 : I → Rep}
    {s : FleetSt I Rep} (h : FleetReach Cmax D r0 s)
    (hsettled : ∀ i, (s i).settled = true) :
    (∑ i, ((s i).payerPay + (s i).payeePay)) = Fintype.card I * D := by
  calc
    (∑ i, ((s i).payerPay + (s i).payeePay)) = ∑ _i : I, D := by
      apply Finset.sum_congr rfl
      intro i _
      exact conservation (h.component i) (hsettled i)
    _ = Fintype.card I * D := by simp

/-- If every channel settles cooperatively, the aggregate payer payout plus
aggregate accepted cost equals the fleet's total locked deposit. -/
theorem fleet_payer_floor {Cmax D : ℕ} {r0 : I → Rep}
    {s : FleetSt I Rep} (h : FleetReach Cmax D r0 s)
    (hsettled : ∀ i, (s i).settled = true)
    (hunslashed : ∀ i, (s i).slashed = false) :
    (∑ i, (s i).payerPay) + (∑ i, (s i).sumc) = Fintype.card I * D := by
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i, ((s i).payerPay + (s i).sumc)) = ∑ _i : I, D := by
      apply Finset.sum_congr rfl
      intro i _
      exact T3_B_floor (h.component i) (hsettled i) (hunslashed i)
    _ = Fintype.card I * D := by simp

end Finite

end Zkpc.Refund

#print axioms Zkpc.Refund.FleetReach.component
#print axioms Zkpc.Refund.fleet_no_overspend
#print axioms Zkpc.Refund.fleet_conservation
#print axioms Zkpc.Refund.fleet_payer_floor
