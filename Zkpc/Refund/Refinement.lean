import Zkpc.Refund.Safety

/-!
# Executable refinement for refund-bearing channels

The refund safety development is phrased over `Refund.Step`.  This module
supplies deterministic, executable versions of its three public operations
and proves that every successful call is exactly the corresponding symbolic
transition.  Hence the representation-generic T1-B/T3-B/conservation results
apply to traces produced by these functions for both static and rerandomized
ciphertext representations.
-/

namespace Zkpc.Refund

variable {Rep : Type}

/-- Execute one receipt-bearing acceptance, rejecting a closed, over-priced,
or insolvent request. -/
def execAccept (Cmax D : ℕ) (s : St Rep) (c : ℕ) (r' : Rep) : Option (St Rep) :=
  if s.closed = false ∧ c ≤ Cmax ∧ (s.idx + 1) * Cmax ≤ D + s.R then
    some { s with idx := s.idx + 1, R := s.R + (Cmax - c),
                  sumc := s.sumc + c, rep := r' }
  else none

/-- Execute cooperative certified-count settlement. -/
def execClose (Cmax D : ℕ) (s : St Rep) : Option (St Rep) :=
  if s.closed = false then
    some { s with closed := true, settled := true,
                  payerPay := (D + s.R) - s.idx * Cmax,
                  payeePay := s.idx * Cmax - s.R }
  else none

/-- Execute the silent-channel/fund-slash forfeit path. -/
def execForceClose (D : ℕ) (s : St Rep) : Option (St Rep) :=
  if s.closed = false then
    some { s with closed := true, settled := true, slashed := true,
                  payerPay := 0, payeePay := D }
  else none

/-- Successful executable acceptance is exactly `Step.accept`. -/
theorem execAccept_refines_step (Cmax D : ℕ) (s : St Rep) (c : ℕ) (r' : Rep)
    (hlive : s.closed = false) (hc : c ≤ Cmax)
    (hsolv : (s.idx + 1) * Cmax ≤ D + s.R) :
    ∃ s', execAccept Cmax D s c r' = some s' ∧
      Step Cmax D s (.accept c r') s' := by
  let s' : St Rep :=
    { s with idx := s.idx + 1, R := s.R + (Cmax - c),
             sumc := s.sumc + c, rep := r' }
  refine ⟨s', ?_, ?_⟩
  · simp [execAccept, hlive, hc, hsolv, s']
  · exact Step.accept s c r' hlive hc hsolv

/-- Successful executable cooperative close is exactly `Step.close`. -/
theorem execClose_refines_step (Cmax D : ℕ) (s : St Rep)
    (hlive : s.closed = false) :
    ∃ s', execClose Cmax D s = some s' ∧ Step Cmax D s .close s' := by
  let s' : St Rep :=
    { s with closed := true, settled := true,
             payerPay := (D + s.R) - s.idx * Cmax,
             payeePay := s.idx * Cmax - s.R }
  refine ⟨s', by simp [execClose, hlive, s'], Step.close s hlive⟩

/-- Successful executable force-close is exactly `Step.forceClose`. -/
theorem execForceClose_refines_step (Cmax D : ℕ) (s : St Rep)
    (hlive : s.closed = false) :
    ∃ s', execForceClose D s = some s' ∧ Step Cmax D s .forceClose s' := by
  let s' : St Rep :=
    { s with closed := true, settled := true, slashed := true,
             payerPay := 0, payeePay := D }
  refine ⟨s', by simp [execForceClose, hlive, s'], Step.forceClose s hlive⟩

/-- One successful executable refund operation preserves symbolic
reachability and therefore all established refund invariants. -/
theorem exec_step_reachable (Cmax D : ℕ) (r0 : Rep)
    {s s' : St Rep} (hreach : Reach Rep Cmax D r0 s)
    {a : Act Rep} (hstep : Step Cmax D s a s') :
    Reach Rep Cmax D r0 s' :=
  Reach.step hreach hstep

end Zkpc.Refund

#print axioms Zkpc.Refund.execAccept_refines_step
#print axioms Zkpc.Refund.execClose_refines_step
#print axioms Zkpc.Refund.execForceClose_refines_step
#print axioms Zkpc.Refund.exec_step_reachable
