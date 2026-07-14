import Zkpc.Chain.Collision

/-!
# Executable refinement for the nullifier-chain channel

`Chain.State` is the relational ledger model.  This module supplies the
corresponding deterministic guarded executor and proves both directions of
refinement: every successful execution is a `Step`, and every relational step
is reproduced by the executor.  Consequently an executable trace from
genesis inherits all channel safety theorems.
-/

namespace Zkpc.Chain

/-- Execute one nullifier-chain ledger action.  The boolean/ordering guards
are exactly those of `Step`; a disabled action returns `none`. -/
def execStep (D : ℕ) (s : St) : Act → Option St
  | .pay δ =>
      if s.settled = false ∧ s.closing = none ∧ s.earned + δ ≤ D then
        some { s with len := s.len + 1, balOf := Function.update s.balOf (s.len + 1) (s.earned + δ) }
      else none
  | .closeOn i =>
      if s.settled = false ∧ s.closing = none ∧ i ≤ s.len then
        some { s with closing := some i }
      else none
  | .settleSplit =>
      match s.closing with
      | some i =>
          if s.settled = false ∧ i = s.len then
            some { s with settled := true, alicePay := D - s.balOf i, bobPay := s.balOf i }
          else none
      | none => none
  | .challenge =>
      match s.closing with
      | some i =>
          if s.settled = false ∧ i < s.len then
            some { s with settled := true, forfeited := true, alicePay := 0, bobPay := D }
          else none
      | none => none
  | .timeoutForfeit =>
      if s.settled = false ∧ s.closing = none then
        some { s with settled := true, forfeited := true, alicePay := 0, bobPay := D }
      else none

/-- Every successful executable action is admitted by the relational ledger. -/
theorem execStep_sound {D : ℕ} {s s' : St} {a : Act}
    (h : execStep D s a = some s') : Step D s a s' := by
  cases a with
  | pay δ =>
      simp only [execStep] at h
      split at h <;> rename_i hg
      · rcases hg with ⟨hlive, hopen, hcap⟩
        exact Option.some.inj h ▸ Step.pay s δ hlive hopen hcap
      · contradiction
  | closeOn i =>
      simp only [execStep] at h
      split at h <;> rename_i hg
      · rcases hg with ⟨hlive, hopen, hi⟩
        exact Option.some.inj h ▸ Step.closeOn s i hlive hopen hi
      · contradiction
  | settleSplit =>
      simp only [execStep] at h
      split at h
      · rename_i i hclosing
        split at h <;> rename_i hg
        · rcases hg with ⟨hlive, hlatest⟩
          exact Option.some.inj h ▸ Step.settleSplit s i hlive hclosing hlatest
        · contradiction
      · contradiction
  | challenge =>
      simp only [execStep] at h
      split at h
      · rename_i i hclosing
        split at h <;> rename_i hg
        · rcases hg with ⟨hlive, hstale⟩
          exact Option.some.inj h ▸ Step.challenge s i hlive hclosing hstale
        · contradiction
      · contradiction
  | timeoutForfeit =>
      simp only [execStep] at h
      split at h <;> rename_i hg
      · rcases hg with ⟨hlive, hopen⟩
        exact Option.some.inj h ▸ Step.timeoutForfeit s hlive hopen
      · contradiction

/-- The executor is complete for the relational transition system. -/
theorem execStep_complete {D : ℕ} {s s' : St} {a : Act}
    (h : Step D s a s') : execStep D s a = some s' := by
  cases h with
  | pay δ hlive hopen hcap => simp [execStep, hlive, hopen, hcap]
  | closeOn i hlive hopen hi => simp [execStep, hlive, hopen, hi]
  | settleSplit i hlive hclosing hlatest =>
      simp [execStep, hclosing, hlive, hlatest]
  | challenge i hlive hclosing hstale =>
      simp [execStep, hclosing, hlive, hstale]
  | timeoutForfeit hlive hopen => simp [execStep, hlive, hopen]

/-- Successful executable actions preserve reachability and therefore all
proved conservation, no-overpay, and honest-close guarantees. -/
theorem execStep_reachable {D : ℕ} {s s' : St} {a : Act}
    (hs : Reach D s) (h : execStep D s a = some s') : Reach D s' :=
  Reach.step hs (execStep_sound h)

end Zkpc.Chain

#print axioms Zkpc.Chain.execStep_sound
#print axioms Zkpc.Chain.execStep_complete
#print axioms Zkpc.Chain.execStep_reachable
