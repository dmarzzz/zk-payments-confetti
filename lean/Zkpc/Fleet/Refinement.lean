import Zkpc.Fleet.T6

/-!
# Executable refinement for the gateway fleet

Deterministic operations corresponding to the fleet machine's clock,
admission, and reconciliation/slash transitions.  The success theorems tie
the executable guards directly to `FStep`, allowing T6 and the fleet
invariants to be applied to generated states.
-/

namespace Zkpc.Fleet

variable {N : ℕ} {P : Type} [DecidableEq P]

/-- Advance fleet time by one machine tick. -/
def execTick (s : FSt N P) : FSt N P := { s with clock := s.clock + 1 }

/-- Execute one gateway admission after all five fleet checks. -/
def execAccept (C D b Te : ℕ) (s : FSt N P) (g : Fin N) (i : ℕ)
    (m : Fin N × P) : Option (FSt N P) :=
  if m.1 = g ∧ s.slashed = none ∧ (i + 1) * C ≤ D ∧
      (∀ e ∈ s.log, e.gw = g → e.idx ≠ i) ∧
      rateCount Te s.log g (s.clock / Te) < b then
    some { s with log := insert ⟨s.clock, g, i, m⟩ s.log }
  else none

/-- Execute fleet-wide identity slashing once reconciled evidence exists. -/
def execSlash (s : FSt N P) : Option (FSt N P) :=
  if (∃ e₁ ∈ s.log, ∃ e₂ ∈ s.log, Conflict e₁ e₂) ∧
      s.slashed = none then
    some { s with slashed := some s.clock }
  else none

/-- Executable ticking is exactly `FStep.tick`. -/
theorem execTick_refines_step (C D b Te : ℕ) (s : FSt N P) :
    FStep C D b Te s (execTick s) := by
  exact FStep.tick s

/-- A successful executable admission is exactly `FStep.accept`. -/
theorem execAccept_refines_step (C D b Te : ℕ) (s : FSt N P)
    (g : Fin N) (i : ℕ) (m : Fin N × P)
    (hbind : m.1 = g) (hslash : s.slashed = none)
    (hsolv : (i + 1) * C ≤ D)
    (hfresh : ∀ e ∈ s.log, e.gw = g → e.idx ≠ i)
    (hrate : rateCount Te s.log g (s.clock / Te) < b) :
    ∃ s', execAccept C D b Te s g i m = some s' ∧
      FStep C D b Te s s' := by
  let s' : FSt N P := { s with log := insert ⟨s.clock, g, i, m⟩ s.log }
  refine ⟨s', ?_, ?_⟩
  · have hfresh' : ∀ e ∈ s.log, e.gw = g → ¬ e.idx = i := by
      intro e he heg hei
      exact hfresh e he heg hei
    have hguard : m.1 = g ∧ s.slashed = none ∧ (i + 1) * C ≤ D ∧
        (∀ e ∈ s.log, e.gw = g → ¬ e.idx = i) ∧
        rateCount Te s.log g (s.clock / Te) < b :=
      ⟨hbind, hslash, hsolv, hfresh', hrate⟩
    rw [execAccept, if_pos hguard]
  · exact FStep.accept s g i m hbind hslash hsolv hfresh hrate

/-- A successful executable reconciliation slash is exactly `FStep.slash`. -/
theorem execSlash_refines_step (C D b Te : ℕ) (s : FSt N P)
    (hconf : ∃ e₁ ∈ s.log, ∃ e₂ ∈ s.log, Conflict e₁ e₂)
    (hns : s.slashed = none) :
    ∃ s', execSlash s = some s' ∧ FStep C D b Te s s' := by
  let s' : FSt N P := { s with slashed := some s.clock }
  refine ⟨s', by simp [execSlash, hconf, hns, s'], FStep.slash s hconf hns⟩

/-- A refined fleet operation extends an executable reachable trace. -/
theorem exec_step_reachable (C D b Te : ℕ) {s s' : FSt N P}
    (hreach : FReach C D b Te s) (hstep : FStep C D b Te s s') :
    FReach C D b Te s' :=
  FReach.step hreach hstep

end Zkpc.Fleet

#print axioms Zkpc.Fleet.execTick_refines_step
#print axioms Zkpc.Fleet.execAccept_refines_step
#print axioms Zkpc.Fleet.execSlash_refines_step
#print axioms Zkpc.Fleet.exec_step_reachable
