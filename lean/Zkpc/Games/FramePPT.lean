import Zkpc.Games.FrameAsymptotic

/-!
# Explicit PPT/cost lift for FRAME

`FrameAsymptotic` accepts a polynomial query bound directly.  This module
adds the missing runtime layer without baking in a particular virtual
machine: a `FrameCostModel` assigns a natural-number execution cost to each
security-parameter instance, and `PPTFrameFamily` certifies

1. the measured cost is bounded by one polynomial;
2. the concrete `FrameQueryBounds` certificate is bounded by measured cost.

The second condition is the cost-model soundness seam: every charged oracle
query must consume at least one cost unit.  From these two independently
reviewable facts, `pptFrameWinProb_negligible` derives the polynomial query
bound and applies unconditional T7.  A deployed VM refinement must instantiate
the cost function with its actual step/gas semantics and prove these fields.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F M : ℕ → Type}
variable [∀ n, Field (F n)] [∀ n, DecidableEq (F n)]
variable [∀ n, SampleableType (F n)] [∀ n, Fintype (F n)]
variable [∀ n, DecidableEq (M n)]

/-- A security-parameter-indexed operational cost semantics for FRAME
adversaries.  Different instances may use circuit constraints, VM steps, gas,
or another audited unit. -/
abbrev FrameCostModel :=
  (n : ℕ) →
    (F n → OracleComp (frameSpec (F n) (M n)) (Evidence (F n))) → ℕ

/-- Proof-bearing PPT classification of one FRAME adversary family under an
explicit cost model. -/
structure PPTFrameFamily
    (cost : FrameCostModel (F := F) (M := M))
    (A : (n : ℕ) →
      F n → OracleComp (frameSpec (F n) (M n)) (Evidence (F n))) where
  queryBounds : (n : ℕ) → FrameQueryBounds (A n)
  runtimePolynomial : Polynomial ℕ
  runtimeBound : ∀ n, cost n (A n) ≤ runtimePolynomial.eval n
  queryCostSound : ∀ n, (queryBounds n).total + 1 ≤ cost n (A n)

/-- A PPT certificate supplies the polynomial query numerator required by
the finite-to-asymptotic T7 lift. -/
theorem PPTFrameFamily.queryPolynomialBound
    {cost : FrameCostModel (F := F) (M := M)}
    {A : (n : ℕ) →
      F n → OracleComp (frameSpec (F n) (M n)) (Evidence (F n))}
    (ppt : PPTFrameFamily cost A) :
    ∀ n, (ppt.queryBounds n).total + 1 ≤ ppt.runtimePolynomial.eval n := by
  intro n
  exact (ppt.queryCostSound n).trans (ppt.runtimeBound n)

/-- **PPT-to-negligible unconditional T7.** Polynomial measured runtime,
query-cost soundness, and negligible inverse field size imply negligible
FRAME win probability. -/
theorem pptFrameWinProb_negligible
    (mclose : (n : ℕ) → M n)
    (A : (n : ℕ) →
      F n → OracleComp (frameSpec (F n) (M n)) (Evidence (F n)))
    (cost : FrameCostModel (F := F) (M := M))
    (ppt : PPTFrameFamily cost A)
    (hfield : negligible (fun n =>
      (Fintype.card (F n) : ENNReal)⁻¹)) :
    negligible (fun n => frameWinProb (mclose n) (A n)) :=
  frameWinProb_negligible_of_polynomial_query_bound
    mclose A ppt.queryBounds ppt.runtimePolynomial
      ppt.queryPolynomialBound hfield

end Zkpc.Games

#print axioms Zkpc.Games.PPTFrameFamily.queryPolynomialBound
#print axioms Zkpc.Games.pptFrameWinProb_negligible
