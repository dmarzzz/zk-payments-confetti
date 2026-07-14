import Zkpc.Games.FrameComplete
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Asymptotic lift of the finite FRAME bound

This module lifts the finite, query-bounded T7 theorem to a
security-parameter-indexed family.  The lift assumes directly that the
explicit finite-error sequence is negligible and transfers that fact to the
corresponding family of FRAME win probabilities.

This is only a scaling bridge.  It does not formalize a runtime or PPT
classifier for the adversary family, and it does not reduce a deployed hash
function to the ideal-oracle model.  In particular, it supplies neither a
PPT-to-polynomial-query theorem nor a field-growth theorem; the per-parameter
query certificates and negligibility of the displayed scaling sequence are
explicit hypotheses.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F M : ℕ → Type}
variable [∀ n, Field (F n)] [∀ n, DecidableEq (F n)]
variable [∀ n, SampleableType (F n)] [∀ n, Fintype (F n)]
variable [∀ n, DecidableEq (M n)]

/-- If the explicit query-to-field-size error bound is negligible across a
family of FRAME instances, then the corresponding win-probability family is
negligible.  Query boundedness remains an explicit certificate at every
security parameter. -/
theorem frameWinProb_negligible_of_query_bound
    (mclose : (n : ℕ) → M n)
    (A : (n : ℕ) →
      F n → OracleComp (frameSpec (F n) (M n)) (Evidence (F n)))
    (qb : (n : ℕ) → FrameQueryBounds (A n))
    (hscale : negligible (fun n =>
      (((qb n).total + 1 : ℕ) : ENNReal) /
        (Fintype.card (F n) : ENNReal))) :
    negligible (fun n => frameWinProb (mclose n) (A n)) :=
  negligible_of_le (fun n => by
    simpa only [div_eq_mul_inv] using
      T7_frame_query_bound_unconditional (mclose n) (A n) (qb n)) hscale

/-- A polynomial bound on the certified query numerator and negligible
inverse field cardinality imply negligible FRAME win probability.  This
corollary packages polynomial-query growth together with field growth; it
still does not classify adversary runtime or derive query bounds from a PPT
predicate. -/
theorem frameWinProb_negligible_of_polynomial_query_bound
    (mclose : (n : ℕ) → M n)
    (A : (n : ℕ) →
      F n → OracleComp (frameSpec (F n) (M n)) (Evidence (F n)))
    (qb : (n : ℕ) → FrameQueryBounds (A n))
    (p : Polynomial ℕ)
    (hqueries : ∀ n, (qb n).total + 1 ≤ p.eval n)
    (hfield : negligible (fun n =>
      (Fintype.card (F n) : ENNReal)⁻¹)) :
    negligible (fun n => frameWinProb (mclose n) (A n)) := by
  apply frameWinProb_negligible_of_query_bound mclose A qb
  refine negligible_of_le
    (g := fun n => ((p.eval n : ℕ) : ENNReal) *
      (Fintype.card (F n) : ENNReal)⁻¹) ?_
    (negligible_polynomial_mul hfield p)
  intro n
  rw [div_eq_mul_inv]
  exact mul_le_mul' (by exact_mod_cast hqueries n) le_rfl

end Zkpc.Games

#print axioms Zkpc.Games.frameWinProb_negligible_of_query_bound
#print axioms Zkpc.Games.frameWinProb_negligible_of_polynomial_query_bound
