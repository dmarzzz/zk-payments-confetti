import Zkpc.Games.FrameGhost

/-!
# Quantitative bounds for the ghost FRAME transcript

This file begins the bad-mass lane of the averaged T7 proof.  Because the
ghost handler is secret-independent, the honest secret may be sampled after
the complete transcript.  Membership in a fixed transcript list then costs at
most its length divided by the field cardinality.  The final theorem applies
that elementary fact to the combined `roA`/`roE`/`roId` probe list and the
structural bounds already proved by `ghostFrameRun_audit_bounds`.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Fintype F]
variable {M : Type} [DecidableEq M]

/-- A uniform field element belongs to a fixed list with probability at most
the list length divided by the field cardinality.  Repetitions only make the
length bound more conservative. -/
theorem probEvent_uniform_mem_list_le (xs : List F) :
    Pr[(fun k : F => k ∈ xs) | ($ᵗ F)]
      ≤ (xs.length : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  rw [probEvent_uniformSample]
  have hcard : (Finset.univ.filter (fun k : F => k ∈ xs)).card ≤ xs.length := by
    calc
      (Finset.univ.filter (fun k : F => k ∈ xs)).card = xs.toFinset.card := by
        congr
        ext k
        simp
      _ ≤ xs.length := List.toFinset_card_le xs
  simpa [div_eq_mul_inv] using
    (ENNReal.mul_le_mul_right (Fintype.card F : ENNReal)⁻¹
      (ENNReal.natCast_le_natCast.2 hcard))

/-- Postponing the uniform secret until after an arbitrary transcript
computation preserves the fixed-list membership bound, provided every
supported transcript carries at most `q` candidates. -/
theorem probEvent_deferred_uniform_mem_list_le {α : Type}
    (gen : ProbComp α) (probes : α → List F) (q : ℕ)
    (hbound : ∀ z ∈ support gen, (probes z).length ≤ q) :
    Pr[(fun z : α × F => z.2 ∈ probes z.1) |
        (gen >>= fun z => ($ᵗ F) >>= fun k => pure (z, k))]
      ≤ (q : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  refine probEvent_bind_le_of_forall_le
    (ε := (q : ENNReal) * (Fintype.card F : ENNReal)⁻¹) ?_
  intro z hz
  rw [probEvent_bind_pure_comp]
  refine (probEvent_uniform_mem_list_le (probes z)).trans ?_
  exact ENNReal.mul_le_mul_right _ (ENNReal.natCast_le_natCast.2 (hbound z hz))

/-- The complete ghost FRAME run hits the deferred secret through a direct
`roA`, `roE`, or `roId` probe with probability at most
`(qA + qE + qId)/|F|`.  This discharges the direct-secret summand of the
averaged `FrameDeferredSamplingAvg` bad-event budget. -/
theorem ghostFrameRun_secret_probe_bound (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) :
    Pr[(fun z : (Evidence F × GhostFrameSt F M) × F =>
          z.2 ∈ z.1.2.audit.secretProbes) |
        (ghostFrameRun mclose A >>= fun z =>
          ($ᵗ F) >>= fun k => pure (z, k))]
      ≤ ((qb.qA + qb.qE + qb.qId : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  exact probEvent_deferred_uniform_mem_list_le
    (ghostFrameRun mclose A) (fun z => z.2.audit.secretProbes)
      (qb.qA + qb.qE + qb.qId)
      (ghostFrameRun_secretProbes_length mclose A qb)

end Zkpc.Games

#print axioms Zkpc.Games.probEvent_uniform_mem_list_le
#print axioms Zkpc.Games.probEvent_deferred_uniform_mem_list_le
#print axioms Zkpc.Games.ghostFrameRun_secret_probe_bound
