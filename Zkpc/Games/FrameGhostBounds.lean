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

omit [Field F] in
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
  simp only [div_eq_mul_inv]
  gcongr

/-- Postponing the uniform secret until after an arbitrary transcript
computation preserves the fixed-list membership bound, provided every
supported transcript carries at most `q` candidates. -/
omit [Field F] in
theorem probEvent_deferred_uniform_mem_list_le {α : Type}
    (gen : ProbComp α) (probes : α → List F) (q : ℕ)
    (hbound : ∀ z ∈ support gen, (probes z).length ≤ q) :
    Pr[(fun z : α × F => z.2 ∈ probes z.1) |
        (gen >>= fun z => ($ᵗ F) >>= fun k => pure (z, k))]
      ≤ (q : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  refine probEvent_bind_le_of_forall_le
    (ε := (q : ENNReal) * (Fintype.card F : ENNReal)⁻¹) ?_
  intro z hz
  have hmem := probEvent_uniform_mem_list_le (F := F) (probes z)
  have hq : ((probes z).length : ENNReal) * (Fintype.card F : ENNReal)⁻¹ ≤
      (q : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
    gcongr
    exact hbound z hz
  rw [show (do let k ← ($ᵗ F); pure (z, k)) =
      ($ᵗ F) >>= (pure ∘ fun k => (z, k)) from rfl,
    probEvent_bind_pure_comp]
  change Pr[(fun k : F => k ∈ probes z) | ($ᵗ F)] ≤ _
  exact hmem.trans hq

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

/-! ## Assembly socket for the two slope-dependent terms -/

/-- The complete ghost transcript paired with a secret sampled only after the
secret-independent run. -/
def ghostDeferredRun (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    ProbComp ((Evidence F × GhostFrameSt F M) × F) :=
  ghostFrameRun mclose A >>= fun z => ($ᵗ F) >>= fun k => pure (z, k)

/-- The two genuinely slope-dependent probability obligations.  Keeping them
together makes the remaining T7 boundary precise: the direct-secret term is
already discharged above, while these fields are supplied by the forthcoming
continuation-level hidden-slope argument. -/
structure GhostSlopeBadBounds (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) : Prop where
  slope_hit :
    Pr[(fun z => ∃ slope ∈ z.1.2.audit.slopeProbes,
          slope ∈ z.1.2.audit.honestSlopes) | ghostDeferredRun mclose A]
      ≤ ((qb.qNf * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹
  honest_collision :
    Pr[(fun z => ¬ z.1.2.audit.honestSlopes.Nodup) |
        ghostDeferredRun mclose A]
      ≤ ((qb.qSig * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹

/-- Union-bound assembly of the complete ghost leakage budget.  Once the two
hidden-slope fields are constructed, all three bad-event branches cost exactly
`qb.total/|F|`, with no extra constants hidden at composition time. -/
theorem ghostFrameRun_leak_bad_bound (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (hs : GhostSlopeBadBounds mclose A qb) :
    Pr[(fun z => GhostLeakBad z.2 z.1.2.audit) | ghostDeferredRun mclose A]
      ≤ (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  let run := ghostDeferredRun mclose A
  let direct : ((Evidence F × GhostFrameSt F M) × F) → Prop :=
    fun z => z.2 ∈ z.1.2.audit.secretProbes
  let slopeHit : ((Evidence F × GhostFrameSt F M) × F) → Prop :=
    fun z => ∃ slope ∈ z.1.2.audit.slopeProbes, slope ∈ z.1.2.audit.honestSlopes
  let collision : ((Evidence F × GhostFrameSt F M) × F) → Prop :=
    fun z => ¬ z.1.2.audit.honestSlopes.Nodup
  have hdirect : Pr[direct | run] ≤
      ((qb.qA + qb.qE + qb.qId : ℕ) : ENNReal) *
        (Fintype.card F : ENNReal)⁻¹ := by
    simpa [run, direct, ghostDeferredRun] using
      ghostFrameRun_secret_probe_bound mclose A qb
  have hunion : Pr[(fun z => direct z ∨ slopeHit z ∨ collision z) | run]
      ≤ Pr[direct | run] + (Pr[slopeHit | run] + Pr[collision | run]) :=
    (probEvent_or_le run direct (fun z => slopeHit z ∨ collision z)).trans
      (add_le_add le_rfl (probEvent_or_le run slopeHit collision))
  change Pr[(fun z => direct z ∨ slopeHit z ∨ collision z) | run] ≤ _
  refine hunion.trans ((add_le_add hdirect
    (add_le_add hs.slope_hit hs.honest_collision)).trans ?_)
  simp only [FrameQueryBounds.total, Nat.cast_add, Nat.cast_mul, add_mul]
  simp only [add_assoc]
  exact le_refl _

end Zkpc.Games

#print axioms Zkpc.Games.probEvent_uniform_mem_list_le
#print axioms Zkpc.Games.probEvent_deferred_uniform_mem_list_le
#print axioms Zkpc.Games.ghostFrameRun_secret_probe_bound
#print axioms Zkpc.Games.ghostFrameRun_leak_bad_bound
