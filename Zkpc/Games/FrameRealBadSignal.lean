import Zkpc.Games.FrameRealBadStep

/-!
# Honest-signal real/deferred FRAME step couplings (Spec.md §7 T7)

This file discharges the three honest-operation families left after the
public random-oracle couplings in `FrameRealBadStep`: `spend`, legacy
`close`, and `nfAt`.  Their closed/no-op, materialized-slope, and fresh-slope
branches are separated explicitly so every lazy sample is coupled exactly
once and every cache-divergence branch is charged to `FrameLeakBad`.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-- The common postcondition of a real/deferred step. -/
private def SignalStepPost (k : F) (γ : Type) :
    γ × AuditedFrameSt F M → γ × DSFrameSt F M → Prop :=
  fun p₁ p₂ => (p₁.1 = p₂.1 ∧ RealDSGood k p₁.2 p₂.2) ∨
    (FrameLeakBad k p₁.2.audit ∧ FrameLeakBad k p₂.2.audit)

/-- Legacy close against a closed member is likewise the same pure no-op. -/
theorem realDSStep_close_closed (k : F) (mclose : M)
    (r : AuditedFrameSt F M) (d : DSFrameSt F M) (hg : RealDSGood k r d)
    (hclosed : r.base.closed = true) :
    RelTriple (((auditedFrameImpl k mclose) (.close)).run r)
      (((dsFrameImpl k mclose) (.close)).run d)
      (SignalStepPost k ((frameSpec F M).Range (.close))) := by
  have hdclosed : d.ideal.closed = true := by
    rw [hg.1.closed_eq]
    exact hclosed
  simp only [auditedFrameImpl, frameImpl, dsFrameImpl, StateT.run_mk,
    hclosed, hdclosed, if_pos, pure_bind, auditAfter]
  exact relTriple_pure_pure (Or.inl ⟨rfl, hg⟩)

/-! ## Materialized `nfAt` -/

/-- Once index `i`'s deferred slope is pinned, `dsTouch` is deterministic;
erasing the private slope/audit ornaments makes the deferred `nfAt` step
literally the ideal indexed-nullifier step. -/
theorem dsFrameImpl_nfAt_materialized_project (k : F) (mclose : M)
    (i : ℕ) (a : F) (d : DSFrameSt F M) (ha : d.slope i = some a) :
    Prod.map id DSFrameSt.ideal <$>
        ((dsFrameImpl k mclose) (.nfAt i)).run d =
      ((idealFrameImpl mclose) (.nfAt i)).run d.ideal := by
  simp [dsFrameImpl, idealFrameImpl, StateT.run_mk, dsTouch, ha]

end Zkpc.Games

#print axioms Zkpc.Games.realDSStep_close_closed
#print axioms Zkpc.Games.dsFrameImpl_nfAt_materialized_project
