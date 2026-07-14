import Zkpc.Games.FrameRealBadStep

/-!
# Honest-signal real/deferred FRAME step couplings (Spec.md §7 T7)

The honest-operation step couplings themselves landed in
`Zkpc/Games/FrameRealBadStep.lean` (all eight operations, assembled into
`realDSStepCoupling_holds`).  This file keeps the complementary projection
substrate for the deferred handler used by the good-slice lane.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

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

#print axioms Zkpc.Games.dsFrameImpl_nfAt_materialized_project
