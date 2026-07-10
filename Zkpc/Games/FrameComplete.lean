import Zkpc.Games.FrameRealBadStep
import Zkpc.Games.FrameDSCountInduction
import Zkpc.Games.FrameGoodSliceTapeInduction

/-!
# Complete query-bounded FRAME theorem

This module is the final assembly boundary for the corrected, secret-averaged
T7 theorem.  The two adaptive inductions supply the good-slice transfer and
the deferred-slope bad-mass count; the already verified real/deferred step
coupling transports that count to the real execution.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Fintype F]
variable {M : Type} [DecidableEq M]

/-- The corrected secret-averaged deferred-sampling certificate for every
adversary satisfying the declared five query bounds. -/
noncomputable def frameDeferredSamplingAvg_holds (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) : FrameDeferredSamplingAvg mclose A qb :=
  frameDeferredSamplingAvg_of_goodSlice_and_realBad mclose A qb
    (frameGoodSliceTransfer_of_tape mclose A)
    (frameRealBadMassLe_of_dsCount mclose A qb
      (dsBadMassLe_of_queryBounds mclose A qb))

/-- Corrected secret-averaged FRAME/T7 bound with no residual coupling or
counting hypotheses, for every adversary carrying the five declared
query-bound certificates. -/
theorem T7_frame_query_bound_unconditional (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) :
    frameWinProb mclose A
      ≤ ((qb.total + 1 : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ :=
  T7_frame_query_bound_avg mclose A qb
    (frameDeferredSamplingAvg_holds mclose A qb)

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.frameGoodSliceTransfer_of_tape
#print axioms Zkpc.Games.dsBadMassLe_of_queryBounds
#print axioms Zkpc.Games.frameRealBadMassLe_of_dsCount
#print axioms Zkpc.Games.frameDeferredSamplingAvg_holds
#print axioms Zkpc.Games.T7_frame_query_bound_unconditional
