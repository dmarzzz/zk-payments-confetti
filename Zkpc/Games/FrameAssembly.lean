import Zkpc.Games.FrameFactor
import Zkpc.Games.FrameBadMass

/-!
# Assembly of the k-averaged T7 certificate (Spec.md §7 T7)

This file stitches the three landed lanes of the corrected T7 proof into the
composition endpoint:

* the **master factorization** `frame_real_le_ghost_plus_bad`
  (`Zkpc/Games/FrameFactor.lean`): the k-averaged real slash probability is
  bounded by the deferred-secret ghost win mass plus the deferred-secret
  ghost bad mass, given the two named transfer residuals
  `FrameGoodSliceTransfer` / `FrameBadMassTransfer`;
* the **ghost bad-mass budget** `ghostFrameRun_leak_bad_bound`
  (`Zkpc/Games/FrameGhostBounds.lean`): the deferred-secret ghost leakage
  event costs at most `qb.total/|F|` given the slope-dependent socket
  `GhostSlopeBadBounds` (whose direct-secret summand is already
  unconditional and whose two slope fields are supplied by the slope-tape
  lane of `Zkpc/Games/FrameBadMass.lean`);
* the **ghost erasure** `fst_map_ghostFrameRun` / `ghostFrameEvidence`
  (`Zkpc/Games/FrameGhost.lean`): the ghost win mass is exactly the
  secret-averaged slash probability of the secret-independent evidence
  generator, in the shape consumed by `FrameDeferredSamplingAvg`.

Consequently `frameDeferredSamplingAvg_of_transfers` constructs the corrected
averaged deferred-sampling certificate for every query-bounded adversary from
the two transfer residuals and the slope socket, and
`T7_frame_query_bound_of_transfers` derives the complete corrected FRAME
bound `(qb.total + 1)/|F|`. The entire unconditional Spec.md §7 T7 obligation
is thereby reduced to discharging `FrameGoodSliceTransfer`,
`FrameBadMassTransfer` (the run-level off-bad coupling between the audited
real handler and the ghost handler) and `GhostSlopeBadBounds` (the ghost-side
slope-tape masses, whose closing induction lives in the bad-mass lane).
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-- **The ghost win mass in certificate shape.** The deferred-secret slash
probability of the paired ghost run equals the secret-averaged slash
probability of the secret-independent generator `ghostFrameEvidence`: the
final ghost state is discarded by the win test, and the independent uniform
secret commutes to the front. -/
theorem ghostFrameRun_win_eq_certificate_form (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    Pr[= true | (do
        let z ← ghostFrameRun mclose A
        let k ← ($ᵗ F)
        pure (decide (Slashes k z.1)))]
      = Pr[= true | (do
          let k ← ($ᵗ F)
          let ev ← ghostFrameEvidence mclose A
          pure (decide (Slashes k ev)))] := by
  have hmarg : (do
      let z ← ghostFrameRun mclose A
      let k ← ($ᵗ F)
      pure (decide (Slashes k z.1)))
      = (ghostFrameEvidence mclose A >>= fun ev =>
          ($ᵗ F) >>= fun k => pure (decide (Slashes k ev))) := by
    rw [← fst_map_ghostFrameRun mclose A, bind_map_left]
  rw [hmarg]
  exact (probOutput_congr rfl
    (OracleComp.DeferredSampling.evalDist_bind_comm ($ᵗ F)
      (ghostFrameEvidence mclose A)
      (fun k ev => pure (decide (Slashes k ev))))).symm

section Assembly

variable [Fintype F]

/-- **The deferred-secret ghost bad mass in certificate shape.** The
Boolean-decided ghost leakage probability equals the event-form probability
over `ghostDeferredRun`, so the `GhostSlopeBadBounds` socket pays the full
`qb.total/|F|` budget in the shape the master factorization emits. -/
theorem ghostFrameRun_leakBad_decide_le (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (hs : GhostSlopeBadBounds mclose A qb) :
    Pr[= true | (do
        let z ← ghostFrameRun mclose A
        let k ← ($ᵗ F)
        pure (decide (GhostLeakBad k z.2.audit)))]
      ≤ (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  have hprog : (do
      let z ← ghostFrameRun mclose A
      let k ← ($ᵗ F)
      pure (decide (GhostLeakBad k z.2.audit)))
      = (ghostDeferredRun mclose A >>= fun w =>
          pure (decide (GhostLeakBad w.2 w.1.2.audit))) := by
    simp only [ghostDeferredRun, bind_assoc, pure_bind]
  rw [hprog, probOutput_bind_decide_eq_probEvent]
  exact ghostFrameRun_leak_bad_bound mclose A qb hs

/-- **Assembly of the corrected T7 certificate** (Spec.md §7 T7). For every
query-bounded FRAME adversary, the two run-level transfer residuals and the
ghost slope socket construct the k-averaged deferred-sampling certificate
outright: the secret-independent generator is the ghost evidence process,
the win mass transports through the ghost erasure and secret commutation,
and the bad mass is paid by the `qb.total/|F|` ghost leakage budget. -/
noncomputable def frameDeferredSamplingAvg_of_transfers (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (hgood : FrameGoodSliceTransfer mclose A)
    (hbad : FrameBadMassTransfer mclose A)
    (hs : GhostSlopeBadBounds mclose A qb) :
    FrameDeferredSamplingAvg mclose A qb where
  idealEvidence := ghostFrameEvidence mclose A
  close_avg := by
    refine le_trans (frame_real_le_ghost_plus_bad mclose A hgood hbad) ?_
    exact add_le_add
      (le_of_eq (ghostFrameRun_win_eq_certificate_form mclose A))
      (ghostFrameRun_leakBad_decide_le mclose A qb hs)

/-- **The corrected FRAME bound from the named residuals** (Spec.md §7 T7).
For every query-bounded adversary, the two run-level transfer inequalities
and the ghost slope socket yield the complete corrected exculpability bound
`(qb.total + 1)/|F|`: the whole remaining unconditional T7 obligation is
exactly `FrameGoodSliceTransfer ∧ FrameBadMassTransfer ∧
GhostSlopeBadBounds`. -/
theorem T7_frame_query_bound_of_transfers (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (hgood : FrameGoodSliceTransfer mclose A)
    (hbad : FrameBadMassTransfer mclose A)
    (hs : GhostSlopeBadBounds mclose A qb) :
    frameWinProb mclose A
      ≤ ((qb.total + 1 : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ :=
  T7_frame_query_bound_avg mclose A qb
    (frameDeferredSamplingAvg_of_transfers mclose A qb hgood hbad hs)

/-- The corrected deferred-sampling certificate now needs only the two
real/ghost transfer lemmas: the ghost slope socket is unconditional. -/
noncomputable def frameDeferredSamplingAvg_of_realGhostTransfers (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (hgood : FrameGoodSliceTransfer mclose A)
    (hbad : FrameBadMassTransfer mclose A) :
    FrameDeferredSamplingAvg mclose A qb :=
  frameDeferredSamplingAvg_of_transfers mclose A qb hgood hbad
    (ghostSlopeBadBounds_holds mclose A qb)

/-- **Unconditional ghost-side T7 assembly.** Once the two real/ghost
identical-until-bad transfers are proved, no quantitative or slope-dependent
hypothesis remains. -/
theorem T7_frame_query_bound_of_realGhostTransfers (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (hgood : FrameGoodSliceTransfer mclose A)
    (hbad : FrameBadMassTransfer mclose A) :
    frameWinProb mclose A
      ≤ ((qb.total + 1 : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ :=
  T7_frame_query_bound_of_transfers mclose A qb hgood hbad
    (ghostSlopeBadBounds_holds mclose A qb)

end Assembly

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.ghostFrameRun_win_eq_certificate_form
#print axioms Zkpc.Games.T7_frame_query_bound_of_transfers
#print axioms Zkpc.Games.T7_frame_query_bound_of_realGhostTransfers
