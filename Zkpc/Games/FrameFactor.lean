import Zkpc.Games.FrameGhost
import Zkpc.Games.FrameCoupling

/-!
# The off-bad factorization socket for the k-averaged T7 certificate (Spec.md §7 T7)

The corrected T7 composition (`FrameDeferredSamplingAvg`, `T7_frame_query_bound_avg`)
consumes a *k-averaged* comparison between the real FRAME evidence process and one
secret-independent generator. This file builds the identical-until-bad *factorization*
of that comparison through the audited real run (`auditedFrameImpl`) and the ghost run
(`ghostFrameRun`):

    Pr[k ← $ᵗF; real run; Slashes k ev]
      ≤ Pr[ghost run; k ← $ᵗF; Slashes k ev']       (win mass, secret deferred)
        + Pr[ghost run; k ← $ᵗF; GhostLeakBad k audit']   (bad mass, secret deferred)

The derivation chain, fully proved here:

1. `auditedFrameRun` — the real evidence process with the write-only audit ornament
   kept, and `fst_map_auditedFrameRun` — its exact erasure back to `frameEvidence`
   (so probabilities of evidence tests are unchanged by auditing).
2. `frameRealSlashGame_eq_auditedJoint` — the master's left side rewritten as a
   decidable test over the audited joint experiment `auditedFrameJoint` (secret first,
   audited run, keep the secret, evidence, and final audit).
3. `probOutput_bind_decide_le_split` — the generic identical-until-bad split
   `Pr[P] ≤ Pr[P ∧ ¬Q] + Pr[Q]` for decidable tests behind one generator.
4. `frame_real_le_ghost_plus_bad` — the master theorem, assembled from 1–3 and the
   two run-level transfer inequalities.

The two transfer inequalities are the named residual hypotheses of the master
theorem (house convention: open sub-proofs are explicit named hypotheses, never
silent gaps):

* `FrameGoodSliceTransfer` — the good-slice coupling: the k-averaged probability
  that the real run both slashes and never trips the audited leakage event is at
  most the deferred-secret ghost win probability. On the good slice every honest
  `y = k + a·x` is uniformized by its fresh hidden slope, every public oracle
  answer is exactly coupled (`idealize_roX/roA/roE/roId/roNf_step`,
  `idealize_nfAt_step_cached/freshNf`), and the ghost ornament erases
  (`ghostFrameEvidence_evalDist_eq`).
* `FrameBadMassTransfer` — the bad-mass coupling: the k-averaged probability that
  the real audited run ends with `FrameLeakBad k` is at most the deferred-secret
  probability that the ghost audit fails `GhostLeakBad k`. Since `OracleComp` is a
  plain free monad (no failure leaf), runs are total, both bad events are
  monotone (`auditedFrameImpl_run_bad_monotone`, `ghostFrameImpl_run_bad_monotone`),
  and bad-at-end coincides with bad-ever-fired on both sides.

The transfer predicates remain explicit residuals: this module performs the
run-level probability algebra but does not claim the continuation-level
fresh-slope induction. Its per-operation ingredients live in
`FrameCoupling`, `FrameGhostCoupling`, and `FrameGhostCoverage`.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## The audited real run and its erasure -/

/-- The complete audited real run of a FRAME adversary at honest secret `k`:
sample the public commitment, program `H_id(k) = cm` exactly as `frameEvidence`
does, and run the adversary against the audited real handler, keeping the final
audited state. This is the real-side object of the k-averaged coupling. -/
def auditedFrameRun (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) (k : F) :
    ProbComp (Evidence F × AuditedFrameSt F M) := do
  let cm ← ($ᵗ F)
  (simulateQ (auditedFrameImpl k mclose) (A cm)).run
    ⟨{ FrameSt.init F M with
        roId := Function.update (FrameSt.init F M).roId k (some cm) },
      FrameAudit.init⟩

/-- **Audit erasure of the real run.** Dropping the final audited state from
`auditedFrameRun` gives back exactly `frameEvidence`: the audit ornament is
write-only, so the real evidence process is unchanged by auditing. -/
theorem fst_map_auditedFrameRun (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) (k : F) :
    Prod.fst <$> auditedFrameRun mclose A k = frameEvidence mclose A k := by
  unfold auditedFrameRun frameEvidence
  rw [lazyRO_eq_of_none (rfl : (FrameSt.init F M).roId k = none), bind_assoc,
    map_bind]
  refine bind_congr fun cm => ?_
  rw [pure_bind, ← StateT.run'_eq]
  exact OracleComp.run'_simulateQ_eq_of_query_map_eq
    (auditedFrameImpl k mclose) (frameImpl k mclose) AuditedFrameSt.base
    (fun t s => auditedFrameImpl_project_step k mclose t s) (A cm) _

/-- The audited joint FRAME experiment: draw the honest secret first (as the real
game does), run the audited real evidence process, and keep the secret together
with the evidence and the final audited state. All real-side win/bad tests of the
k-averaged certificate are decidable tests over this one generator. -/
def auditedFrameJoint (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    ProbComp (F × (Evidence F × AuditedFrameSt F M)) := do
  let k ← ($ᵗ F)
  let z ← auditedFrameRun mclose A k
  pure (k, z)

/-- The k-averaged real slash game — the left side of the corrected T7
certificate — is exactly the `Slashes` test over the audited joint experiment.
Pure monad-law reassociation plus the audit erasure. -/
theorem frameRealSlashGame_eq_auditedJoint (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    (do
      let k ← ($ᵗ F)
      let ev ← frameEvidence mclose A k
      pure (decide (Slashes k ev)))
    = auditedFrameJoint mclose A >>= fun w =>
        pure (decide (Slashes w.1 w.2.1)) := by
  unfold auditedFrameJoint
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun k => ?_
  rw [← fst_map_auditedFrameRun mclose A k, bind_map_left]

/-! ## Generic split and decide/event bridges -/

/-- Splitting a decidable test behind one generator along a second decidable
test: `Pr[P] ≤ Pr[P ∧ ¬Q] + Pr[Q]`. This is the probability-level shape of the
fundamental identical-until-bad decomposition. -/
theorem probOutput_bind_decide_le_split {α : Type} (oa : ProbComp α)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    Pr[= true | oa >>= fun z => pure (decide (P z))]
      ≤ Pr[= true | oa >>= fun z => pure (decide (P z ∧ ¬ Q z))]
        + Pr[= true | oa >>= fun z => pure (decide (Q z))] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun z => ?_
  rw [← mul_add]
  refine mul_le_mul_right ?_ _
  by_cases hp : P z <;> by_cases hq : Q z <;> simp [hp, hq]

/-- A decidable test delivered as a `Bool` output has the same probability as
the corresponding event over the bare generator. Bridges the `decide`-style
games of this file to the `probEvent`-style bounds of the bad-mass lane
(`ghostFrameRun_secret_probe_bound`). -/
theorem probOutput_bind_decide_eq_probEvent {α : Type} (oa : ProbComp α)
    (P : α → Prop) [DecidablePred P] :
    Pr[= true | oa >>= fun z => pure (decide (P z))] = Pr[P | oa] := by
  conv_rhs => rw [← bind_pure oa]
  rw [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun z => ?_
  by_cases h : P z <;> simp [h, probEvent_pure, probOutput_pure]

/-! ## The two named transfer residuals

These are the two run-level coupling inequalities that the master theorem
consumes. They are stated as named `Prop`s (house convention for open
sub-proofs): the coupling lane discharges them by the two-functional
k-averaged induction over the adversary computation, whose per-operation
ingredients are the landed `idealize_*_step` lemmas, ghost erasure, and the
real/ghost invariants. -/

/-- **Good-slice transfer (named residual).** The k-averaged probability that
the real audited run slashes *and* never trips the audited leakage event is at
most the deferred-secret ghost win probability. True because off the bad event
every real oracle answer is exactly coupled to the ghost answer and each honest
line value is uniformized by its fresh hidden slope; restricting the ghost side
to its own good slice is then dropped (monotone weakening). -/
def FrameGoodSliceTransfer (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) : Prop :=
  Pr[= true | auditedFrameJoint mclose A >>= fun w =>
      pure (decide (Slashes w.1 w.2.1 ∧ ¬ FrameLeakBad w.1 w.2.2.audit))]
    ≤ Pr[= true | (do
        let z ← ghostFrameRun mclose A
        let k ← ($ᵗ F)
        pure (decide (Slashes k z.1)))]

/-- **Bad-mass transfer (named residual).** The k-averaged probability that the
real audited run ends in the leakage event is at most the deferred-secret
probability that the ghost audit fails `GhostLeakBad`. True because both bad
events are suffix-monotone, runs are total (`OracleComp` has no failure leaf),
the probe lists agree along the off-bad coupling, and each first-fire step has
identical k-averaged mass on the two sides. -/
def FrameBadMassTransfer (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) : Prop :=
  Pr[= true | auditedFrameJoint mclose A >>= fun w =>
      pure (decide (FrameLeakBad w.1 w.2.2.audit))]
    ≤ Pr[= true | (do
        let z ← ghostFrameRun mclose A
        let k ← ($ᵗ F)
        pure (decide (GhostLeakBad k z.2.audit)))]

/-! ## The master theorem -/

/-- **The k-averaged identical-until-bad master inequality** (Spec.md §7 T7,
composition layer). The complete real FRAME slash probability — secret drawn
first, exactly as `frameGame` does — is bounded by the ghost run's win mass
plus the ghost run's bad mass, both with the secret deferred to *after* the
run. Assembled, fully proved, from the audit erasure, the generic split, and
the two named transfer residuals; instantiating `FrameGoodSliceTransfer` and
`FrameBadMassTransfer` is the remaining coupling obligation. -/
theorem frame_real_le_ghost_plus_bad (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (hgood : FrameGoodSliceTransfer mclose A)
    (hbad : FrameBadMassTransfer mclose A) :
    Pr[= true | (do
        let k ← ($ᵗ F)
        let ev ← frameEvidence mclose A k
        pure (decide (Slashes k ev)))]
      ≤ Pr[= true | (do
          let z ← ghostFrameRun mclose A
          let k ← ($ᵗ F)
          pure (decide (Slashes k z.1)))]
        + Pr[= true | (do
            let z ← ghostFrameRun mclose A
            let k ← ($ᵗ F)
            pure (decide (GhostLeakBad k z.2.audit)))] := by
  rw [frameRealSlashGame_eq_auditedJoint mclose A]
  refine le_trans (probOutput_bind_decide_le_split (auditedFrameJoint mclose A)
    (fun w => Slashes w.1 w.2.1) (fun w => FrameLeakBad w.1 w.2.2.audit)) ?_
  exact add_le_add hgood hbad

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.fst_map_auditedFrameRun
#print axioms Zkpc.Games.frameRealSlashGame_eq_auditedJoint
#print axioms Zkpc.Games.probOutput_bind_decide_le_split
#print axioms Zkpc.Games.probOutput_bind_decide_eq_probEvent
#print axioms Zkpc.Games.frame_real_le_ghost_plus_bad
