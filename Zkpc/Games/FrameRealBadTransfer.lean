import Zkpc.Games.FrameRealBad

/-!
# Stage-1 wiring: real bad mass ≤ deferred-slope bad mass (Spec.md §7 T7)

This file assembles the route-B reduction skeleton on top of the
deferred-slope handler of `Zkpc/Games/FrameRealBad.lean`. It fixes the
good-state relation `RealDSGood` of the identical-until-bad coupling, states
the per-operation coupling obligation `RealDSStepCoupling` as a named
residual (house convention: open sub-proofs are explicit named hypotheses),
and derives from it — through the generic absorbing rule
`relTriple_simulateQ_run_untilAbsorbing` — the complete run-level and
k-averaged transfer of the audited leakage mass from the real handler to the
deferred-slope handler. Combined with the deferred-slope counting residual
`DSBadMassLe` (stage 2, the k-root union bound), this discharges
`FrameRealBadMassLe`, which the landed assembly
`T7_frame_query_bound_of_goodSlice_and_realBad` consumes.

The reduction surface after this file is exactly:
`RealDSStepCoupling` (eight per-operation coupled steps) and
`DSBadMassLe` (first-order k-root counting over the deferred run).
-/

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## The good-state relation of the stage-1 coupling -/

/-- Good-state relation for the real/deferred-slope identical-until-bad
coupling: the deferred state is the canonical secret-erasure of the real
state with the hidden slopes retained (`RealDSCoupled`), every pinned
deferred slope is recorded (`DSSlopesCovered`), every populated real `H_nf`
key is a recorded probe or recorded honest slope (`RoNfCovered`), hidden real
slopes are injective across indices (`HiddenSlopeInj`), and the shared
audit has not raised the leakage event. -/
def RealDSGood (k : F) (r : AuditedFrameSt F M) (d : DSFrameSt F M) : Prop :=
  RealDSCoupled k r d ∧ DSSlopesCovered d ∧ RoNfCovered r ∧
    HiddenSlopeInj k r ∧ ¬ FrameLeakBad k r.audit

omit [Field F] [SampleableType F] in
/-- The empty audit never raises the leakage event. -/
theorem not_frameLeakBad_init (k : F) :
    ¬ FrameLeakBad k (FrameAudit.init (F := F)) := by
  intro h
  rcases h with h | ⟨s, hs, -⟩ | h
  · simp [FrameAudit.init] at h
  · simp [FrameAudit.init] at hs
  · exact h (by simp [FrameAudit.init])

/-- The programmed real initial state and the empty deferred state are
good-related for every secret and sampled commitment. -/
theorem realDSGood_initial (k cm : F) :
    RealDSGood k
      (⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩ : AuditedFrameSt F M)
      (DSFrameSt.init F M) := by
  refine ⟨realDSCoupled_initial k cm, dsSlopesCovered_init, ?_, ?_, ?_⟩
  · intro aq v h
    simp [FrameSt.init] at h
  · exact hiddenSlopeInj_initial k cm
  · exact not_frameLeakBad_init k

/-! ## The per-operation coupling obligation (named residual) -/

/-- **Stage-1 per-operation coupling (named residual).** From good-related
states, each coupled real/deferred oracle step either returns equal answers
with good-related next states, or raises the (shared) audited leakage event
on both sides simultaneously. True by the divergence enumeration recorded in
`OPEN-PROOFS.md` §1: direct probes at the secret, `H_nf` probes at recorded
honest slopes, fresh honest slopes colliding with recorded probes or
slopes, and `H_id(k)` probes each mark the audit bad on both sides in the
same step, while every other step is answer- and audit-identical under the
cache relation. -/
def RealDSStepCoupling (k : F) (mclose : M) : Prop :=
  ∀ (op : FrameOp F M) (r : AuditedFrameSt F M) (d : DSFrameSt F M),
    RealDSGood k r d →
    RelTriple (((auditedFrameImpl k mclose) op).run r)
      (((dsFrameImpl k mclose) op).run d)
      (fun p₁ p₂ => (p₁.1 = p₂.1 ∧ RealDSGood k p₁.2 p₂.2) ∨
        (FrameLeakBad k p₁.2.audit ∧ FrameLeakBad k p₂.2.audit))

/-! ## Run-level and averaged bad-mass transfer -/

/-- **Fixed-secret run-level bad-mass transfer.** Under the per-operation
coupling, the probability that a full adaptive real run ends in the audited
leakage event is at most the same probability for the deferred-slope run:
runs agree until the leakage event, which fires simultaneously and is
absorbing on both sides (Spec.md §7 T7, stage-1 endpoint). -/
theorem auditedFrameImpl_bad_le_ds (k cm : F) (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α)
    (hstep : RealDSStepCoupling (F := F) (M := M) k mclose) :
    Pr[fun z : α × AuditedFrameSt F M => FrameLeakBad k z.2.audit |
        (simulateQ (auditedFrameImpl k mclose) oa).run
          ⟨{ FrameSt.init F M with
              roId := Function.update (FrameSt.init F M).roId k (some cm) },
            FrameAudit.init⟩]
      ≤ Pr[fun z : α × DSFrameSt F M => FrameLeakBad k z.2.audit |
          (simulateQ (dsFrameImpl k mclose) oa).run (DSFrameSt.init F M)] := by
  refine probEvent_le_of_untilAbsorbing
    (auditedFrameImpl k mclose) (dsFrameImpl k mclose)
    (RealDSGood k) (fun r => FrameLeakBad k r.audit)
    (fun d => FrameLeakBad k d.audit)
    (fun t s hb z hz => auditedFrameImpl_bad_monotone k mclose t s hb z hz)
    (fun t s hb z hz => dsFrameImpl_bad_monotone k mclose t s hb z hz)
    (fun t r d hg => hstep t r d hg)
    oa _ _ (realDSGood_initial k cm) _ _ ?_ ?_
  · intro z₁ z₂ heq hg hbad
    exact absurd hbad hg.2.2.2.2
  · intro z₂ hb
    exact hb

/-- Event-monotone bind: pointwise domination of the continuation event
masses transports through a shared sampling prefix. -/
theorem probEvent_bind_mono_of_le {α β γ : Type} (oa : ProbComp α)
    (f : α → ProbComp β) (g : α → ProbComp γ)
    (P : β → Prop) (Q : γ → Prop)
    (h : ∀ a, Pr[P | f a] ≤ Pr[Q | g a]) :
    Pr[P | oa >>= f] ≤ Pr[Q | oa >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _

/-- The complete deferred-slope joint experiment: honest secret first, then
the deferred-slope run, keeping the secret with the evidence and final
deferred state. This is the stage-2 counting target. -/
def dsFrameJoint (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    ProbComp (F × (Evidence F × DSFrameSt F M)) := do
  let k ← ($ᵗ F)
  let z ← dsFrameRun k mclose A
  pure (k, z)

/-- **k-averaged bad-mass transfer.** Under the per-operation coupling at
every secret, the audited real leakage mass of the joint experiment is at
most the deferred-slope leakage mass of the deferred joint experiment
(Spec.md §7 T7). -/
theorem auditedFrameJoint_bad_le_dsFrameJoint (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (hstep : ∀ k : F, RealDSStepCoupling (F := F) (M := M) k mclose) :
    Pr[fun w => FrameLeakBad w.1 w.2.2.audit | auditedFrameJoint mclose A]
      ≤ Pr[fun w => FrameLeakBad w.1 w.2.2.audit | dsFrameJoint mclose A] := by
  unfold auditedFrameJoint dsFrameJoint
  refine probEvent_bind_mono_of_le _ _ _ _ _ fun k => ?_
  have hpair₁ : ∀ z : Evidence F × AuditedFrameSt F M,
      (pure (k, z) : ProbComp (F × (Evidence F × AuditedFrameSt F M)))
        = (pure ∘ fun z => (k, z)) z := fun _ => rfl
  rw [funext hpair₁, probEvent_bind_pure_comp]
  have hpair₂ : ∀ z : Evidence F × DSFrameSt F M,
      (pure (k, z) : ProbComp (F × (Evidence F × DSFrameSt F M)))
        = (pure ∘ fun z => (k, z)) z := fun _ => rfl
  rw [funext hpair₂, probEvent_bind_pure_comp]
  unfold auditedFrameRun dsFrameRun
  refine probEvent_bind_mono_of_le _ _ _ _ _ fun cm => ?_
  simpa using auditedFrameImpl_bad_le_ds k cm mclose (A cm) (hstep k)

section Counting

variable [Fintype F]

/-- **Stage-2 counting obligation (named residual).** The k-averaged
leakage mass of the deferred-slope run is at most `qb.total/|F|`: with the
honest nullifiers private and hidden slopes read only through
`y = k + a·x`, every leakage branch pins the uniform secret or one fresh
slope to a single root per budget pair — `qA + qE + qId` direct-probe
roots, `qNf · qSig` slope-probe roots, `qSig²` collision roots
(Spec.md §7 T7, first-order union bound). -/
def DSBadMassLe (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) : Prop :=
  Pr[fun w => FrameLeakBad w.1 w.2.2.audit | dsFrameJoint mclose A]
    ≤ (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹

/-- **Route-B endpoint reduction** (Spec.md §7 T7). The stage-1 coupling and
the stage-2 counting residual together discharge the direct real-side
bad-mass bound consumed by the T7 assembly. -/
theorem frameRealBadMassLe_of_stepCoupling_and_count (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (hstep : ∀ k : F, RealDSStepCoupling (F := F) (M := M) k mclose)
    (hcount : DSBadMassLe mclose A qb) :
    FrameRealBadMassLe mclose A qb := by
  unfold FrameRealBadMassLe
  rw [probOutput_bind_decide_eq_probEvent]
  exact le_trans (auditedFrameJoint_bad_le_dsFrameJoint mclose A hstep) hcount

/-- **Unconditional T7 endpoint shape through route B** (Spec.md §7 T7):
good-slice transfer + stage-1 coupling + stage-2 counting give the complete
corrected FRAME bound `(qb.total + 1)/|F|`. -/
theorem T7_frame_query_bound_of_goodSlice_stepCoupling_count (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (hgood : FrameGoodSliceTransfer mclose A)
    (hstep : ∀ k : F, RealDSStepCoupling (F := F) (M := M) k mclose)
    (hcount : DSBadMassLe mclose A qb) :
    frameWinProb mclose A
      ≤ ((qb.total + 1 : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ :=
  T7_frame_query_bound_of_goodSlice_and_realBad mclose A qb hgood
    (frameRealBadMassLe_of_stepCoupling_and_count mclose A qb hstep hcount)

end Counting

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.auditedFrameImpl_bad_le_ds
#print axioms Zkpc.Games.auditedFrameJoint_bad_le_dsFrameJoint
#print axioms Zkpc.Games.frameRealBadMassLe_of_stepCoupling_and_count
#print axioms Zkpc.Games.T7_frame_query_bound_of_goodSlice_stepCoupling_count
