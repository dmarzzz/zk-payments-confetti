import Zkpc.Games.FrameFactor

/-!
# The good-slice transfer lane (Spec.md §7 T7)

`Zkpc/Games/FrameFactor.lean` reduced the k-averaged T7 certificate to two
run-level transfer residuals; this file is the **good-slice lane**: it works
on `FrameGoodSliceTransfer`, the claim that the k-averaged probability that
the audited real FRAME run both slashes and never trips the audited leakage
event is at most the deferred-secret ghost win probability.

## Architecture

1. **k-average reduction** (`frameGoodSliceTransfer_of_pointwise`): unlike the
   bad-mass lane, the good-slice comparison holds *pointwise in the secret*:
   for every fixed `k`, the real run's win-and-good mass is dominated by the
   ghost run's win mass at that same `k`. Summing against the uniform secret
   yields the averaged transfer. The pointwise claim is the named residual
   `FramePointwiseGoodSlice`.
2. **Ghost-to-ideal transport** (`framePointwiseGoodSlice_of_idealDom`): the
   ghost ornament is erased (`fst_map_ghostFrameRun`,
   `ghostFrameEvidence_evalDist_eq`), so the pointwise claim follows from a
   per-commitment expectation dominance between the audited real handler and
   the secret-free ideal handler, in the tsum functional form that the
   step-dominance suite below produces.
3. **The step-dominance suite** (`goodSliceStepDom` and the per-operation
   theorems): for every FRAME operation except honest signal emission at a
   *pre-materialized* (`nfAt`-pinned) slope, one audited real step followed by
   any nonnegative payoff of the answer and the secret-erased state is
   dominated by the corresponding ideal step — with the leakage-firing
   branches contributing zero (the payoff carries the `¬ FrameLeakBad` guard,
   and the audited bad event is monotone). The fresh-slope signal cases are
   the quantitative crux: the hidden slope uniformizes the emitted line value
   through the bijection `a ↦ a·x + k` (`x ≠ 0` by the digest normalization),
   and the fresh-slope collision branches are *detected* (`RoNfCovered`) and
   drop out of the good slice.
4. **The pin-free induction** (`goodSlice_run_le_of_nfAtFree`): assembling the
   suite over an arbitrary adversary computation discharges the pointwise
   claim outright for every adversary that never queries the MC20 reveal
   oracle `nfAt` (`framePointwiseGoodSlice_of_nfAtFree`) — on such runs no
   unconsumed pinned slope ever exists, which is exactly the case split the
   suite covers.

## The named residual

The single remaining case is honest emission at an `nfAt`-pinned slope: from
a *fixed* real state whose future emission slope is already materialized, the
emitted `y = k + a₀·x` is deterministic while the ideal `y` is fresh-uniform,
so no per-state step dominance exists (`OPEN-PROOFS.md` §1, the eager-read
obstruction; the counterexample state pins `a₀ = 0`). The value of an
unconsumed pin must stay *deferred* (averaged) between its `nfAt` draw and
its consuming emission — a run-level tape argument in the style of
`FrameBadMass.materializeSlopeTape`, not a pointwise state coupling. The
honest scope of this file is therefore: the full reduction chain, the
complete step suite (including both fresh-slope emission cruxes at arbitrary
audit-complete states), and the assembled induction for the `nfAt`-free
fragment; `FramePointwiseGoodSlice` at general adversaries remains the
precisely-stated open hypothesis of the final theorem
(`frameGoodSliceTransfer_of_pointwise`), per the house named-residual
convention.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## The pointwise-in-`k` residual and the k-average reduction -/

/-- **Pointwise good-slice dominance (named residual, Spec.md §7 T7).** At a
fixed honest secret `k`, the probability that the audited real run slashes
`k` while never tripping the audited leakage event is at most the probability
that the secret-independent ghost run slashes that same `k`. The k-average of
this claim is exactly `FrameGoodSliceTransfer`; unlike the bad-mass lane the
comparison needs no averaging, because on the good slice every real oracle
answer is exactly coupled to a ghost answer and every emitted line value is
uniformized by its fresh hidden slope. -/
def FramePointwiseGoodSlice (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) (k : F) : Prop :=
  Pr[= true | auditedFrameRun mclose A k >>= fun z =>
      pure (decide (Slashes k z.1 ∧ ¬ FrameLeakBad k z.2.audit))]
    ≤ Pr[= true | ghostFrameRun mclose A >>= fun z =>
        pure (decide (Slashes k z.1))]

/-- **The k-average reduction (Spec.md §7 T7).** The good-slice transfer of
the k-averaged T7 certificate follows from its pointwise-in-`k` form: the
audited joint experiment draws the secret first, the deferred-secret ghost
win mass commutes the secret draw to the front, and the two integrands are
compared pointwise under the uniform secret. -/
theorem frameGoodSliceTransfer_of_pointwise (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (h : ∀ k : F, FramePointwiseGoodSlice mclose A k) :
    FrameGoodSliceTransfer mclose A := by
  unfold FrameGoodSliceTransfer
  have hleft : (auditedFrameJoint mclose A >>= fun w =>
      pure (decide (Slashes w.1 w.2.1 ∧ ¬ FrameLeakBad w.1 w.2.2.audit)))
      = (($ᵗ F) >>= fun k => auditedFrameRun mclose A k >>= fun z =>
          pure (decide (Slashes k z.1 ∧ ¬ FrameLeakBad k z.2.audit))) := by
    unfold auditedFrameJoint
    simp only [bind_assoc, pure_bind]
  have hright : Pr[= true | (do
      let z ← ghostFrameRun mclose A
      let k ← ($ᵗ F)
      pure (decide (Slashes k z.1)))]
      = Pr[= true | ($ᵗ F) >>= fun k => ghostFrameRun mclose A >>= fun z =>
          pure (decide (Slashes k z.1))] :=
    probOutput_congr rfl
      (OracleComp.DeferredSampling.evalDist_bind_comm (ghostFrameRun mclose A)
        ($ᵗ F) (fun z k => pure (decide (Slashes k z.1))))
  rw [hleft, hright, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun k => mul_le_mul_right (h k) _

/-! ## Decide-to-expectation bridges -/

/-- The Boolean-decided probability of a predicate behind a generator, in
expectation form: the indicator of the predicate integrated against the
output distribution. -/
theorem probOutput_true_bind_decide_eq_tsum {α : Type} (oc : ProbComp α)
    (P : α → Prop) [DecidablePred P] :
    Pr[= true | oc >>= fun z => pure (decide (P z))]
      = ∑' z : α, Pr[= z | oc] * (if P z then 1 else 0) := by
  rw [probOutput_bind_eq_tsum]
  refine tsum_congr fun z => ?_
  by_cases h : P z <;> simp [h]

omit [SampleableType F] [DecidableEq M] in
/-- The good-slice indicator factors as the bad-guard applied to the win
indicator. -/
theorem goodSlice_indicator_eq (k : F) (z : Evidence F × AuditedFrameSt F M) :
    (if Slashes k z.1 ∧ ¬ FrameLeakBad k z.2.audit then (1 : ENNReal) else 0)
      = (if FrameLeakBad k z.2.audit then 0
          else if Slashes k z.1 then 1 else 0) := by
  by_cases hb : FrameLeakBad k z.2.audit <;> by_cases hs : Slashes k z.1 <;>
    simp [hb, hs]

/-! ## Ghost-to-ideal transport of the pointwise claim -/

/-- **Sufficiency of the real/ideal expectation dominance** (Spec.md §7 T7).
The pointwise good-slice claim follows from the per-commitment comparison of
the audited real run against the plain secret-free ideal run, in tsum
functional form: the ghost win mass equals the ideal win mass by ghost
erasure, and both runs sample the public commitment identically. This is the
exact interface produced by the step-dominance induction below. -/
theorem framePointwiseGoodSlice_of_idealDom (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) (k : F)
    (h : ∀ cm : F,
      (∑' z : Evidence F × AuditedFrameSt F M,
        Pr[= z | (simulateQ (auditedFrameImpl k mclose) (A cm)).run
            ⟨{ FrameSt.init F M with
                roId := Function.update (FrameSt.init F M).roId k (some cm) },
              FrameAudit.init⟩] *
          (if FrameLeakBad k z.2.audit then 0
            else if Slashes k z.1 then 1 else 0))
        ≤ ∑' w : Evidence F × IdealFrameSt F M,
            Pr[= w | (simulateQ (idealFrameImpl mclose) (A cm)).run
                (IdealFrameSt.init F M)] *
              (if Slashes k w.1 then 1 else 0)) :
    FramePointwiseGoodSlice mclose A k := by
  unfold FramePointwiseGoodSlice
  -- Rewrite the ghost side as the ideal run's win mass.
  have hghost : Pr[= true | ghostFrameRun mclose A >>= fun z =>
      pure (decide (Slashes k z.1))]
      = Pr[= true | (do
          let cm ← ($ᵗ F)
          (simulateQ (idealFrameImpl mclose) (A cm)).run (IdealFrameSt.init F M))
            >>= fun w => pure (decide (Slashes k w.1))] := by
    have h1 : (ghostFrameRun mclose A >>= fun z => pure (decide (Slashes k z.1)))
        = (Prod.fst <$> ghostFrameRun mclose A) >>= fun ev =>
            pure (decide (Slashes k ev)) := by
      rw [bind_map_left]
    have h2 : 𝒟[(ghostFrameEvidence mclose A) >>= fun ev =>
        pure (decide (Slashes k ev))]
        = 𝒟[(idealFrameEvidence mclose A) >>= fun ev =>
            pure (decide (Slashes k ev))] := by
      rw [evalDist_bind, evalDist_bind, ghostFrameEvidence_evalDist_eq]
    have h3 : (idealFrameEvidence mclose A >>= fun ev =>
        pure (decide (Slashes k ev)))
        = ((do
            let cm ← ($ᵗ F)
            (simulateQ (idealFrameImpl mclose) (A cm)).run (IdealFrameSt.init F M))
              >>= fun w => pure (decide (Slashes k w.1))) := by
      unfold idealFrameEvidence QueryImpl.Stateful.run
      simp only [bind_assoc]
      refine bind_congr fun cm => ?_
      rw [StateT.run'_eq, bind_map_left]
    rw [h1, fst_map_ghostFrameRun, probOutput_congr rfl h2, h3]
  rw [hghost]
  -- Expand both sides over the shared commitment draw.
  unfold auditedFrameRun
  simp only [bind_assoc]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun cm => mul_le_mul_right ?_ _
  rw [probOutput_true_bind_decide_eq_tsum, probOutput_true_bind_decide_eq_tsum]
  calc ∑' z : Evidence F × AuditedFrameSt F M,
        Pr[= z | (simulateQ (auditedFrameImpl k mclose) (A cm)).run
            ⟨{ FrameSt.init F M with
                roId := Function.update (FrameSt.init F M).roId k (some cm) },
              FrameAudit.init⟩] *
          (if Slashes k z.1 ∧ ¬ FrameLeakBad k z.2.audit then 1 else 0)
      = ∑' z : Evidence F × AuditedFrameSt F M,
          Pr[= z | (simulateQ (auditedFrameImpl k mclose) (A cm)).run
              ⟨{ FrameSt.init F M with
                  roId := Function.update (FrameSt.init F M).roId k (some cm) },
                FrameAudit.init⟩] *
            (if FrameLeakBad k z.2.audit then 0
              else if Slashes k z.1 then 1 else 0) := by
        refine tsum_congr fun z => ?_
        rw [goodSlice_indicator_eq]
    _ ≤ ∑' w : Evidence F × IdealFrameSt F M,
          Pr[= w | (simulateQ (idealFrameImpl mclose) (A cm)).run
              (IdealFrameSt.init F M)] *
            (if Slashes k w.1 then 1 else 0) := h cm

/-! ## Generic dominance machinery

Three reusable kernels: the guarded expectation of a generator that is
support-wise bad vanishes; a run from an already-bad audited state has zero
good-slice mass; and an exact idealization equality of one step upgrades to
the guarded step dominance. -/

/-- A guarded expectation vanishes when every supported outcome trips the
leakage event: the guard zeroes every term with positive probability. -/
theorem tsum_goodGuard_zero_of_support_bad {α : Type} (k : F)
    (oc : ProbComp (α × AuditedFrameSt F M))
    (hsupp : ∀ z ∈ support oc, FrameLeakBad k z.2.audit)
    (X : α × AuditedFrameSt F M → ENNReal) :
    (∑' z : α × AuditedFrameSt F M,
      Pr[= z | oc] * (if FrameLeakBad k z.2.audit then 0 else X z)) = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun z => ?_
  by_cases hz : z ∈ support oc
  · rw [if_pos (hsupp z hz), mul_zero]
  · rw [(probOutput_eq_zero_iff _ _).mpr hz, zero_mul]

/-- **The bad-state kill.** A full audited run started from a state whose
audit has already tripped the leakage event contributes no good-slice mass:
the audited bad event is monotone, so the final guard vanishes on the whole
support. -/
theorem goodSlice_run_zero_of_bad (k : F) (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (r : AuditedFrameSt F M)
    (hbad : FrameLeakBad k r.audit) (X : α × AuditedFrameSt F M → ENNReal) :
    (∑' z : α × AuditedFrameSt F M,
      Pr[= z | (simulateQ (auditedFrameImpl k mclose) oa).run r] *
        (if FrameLeakBad k z.2.audit then 0 else X z)) = 0 :=
  tsum_goodGuard_zero_of_support_bad k _
    (fun z hz => auditedFrameImpl_run_bad_monotone k mclose oa r hbad z hz) X

/-- **Exact-step upgrade.** Whenever one audited step commutes exactly with
canonical secret erasure (the landed `idealize_*_step` equalities), the
guarded real expectation of any payoff of the answer and erased state is
dominated by the ideal expectation: drop the guard and push forward. -/
theorem goodSlice_step_le_of_idealize_eq (k : F) (mclose : M)
    {op : FrameOp F M} (r : AuditedFrameSt F M)
    (heq : Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) op).run r =
      ((idealFrameImpl mclose) op).run (idealizeFrame k r))
    (G : (frameSpec F M).Range op × IdealFrameSt F M → ENNReal) :
    (∑' z : (frameSpec F M).Range op × AuditedFrameSt F M,
      Pr[= z | ((auditedFrameImpl k mclose) op).run r] *
        (if FrameLeakBad k z.2.audit then 0 else G (z.1, idealizeFrame k z.2)))
      ≤ ∑' w : (frameSpec F M).Range op × IdealFrameSt F M,
          Pr[= w | ((idealFrameImpl mclose) op).run (idealizeFrame k r)] *
            G w := by
  rw [← heq, tsum_probOutput_map_mul]
  refine ENNReal.tsum_le_tsum fun z => mul_le_mul_right ?_ _
  show (if FrameLeakBad k z.2.audit then 0 else G (z.1, idealizeFrame k z.2))
    ≤ G (z.1, idealizeFrame k z.2)
  split
  · exact zero_le
  · exact le_rfl

/-! ## Support-wise bad extraction for the secret-touching operations -/

/-- Every outcome of a direct `H_a` probe at the honest secret is bad. -/
theorem auditedFrameImpl_support_bad_roA (k : F) (mclose : M) (i : ℕ)
    (r : AuditedFrameSt F M)
    (z : F × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) (.roA k i)).run r)) :
    FrameLeakBad k z.2.audit := by
  exact (auditedFrameImpl_support_audit k mclose (.roA k i) r z hz).symm ▸
    auditAfter_direct_secret_bad k i r.base z.2.base r.audit

/-- Every outcome of a direct `H_e` probe at the honest secret is bad. -/
theorem auditedFrameImpl_support_bad_roE (k : F) (mclose : M) (e : ℕ)
    (r : AuditedFrameSt F M)
    (z : F × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) (.roE k e)).run r)) :
    FrameLeakBad k z.2.audit := by
  exact (auditedFrameImpl_support_audit k mclose (.roE k e) r z hz).symm ▸
    auditAfter_epoch_secret_bad k e r.base z.2.base r.audit

/-- Every outcome of a direct `H_id` probe at the honest secret is bad. -/
theorem auditedFrameImpl_support_bad_roId (k : F) (mclose : M)
    (r : AuditedFrameSt F M)
    (z : F × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) (.roId k)).run r)) :
    FrameLeakBad k z.2.audit := by
  exact (auditedFrameImpl_support_audit k mclose (.roId k) r z hz).symm ▸
    auditAfter_identity_secret_bad k r.base z.2.base r.audit

/-- Every outcome of a direct `H_nf` probe at an exposed honest slope is
bad. -/
theorem auditedFrameImpl_support_bad_roNf (k : F) (mclose : M) (aq : F)
    (r : AuditedFrameSt F M) (ha : aq ∈ r.audit.honestSlopes)
    (z : F × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) (.roNf aq)).run r)) :
    FrameLeakBad k z.2.audit := by
  exact (auditedFrameImpl_support_audit k mclose (.roNf aq) r z hz).symm ▸
    auditAfter_slope_hit_bad k aq r.base z.2.base r.audit ha

/-! ## Closed-member signal steps: exact idealization -/

/-- A `spend` query on a closed member is a pure no-op on both sides and
commutes exactly with canonical secret erasure. -/
theorem idealize_spend_step_closed (k : F) (mclose m : M)
    (r : AuditedFrameSt F M) (hcl : r.base.closed = true) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.spend m)).run r =
      ((idealFrameImpl mclose) (.spend m)).run (idealizeFrame k r) := by
  have hicl : (idealizeFrame k r).closed = true := hcl
  unfold auditedFrameImpl idealFrameImpl frameImpl
  simp only [StateT.run_mk, hcl, hicl, if_pos, pure_bind, map_pure, auditAfter]
  rfl

/-- A legacy `close` query on a closed member is a pure no-op on both sides
and commutes exactly with canonical secret erasure. -/
theorem idealize_close_step_closed (k : F) (mclose : M)
    (r : AuditedFrameSt F M) (hcl : r.base.closed = true) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) .close).run r =
      ((idealFrameImpl mclose) .close).run (idealizeFrame k r) := by
  have hicl : (idealizeFrame k r).closed = true := hcl
  unfold auditedFrameImpl idealFrameImpl frameImpl
  simp only [StateT.run_mk, hcl, hicl, if_pos, pure_bind, map_pure, auditAfter]
  rfl

end Zkpc.Games
