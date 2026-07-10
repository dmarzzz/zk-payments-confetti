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

omit [Field F] [SampleableType F] [DecidableEq M] in
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
  split <;> simp

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

/-! ## Audit-extension lemmas for a fresh honest slope -/

omit [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] in
/-- Recording a fresh honest slope that was neither probed nor previously
exposed keeps the audit good: no leakage branch can fire on the extension. -/
theorem not_frameLeakBad_honest_cons (k a : F) (audit : FrameAudit F)
    (hgood : ¬ FrameLeakBad k audit) (hp : a ∉ audit.slopeProbes)
    (hh : a ∉ audit.honestSlopes) :
    ¬ FrameLeakBad k { audit with honestSlopes := a :: audit.honestSlopes } := by
  intro hbad
  rcases hbad with hk | ⟨s, hs1, hs2⟩ | hdup
  · exact hgood (Or.inl hk)
  · rcases List.mem_cons.mp hs2 with rfl | hs2'
    · exact hp hs1
    · exact hgood (Or.inr (Or.inl ⟨s, hs1, hs2'⟩))
  · have hnd : audit.honestSlopes.Nodup := by
      by_contra hnd
      exact hgood (Or.inr (Or.inr hnd))
    exact hdup (List.nodup_cons.mpr ⟨hh, hnd⟩)

omit [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] in
/-- On a covered state, an unprobed and unexposed slope has no public
nullifier-cache entry — the contrapositive of `RoNfCovered` that turns the
fresh-slope collision branch into a detected bad event. -/
theorem roNf_none_of_unrecorded (r : AuditedFrameSt F M) (hcov : RoNfCovered r)
    {a : F} (hp : a ∉ r.audit.slopeProbes) (hh : a ∉ r.audit.honestSlopes) :
    r.base.roNf a = none := by
  cases hv : r.base.roNf a with
  | none => rfl
  | some v =>
      rcases hcov a v hv with h | h
      · exact absurd h hp
      · exact absurd h hh

/-! ## The line-value uniformization -/

omit [DecidableEq F] in
/-- **The slope-to-line-value reindexing** (Spec.md §3, the RLN line). For a
nonzero abscissa `x`, the map `a ↦ k + a·x` is a bijection of `F`, so summing
any payoff of the emitted line value against the uniform hidden slope equals
summing it against a uniform line value directly. This is the tsum-level form
of the one-time-pad step used by `freshRealSignal_evalDist_eq`. -/
theorem tsum_uniform_rlnY_reindex [Fintype F] (k x : F) (hx : x ≠ 0)
    (T : F → ENNReal) :
    (∑' a : F, Pr[= a | ($ᵗ F)] * T (rlnY k a x))
      = ∑' y : F, Pr[= y | ($ᵗ F)] * T y := by
  have hbij : Function.Bijective (fun a : F => rlnY k a x) := by
    constructor
    · intro a b hab
      simp only [rlnY, add_right_inj] at hab
      exact mul_right_cancel₀ hx hab
    · intro y
      refine ⟨(y - k) / x, ?_⟩
      simp only [rlnY]
      rw [div_mul_cancel₀ _ hx]
      ring
  simp only [probOutput_uniformSample]
  calc (∑' a : F, (Fintype.card F : ENNReal)⁻¹ * T (rlnY k a x))
      = ∑' a : F, (fun y => (Fintype.card F : ENNReal)⁻¹ * T y)
          ((Equiv.ofBijective _ hbij) a) := tsum_congr fun a => rfl
    _ = ∑' y : F, (Fintype.card F : ENNReal)⁻¹ * T y :=
        Equiv.tsum_eq (Equiv.ofBijective _ hbij)
          (fun y => (Fintype.card F : ENNReal)⁻¹ * T y)

/-! ## Secret erasure of a fresh-slope successor state -/

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- **Fresh-slope idealization algebra.** Materializing a fresh hidden slope
`a` (unexposed, unprobed, no public nullifier entry) with its fresh nullifier
`nf` at index `i`, and recording it in the audit, idealizes to a single
per-index nullifier update: the new `H_a` entry sits in the masked hidden
row, the new `H_nf` entry sits at the newly masked honest slope, and audit
completeness confines the composed-nullifier change to index `i`. The
counter, closed flag, and digest cache ride along unchanged. -/
theorem idealize_freshSlope_state (k a nf : F) (i n : ℕ) (cl : Bool)
    (cX : M → Option F) (r : AuditedFrameSt F M)
    (hc : FrameAuditComplete k r)
    (hh : a ∉ r.audit.honestSlopes) (hnfa : r.base.roNf a = none) :
    idealizeFrame k
      (⟨{ r.base with
          idx := n
          closed := cl
          roA := Function.update r.base.roA (k, i) (some a)
          roX := cX
          roNf := Function.update r.base.roNf a (some nf) },
        { r.audit with honestSlopes := a :: r.audit.honestSlopes }⟩ :
          AuditedFrameSt F M)
      = { idealizeFrame k r with
          idx := n
          closed := cl
          roX := cX
          honestNf :=
            Function.update (idealizeFrame k r).honestNf i (some nf) } := by
  apply IdealFrameSt.ext
  · rfl
  · rfl
  · funext q
    by_cases hq : q.1 = k
    · simp [idealizeFrame, hq]
    · have hne : q ≠ (k, i) := fun h => hq (by rw [h])
      simp [idealizeFrame, hq, Function.update_of_ne hne]
  · rfl
  · funext q
    by_cases hqm : q ∈ r.audit.honestSlopes
    · simp [idealizeFrame, hqm, List.mem_cons]
    · by_cases hqa : q = a
      · subst hqa
        simp [idealizeFrame, hqm, hnfa]
      · simp [idealizeFrame, hqm, hqa]
  · funext q
    simp [idealizeFrame]
  · funext q
    simp [idealizeFrame]
  · funext j
    by_cases hj : j = i
    · subst hj
      simp [idealizeFrame]
    · have hpair : (k, j) ≠ (k, i) := fun h => hj (congrArg Prod.snd h)
      simp only [idealizeFrame, Function.update_of_ne hpair,
        Function.update_of_ne hj]
      cases hb : r.base.roA (k, j) with
      | none => simp
      | some b =>
          have hba : b ≠ a := fun h => hh (h ▸ hc j b hb)
          simp [Function.update_of_ne hba]

/-! ## The fresh-slope step-dominance cruxes -/

section FreshSlopeCrux

variable [Fintype F]

/-- **MC20 reveal at a fresh index (crux, Spec.md §7 T7).** An `nfAt i` query
whose hidden slope is not yet materialized dominates into the ideal per-index
reveal: the fresh slope either collides with recorded audit data — a detected
leakage branch whose good-slice mass is zero — or is genuinely new, in which
case the drawn nullifier couples exactly and the slope disappears under
secret erasure. Unlike the pinned-emission case, the slope value never
reaches an answer here, so the dominance holds pointwise at every covered,
audit-complete, still-good state. -/
theorem goodSlice_step_le_nfAt_fresh (k : F) (mclose : M) (i : ℕ)
    (r : AuditedFrameSt F M) (ha : r.base.roA (k, i) = none)
    (hc : FrameAuditComplete k r) (hcov : RoNfCovered r)
    (hgood : ¬ FrameLeakBad k r.audit)
    (G : F × IdealFrameSt F M → ENNReal) :
    (∑' z : F × AuditedFrameSt F M,
      Pr[= z | ((auditedFrameImpl k mclose) (.nfAt i)).run r] *
        (if FrameLeakBad k z.2.audit then 0 else G (z.1, idealizeFrame k z.2)))
      ≤ ∑' w : F × IdealFrameSt F M,
          Pr[= w | ((idealFrameImpl mclose) (.nfAt i)).run (idealizeFrame k r)] *
            G w := by
  have hreal : ((auditedFrameImpl k mclose) (.nfAt i)).run r
      = (($ᵗ F) >>= fun a => lazyRO r.base.roNf a >>= fun q =>
          pure ((q.1 : F),
            (⟨{ r.base with
                roA := Function.update r.base.roA (k, i) (some a)
                roNf := q.2 },
              { r.audit with
                  honestSlopes := a :: r.audit.honestSlopes }⟩ :
                AuditedFrameSt F M))) := by
    unfold auditedFrameImpl frameImpl
    simp only [StateT.run_mk]
    rw [lazyRO_eq_of_none ha]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun a => ?_
    refine bind_congr fun q => ?_
    simp [auditAfter, ha, Function.update_self]
  have hnfI : (idealizeFrame k r).honestNf i = none := by
    simp [idealizeFrame, ha]
  have hideal : ((idealFrameImpl mclose) (.nfAt i)).run (idealizeFrame k r)
      = (($ᵗ F) >>= fun nf =>
          pure ((nf : F),
            ({ idealizeFrame k r with
                honestNf := Function.update (idealizeFrame k r).honestNf i
                  (some nf) } : IdealFrameSt F M))) := by
    unfold idealFrameImpl
    simp only [StateT.run_mk]
    rw [lazyRO_eq_of_none hnfI]
    simp only [bind_assoc, pure_bind]
  rw [hreal, hideal]
  simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  have hstep : ∀ a : F,
      (∑' q : F × (F → Option F),
        Pr[= q | lazyRO r.base.roNf a] *
          (if FrameLeakBad k
              { r.audit with honestSlopes := a :: r.audit.honestSlopes }
            then 0
            else G (q.1, idealizeFrame k
              (⟨{ r.base with
                  roA := Function.update r.base.roA (k, i) (some a)
                  roNf := q.2 },
                { r.audit with
                    honestSlopes := a :: r.audit.honestSlopes }⟩ :
                  AuditedFrameSt F M))))
        ≤ ∑' nf : F, Pr[= nf | ($ᵗ F)] *
            G (nf, { idealizeFrame k r with
              honestNf := Function.update (idealizeFrame k r).honestNf i
                (some nf) }) := by
    intro a
    by_cases hrec : a ∈ r.audit.slopeProbes ∨ a ∈ r.audit.honestSlopes
    · have hbad : FrameLeakBad k
          { r.audit with honestSlopes := a :: r.audit.honestSlopes } :=
        FrameLeakBad.honest_collision k a r.audit hrec
      refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun q => ?_)) zero_le'
      rw [if_pos hbad, mul_zero]
    · rw [not_or] at hrec
      obtain ⟨hprobe, hhon⟩ := hrec
      have hnfa : r.base.roNf a = none :=
        roNf_none_of_unrecorded r hcov hprobe hhon
      have hgood' : ¬ FrameLeakBad k
          { r.audit with honestSlopes := a :: r.audit.honestSlopes } :=
        not_frameLeakBad_honest_cons k a r.audit hgood hprobe hhon
      rw [lazyRO_eq_of_none hnfa]
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
      refine le_of_eq (tsum_congr fun nf => ?_)
      rw [if_neg hgood',
        idealize_freshSlope_state k a nf i r.base.idx r.base.closed r.base.roX
          r hc hhon hnfa]
      simp [idealizeFrame]
  refine le_trans (ENNReal.tsum_le_tsum fun a =>
    mul_le_mul_right (hstep a) _) ?_
  rw [ENNReal.tsum_mul_right]
  refine le_trans (mul_le_mul' tsum_probOutput_le_one le_rfl) ?_
  rw [one_mul]

/-- **Fresh-slope honest emission (crux, Spec.md §7 T7).** An `Ospend(m)`
query at an open state whose next-index hidden slope is unmaterialized
dominates into the ideal emission: the digest draw is shared verbatim; the
fresh hidden slope either collides with recorded audit data — detected, zero
good-slice mass — or is new, in which case the recorded slope masks away and
the emitted line value `y = k + a·x` reindexes along the bijection
`a ↦ k + a·x` (`x ≠ 0`) onto the ideal's uniform line value. This is the
general-state form of the atomic `initial_spend_deferredSecret_ghost_eq`,
here pointwise in `k` because the slope is consumed at its own draw. -/
theorem goodSlice_step_le_spend_fresh (k : F) (mclose m : M)
    (r : AuditedFrameSt F M)
    (hopen : r.base.closed = false)
    (ha : r.base.roA (k, r.base.idx) = none)
    (hc : FrameAuditComplete k r) (hcov : RoNfCovered r)
    (hx0 : RoXCacheNonzero r.base.roX)
    (hgood : ¬ FrameLeakBad k r.audit)
    (G : Option (Signal F) × IdealFrameSt F M → ENNReal) :
    (∑' z : Option (Signal F) × AuditedFrameSt F M,
      Pr[= z | ((auditedFrameImpl k mclose) (.spend m)).run r] *
        (if FrameLeakBad k z.2.audit then 0 else G (z.1, idealizeFrame k z.2)))
      ≤ ∑' w : Option (Signal F) × IdealFrameSt F M,
          Pr[= w | ((idealFrameImpl mclose) (.spend m)).run
              (idealizeFrame k r)] * G w := by
  have hreal : ((auditedFrameImpl k mclose) (.spend m)).run r
      = (lazyROX r.base.roX m >>= fun p =>
          ($ᵗ F) >>= fun a => lazyRO r.base.roNf a >>= fun q =>
            pure ((some ⟨p.1, rlnY k a p.1, q.1⟩ : Option (Signal F)),
              (⟨{ r.base with
                  idx := r.base.idx + 1
                  roA := Function.update r.base.roA (k, r.base.idx) (some a)
                  roX := p.2
                  roNf := q.2 },
                { r.audit with
                    honestSlopes := a :: r.audit.honestSlopes }⟩ :
                  AuditedFrameSt F M))) := by
    unfold auditedFrameImpl frameImpl emitSignal
    simp only [StateT.run_mk, hopen, Bool.false_eq_true, ↓reduceIte]
    rw [lazyRO_eq_of_none ha]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun p => ?_
    obtain ⟨x, cX⟩ := p
    refine bind_congr fun a => ?_
    refine bind_congr fun q => ?_
    obtain ⟨nf, cNf⟩ := q
    simp [auditAfter, hopen, ha, Function.update_self]
  have hopen' : (idealizeFrame k r).closed = false := hopen
  have hrx : (idealizeFrame k r).roX = r.base.roX := rfl
  have hidx : (idealizeFrame k r).idx = r.base.idx := rfl
  have hnfI : (idealizeFrame k r).honestNf r.base.idx = none := by
    simp [idealizeFrame, ha]
  have hideal : ((idealFrameImpl mclose) (.spend m)).run (idealizeFrame k r)
      = (lazyROX r.base.roX m >>= fun p =>
          ($ᵗ F) >>= fun y => ($ᵗ F) >>= fun nf =>
            pure ((some ⟨p.1, y, nf⟩ : Option (Signal F)),
              ({ idealizeFrame k r with
                  idx := r.base.idx + 1
                  roX := p.2
                  honestNf := Function.update (idealizeFrame k r).honestNf
                    r.base.idx (some nf) } : IdealFrameSt F M))) := by
    unfold idealFrameImpl emitIdealSignal
    simp only [StateT.run_mk, hopen', Bool.false_eq_true, ↓reduceIte]
    rw [hrx, hidx, lazyRO_eq_of_none hnfI]
    simp only [bind_assoc, pure_bind]
  rw [hreal, hideal]
  simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases hp : p ∈ support (lazyROX r.base.roX m)
  · obtain ⟨hx, -⟩ := lazyROX_support_nonzero hx0 m p hp
    refine mul_le_mul_right ?_ _
    have hstep : ∀ a : F,
        (∑' q : F × (F → Option F),
          Pr[= q | lazyRO r.base.roNf a] *
            (if FrameLeakBad k
                { r.audit with honestSlopes := a :: r.audit.honestSlopes }
              then 0
              else G ((some ⟨p.1, rlnY k a p.1, q.1⟩ : Option (Signal F)),
                idealizeFrame k
                  (⟨{ r.base with
                      idx := r.base.idx + 1
                      roA := Function.update r.base.roA (k, r.base.idx)
                        (some a)
                      roX := p.2
                      roNf := q.2 },
                    { r.audit with
                        honestSlopes := a :: r.audit.honestSlopes }⟩ :
                      AuditedFrameSt F M))))
          ≤ ∑' nf : F, Pr[= nf | ($ᵗ F)] *
              G ((some ⟨p.1, rlnY k a p.1, nf⟩ : Option (Signal F)),
                { idealizeFrame k r with
                    idx := r.base.idx + 1
                    roX := p.2
                    honestNf := Function.update (idealizeFrame k r).honestNf
                      r.base.idx (some nf) }) := by
      intro a
      by_cases hrec : a ∈ r.audit.slopeProbes ∨ a ∈ r.audit.honestSlopes
      · have hbad : FrameLeakBad k
            { r.audit with honestSlopes := a :: r.audit.honestSlopes } :=
          FrameLeakBad.honest_collision k a r.audit hrec
        refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun q => ?_))
          zero_le'
        rw [if_pos hbad, mul_zero]
      · rw [not_or] at hrec
        obtain ⟨hprobe, hhon⟩ := hrec
        have hnfa : r.base.roNf a = none :=
          roNf_none_of_unrecorded r hcov hprobe hhon
        have hgood' : ¬ FrameLeakBad k
            { r.audit with honestSlopes := a :: r.audit.honestSlopes } :=
          not_frameLeakBad_honest_cons k a r.audit hgood hprobe hhon
        rw [lazyRO_eq_of_none hnfa]
        simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
        refine le_of_eq (tsum_congr fun nf => ?_)
        rw [if_neg hgood',
          idealize_freshSlope_state k a nf r.base.idx (r.base.idx + 1)
            r.base.closed p.2 r hc hhon hnfa]
        simp [idealizeFrame]
    refine le_trans (ENNReal.tsum_le_tsum fun a =>
      mul_le_mul_right (hstep a) _) ?_
    exact le_of_eq (tsum_uniform_rlnY_reindex k p.1 hx
      (fun y => ∑' nf : F, Pr[= nf | ($ᵗ F)] *
        G ((some ⟨p.1, y, nf⟩ : Option (Signal F)),
          { idealizeFrame k r with
              idx := r.base.idx + 1
              roX := p.2
              honestNf := Function.update (idealizeFrame k r).honestNf
                r.base.idx (some nf) })))
  · rw [(probOutput_eq_zero_iff _ _).mpr hp]
    simp

/-- **Fresh-slope legacy close (crux, Spec.md §7 T7).** The legacy `Oclose`
surplus signal at an open state with an unmaterialized next-index slope: the
same dominance as `goodSlice_step_le_spend_fresh` on the distinguished close
message, with the closed flag set on both sides. -/
theorem goodSlice_step_le_close_fresh (k : F) (mclose : M)
    (r : AuditedFrameSt F M)
    (hopen : r.base.closed = false)
    (ha : r.base.roA (k, r.base.idx) = none)
    (hc : FrameAuditComplete k r) (hcov : RoNfCovered r)
    (hx0 : RoXCacheNonzero r.base.roX)
    (hgood : ¬ FrameLeakBad k r.audit)
    (G : Option (Signal F) × IdealFrameSt F M → ENNReal) :
    (∑' z : Option (Signal F) × AuditedFrameSt F M,
      Pr[= z | ((auditedFrameImpl k mclose) .close).run r] *
        (if FrameLeakBad k z.2.audit then 0 else G (z.1, idealizeFrame k z.2)))
      ≤ ∑' w : Option (Signal F) × IdealFrameSt F M,
          Pr[= w | ((idealFrameImpl mclose) .close).run
              (idealizeFrame k r)] * G w := by
  have hreal : ((auditedFrameImpl k mclose) .close).run r
      = (lazyROX r.base.roX mclose >>= fun p =>
          ($ᵗ F) >>= fun a => lazyRO r.base.roNf a >>= fun q =>
            pure ((some ⟨p.1, rlnY k a p.1, q.1⟩ : Option (Signal F)),
              (⟨{ r.base with
                  idx := r.base.idx + 1
                  closed := true
                  roA := Function.update r.base.roA (k, r.base.idx) (some a)
                  roX := p.2
                  roNf := q.2 },
                { r.audit with
                    honestSlopes := a :: r.audit.honestSlopes }⟩ :
                  AuditedFrameSt F M))) := by
    unfold auditedFrameImpl frameImpl emitSignal
    simp only [StateT.run_mk, hopen, Bool.false_eq_true, ↓reduceIte]
    rw [lazyRO_eq_of_none ha]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun p => ?_
    obtain ⟨x, cX⟩ := p
    refine bind_congr fun a => ?_
    refine bind_congr fun q => ?_
    obtain ⟨nf, cNf⟩ := q
    simp [auditAfter, hopen, ha, Function.update_self]
  have hopen' : (idealizeFrame k r).closed = false := hopen
  have hrx : (idealizeFrame k r).roX = r.base.roX := rfl
  have hidx : (idealizeFrame k r).idx = r.base.idx := rfl
  have hnfI : (idealizeFrame k r).honestNf r.base.idx = none := by
    simp [idealizeFrame, ha]
  have hideal : ((idealFrameImpl mclose) .close).run (idealizeFrame k r)
      = (lazyROX r.base.roX mclose >>= fun p =>
          ($ᵗ F) >>= fun y => ($ᵗ F) >>= fun nf =>
            pure ((some ⟨p.1, y, nf⟩ : Option (Signal F)),
              ({ idealizeFrame k r with
                  idx := r.base.idx + 1
                  closed := true
                  roX := p.2
                  honestNf := Function.update (idealizeFrame k r).honestNf
                    r.base.idx (some nf) } : IdealFrameSt F M))) := by
    unfold idealFrameImpl emitIdealSignal
    simp only [StateT.run_mk, hopen', Bool.false_eq_true, ↓reduceIte]
    rw [hrx, hidx, lazyRO_eq_of_none hnfI]
    simp only [bind_assoc, pure_bind]
  rw [hreal, hideal]
  simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases hp : p ∈ support (lazyROX r.base.roX mclose)
  · obtain ⟨hx, -⟩ := lazyROX_support_nonzero hx0 mclose p hp
    refine mul_le_mul_right ?_ _
    have hstep : ∀ a : F,
        (∑' q : F × (F → Option F),
          Pr[= q | lazyRO r.base.roNf a] *
            (if FrameLeakBad k
                { r.audit with honestSlopes := a :: r.audit.honestSlopes }
              then 0
              else G ((some ⟨p.1, rlnY k a p.1, q.1⟩ : Option (Signal F)),
                idealizeFrame k
                  (⟨{ r.base with
                      idx := r.base.idx + 1
                      closed := true
                      roA := Function.update r.base.roA (k, r.base.idx)
                        (some a)
                      roX := p.2
                      roNf := q.2 },
                    { r.audit with
                        honestSlopes := a :: r.audit.honestSlopes }⟩ :
                      AuditedFrameSt F M))))
          ≤ ∑' nf : F, Pr[= nf | ($ᵗ F)] *
              G ((some ⟨p.1, rlnY k a p.1, nf⟩ : Option (Signal F)),
                { idealizeFrame k r with
                    idx := r.base.idx + 1
                    closed := true
                    roX := p.2
                    honestNf := Function.update (idealizeFrame k r).honestNf
                      r.base.idx (some nf) }) := by
      intro a
      by_cases hrec : a ∈ r.audit.slopeProbes ∨ a ∈ r.audit.honestSlopes
      · have hbad : FrameLeakBad k
            { r.audit with honestSlopes := a :: r.audit.honestSlopes } :=
          FrameLeakBad.honest_collision k a r.audit hrec
        refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun q => ?_))
          zero_le'
        rw [if_pos hbad, mul_zero]
      · rw [not_or] at hrec
        obtain ⟨hprobe, hhon⟩ := hrec
        have hnfa : r.base.roNf a = none :=
          roNf_none_of_unrecorded r hcov hprobe hhon
        have hgood' : ¬ FrameLeakBad k
            { r.audit with honestSlopes := a :: r.audit.honestSlopes } :=
          not_frameLeakBad_honest_cons k a r.audit hgood hprobe hhon
        rw [lazyRO_eq_of_none hnfa]
        simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
        refine le_of_eq (tsum_congr fun nf => ?_)
        rw [if_neg hgood',
          idealize_freshSlope_state k a nf r.base.idx (r.base.idx + 1)
            true p.2 r hc hhon hnfa]
    refine le_trans (ENNReal.tsum_le_tsum fun a =>
      mul_le_mul_right (hstep a) _) ?_
    exact le_of_eq (tsum_uniform_rlnY_reindex k p.1 hx
      (fun y => ∑' nf : F, Pr[= nf | ($ᵗ F)] *
        G ((some ⟨p.1, y, nf⟩ : Option (Signal F)),
          { idealizeFrame k r with
              idx := r.base.idx + 1
              closed := true
              roX := p.2
              honestNf := Function.update (idealizeFrame k r).honestNf
                r.base.idx (some nf) })))
  · rw [(probOutput_eq_zero_iff _ _).mpr hp]
    simp

end FreshSlopeCrux

end Zkpc.Games
