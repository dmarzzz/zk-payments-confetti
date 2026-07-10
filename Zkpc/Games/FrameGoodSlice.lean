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

/-! ## Invariant preservation for the good-slice induction

The induction threads six facts through every good step: audit completeness,
hidden-slope injectivity, nullifier coverage, digest nonzeroness, absence of
unconsumed pins, and goodness itself. Completeness (`badOrComplete`),
injectivity (per-op lemmas of `FrameCoupling`), and nonzeroness are landed;
this section adds coverage and pin-freeness, plus the injectivity
dispatcher. -/

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- **No unconsumed pinned slopes.** Every hidden `H_a` entry at or beyond
the honest counter is unmaterialized: the eager-read obstruction cannot
arise, because every materialized hidden slope has already been consumed by
the emission that created it. Maintained by every FRAME operation except the
MC20 reveal `nfAt` (which is exactly the pin-creating operation). -/
def NoPending (k : F) (r : AuditedFrameSt F M) : Prop :=
  ∀ i, r.base.idx ≤ i → r.base.roA (k, i) = none

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- The programmed initial FRAME state has no pinned slopes at all. -/
theorem noPending_initial (k cm : F) :
    NoPending k
      (⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩ : AuditedFrameSt F M) := by
  intro i _
  rfl

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- The empty audit is good: no leakage branch fires on empty lists. -/
theorem goodSlice_not_frameLeakBad_init (k : F) :
    ¬ FrameLeakBad k (FrameAudit.init (F := F)) := by
  intro hbad
  rcases hbad with hk | ⟨s, hs1, -⟩ | hdup
  · simp [FrameAudit.init] at hk
  · simp [FrameAudit.init] at hs1
  · exact hdup (by simp [FrameAudit.init])

/-- **Coverage preservation.** Every supported audited step preserves the
`H_nf` coverage invariant on audit-complete states: adversarial probes are
recorded before they populate, and honest signal or reveal steps populate
only at slopes that the audit records (fresh) or already recorded
(materialized, via completeness). -/
theorem auditedFrameImpl_roNfCovered_step (k : F) (mclose : M)
    (op : FrameOp F M) (r : AuditedFrameSt F M)
    (hc : FrameAuditComplete k r) (hcov : RoNfCovered r)
    (z : (frameSpec F M).Range op × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) op).run r)) :
    RoNfCovered z.2 := by
  unfold auditedFrameImpl at hz
  simp only [StateT.run_mk] at hz
  obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  cases op with
  | spend m =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : r.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        intro q v hqv
        have haud : auditAfter k (.spend m) r.base r.base r.audit = r.audit := by
          simp [auditAfter, hcl]
        rw [haud]
        exact hcov q v hqv
      · rw [if_neg hcl] at hp
        have hopen : r.base.closed = false := by simpa using hcl
        obtain ⟨w, hw, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        unfold emitSignal at hw
        obtain ⟨xc, hxc, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        obtain ⟨ac, hac, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        obtain ⟨nc, hnc, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        rw [support_pure, Set.mem_singleton_iff] at hw
        subst hw
        rw [auditAfter_signal_eq k m (.spend m) r.base _ r.audit
          (Or.inl rfl) hopen]
        intro q v hqv
        change nc.2 q = some v at hqv
        by_cases hq : q = ac.1
        · subst hq
          cases hold : r.base.roA (k, r.base.idx) with
          | some a₀ =>
              simp only [hold]
              have hval := lazyRO_support_value_of_entry r.base.roA
                (k, r.base.idx) ac hac hold
              exact Or.inr (hval ▸ hc r.base.idx a₀ hold)
          | none =>
              have hnew := lazyRO_support_entry r.base.roA (k, r.base.idx)
                ac hac
              simp only [hold, hnew]
              exact Or.inr (List.mem_cons_self ..)
        · have hold' : r.base.roNf q = some v := by
            rw [← lazyRO_support_eq_of_ne r.base.roNf ac.1 nc hnc hq]
            exact hqv
          rcases hcov q v hold' with h | h
          · cases hold : r.base.roA (k, r.base.idx) with
            | some a₀ => simp only [hold]; exact Or.inl h
            | none =>
                have hnew := lazyRO_support_entry r.base.roA (k, r.base.idx)
                  ac hac
                simp only [hold, hnew]
                exact Or.inl h
          · cases hold : r.base.roA (k, r.base.idx) with
            | some a₀ => simp only [hold]; exact Or.inr h
            | none =>
                have hnew := lazyRO_support_entry r.base.roA (k, r.base.idx)
                  ac hac
                simp only [hold, hnew]
                exact Or.inr (List.mem_cons_of_mem _ h)
  | close =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : r.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        intro q v hqv
        have haud : auditAfter k .close r.base r.base r.audit = r.audit := by
          simp [auditAfter, hcl]
        rw [haud]
        exact hcov q v hqv
      · rw [if_neg hcl] at hp
        have hopen : r.base.closed = false := by simpa using hcl
        obtain ⟨w, hw, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        unfold emitSignal at hw
        obtain ⟨xc, hxc, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        obtain ⟨ac, hac, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        obtain ⟨nc, hnc, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        rw [support_pure, Set.mem_singleton_iff] at hw
        subst hw
        rw [auditAfter_signal_eq k mclose .close r.base _ r.audit
          (Or.inr rfl) hopen]
        intro q v hqv
        change nc.2 q = some v at hqv
        by_cases hq : q = ac.1
        · subst hq
          cases hold : r.base.roA (k, r.base.idx) with
          | some a₀ =>
              simp only [hold]
              have hval := lazyRO_support_value_of_entry r.base.roA
                (k, r.base.idx) ac hac hold
              exact Or.inr (hval ▸ hc r.base.idx a₀ hold)
          | none =>
              have hnew := lazyRO_support_entry r.base.roA (k, r.base.idx)
                ac hac
              simp only [hold, hnew]
              exact Or.inr (List.mem_cons_self ..)
        · have hold' : r.base.roNf q = some v := by
            rw [← lazyRO_support_eq_of_ne r.base.roNf ac.1 nc hnc hq]
            exact hqv
          rcases hcov q v hold' with h | h
          · cases hold : r.base.roA (k, r.base.idx) with
            | some a₀ => simp only [hold]; exact Or.inl h
            | none =>
                have hnew := lazyRO_support_entry r.base.roA (k, r.base.idx)
                  ac hac
                simp only [hold, hnew]
                exact Or.inl h
          · cases hold : r.base.roA (k, r.base.idx) with
            | some a₀ => simp only [hold]; exact Or.inr h
            | none =>
                have hnew := lazyRO_support_entry r.base.roA (k, r.base.idx)
                  ac hac
                simp only [hold, hnew]
                exact Or.inr (List.mem_cons_of_mem _ h)
  | nfAt i =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨ac, hac, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain ⟨nc, hnc, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      intro q v hqv
      change nc.2 q = some v at hqv
      show q ∈ (auditAfter k (.nfAt i) r.base
          { r.base with roA := ac.2, roNf := nc.2 } r.audit).slopeProbes ∨
        q ∈ (auditAfter k (.nfAt i) r.base
          { r.base with roA := ac.2, roNf := nc.2 } r.audit).honestSlopes
      unfold auditAfter
      by_cases hq : q = ac.1
      · subst hq
        cases hold : r.base.roA (k, i) with
        | some a₀ =>
            simp only [hold]
            have hval := lazyRO_support_value_of_entry r.base.roA (k, i)
              ac hac hold
            exact Or.inr (hval ▸ hc i a₀ hold)
        | none =>
            have hnew := lazyRO_support_entry r.base.roA (k, i) ac hac
            simp only [hold, hnew]
            exact Or.inr (List.mem_cons_self ..)
      · have hold' : r.base.roNf q = some v := by
          rw [← lazyRO_support_eq_of_ne r.base.roNf ac.1 nc hnc hq]
          exact hqv
        rcases hcov q v hold' with h | h
        · cases hold : r.base.roA (k, i) with
          | some a₀ => simp only [hold]; exact Or.inl h
          | none =>
              have hnew := lazyRO_support_entry r.base.roA (k, i) ac hac
              simp only [hold, hnew]
              exact Or.inl h
        · cases hold : r.base.roA (k, i) with
          | some a₀ => simp only [hold]; exact Or.inr h
          | none =>
              have hnew := lazyRO_support_entry r.base.roA (k, i) ac hac
              simp only [hold, hnew]
              exact Or.inr (List.mem_cons_of_mem _ h)
  | roA kq n =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      intro q v hqv
      change r.base.roNf q = some v at hqv
      rcases hcov q v hqv with h | h
      · exact Or.inl h
      · exact Or.inr h
  | roX m =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      intro q v hqv
      change r.base.roNf q = some v at hqv
      rcases hcov q v hqv with h | h
      · exact Or.inl h
      · exact Or.inr h
  | roNf aq =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      intro q v hqv
      change c.2 q = some v at hqv
      by_cases hq : q = aq
      · subst hq
        exact Or.inl (List.mem_cons_self ..)
      · have hold' : r.base.roNf q = some v := by
          rw [← lazyRO_support_eq_of_ne r.base.roNf aq c hcm hq]
          exact hqv
        rcases hcov q v hold' with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
  | roE kq e =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      intro q v hqv
      change r.base.roNf q = some v at hqv
      rcases hcov q v hqv with h | h
      · exact Or.inl h
      · exact Or.inr h
  | roId kq =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      intro q v hqv
      change r.base.roNf q = some v at hqv
      rcases hcov q v hqv with h | h
      · exact Or.inl h
      · exact Or.inr h

/-- **Pin-freeness preservation off the reveal oracle.** Every supported
audited step of an operation other than `nfAt` preserves the absence of
unconsumed pinned slopes on good outcomes: honest emissions consume the
entry they materialize, public queries never touch the hidden row, and a
direct hidden-row probe is an immediately-bad branch. -/
theorem auditedFrameImpl_noPending_step (k : F) (mclose : M)
    (op : FrameOp F M) (hop : ∀ i, op ≠ .nfAt i)
    (r : AuditedFrameSt F M) (hnp : NoPending k r)
    (z : (frameSpec F M).Range op × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) op).run r))
    (hgoodz : ¬ FrameLeakBad k z.2.audit) :
    NoPending k z.2 := by
  unfold auditedFrameImpl at hz
  simp only [StateT.run_mk] at hz
  obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  cases op with
  | nfAt i => exact absurd rfl (hop i)
  | spend m =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : r.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hnp
      · rw [if_neg hcl] at hp
        obtain ⟨w, hw, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        unfold emitSignal at hw
        obtain ⟨xc, hxc, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        obtain ⟨ac, hac, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        obtain ⟨nc, hnc, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        rw [support_pure, Set.mem_singleton_iff] at hw
        subst hw
        intro i hi
        change r.base.idx + 1 ≤ i at hi
        change ac.2 (k, i) = none
        have hne : (k, i) ≠ (k, r.base.idx) := fun h => by
          have := congrArg Prod.snd h
          simp only at this
          omega
        rw [lazyRO_support_eq_of_ne r.base.roA (k, r.base.idx) ac hac hne]
        exact hnp i (by omega)
  | close =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : r.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hnp
      · rw [if_neg hcl] at hp
        obtain ⟨w, hw, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        unfold emitSignal at hw
        obtain ⟨xc, hxc, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        obtain ⟨ac, hac, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        obtain ⟨nc, hnc, hw⟩ := (mem_support_bind_iff _ _ _).mp hw
        rw [support_pure, Set.mem_singleton_iff] at hw
        subst hw
        intro i hi
        change r.base.idx + 1 ≤ i at hi
        change ac.2 (k, i) = none
        have hne : (k, i) ≠ (k, r.base.idx) := fun h => by
          have := congrArg Prod.snd h
          simp only at this
          omega
        rw [lazyRO_support_eq_of_ne r.base.roA (k, r.base.idx) ac hac hne]
        exact hnp i (by omega)
  | roA kq n =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      by_cases hk : kq = k
      · exfalso
        subst hk
        exact hgoodz (auditAfter_direct_secret_bad kq n r.base
          { r.base with roA := c.2 } r.audit)
      · intro i hi
        change c.2 (k, i) = none
        have hne : (k, i) ≠ (kq, n) := fun h =>
          hk ((congrArg Prod.fst h).symm)
        rw [lazyRO_support_eq_of_ne r.base.roA (kq, n) c hcm hne]
        exact hnp i hi
  | roX m =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hnp
  | roNf aq =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hnp
  | roE kq e =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hnp
  | roId kq =>
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hnp

/-- **Injectivity dispatcher.** Hidden-slope injectivity is preserved by
every supported audited step whose outcome stays good, assembled from the
per-operation lemmas of `FrameCoupling`. -/
theorem auditedFrameImpl_hiddenSlopeInj_step (k : F) (mclose : M)
    (op : FrameOp F M) (r : AuditedFrameSt F M)
    (hc : FrameAuditComplete k r) (hinj : HiddenSlopeInj k r)
    (z : (frameSpec F M).Range op × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) op).run r))
    (hgoodz : ¬ FrameLeakBad k z.2.audit) :
    HiddenSlopeInj k z.2 := by
  cases op with
  | roA kq n => exact hiddenSlopeInj_roA_step k mclose kq n r hinj z hz hgoodz
  | roX m =>
      exact hiddenSlopeInj_public_step k mclose (.roX m) trivial r hinj z hz
  | roNf aq =>
      exact hiddenSlopeInj_public_step k mclose (.roNf aq) trivial r hinj z hz
  | roE kq e =>
      exact hiddenSlopeInj_public_step k mclose (.roE kq e) trivial r hinj z hz
  | roId kq =>
      exact hiddenSlopeInj_public_step k mclose (.roId kq) trivial r hinj z hz
  | nfAt i => exact hiddenSlopeInj_nfAt_step k mclose i r hc hinj z hz hgoodz
  | spend m =>
      unfold auditedFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : r.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hinj
      · rw [if_neg hcl] at hp
        have hopen : r.base.closed = false := by simpa using hcl
        obtain ⟨w, hw, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hiddenSlopeInj_emitSignal k m (.spend m) r hc hinj
          (Or.inl rfl) hopen w hw hgoodz
  | close =>
      unfold auditedFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : r.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hinj
      · rw [if_neg hcl] at hp
        have hopen : r.base.closed = false := by simpa using hcl
        obtain ⟨w, hw, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hiddenSlopeInj_emitSignal k mclose .close r hc hinj
          (Or.inr rfl) hopen w hw hgoodz


/-! ## The pin-free good-slice induction -/

/-- Classifier for the MC20 reveal oracle `nfAt`. -/
def isNfAtOp : FrameOp F M → Bool
  | .nfAt _ => true
  | _ => false

/-- An adversary is `nfAt`-free when it never queries the MC20 reveal
oracle, certified structurally per delivered commitment. On such runs no
unconsumed pinned slope ever exists, so the good-slice dominance closes
pointwise (`goodSlice_run_le_of_nfAtFree`). -/
def NfAtFree (A : F → OracleComp (frameSpec F M) (Evidence F)) : Prop :=
  ∀ cm : F, OracleComp.IsQueryBoundP (A cm) (fun t => isNfAtOp t = true) 0

section Induction

variable [Fintype F]

/-- **The assembled good-slice induction, pin-free fragment (Spec.md §7
T7).** For an adversary computation that never queries `nfAt`, from any
state satisfying the six threaded invariants, the guarded real win
expectation is dominated by the ideal win expectation. Each step is one of:
a killed secret-touching branch (`roA`/`roE`/`roId` at `k`, `roNf` at an
exposed slope — zero good-slice mass), an exactly-idealized public or closed
step, or a fresh-slope emission crux; `NoPending` rules out the pinned
emission, and is itself maintained because `nfAt` — the only pin creator —
is excluded by the query bound. -/
theorem goodSlice_run_le_of_nfAtFree (k : F) (mclose : M)
    (φ : Evidence F → ENNReal) :
    ∀ (oa : OracleComp (frameSpec F M) (Evidence F)),
      OracleComp.IsQueryBoundP oa (fun t => isNfAtOp t = true) 0 →
      ∀ (r : AuditedFrameSt F M),
        FrameAuditComplete k r → HiddenSlopeInj k r → RoNfCovered r →
        RoXCacheNonzero r.base.roX → NoPending k r →
        ¬ FrameLeakBad k r.audit →
        (∑' z : Evidence F × AuditedFrameSt F M,
          Pr[= z | (simulateQ (auditedFrameImpl k mclose) oa).run r] *
            (if FrameLeakBad k z.2.audit then 0 else φ z.1))
          ≤ ∑' w : Evidence F × IdealFrameSt F M,
              Pr[= w | (simulateQ (idealFrameImpl mclose) oa).run
                  (idealizeFrame k r)] * φ w.1 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure ev =>
      intro _ r _ _ _ _ _ hgood
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      rw [if_neg hgood]
  | query_bind t kont ih =>
      intro hqb r hc hinj hcov hx0 hnp hgood
      rw [isQueryBoundP_query_bind_iff] at hqb
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        tsum_probOutput_bind_mul]
      have hcont : (∀ i, t ≠ FrameOp.nfAt i) →
          ∀ (p : (frameSpec F M).Range t × AuditedFrameSt F M),
          p ∈ support (((auditedFrameImpl k mclose) t).run r) →
          (∑' z : Evidence F × AuditedFrameSt F M,
            Pr[= z | (simulateQ (auditedFrameImpl k mclose)
                (kont p.1)).run p.2] *
              (if FrameLeakBad k z.2.audit then 0 else φ z.1))
            ≤ (if FrameLeakBad k p.2.audit then 0
                else ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont p.1)).run (idealizeFrame k p.2)] * φ w.1) := by
        intro hnfat p hp
        by_cases hbadp : FrameLeakBad k p.2.audit
        · rw [if_pos hbadp]
          exact le_of_eq
            (goodSlice_run_zero_of_bad k mclose (kont p.1) p.2 hbadp _)
        · rw [if_neg hbadp]
          refine ih p.1 (hqb.2 p.1) p.2 ?_ ?_ ?_ ?_ ?_ hbadp
          · rcases auditedFrameImpl_badOrComplete_step k mclose t r
              (Or.inr hc) p hp with h | h
            · exact absurd h hbadp
            · exact h
          · exact auditedFrameImpl_hiddenSlopeInj_step k mclose t r hc hinj
              p hp hbadp
          · exact auditedFrameImpl_roNfCovered_step k mclose t r hc hcov p hp
          · exact auditedFrameImpl_roXNonzero_step k mclose t r hx0 p hp
          · exact auditedFrameImpl_noPending_step k mclose t hnfat r hnp
              p hp hbadp
      cases t with
      | nfAt i =>
          exfalso
          rcases hqb.1 with hnot | hlt
          · exact hnot rfl
          · exact absurd hlt (lt_irrefl 0)
      | roX m =>
          refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
            (goodSlice_step_le_of_idealize_eq k mclose r
              (idealize_roX_step k mclose m r)
              (fun q => ∑' w : Evidence F × IdealFrameSt F M,
                Pr[= w | (simulateQ (idealFrameImpl mclose)
                    (kont q.1)).run q.2] * φ w.1))
          by_cases hp : p ∈ support
            (((auditedFrameImpl k mclose) (FrameOp.roX m)).run r)
          · exact mul_le_mul_right
              (hcont (fun i h => FrameOp.noConfusion h) p hp) _
          · rw [(probOutput_eq_zero_iff _ _).mpr hp]
            simp
      | roA kq n =>
          by_cases hk : kq = k
          · subst hk
            refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (le_trans (le_of_eq (tsum_goodGuard_zero_of_support_bad k
                (((auditedFrameImpl k mclose) (FrameOp.roA k n)).run r)
                (fun z hz =>
                  auditedFrameImpl_support_bad_roA k mclose n r z hz)
                (fun p => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont p.1)).run (idealizeFrame k p.2)] * φ w.1)))
                zero_le')
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.roA k n)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
          · refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (goodSlice_step_le_of_idealize_eq k mclose r
                (idealize_roA_step k mclose kq n r hk)
                (fun q => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont q.1)).run q.2] * φ w.1))
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.roA kq n)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
      | roE kq e =>
          by_cases hk : kq = k
          · subst hk
            refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (le_trans (le_of_eq (tsum_goodGuard_zero_of_support_bad k
                (((auditedFrameImpl k mclose) (FrameOp.roE k e)).run r)
                (fun z hz =>
                  auditedFrameImpl_support_bad_roE k mclose e r z hz)
                (fun p => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont p.1)).run (idealizeFrame k p.2)] * φ w.1)))
                zero_le')
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.roE k e)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
          · refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (goodSlice_step_le_of_idealize_eq k mclose r
                (idealize_roE_step k mclose kq e r hk)
                (fun q => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont q.1)).run q.2] * φ w.1))
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.roE kq e)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
      | roId kq =>
          by_cases hk : kq = k
          · subst hk
            refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (le_trans (le_of_eq (tsum_goodGuard_zero_of_support_bad k
                (((auditedFrameImpl k mclose) (FrameOp.roId k)).run r)
                (fun z hz =>
                  auditedFrameImpl_support_bad_roId k mclose r z hz)
                (fun p => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont p.1)).run (idealizeFrame k p.2)] * φ w.1)))
                zero_le')
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.roId k)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
          · refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (goodSlice_step_le_of_idealize_eq k mclose r
                (idealize_roId_step k mclose kq r hk)
                (fun q => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont q.1)).run q.2] * φ w.1))
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.roId kq)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
      | roNf aq =>
          by_cases haq : aq ∈ r.audit.honestSlopes
          · refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (le_trans (le_of_eq (tsum_goodGuard_zero_of_support_bad k
                (((auditedFrameImpl k mclose) (FrameOp.roNf aq)).run r)
                (fun z hz =>
                  auditedFrameImpl_support_bad_roNf k mclose aq r haq z hz)
                (fun p => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont p.1)).run (idealizeFrame k p.2)] * φ w.1)))
                zero_le')
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.roNf aq)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
          · refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (goodSlice_step_le_of_idealize_eq k mclose r
                (idealize_roNf_step k mclose aq r hc haq)
                (fun q => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont q.1)).run q.2] * φ w.1))
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.roNf aq)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
      | spend m =>
          by_cases hcl : r.base.closed
          · refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (goodSlice_step_le_of_idealize_eq k mclose r
                (idealize_spend_step_closed k mclose m r hcl)
                (fun q => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont q.1)).run q.2] * φ w.1))
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.spend m)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
          · have hopen : r.base.closed = false := by simpa using hcl
            refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (goodSlice_step_le_spend_fresh k mclose m r hopen
                (hnp r.base.idx le_rfl) hc hcov hx0 hgood
                (fun q => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont q.1)).run q.2] * φ w.1))
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) (FrameOp.spend m)).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
      | close =>
          by_cases hcl : r.base.closed
          · refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (goodSlice_step_le_of_idealize_eq k mclose r
                (idealize_close_step_closed k mclose r hcl)
                (fun q => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont q.1)).run q.2] * φ w.1))
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) FrameOp.close).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp
          · have hopen : r.base.closed = false := by simpa using hcl
            refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
              (goodSlice_step_le_close_fresh k mclose r hopen
                (hnp r.base.idx le_rfl) hc hcov hx0 hgood
                (fun q => ∑' w : Evidence F × IdealFrameSt F M,
                  Pr[= w | (simulateQ (idealFrameImpl mclose)
                      (kont q.1)).run q.2] * φ w.1))
            by_cases hp : p ∈ support
              (((auditedFrameImpl k mclose) FrameOp.close).run r)
            · exact mul_le_mul_right
                (hcont (fun i h => FrameOp.noConfusion h) p hp) _
            · rw [(probOutput_eq_zero_iff _ _).mpr hp]
              simp

/-- **Pointwise good-slice dominance for `nfAt`-free adversaries (Spec.md §7
T7).** The named residual `FramePointwiseGoodSlice` holds unconditionally on
the fragment that never queries the MC20 reveal oracle: instantiate the
pin-free induction at the programmed initial state and erase the ghost. -/
theorem framePointwiseGoodSlice_of_nfAtFree (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (hA : NfAtFree A) (k : F) :
    FramePointwiseGoodSlice mclose A k := by
  refine framePointwiseGoodSlice_of_idealDom mclose A k fun cm => ?_
  have h := goodSlice_run_le_of_nfAtFree k mclose
    (fun ev => if Slashes k ev then 1 else 0) (A cm) (hA cm)
    ⟨{ FrameSt.init F M with
        roId := Function.update (FrameSt.init F M).roId k (some cm) },
      FrameAudit.init⟩
    (frameAuditComplete_initial k cm) (hiddenSlopeInj_initial k cm)
    (roNfCovered_initial k cm) roXCacheNonzero_init (noPending_initial k cm)
    (not_frameLeakBad_init k)
  rw [idealizeFrame_initial k cm] at h
  exact h

/-- **The k-averaged good-slice transfer for `nfAt`-free adversaries**
(Spec.md §7 T7): the transfer residual of the corrected certificate holds
outright on the reveal-free fragment. -/
theorem frameGoodSliceTransfer_of_nfAtFree (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) (hA : NfAtFree A) :
    FrameGoodSliceTransfer mclose A :=
  frameGoodSliceTransfer_of_pointwise mclose A fun k =>
    framePointwiseGoodSlice_of_nfAtFree mclose A hA k

end Induction

end Zkpc.Games
