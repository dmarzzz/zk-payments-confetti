import Zkpc.Games.FrameAssembly

/-!
# The real-side bad-mass route to the k-averaged T7 certificate (Spec.md §7 T7)

`Zkpc/Games/FrameAssembly.lean` reduced the unconditional T7 endpoint to
three named residuals: `FrameGoodSliceTransfer`, `FrameBadMassTransfer`,
and `GhostSlopeBadBounds`. This file records a **statement-level warning**
about `FrameBadMassTransfer` and lands the safer alternative assembly that
bypasses it.

## Why `FrameBadMassTransfer` is second-order delicate

`FrameBadMassTransfer` asks for real-bad ≤ ghost-bad, k-averaged. It is
**not per-transcript dominated**. Off the bad event, the real run is
re-parameterizable by its answer transcript: each consumed honest signal
contributes `y = k + a·x` with a single-use hidden slope, so conditioned on
a fixed answer transcript the consumed slopes are the *deterministic
`k`-roots* `a_i = (y_i − k)/x_i`, correlated through the one deferred `k`,
whereas the ghost slopes are independent uniforms. Example: two consumed
signals and one `H_nf` probe `q`, no direct secret probes. Conditioned on a
generic transcript the real leakage event is `k ∈ {y₁ − q·x₁, y₂ − q·x₂,
(y₁x₂ − y₂x₁)/(x₂ − x₁)}` — exactly `3/|F|` — while the ghost leakage mass
is `Pr[q = a'₁ ∨ q = a'₂ ∨ a'₁ = a'₂] = 3/|F| − 2/|F|²`, *strictly
smaller*. The k-averaged inequality can therefore only hold (if it holds)
by exact cancellation against transcripts with coincident roots; no
per-step or per-transcript coupling argument can close it, and any attempt
must carry exact second-order bookkeeping.

## The union-bound-clean alternative

By contrast, the *direct* real-side bound
`Pr[FrameLeakBad] ≤ qb.total/|F|` is first-order clean under the same
re-parameterization: every branch of the leakage event pins the deferred
uniform `k` to at most one root (or an unconsumed fresh slope to at most
one value) per budget pair — `qA + qE + qId` direct-probe roots,
`qNf · qSig` slope-probe roots, `qSig²` collision roots — so plain union
bounds suffice, exactly as in the ghost lane's tape argument. The
definition `FrameRealBadMassLe` names that obligation, and the assembly
below shows it (together with the good-slice transfer) suffices for the
complete corrected endpoint, with **no** ghost-side bad-mass comparison at
all. The endpoint therefore has two independent routes:

* route A (`FrameAssembly`): `FrameGoodSliceTransfer` +
  `FrameBadMassTransfer` + `GhostSlopeBadBounds`;
* route B (this file): `FrameGoodSliceTransfer` + `FrameRealBadMassLe`.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

section RealBadRoute

variable [Fintype F]

/-- Two predicate-targeted query bounds combine into a bound for their union.
The predicates may overlap; an overlapping query spends both source budgets,
which is conservatively dominated by spending one unit from their sum. -/
theorem isQueryBoundP_or {ι α : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec α) (p q : ι → Prop)
    [DecidablePred p] [DecidablePred q] (n m : ℕ)
    (hp : OracleComp.IsQueryBoundP oa p n)
    (hq : OracleComp.IsQueryBoundP oa q m) :
    OracleComp.IsQueryBoundP oa (fun t => p t ∨ q t) (n + m) := by
  induction oa using OracleComp.inductionOn generalizing n m with
  | pure x => trivial
  | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hp hq ⊢
      constructor
      · by_cases h : p t ∨ q t
        · right
          rcases h with h | h
          · rcases hp.1 with hnp | hn
            · exact (hnp h).elim
            · omega
          · rcases hq.1 with hnq | hm
            · exact (hnq h).elim
            · omega
        · exact Or.inl h
      · intro u
        have hrest := ih u _ _ (hp.2 u) (hq.2 u)
        refine hrest.mono ?_
        have hpPos : p t → 0 < n := fun h => hp.1.resolve_left (not_not_intro h)
        have hqPos : q t → 0 < m := fun h => hq.1.resolve_left (not_not_intro h)
        by_cases hpt : p t
        · have hn := hpPos hpt
          by_cases hqt : q t
          · have hm := hqPos hqt
            simp [hpt, hqt]
            omega
          · simp [hpt, hqt]
            omega
        · by_cases hqt : q t
          · have hm := hqPos hqt
            simp [hpt, hqt]
            omega
          · simp [hpt, hqt]

/-- The three direct-secret query budgets combine into the aggregate audit
classifier used by `FrameAudit.secretProbes`. -/
theorem frameQueryBounds_secret_bound
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (cm : F) :
    OracleComp.IsQueryBoundP (A cm)
      (fun t => decide ((isDirectRoAQuery t = true ∨
        isDirectRoEQuery t = true) ∨ isDirectRoIdQuery t = true) = true)
      (qb.qA + qb.qE + qb.qId) := by
  have hAE := isQueryBoundP_or (A cm)
    (fun t => isDirectRoAQuery t = true)
    (fun t => isDirectRoEQuery t = true) qb.qA qb.qE
    (qb.roA_bound cm) (qb.roE_bound cm)
  have hAEI := isQueryBoundP_or (A cm)
    (fun t => isDirectRoAQuery t = true ∨ isDirectRoEQuery t = true)
    (fun t => isDirectRoIdQuery t = true) (qb.qA + qb.qE) qb.qId
    hAE (qb.roId_bound cm)
  simpa only [decide_eq_true_eq, Nat.add_assoc] using hAEI

/-- Structural audit bounds for a fixed-secret, fixed-commitment audited run.
These are the support invariants consumed by each real bad-mass component
induction. -/
theorem auditedFrameImpl_run_audit_bounds (k : F) (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (cm : F)
    (z : Evidence F × AuditedFrameSt F M)
    (hz : z ∈ support ((simulateQ (auditedFrameImpl k mclose) (A cm)).run
      ⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩)) :
    z.2.audit.secretProbes.length ≤ qb.qA + qb.qE + qb.qId ∧
    z.2.audit.slopeProbes.length ≤ qb.qNf ∧
    z.2.audit.honestSlopes.length ≤ qb.qSig := by
  let s0 : AuditedFrameSt F M :=
    ⟨{ FrameSt.init F M with
        roId := Function.update (FrameSt.init F M).roId k (some cm) },
      FrameAudit.init⟩
  have hsecret := support_measure_le_of_isQueryBoundP
    (auditedFrameImpl k mclose) (fun s => s.audit.secretProbes.length)
    (fun t => (isDirectRoAQuery t = true ∨ isDirectRoEQuery t = true) ∨
      isDirectRoIdQuery t = true)
    (fun t s y hy => by
      change y.2.audit.secretProbes.length ≤
        s.audit.secretProbes.length +
          if decide ((isDirectRoAQuery t = true ∨ isDirectRoEQuery t = true) ∨
            isDirectRoIdQuery t = true) = true then 1 else 0
      rw [auditedFrameImpl_support_audit k mclose t s y hy]
      have ha := auditAfter_secret_length_le k t s.base y.2.base s.audit
      cases t <;> simpa [isSecretProbe, isDirectRoAQuery, isDirectRoEQuery,
        isDirectRoIdQuery] using ha)
    (A cm) (frameQueryBounds_secret_bound A qb cm) s0 z hz
  have hslope := support_measure_le_of_isQueryBoundP
    (auditedFrameImpl k mclose) (fun s => s.audit.slopeProbes.length)
    isSlopeProbe
    (fun t s y hy => by
      change y.2.audit.slopeProbes.length ≤
        s.audit.slopeProbes.length + if isSlopeProbe t then 1 else 0
      rw [auditedFrameImpl_support_audit k mclose t s y hy]
      exact auditAfter_slope_length_le k t s.base y.2.base s.audit)
    (A cm) (by simpa [isSlopeProbe, isDirectRoNfQuery] using qb.roNf_bound cm)
    s0 z hz
  have hhonest := support_measure_le_of_isQueryBoundP
    (auditedFrameImpl k mclose) (fun s => s.audit.honestSlopes.length)
    isHonestSignalOp
    (fun t s y hy => by
      change y.2.audit.honestSlopes.length ≤
        s.audit.honestSlopes.length + if isHonestSignalOp t then 1 else 0
      rw [auditedFrameImpl_support_audit k mclose t s y hy]
      exact auditAfter_honest_length_le k t s.base y.2.base s.audit)
    (A cm) (by simpa [isHonestSignalOp, isSignalQuery] using qb.signal_bound cm)
    s0 z hz
  constructor
  · simpa [s0, FrameAudit.init] using hsecret
  · constructor
    · simpa [s0, FrameAudit.init] using hslope
    · simpa [s0, FrameAudit.init] using hhonest

/-- The same structural audit bounds after the public commitment is sampled
inside the complete real run. -/
theorem auditedFrameRun_audit_bounds (k : F) (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (z : Evidence F × AuditedFrameSt F M)
    (hz : z ∈ support (auditedFrameRun mclose A k)) :
    z.2.audit.secretProbes.length ≤ qb.qA + qb.qE + qb.qId ∧
    z.2.audit.slopeProbes.length ≤ qb.qNf ∧
    z.2.audit.honestSlopes.length ≤ qb.qSig := by
  unfold auditedFrameRun at hz
  obtain ⟨cm, -, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  exact auditedFrameImpl_run_audit_bounds k mclose A qb cm z hz

/-- **Direct real-side bad-mass obligation (named residual).** Over the
audited joint FRAME experiment — honest secret first, exactly as the real
game draws it — the audited leakage event has probability at most
`qb.total/|F|`. Unlike `FrameBadMassTransfer`, this is a first-order
union-bound target under the answer-transcript re-parameterization of the
real run (each leakage branch pins the secret or one fresh slope to a
single root per budget pair). -/
def FrameRealBadMassLe (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) : Prop :=
  Pr[= true | auditedFrameJoint mclose A >>= fun w =>
      pure (decide (FrameLeakBad w.1 w.2.2.audit))]
    ≤ (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹

/-- The three first-order components of the real audited leakage event.  This
is the exact real-side analogue of `GhostSlopeBadBounds`, with the direct
secret channel included because the real run draws `k` first. -/
structure FrameRealBadComponents (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) : Prop where
  direct_secret :
    Pr[fun w => w.1 ∈ w.2.2.audit.secretProbes | auditedFrameJoint mclose A]
      ≤ ((qb.qA + qb.qE + qb.qId : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹
  slope_hit :
    Pr[fun w => ∃ slope ∈ w.2.2.audit.slopeProbes,
        slope ∈ w.2.2.audit.honestSlopes | auditedFrameJoint mclose A]
      ≤ ((qb.qNf * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹
  honest_collision :
    Pr[fun w => ¬ w.2.2.audit.honestSlopes.Nodup | auditedFrameJoint mclose A]
      ≤ ((qb.qSig * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹

/-- Union-bound closure of the direct real-side bad mass.  All probability
arithmetic is discharged here; the handler induction only has to construct
the three component fields. -/
theorem frameRealBadMassLe_of_components (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (h : FrameRealBadComponents mclose A qb) :
    FrameRealBadMassLe mclose A qb := by
  unfold FrameRealBadMassLe
  rw [probOutput_bind_decide_eq_probEvent]
  let direct : F × (Evidence F × AuditedFrameSt F M) → Prop :=
    fun w => w.1 ∈ w.2.2.audit.secretProbes
  let slopeHit : F × (Evidence F × AuditedFrameSt F M) → Prop :=
    fun w => ∃ slope ∈ w.2.2.audit.slopeProbes,
      slope ∈ w.2.2.audit.honestSlopes
  let collision : F × (Evidence F × AuditedFrameSt F M) → Prop :=
    fun w => ¬ w.2.2.audit.honestSlopes.Nodup
  change Pr[fun w => direct w ∨ slopeHit w ∨ collision w |
      auditedFrameJoint mclose A] ≤ _
  refine le_trans
    ((probEvent_or_le (auditedFrameJoint mclose A) direct
      (fun w => slopeHit w ∨ collision w)).trans
        (add_le_add le_rfl
          (probEvent_or_le (auditedFrameJoint mclose A) slopeHit collision))) ?_
  refine (add_le_add h.direct_secret
    (add_le_add h.slope_hit h.honest_collision)).trans ?_
  simp only [FrameQueryBounds.total, Nat.cast_add, Nat.cast_mul, add_mul]
  simp only [add_assoc]
  exact le_refl _

/-- **Assembly of the corrected T7 certificate, real-side bad route**
(Spec.md §7 T7). The good-slice transfer plus the direct real-side
bad-mass bound construct the k-averaged deferred-sampling certificate,
bypassing both the ghost bad-mass comparison (`FrameBadMassTransfer`) and
the ghost slope socket (`GhostSlopeBadBounds`) entirely. -/
noncomputable def frameDeferredSamplingAvg_of_goodSlice_and_realBad
    (mclose : M) (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (hgood : FrameGoodSliceTransfer mclose A)
    (hreal : FrameRealBadMassLe mclose A qb) :
    FrameDeferredSamplingAvg mclose A qb where
  idealEvidence := ghostFrameEvidence mclose A
  close_avg := by
    rw [frameRealSlashGame_eq_auditedJoint mclose A]
    refine le_trans (probOutput_bind_decide_le_split (auditedFrameJoint mclose A)
      (fun w => Slashes w.1 w.2.1) (fun w => FrameLeakBad w.1 w.2.2.audit)) ?_
    exact add_le_add
      (le_trans hgood
        (le_of_eq (ghostFrameRun_win_eq_certificate_form mclose A)))
      hreal

/-- **The corrected FRAME bound, real-side bad route** (Spec.md §7 T7).
For every query-bounded adversary, the good-slice transfer and the direct
real-side bad-mass bound yield the complete corrected exculpability bound
`(qb.total + 1)/|F|`. Together with route A of `FrameAssembly`, the
unconditional T7 endpoint holds as soon as *either*
`FrameBadMassTransfer + GhostSlopeBadBounds` *or* `FrameRealBadMassLe`
is discharged alongside `FrameGoodSliceTransfer`. -/
theorem T7_frame_query_bound_of_goodSlice_and_realBad (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (hgood : FrameGoodSliceTransfer mclose A)
    (hreal : FrameRealBadMassLe mclose A qb) :
    frameWinProb mclose A
      ≤ ((qb.total + 1 : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ :=
  T7_frame_query_bound_avg mclose A qb
    (frameDeferredSamplingAvg_of_goodSlice_and_realBad mclose A qb hgood hreal)

end RealBadRoute

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.T7_frame_query_bound_of_goodSlice_and_realBad
#print axioms Zkpc.Games.frameRealBadMassLe_of_components
#print axioms Zkpc.Games.isQueryBoundP_or
#print axioms Zkpc.Games.frameQueryBounds_secret_bound
#print axioms Zkpc.Games.auditedFrameImpl_run_audit_bounds
#print axioms Zkpc.Games.auditedFrameRun_audit_bounds
