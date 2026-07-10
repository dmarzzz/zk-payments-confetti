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

/-! ## Real-side per-step audit and invariant bricks

Support-level facts about the audited real handler that the two transfer
inductions thread through every step. -/

/-- Every supported audited step's final audit is exactly `auditAfter` of the
step's base transition — the real-side analogue of the per-operation ghost
audit-transition lemmas of `FrameGhost`. -/
theorem auditedFrameImpl_support_audit (k : F) (mclose : M) (op : FrameOp F M)
    (s : AuditedFrameSt F M)
    (z : (frameSpec F M).Range op × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) op).run s)) :
    z.2.audit = auditAfter k op s.base z.2.base s.audit := by
  unfold auditedFrameImpl at hz
  simp only [StateT.run_mk] at hz
  obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

/-- Run-level bad-event monotonicity for the audited real handler: an
already-raised leakage event survives any full simulated run. Together with
`ghostFrameImpl_run_bad_monotone` this makes bad-at-end coincide with
bad-ever-fired on both sides of the coupling. -/
theorem auditedFrameImpl_run_bad_monotone (k : F) (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (s : AuditedFrameSt F M)
    (hbad : FrameLeakBad k s.audit)
    (z : α × AuditedFrameSt F M)
    (hz : z ∈ support ((simulateQ (auditedFrameImpl k mclose) oa).run s)) :
    FrameLeakBad k z.2.audit :=
  OracleComp.simulateQ_run_preserves_inv_of_query (auditedFrameImpl k mclose)
    (fun u => FrameLeakBad k u.audit)
    (fun t u hu y hy => auditedFrameImpl_bad_monotone k mclose t u hu y hy)
    oa s hbad z hz

/-- **The threadable completeness invariant.** `FrameAuditComplete` alone is
*not* preserved through a bad-firing `roA(k,·)` step (such a probe can
materialize a hidden slope that no signal recorded), so the coupling induction
must carry the disjunction with the leakage event: every supported audited step
preserves `FrameLeakBad ∨ FrameAuditComplete`. -/
theorem auditedFrameImpl_badOrComplete_step (k : F) (mclose : M)
    (op : FrameOp F M) (s : AuditedFrameSt F M)
    (h : FrameLeakBad k s.audit ∨ FrameAuditComplete k s)
    (z : (frameSpec F M).Range op × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) op).run s)) :
    FrameLeakBad k z.2.audit ∨ FrameAuditComplete k z.2 := by
  rcases h with hbad | hc
  · exact Or.inl (auditedFrameImpl_bad_monotone k mclose op s hbad z hz)
  cases op with
  | nfAt i =>
      exact Or.inr (auditedFrameImpl_nfAt_complete k mclose i s hc z hz)
  | spend m =>
      unfold auditedFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : s.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        refine Or.inr fun j a h' => ?_
        have haud : auditAfter k (.spend m) s.base s.base s.audit = s.audit := by
          simp [auditAfter, hcl]
        rw [haud]
        exact hc j a h'
      · rw [if_neg hcl] at hp
        have hopen : s.base.closed = false := by simpa using hcl
        obtain ⟨q, hq, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact Or.inr (emitSignal_audit_complete k m (.spend m) s hc
          (Or.inl rfl) hopen q hq)
  | close =>
      unfold auditedFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : s.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        refine Or.inr fun j a h' => ?_
        have haud : auditAfter k .close s.base s.base s.audit = s.audit := by
          simp [auditAfter, hcl]
        rw [haud]
        exact hc j a h'
      · rw [if_neg hcl] at hp
        have hopen : s.base.closed = false := by simpa using hcl
        obtain ⟨q, hq, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact Or.inr (emitSignal_audit_complete k mclose .close s hc
          (Or.inr rfl) hopen q hq)
  | roA kq i =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      by_cases hk : kq = k
      · subst hk
        exact Or.inl (auditAfter_direct_secret_bad kq i s.base p.2 s.audit)
      · obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        refine Or.inr fun j a h' => ?_
        have hpair : (k, j) ≠ (kq, i) := fun hkj =>
          hk ((congrArg Prod.fst hkj).symm)
        have hold : s.base.roA (k, j) = some a := by
          rw [← lazyRO_support_eq_of_ne s.base.roA (kq, i) c hcm hpair]
          exact h'
        exact hc j a hold
  | roX m =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact Or.inr fun j a h' => hc j a h'
  | roNf aq =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact Or.inr fun j a h' => hc j a h'
  | roE kq e =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact Or.inr fun j a h' => hc j a h'
  | roId kq =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact Or.inr fun j a h' => hc j a h'

/-- Run-level preservation of the threadable completeness invariant: from an
audit-complete (or already bad) state, every supported outcome of a full
audited run is bad or audit-complete. -/
theorem auditedFrameImpl_run_badOrComplete (k : F) (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (s : AuditedFrameSt F M)
    (h : FrameLeakBad k s.audit ∨ FrameAuditComplete k s)
    (z : α × AuditedFrameSt F M)
    (hz : z ∈ support ((simulateQ (auditedFrameImpl k mclose) oa).run s)) :
    FrameLeakBad k z.2.audit ∨ FrameAuditComplete k z.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (auditedFrameImpl k mclose)
    (fun u => FrameLeakBad k u.audit ∨ FrameAuditComplete k u)
    (fun t u hu y hy => auditedFrameImpl_badOrComplete_step k mclose t u hu y hy)
    oa s h z hz

omit [DecidableEq F] [SampleableType F] [DecidableEq M] in
/-- The empty message-digest cache is (vacuously) nonzero-valued. -/
theorem roXCacheNonzero_init :
    RoXCacheNonzero ((FrameSt.init F M).roX) := by
  intro m x h
  simp [FrameSt.init] at h

/-- **The `H_x` nonzero invariant threads through every audited step.** The
spend/close coupling consumes `x ≠ 0` at `roX` cache hits (the `y`-uniformity
bijection divides by `x`), so the coupling induction must carry
`RoXCacheNonzero` explicitly; this is its per-step preservation. -/
theorem auditedFrameImpl_roXNonzero_step (k : F) (mclose : M)
    (op : FrameOp F M) (s : AuditedFrameSt F M)
    (hx : RoXCacheNonzero s.base.roX)
    (z : (frameSpec F M).Range op × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) op).run s)) :
    RoXCacheNonzero z.2.base.roX := by
  cases op with
  | spend m =>
      unfold auditedFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : s.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hx
      · rw [if_neg hcl] at hp
        obtain ⟨q, hq, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        unfold emitSignal at hq
        obtain ⟨xc, hxc, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
        obtain ⟨ac, hac, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
        obtain ⟨nc, hnc, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
        rw [support_pure, Set.mem_singleton_iff] at hq
        subst hq
        exact (lazyROX_support_nonzero hx m xc hxc).2
  | close =>
      unfold auditedFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      unfold frameImpl at hp
      simp only [StateT.run_mk] at hp
      by_cases hcl : s.base.closed
      · rw [if_pos hcl, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hx
      · rw [if_neg hcl] at hp
        obtain ⟨q, hq, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        unfold emitSignal at hq
        obtain ⟨xc, hxc, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
        obtain ⟨ac, hac, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
        obtain ⟨nc, hnc, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
        rw [support_pure, Set.mem_singleton_iff] at hq
        subst hq
        exact (lazyROX_support_nonzero hx mclose xc hxc).2
  | nfAt i =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨ac, hac, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain ⟨nc, hnc, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hx
  | roA kq i =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hx
  | roX m =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact (lazyROX_support_nonzero hx m c hcm).2
  | roNf aq =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hx
  | roE kq e =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hx
  | roId kq =>
      unfold auditedFrameImpl frameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hx

/-- Run-level preservation of the `H_x` nonzero invariant. -/
theorem auditedFrameImpl_run_roXNonzero (k : F) (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (s : AuditedFrameSt F M)
    (hx : RoXCacheNonzero s.base.roX)
    (z : α × AuditedFrameSt F M)
    (hz : z ∈ support ((simulateQ (auditedFrameImpl k mclose) oa).run s)) :
    RoXCacheNonzero z.2.base.roX :=
  OracleComp.simulateQ_run_preserves_inv_of_query (auditedFrameImpl k mclose)
    (fun u => RoXCacheNonzero u.base.roX)
    (fun t u hu y hy => auditedFrameImpl_roXNonzero_step k mclose t u hu y hy)
    oa s hx z hz

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.fst_map_auditedFrameRun
#print axioms Zkpc.Games.frameRealSlashGame_eq_auditedJoint
#print axioms Zkpc.Games.probOutput_bind_decide_le_split
#print axioms Zkpc.Games.probOutput_bind_decide_eq_probEvent
#print axioms Zkpc.Games.frame_real_le_ghost_plus_bad
#print axioms Zkpc.Games.auditedFrameImpl_support_audit
#print axioms Zkpc.Games.auditedFrameImpl_run_bad_monotone
#print axioms Zkpc.Games.auditedFrameImpl_badOrComplete_step
#print axioms Zkpc.Games.auditedFrameImpl_run_badOrComplete
#print axioms Zkpc.Games.roXCacheNonzero_init
#print axioms Zkpc.Games.auditedFrameImpl_roXNonzero_step
#print axioms Zkpc.Games.auditedFrameImpl_run_roXNonzero
