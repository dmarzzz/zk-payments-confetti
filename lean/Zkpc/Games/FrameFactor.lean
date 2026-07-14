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

The two transfer inequalities are explicit interface hypotheses of the master
theorem.  They record the historical route-A decomposition:

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

The final proof keeps this factorization as reusable history but closes T7 by
route B: `FrameGoodSliceTapeInduction.lean` proves the good-slice interface,
while `FrameRealBadStep.lean` and `FrameDSCountInduction.lean` bound the real
bad mass directly, bypassing `FrameBadMassTransfer`.  `FrameComplete.lean`
assembles the resulting premise-free query-bounded theorem.
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

/-! ## The two route-A transfer interfaces

These are the two run-level coupling inequalities that the master theorem
consumes. They remain named `Prop`s so the factorization can be reused.  The
completed route-B proof establishes the good-slice interface and bypasses the
second interface with a direct real-bad bound. -/

/-- **Good-slice transfer interface.** The k-averaged probability that
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

/-- **Historical route-A bad-mass transfer interface.** The k-averaged probability that the
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
the two transfer interfaces.  The final route-B theorem uses the proved
`FrameGoodSliceTransfer` together with a direct real-bad bound, so no
unresolved interface remains in the public T7 endpoint. -/
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

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- **Bad-event bridge across the two audit types.** The real leakage event and
the ghost leakage event coincide whenever the audits agree on the membership of
the merged direct-probe list and on the slope-probe and honest-slope lists —
exactly the audit-data correspondence the off-bad coupling maintains (the real
audit interleaves the three secret channels into one list, the ghost audit
keeps them per channel, so only membership of the merge is invariant). -/
theorem frameLeakBad_iff_ghostLeakBad_of_corr (k : F) (fa : FrameAudit F)
    (ga : GhostAudit F)
    (hsec : ∀ x : F, x ∈ fa.secretProbes ↔ x ∈ ga.secretProbes)
    (hslp : fa.slopeProbes = ga.slopeProbes)
    (hhon : fa.honestSlopes = ga.honestSlopes) :
    FrameLeakBad k fa ↔ GhostLeakBad k ga := by
  unfold FrameLeakBad GhostLeakBad
  rw [hslp, hhon, hsec k]

/-! ## The deferred-secret crux instances

The two hardest steps of the good-slice coupling, closed in atomic form at the
initial state. Both consume the secret draw as a *one-time pad*: for a fixed
hidden slope `a`, the map `k ↦ k + a·x` is a bijection of the uniform secret,
so deferring the secret makes the emitted line value an independent fresh
uniform — jointly with the recorded honest slope, which is exactly what the
audit ornament coupling needs (pointwise in `k` the pair `(y, a)` is
constrained by `y = k + a·x`; averaged over `k` it is uniform on `F²`). -/

section DeferredSecretCrux

variable [Finite F]

omit [DecidableEq F] in
/-- **The secret-consumption pad.** A uniform draw used exactly once, in an
additively shifted position, is itself fresh uniform: `k + c` for uniform `k`
is uniform, for any fixed offset `c`. This is the atomic "spend the deferred
secret at its unique consumption point and re-emit a fresh draw" step of the
k-averaged spend coupling. -/
theorem evalDist_uniform_add_pad {γ : Type} (c : F) (cont : F → ProbComp γ) :
    𝒟[($ᵗ F) >>= fun k => cont (k + c)] = 𝒟[($ᵗ F) >>= fun y => cont y] :=
  evalDist_bind_bijective_add_right_uniform F (fun k : F => k)
    Function.bijective_id c cont

/-- **Deferred-secret crux, fresh-slope form.** From the initial state, the
audited real `spend` — with the honest secret drawn (anywhere, hence averaged)
— produces the *joint* distribution of the answer and the recorded honest
slope of the ghost `spend`: the real slope `a` and line value `y = k + a·x`
are decorrelated by the secret pad, matching the ghost's independent fresh
`y` and ghost slope `v`. This is the atomic form of the audit-ornament
coupling at honest signal emissions, strengthening the answer-only
`initial_spend_step_evalDist_eq` by the audit component. -/
theorem initial_spend_deferredSecret_ghost_eq (mclose m : M) :
    𝒟[do
      let k ← ($ᵗ F)
      let z ← ((auditedFrameImpl k mclose) (.spend m)).run (AuditedFrameSt.init F M)
      pure (z.1, z.2.audit.honestSlopes)] =
    𝒟[do
      let w ← ((ghostFrameImpl mclose) (.spend m)).run (GhostFrameSt.init F M)
      pure (w.1, w.2.audit.honestSlopes)] := by
  have hreal : ∀ k : F,
      ((do
        let z ← ((auditedFrameImpl k mclose) (.spend m)).run (AuditedFrameSt.init F M)
        pure (z.1, z.2.audit.honestSlopes)) : ProbComp (Option (Signal F) × List F))
      = (do
        let raw ← ($ᵗ F)
        let a ← ($ᵗ F)
        let nf ← ($ᵗ F)
        pure ((some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
          Option (Signal F)), [a])) := by
    intro k
    unfold auditedFrameImpl frameImpl AuditedFrameSt.init FrameSt.init
      FrameAudit.init emitSignal lazyRO lazyROX
    simp [StateT.run_mk, auditAfter, Function.update_self]
  have hghost :
      ((do
        let w ← ((ghostFrameImpl mclose) (.spend m)).run (GhostFrameSt.init F M)
        pure (w.1, w.2.audit.honestSlopes)) : ProbComp (Option (Signal F) × List F))
      = (do
        let raw ← ($ᵗ F)
        let y ← ($ᵗ F)
        let nf ← ($ᵗ F)
        let v ← ($ᵗ F)
        pure ((some ⟨nonzeroDigest raw, y, nf⟩ : Option (Signal F)), [v])) := by
    unfold ghostFrameImpl emitIdealSignal ghostTouch GhostFrameSt.init
      IdealFrameSt.init GhostAudit.init lazyRO lazyROX
    simp [StateT.run_mk]
  calc 𝒟[do
        let k ← ($ᵗ F)
        let z ← ((auditedFrameImpl k mclose) (.spend m)).run (AuditedFrameSt.init F M)
        pure (z.1, z.2.audit.honestSlopes)]
      = 𝒟[($ᵗ F) >>= fun k => ($ᵗ F) >>= fun raw => ($ᵗ F) >>= fun a =>
          ($ᵗ F) >>= fun nf =>
          (pure ((some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
            Option (Signal F)), [a]) : ProbComp (Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun k => by rw [hreal k]
    _ = 𝒟[($ᵗ F) >>= fun raw => ($ᵗ F) >>= fun k => ($ᵗ F) >>= fun a =>
          ($ᵗ F) >>= fun nf =>
          (pure ((some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
            Option (Signal F)), [a]) : ProbComp (Option (Signal F) × List F))] :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[($ᵗ F) >>= fun raw => ($ᵗ F) >>= fun a => ($ᵗ F) >>= fun k =>
          ($ᵗ F) >>= fun nf =>
          (pure ((some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
            Option (Signal F)), [a]) : ProbComp (Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun raw =>
          OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[($ᵗ F) >>= fun raw => ($ᵗ F) >>= fun a => ($ᵗ F) >>= fun nf =>
          ($ᵗ F) >>= fun k =>
          (pure ((some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
            Option (Signal F)), [a]) : ProbComp (Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun raw =>
          evalDist_bind_congr' ($ᵗ F) fun a =>
            OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[($ᵗ F) >>= fun raw => ($ᵗ F) >>= fun a => ($ᵗ F) >>= fun nf =>
          ($ᵗ F) >>= fun y =>
          (pure ((some ⟨nonzeroDigest raw, y, nf⟩ :
            Option (Signal F)), [a]) : ProbComp (Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun raw =>
          evalDist_bind_congr' ($ᵗ F) fun a =>
            evalDist_bind_congr' ($ᵗ F) fun nf => by
              simp only [rlnY]
              exact evalDist_uniform_add_pad (a * nonzeroDigest raw)
                (fun y => pure ((some ⟨nonzeroDigest raw, y, nf⟩ :
                  Option (Signal F)), [a]))
    _ = 𝒟[($ᵗ F) >>= fun raw => ($ᵗ F) >>= fun nf => ($ᵗ F) >>= fun a =>
          ($ᵗ F) >>= fun y =>
          (pure ((some ⟨nonzeroDigest raw, y, nf⟩ :
            Option (Signal F)), [a]) : ProbComp (Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun raw =>
          OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[($ᵗ F) >>= fun raw => ($ᵗ F) >>= fun nf => ($ᵗ F) >>= fun y =>
          ($ᵗ F) >>= fun a =>
          (pure ((some ⟨nonzeroDigest raw, y, nf⟩ :
            Option (Signal F)), [a]) : ProbComp (Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun raw =>
          evalDist_bind_congr' ($ᵗ F) fun nf =>
            OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[($ᵗ F) >>= fun raw => ($ᵗ F) >>= fun y => ($ᵗ F) >>= fun nf =>
          ($ᵗ F) >>= fun v =>
          (pure ((some ⟨nonzeroDigest raw, y, nf⟩ :
            Option (Signal F)), [v]) : ProbComp (Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun raw =>
          OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[do
          let w ← ((ghostFrameImpl mclose) (.spend m)).run (GhostFrameSt.init F M)
          pure (w.1, w.2.audit.honestSlopes)] := by rw [hghost]

/-- **Deferred-secret crux, pinned-slope form (the slope-draw deferral).** An
`nfAt 0` reveal followed by the `spend` that consumes the pinned slope: at a
fixed secret the spend's line value is *determined* by the earlier `nfAt`
sampling (the eager-read obstruction), but the joint distribution of both
answers and the recorded honest slope still equals the ghost's, because the
slope draw commutes distributionally from its `nfAt` sampling point to the
spend that consumes it, where the secret pad decorrelates it. This is the
atomic closed form of the deepest step of the good-slice coupling. -/
theorem initial_nfAt_spend_deferredSecret_ghost_eq (mclose m : M) :
    𝒟[do
      let k ← ($ᵗ F)
      let z₁ ← ((auditedFrameImpl k mclose) (.nfAt 0)).run (AuditedFrameSt.init F M)
      let z₂ ← ((auditedFrameImpl k mclose) (.spend m)).run z₁.2
      pure (z₁.1, z₂.1, z₂.2.audit.honestSlopes)] =
    𝒟[do
      let w₁ ← ((ghostFrameImpl mclose) (.nfAt 0)).run (GhostFrameSt.init F M)
      let w₂ ← ((ghostFrameImpl mclose) (.spend m)).run w₁.2
      pure (w₁.1, w₂.1, w₂.2.audit.honestSlopes)] := by
  have hreal : ∀ k : F,
      ((do
        let z₁ ← ((auditedFrameImpl k mclose) (.nfAt 0)).run (AuditedFrameSt.init F M)
        let z₂ ← ((auditedFrameImpl k mclose) (.spend m)).run z₁.2
        pure (z₁.1, z₂.1, z₂.2.audit.honestSlopes)) :
          ProbComp (F × Option (Signal F) × List F))
      = (do
        let a ← ($ᵗ F)
        let nf ← ($ᵗ F)
        let raw ← ($ᵗ F)
        pure ((nf : F), (some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
          Option (Signal F)), [a])) := by
    intro k
    have hstep1 : ((auditedFrameImpl k mclose) (.nfAt 0)).run (AuditedFrameSt.init F M)
        = (do
          let a ← ($ᵗ F)
          let nf ← ($ᵗ F)
          pure ((nf : F),
            (⟨{ FrameSt.init F M with
                roA := Function.update (FrameSt.init F M).roA (k, 0) (some a),
                roNf := Function.update (FrameSt.init F M).roNf a (some nf) },
              { FrameAudit.init with honestSlopes := [a] }⟩ : AuditedFrameSt F M))) := by
      unfold auditedFrameImpl frameImpl AuditedFrameSt.init lazyRO
      simp [StateT.run_mk, auditAfter, FrameSt.init, FrameAudit.init,
        Function.update_self]
    rw [hstep1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun a => ?_
    refine bind_congr fun nf => ?_
    unfold auditedFrameImpl frameImpl emitSignal lazyRO lazyROX
    simp [StateT.run_mk, auditAfter, FrameSt.init, FrameAudit.init,
      Function.update_self]
  have hghost :
      ((do
        let w₁ ← ((ghostFrameImpl mclose) (.nfAt 0)).run (GhostFrameSt.init F M)
        let w₂ ← ((ghostFrameImpl mclose) (.spend m)).run w₁.2
        pure (w₁.1, w₂.1, w₂.2.audit.honestSlopes)) :
          ProbComp (F × Option (Signal F) × List F))
      = (do
        let nf ← ($ᵗ F)
        let v ← ($ᵗ F)
        let raw ← ($ᵗ F)
        let y ← ($ᵗ F)
        pure ((nf : F), (some ⟨nonzeroDigest raw, y, nf⟩ : Option (Signal F)), [v])) := by
    have hstep1 : ((ghostFrameImpl mclose) (.nfAt 0)).run (GhostFrameSt.init F M)
        = (do
          let nf ← ($ᵗ F)
          let v ← ($ᵗ F)
          pure ((nf : F),
            (⟨{ IdealFrameSt.init F M with
                honestNf := Function.update (IdealFrameSt.init F M).honestNf 0 (some nf) },
              Function.update (fun _ => none) 0 (some v),
              { GhostAudit.init with honestSlopes := [v] }⟩ : GhostFrameSt F M))) := by
      unfold ghostFrameImpl ghostTouch GhostFrameSt.init lazyRO
      simp [StateT.run_mk, IdealFrameSt.init, GhostAudit.init]
    rw [hstep1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun nf => ?_
    refine bind_congr fun v => ?_
    unfold ghostFrameImpl emitIdealSignal ghostTouch lazyRO lazyROX
    simp [StateT.run_mk, IdealFrameSt.init, GhostAudit.init, Function.update_self]
  calc 𝒟[do
        let k ← ($ᵗ F)
        let z₁ ← ((auditedFrameImpl k mclose) (.nfAt 0)).run (AuditedFrameSt.init F M)
        let z₂ ← ((auditedFrameImpl k mclose) (.spend m)).run z₁.2
        pure (z₁.1, z₂.1, z₂.2.audit.honestSlopes)]
      = 𝒟[($ᵗ F) >>= fun k => ($ᵗ F) >>= fun a => ($ᵗ F) >>= fun nf =>
          ($ᵗ F) >>= fun raw =>
          (pure ((nf : F), (some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
            Option (Signal F)), [a]) : ProbComp (F × Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun k => by rw [hreal k]
    _ = 𝒟[($ᵗ F) >>= fun a => ($ᵗ F) >>= fun k => ($ᵗ F) >>= fun nf =>
          ($ᵗ F) >>= fun raw =>
          (pure ((nf : F), (some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
            Option (Signal F)), [a]) : ProbComp (F × Option (Signal F) × List F))] :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[($ᵗ F) >>= fun a => ($ᵗ F) >>= fun nf => ($ᵗ F) >>= fun k =>
          ($ᵗ F) >>= fun raw =>
          (pure ((nf : F), (some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
            Option (Signal F)), [a]) : ProbComp (F × Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun a =>
          OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[($ᵗ F) >>= fun a => ($ᵗ F) >>= fun nf => ($ᵗ F) >>= fun raw =>
          ($ᵗ F) >>= fun k =>
          (pure ((nf : F), (some ⟨nonzeroDigest raw, rlnY k a (nonzeroDigest raw), nf⟩ :
            Option (Signal F)), [a]) : ProbComp (F × Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun a =>
          evalDist_bind_congr' ($ᵗ F) fun nf =>
            OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[($ᵗ F) >>= fun a => ($ᵗ F) >>= fun nf => ($ᵗ F) >>= fun raw =>
          ($ᵗ F) >>= fun y =>
          (pure ((nf : F), (some ⟨nonzeroDigest raw, y, nf⟩ :
            Option (Signal F)), [a]) : ProbComp (F × Option (Signal F) × List F))] :=
        evalDist_bind_congr' ($ᵗ F) fun a =>
          evalDist_bind_congr' ($ᵗ F) fun nf =>
            evalDist_bind_congr' ($ᵗ F) fun raw => by
              simp only [rlnY]
              exact evalDist_uniform_add_pad (a * nonzeroDigest raw)
                (fun y => pure ((nf : F), (some ⟨nonzeroDigest raw, y, nf⟩ :
                  Option (Signal F)), [a]))
    _ = 𝒟[($ᵗ F) >>= fun nf => ($ᵗ F) >>= fun a => ($ᵗ F) >>= fun raw =>
          ($ᵗ F) >>= fun y =>
          (pure ((nf : F), (some ⟨nonzeroDigest raw, y, nf⟩ :
            Option (Signal F)), [a]) : ProbComp (F × Option (Signal F) × List F))] :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[do
          let w₁ ← ((ghostFrameImpl mclose) (.nfAt 0)).run (GhostFrameSt.init F M)
          let w₂ ← ((ghostFrameImpl mclose) (.spend m)).run w₁.2
          pure (w₁.1, w₂.1, w₂.2.audit.honestSlopes)] := by rw [hghost]

end DeferredSecretCrux

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
#print axioms Zkpc.Games.frameLeakBad_iff_ghostLeakBad_of_corr
#print axioms Zkpc.Games.evalDist_uniform_add_pad
#print axioms Zkpc.Games.initial_spend_deferredSecret_ghost_eq
#print axioms Zkpc.Games.initial_nfAt_spend_deferredSecret_ghost_eq
