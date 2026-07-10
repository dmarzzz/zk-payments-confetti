import Zkpc.Games.FrameCoupling
import Zkpc.Games.FrameGhostBounds

/-!
# Real/ghost FRAME coupling relation

The audited real handler and the secret-independent ghost handler record the
same semantic leakage transcript in different shapes: the real audit combines
all direct-secret probes in one list, while the ghost audit keeps the three
channels separate.  `RealGhostCoupled` is the run invariant needed by the
off-bad simulation.  It relates the canonical secret-erased state, every
materialized hidden slope, and membership in all three bad-event lists.

This file establishes the programmed initial relation and, crucially, proves
that the real and ghost bad predicates are equivalent under the relation.
Thus later stepwise coupling may reason about one monotone bad flag without a
second probability loss.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-- Coupling invariant between the secret-dependent audited real state and
the secret-independent ghost state.  List order is intentionally abstracted
to membership: the real audit interleaves three direct-secret channels whereas
the ghost audit stores them separately, and the leakage predicate only tests
membership. -/
structure RealGhostCoupled (k : F) (r : AuditedFrameSt F M)
    (g : GhostFrameSt F M) : Prop where
  ideal : idealizeFrame k r = g.ideal
  hiddenSlope : ∀ i, r.base.roA (k, i) = g.ghostSlope i
  secretProbes : ∀ q, q ∈ r.audit.secretProbes ↔ q ∈ g.audit.secretProbes
  slopeProbes : ∀ q, q ∈ r.audit.slopeProbes ↔ q ∈ g.audit.slopeProbes
  honestSlopes : ∀ q, q ∈ r.audit.honestSlopes ↔ q ∈ g.audit.honestSlopes
  honestNodup : r.audit.honestSlopes.Nodup ↔ g.audit.honestSlopes.Nodup

/-- Programming `H_id(k)=cm` on the real side is erased by canonical
idealization, so it couples to the empty ghost state. -/
theorem realGhostCoupled_initial (k cm : F) :
    RealGhostCoupled k
      (⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩ : AuditedFrameSt F M)
      (GhostFrameSt.init F M) := by
  constructor
  · exact idealizeFrame_initial k cm
  · intro i
    rfl
  · intro q
    simp [FrameAudit.init, GhostFrameSt.init, GhostAudit.init,
      GhostAudit.secretProbes]
  · intro q
    simp [FrameAudit.init, GhostFrameSt.init, GhostAudit.init]
  · intro q
    simp [FrameAudit.init, GhostFrameSt.init, GhostAudit.init]
  · simp [FrameAudit.init, GhostFrameSt.init, GhostAudit.init]

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- Under the coupling invariant, the real and deferred-secret ghost leakage
events are definitionally the same three semantic cases: direct secret hit,
slope-preimage hit, or honest-slope collision. -/
theorem frameLeakBad_iff_ghostLeakBad {k : F} {r : AuditedFrameSt F M}
    {g : GhostFrameSt F M} (h : RealGhostCoupled k r g) :
    FrameLeakBad k r.audit ↔ GhostLeakBad k g.audit := by
  unfold FrameLeakBad GhostLeakBad
  constructor
  · rintro (hk | ⟨s, hsP, hsH⟩ | hdup)
    · exact Or.inl ((h.secretProbes k).1 hk)
    · exact Or.inr (Or.inl ⟨s, (h.slopeProbes s).1 hsP,
        (h.honestSlopes s).1 hsH⟩)
    · exact Or.inr (Or.inr (fun hg => hdup (h.honestNodup.2 hg)))
  · rintro (hk | ⟨s, hsP, hsH⟩ | hdup)
    · exact Or.inl ((h.secretProbes k).2 hk)
    · exact Or.inr (Or.inl ⟨s, (h.slopeProbes s).2 hsP,
        (h.honestSlopes s).2 hsH⟩)
    · exact Or.inr (Or.inr (fun hr => hdup (h.honestNodup.1 hr)))

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- Goodness is likewise shared exactly; no union-bound or conditioning loss
is incurred when switching between the real and ghost transcript. -/
theorem not_frameLeakBad_iff_not_ghostLeakBad {k : F}
    {r : AuditedFrameSt F M} {g : GhostFrameSt F M}
    (h : RealGhostCoupled k r g) :
    (¬ FrameLeakBad k r.audit) ↔ (¬ GhostLeakBad k g.audit) :=
  not_congr (frameLeakBad_iff_ghostLeakBad h)

/-- The state component of the real/ghost invariant immediately supplies the
existing real/ideal cache relation, so all exact public-step lemmas from
`FrameIdeal` are reusable without reproving cache algebra. -/
theorem RealGhostCoupled.frameCoupled {k : F} {r : AuditedFrameSt F M}
    {g : GhostFrameSt F M} (h : RealGhostCoupled k r g) :
    FrameCoupled k r g.ideal := by
  rw [← h.ideal]
  exact frameCoupled_idealize k r

/-- Ghost-slope completeness transfers to the audited real state.  This is
the prerequisite consumed by the materialized-`nfAt` and fresh-nullifier
coupling lemmas. -/
omit [Field F] [SampleableType F] [DecidableEq M] in
theorem RealGhostCoupled.frameAuditComplete {k : F}
    {r : AuditedFrameSt F M} {g : GhostFrameSt F M}
    (h : RealGhostCoupled k r g) (hg : GhostSlopesComplete g) :
    FrameAuditComplete k r := by
  intro i a ha
  have hga : g.ghostSlope i = some a := by
    rw [← h.hiddenSlope i]
    exact ha
  exact (h.honestSlopes a).2 (hg i a hga)

end Zkpc.Games

#print axioms Zkpc.Games.realGhostCoupled_initial
#print axioms Zkpc.Games.frameLeakBad_iff_ghostLeakBad
#print axioms Zkpc.Games.not_frameLeakBad_iff_not_ghostLeakBad
#print axioms Zkpc.Games.RealGhostCoupled.frameCoupled
#print axioms Zkpc.Games.RealGhostCoupled.frameAuditComplete
