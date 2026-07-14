import Zkpc.Games.FrameGhost

/-!
# Coverage of the ghost public nullifier cache

Honest ghost slopes use the private per-index `honestNf` cache. Therefore
every populated key of the public ghost `roNf` cache must have arisen from an
adversarial `roNf` query and must appear in `slopeProbes`. This invariant is
the ghost-side source of `RoNfCovered` in the real/ghost coupling: a newly
sampled honest slope cannot silently land on an old public nullifier entry.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-- Every populated public nullifier-cache key was explicitly probed. -/
def GhostRoNfCovered (g : GhostFrameSt F M) : Prop :=
  ∀ aq v, g.ideal.roNf aq = some v → aq ∈ g.audit.slopeProbes

omit [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] in
/-- The empty ghost state has no public nullifier entries. -/
theorem ghostRoNfCovered_init : GhostRoNfCovered (GhostFrameSt.init F M) := by
  intro aq v h
  simp [GhostFrameSt.init, IdealFrameSt.init] at h

/-- Honest ideal-signal emission never touches the public nullifier cache. -/
theorem emitIdealSignal_roNf (m : M) (s : IdealFrameSt F M)
    (p : Signal F × IdealFrameSt F M) (hp : p ∈ support (emitIdealSignal m s)) :
    p.2.roNf = s.roNf := by
  unfold emitIdealSignal at hp
  obtain ⟨xc, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
  obtain ⟨y, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
  obtain ⟨nc, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
  rw [support_pure, Set.mem_singleton_iff] at hp
  subst hp
  rfl

omit [Field F] [DecidableEq F] in
/-- Touching a ghost slope records only `honestSlopes`; it never changes the
adversarial slope-probe list. -/
theorem ghostTouch_slopeProbes (gs : ℕ → Option F) (a : GhostAudit F)
    (i : ℕ) (q : (ℕ → Option F) × GhostAudit F)
    (hq : q ∈ support (ghostTouch gs a i)) :
    q.2.slopeProbes = a.slopeProbes := by
  rcases ghostTouch_support gs a i q hq with h | ⟨v, -, h⟩ <;> subst h <;> rfl

/-- Every supported ghost-handler step preserves public-nullifier coverage. -/
theorem ghostFrameImpl_roNfCovered (mclose : M) (op : FrameOp F M)
    (g : GhostFrameSt F M) (hg : GhostRoNfCovered g)
    (z : (frameSpec F M).Range op × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) op).run g)) :
    GhostRoNfCovered z.2 := by
  cases op with
  | spend m =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      by_cases hc : g.ideal.closed
      · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hg
      · rw [if_neg hc] at hz
        obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨q, hq, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        intro aq v hv
        rw [ghostTouch_slopeProbes g.ghostSlope g.audit g.ideal.idx q hq]
        apply hg aq v
        rw [← emitIdealSignal_roNf m g.ideal p hp]
        exact hv
  | close =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      by_cases hc : g.ideal.closed
      · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hg
      · rw [if_neg hc] at hz
        obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨q, hq, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        intro aq v hv
        rw [ghostTouch_slopeProbes g.ghostSlope g.audit g.ideal.idx q hq]
        apply hg aq v
        rw [← emitIdealSignal_roNf mclose g.ideal p hp]
        exact hv
  | nfAt i =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨q, hq, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      intro aq v hv
      rw [ghostTouch_slopeProbes g.ghostSlope g.audit i q hq]
      exact hg aq v hv
  | roA kq i =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hg
  | roX m =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hg
  | roNf aq =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      intro q v hq
      by_cases hqa : q = aq
      · subst q
        simp
      · have hold : g.ideal.roNf q = some v := by
          rw [← lazyRO_support_eq_of_ne g.ideal.roNf aq p hp hqa]
          exact hq
        exact List.mem_cons_of_mem aq (hg q v hold)
  | roE kq e =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hg
  | roId kq =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hg

/-- Coverage holds at every supported outcome of an adaptive ghost run. -/
theorem ghostFrameImpl_run_roNfCovered (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (g : GhostFrameSt F M)
    (hg : GhostRoNfCovered g) (z : α × GhostFrameSt F M)
    (hz : z ∈ support ((simulateQ (ghostFrameImpl mclose) oa).run g)) :
    GhostRoNfCovered z.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (ghostFrameImpl mclose)
    GhostRoNfCovered
    (fun t s hs y hy => ghostFrameImpl_roNfCovered mclose t s hs y hy)
    oa g hg z hz

end Zkpc.Games

#print axioms Zkpc.Games.ghostRoNfCovered_init
#print axioms Zkpc.Games.emitIdealSignal_roNf
#print axioms Zkpc.Games.ghostTouch_slopeProbes
#print axioms Zkpc.Games.ghostFrameImpl_roNfCovered
#print axioms Zkpc.Games.ghostFrameImpl_run_roNfCovered
