import Zkpc.Games.FrameAudit

/-!
# Secret-independent ideal FRAME handler

The ideal handler has no member-secret parameter. Honest line values and
nullifiers live in per-index internal caches, while adversary-facing random
oracle queries use separate public caches. Before a real execution hits one
of the audited bad events, these namespaces can be coupled: honest real slopes
are fresh, distinct, and unqueried, so their line values/nullifiers may be
deferred to the ideal per-index samples.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-- State of the secret-independent handler. -/
structure IdealFrameSt (F M : Type) where
  idx : ℕ
  closed : Bool
  roA : F × ℕ → Option F
  roX : M → Option F
  roNf : F → Option F
  roE : F × ℕ → Option F
  roId : F → Option F
  /-- simulator-side opaque nullifiers, indexed by the honest counter -/
  honestNf : ℕ → Option F

/-- Empty ideal state. -/
def IdealFrameSt.init (F M : Type) : IdealFrameSt F M where
  idx := 0
  closed := false
  roA := fun _ => none
  roX := fun _ => none
  roNf := fun _ => none
  roE := fun _ => none
  roId := fun _ => none
  honestNf := fun _ => none

/-- Real/ideal cache relation on the good event. Public caches agree away
from the hidden secret and internally sampled honest slopes. The ideal
per-index nullifier cache agrees with the real composition
`H_nf(H_a(k,i))`. -/
def FrameCoupled (k : F) (real : AuditedFrameSt F M)
    (ideal : IdealFrameSt F M) : Prop :=
  real.base.idx = ideal.idx ∧
  real.base.closed = ideal.closed ∧
  real.base.roX = ideal.roX ∧
  (∀ kq i, kq ≠ k → real.base.roA (kq, i) = ideal.roA (kq, i)) ∧
  (∀ kq e, kq ≠ k → real.base.roE (kq, e) = ideal.roE (kq, e)) ∧
  (∀ kq, kq ≠ k → real.base.roId kq = ideal.roId kq) ∧
  (∀ aq, aq ∉ real.audit.honestSlopes →
    real.base.roNf aq = ideal.roNf aq) ∧
  (∀ i, (real.base.roA (k, i)).bind real.base.roNf = ideal.honestNf i)

/-- Canonical secret-erasing projection of an audited real state. Entries at
the hidden secret and internally sampled honest slopes are moved out of the
public oracle namespaces; per-index nullifiers retain the real composition. -/
def idealizeFrame (k : F) (real : AuditedFrameSt F M) : IdealFrameSt F M where
  idx := real.base.idx
  closed := real.base.closed
  roA := fun q => if q.1 = k then none else real.base.roA q
  roX := real.base.roX
  roNf := fun aq => if aq ∈ real.audit.honestSlopes then none else real.base.roNf aq
  roE := fun q => if q.1 = k then none else real.base.roE q
  roId := fun kq => if kq = k then none else real.base.roId kq
  honestNf := fun i => (real.base.roA (k, i)).bind real.base.roNf

/-- Every audited state is related to its canonical secret-erasing image. -/
theorem frameCoupled_idealize (k : F) (real : AuditedFrameSt F M) :
    FrameCoupled k real (idealizeFrame k real) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro kq i hk
    simp [idealizeFrame, hk]
  · intro kq e hk
    simp [idealizeFrame, hk]
  · intro kq hk
    simp [idealizeFrame, hk]
  · intro aq ha
    simp [idealizeFrame, ha]
  · intro i
    rfl

/-- Programming `H_id(k)=cm` in the real initial state is invisible to the
secret-independent ideal state away from the bad preimage query. -/
theorem frameCoupled_initial (k cm : F) :
    FrameCoupled k
      ⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩
      (IdealFrameSt.init F M) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro kq i _
    rfl
  · intro kq e _
    rfl
  · intro kq hk
    simp [IdealFrameSt.init, FrameSt.init, Function.update_of_ne hk]
  · intro aq _
    rfl
  · intro i
    rfl

/-- The canonical image of the real programmed initial state is literally the
secret-independent empty ideal state. -/
theorem idealizeFrame_initial (k cm : F) :
    idealizeFrame k
      ⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩ = IdealFrameSt.init F M := by
  ext <;> simp [idealizeFrame, IdealFrameSt.init, FrameSt.init, FrameAudit.init]

/-- Emit a secret-independent simulated signal at the next honest index. -/
def emitIdealSignal (m : M) (s : IdealFrameSt F M) :
    ProbComp (Signal F × IdealFrameSt F M) := do
  let (x, cX) ← lazyROX s.roX m
  let y ← ($ᵗ F)
  let (nf, cNf) ← lazyRO s.honestNf s.idx
  pure (⟨x, y, nf⟩,
    { s with idx := s.idx + 1, roX := cX, honestNf := cNf })

/-- Secret-independent oracle implementation. Direct public-oracle queries
retain ordinary shared-cache behavior; only honest-member internals use the
separate indexed simulator caches. -/
def idealFrameImpl (mclose : M) :
    QueryImpl.Stateful unifSpec (frameSpec F M) (IdealFrameSt F M)
  | .spend m => StateT.mk fun s =>
      if s.closed then pure (none, s)
      else do
        let (sig, s') ← emitIdealSignal m s
        pure (some sig, s')
  | .close => StateT.mk fun s =>
      if s.closed then pure (none, s)
      else do
        let (sig, s') ← emitIdealSignal mclose s
        pure (some sig, { s' with closed := true })
  | .nfAt i => StateT.mk fun s => do
      let (nf, cNf) ← lazyRO s.honestNf i
      pure (nf, { s with honestNf := cNf })
  | .roA kq i => StateT.mk fun s => do
      let (v, c) ← lazyRO s.roA (kq, i)
      pure (v, { s with roA := c })
  | .roX m => StateT.mk fun s => do
      let (v, c) ← lazyROX s.roX m
      pure (v, { s with roX := c })
  | .roNf aq => StateT.mk fun s => do
      let (v, c) ← lazyRO s.roNf aq
      pure (v, { s with roNf := c })
  | .roE kq e => StateT.mk fun s => do
      let (v, c) ← lazyRO s.roE (kq, e)
      pure (v, { s with roE := c })
  | .roId kq => StateT.mk fun s => do
      let (v, c) ← lazyRO s.roId kq
      pure (v, { s with roId := c })

/-- Secret-independent evidence generator used by the final deferred-sampling
certificate. The public commitment is sampled first and is not tied to any
secret in this world; querying its real preimage is precisely an audited bad
event. -/
def idealFrameEvidence (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    ProbComp (Evidence F) := do
  let cm ← ($ᵗ F)
  (idealFrameImpl mclose).run (IdealFrameSt.init F M) (A cm)

/-! ## Exact good-step coupling for public oracle operations -/

/-- Public message-digest queries commute exactly with canonical
idealization. -/
theorem idealize_roX_step (k : F) (mclose m : M)
    (s : AuditedFrameSt F M) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roX m)).run s =
      ((idealFrameImpl mclose) (.roX m)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl
  simp only [StateT.run_mk]
  unfold lazyROX
  split <;> simp [idealizeFrame, auditAfter]

/-- A direct `H_a` query away from the hidden secret commutes exactly with
idealization. -/
theorem idealize_roA_step (k : F) (mclose : M) (kq : F) (i : ℕ)
    (s : AuditedFrameSt F M) (hk : kq ≠ k) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roA kq i)).run s =
      ((idealFrameImpl mclose) (.roA kq i)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl
  simp only [StateT.run_mk]
  unfold lazyRO
  simp only [idealizeFrame, hk, ↓reduceIte]
  split <;> simp [idealizeFrame, auditAfter, hk]

/-- A direct epoch-oracle query away from the hidden secret commutes exactly
with idealization. -/
theorem idealize_roE_step (k : F) (mclose : M) (kq : F) (e : ℕ)
    (s : AuditedFrameSt F M) (hk : kq ≠ k) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roE kq e)).run s =
      ((idealFrameImpl mclose) (.roE kq e)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl
  simp only [StateT.run_mk]
  unfold lazyRO
  simp only [idealizeFrame, hk, ↓reduceIte]
  split <;> simp [idealizeFrame, auditAfter, hk]

/-- A direct identity-oracle query away from the hidden preimage commutes
exactly with idealization. -/
theorem idealize_roId_step (k : F) (mclose : M) (kq : F)
    (s : AuditedFrameSt F M) (hk : kq ≠ k) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roId kq)).run s =
      ((idealFrameImpl mclose) (.roId kq)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl
  simp only [StateT.run_mk]
  unfold lazyRO
  simp only [idealizeFrame, hk, ↓reduceIte]
  split <;> simp [idealizeFrame, auditAfter, hk]

/-- A candidate-slope query that misses every internally sampled honest slope
commutes exactly with idealization. -/
theorem idealize_roNf_step (k : F) (mclose : M) (aq : F)
    (s : AuditedFrameSt F M) (ha : aq ∉ s.audit.honestSlopes) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roNf aq)).run s =
      ((idealFrameImpl mclose) (.roNf aq)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl
  simp only [StateT.run_mk]
  unfold lazyRO
  simp only [idealizeFrame, ha, ↓reduceIte]
  split <;> simp [idealizeFrame, auditAfter, ha]

end Zkpc.Games

#print axioms Zkpc.Games.frameCoupled_initial
#print axioms Zkpc.Games.frameCoupled_idealize
#print axioms Zkpc.Games.idealizeFrame_initial
#print axioms Zkpc.Games.idealize_roX_step
#print axioms Zkpc.Games.idealize_roA_step
#print axioms Zkpc.Games.idealize_roE_step
#print axioms Zkpc.Games.idealize_roId_step
#print axioms Zkpc.Games.idealize_roNf_step
