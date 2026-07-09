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
@[ext] structure IdealFrameSt (F M : Type) where
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

/-- The canonical image of the programmed real initial state is literally the
empty secret-independent ideal state. -/
theorem idealizeFrame_initial (k cm : F) :
    idealizeFrame k
      ⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩ = IdealFrameSt.init F M := by
  apply IdealFrameSt.ext
  · rfl
  · rfl
  · funext q
    simp [idealizeFrame, IdealFrameSt.init, FrameSt.init, FrameAudit.init]
  · funext m
    rfl
  · funext aq
    simp [idealizeFrame, IdealFrameSt.init, FrameSt.init, FrameAudit.init]
  · funext q
    simp [idealizeFrame, IdealFrameSt.init, FrameSt.init, FrameAudit.init]
  · funext kq
    by_cases hk : kq = k
    · simp [idealizeFrame, IdealFrameSt.init, FrameSt.init, FrameAudit.init, hk]
    · simp [idealizeFrame, IdealFrameSt.init, FrameSt.init, FrameAudit.init, hk,
        Function.update_of_ne hk]
  · funext i
    rfl

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

/-! ## Exact coupling for secret-independent public operations -/

/-- Public message-digest queries commute exactly with canonical
idealization, including both cache-hit and cache-miss branches. -/
theorem idealize_roX_step (k : F) (mclose m : M)
    (s : AuditedFrameSt F M) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roX m)).run s =
      ((idealFrameImpl mclose) (.roX m)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl frameImpl
  simp only [StateT.run_mk]
  unfold lazyROX
  split <;> rename_i h <;> simp [h, idealizeFrame, auditAfter]

/-- Updating a public pair-keyed cache away from the hidden first component
commutes with deleting the hidden component. -/
theorem maskFirst_update_of_ne (f : F × ℕ → Option F)
    (k kq value : F) (n : ℕ) (hk : kq ≠ k) :
    (fun q => if q.1 = k then none
      else Function.update f (kq, n) (some value) q) =
      Function.update (fun q => if q.1 = k then none else f q)
        (kq, n) (some value) := by
  funext q
  by_cases hq : q = (kq, n)
  · subst q
    simp [hk]
  · rw [Function.update_of_ne hq, Function.update_of_ne hq]

/-- An update away from `k` does not affect any cache entry whose first
component is `k`. -/
theorem update_pair_at_hidden_of_ne (f : F × ℕ → Option F)
    (k kq value : F) (n i : ℕ) (hk : kq ≠ k) :
    Function.update f (kq, n) (some value) (k, i) = f (k, i) := by
  rw [Function.update_of_ne]
  intro h
  exact hk (congrArg Prod.fst h).symm

/-- Updating a scalar public cache away from the hidden key commutes with
deleting the hidden entry. -/
theorem maskKey_update_of_ne (f : F → Option F)
    (k kq value : F) (hk : kq ≠ k) :
    (fun q => if q = k then none else Function.update f kq (some value) q) =
      Function.update (fun q => if q = k then none else f q) kq (some value) := by
  funext q
  by_cases hq : q = kq
  · subst q
    simp [hk]
  · rw [Function.update_of_ne hq, Function.update_of_ne hq]

/-- A direct `H_a` query away from the hidden secret commutes exactly with
canonical idealization. -/
theorem idealize_roA_step (k : F) (mclose : M) (kq : F) (i : ℕ)
    (s : AuditedFrameSt F M) (hk : kq ≠ k) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roA kq i)).run s =
      ((idealFrameImpl mclose) (.roA kq i)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl frameImpl
  simp only [StateT.run_mk]
  unfold lazyRO
  split <;> rename_i h
  · simp [h, idealizeFrame, auditAfter, hk]
  · simp [h, idealizeFrame, auditAfter, hk, maskFirst_update_of_ne,
      update_pair_at_hidden_of_ne]

/-- A direct epoch-oracle query away from the hidden secret commutes exactly
with canonical idealization. -/
theorem idealize_roE_step (k : F) (mclose : M) (kq : F) (e : ℕ)
    (s : AuditedFrameSt F M) (hk : kq ≠ k) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roE kq e)).run s =
      ((idealFrameImpl mclose) (.roE kq e)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl frameImpl
  simp only [StateT.run_mk]
  unfold lazyRO
  split <;> rename_i h
  · simp [h, idealizeFrame, auditAfter, hk]
  · simp [h, idealizeFrame, auditAfter, hk, maskFirst_update_of_ne]

/-- A direct identity-oracle query away from the hidden secret commutes
exactly with canonical idealization. -/
theorem idealize_roId_step (k : F) (mclose : M) (kq : F)
    (s : AuditedFrameSt F M) (hk : kq ≠ k) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roId kq)).run s =
      ((idealFrameImpl mclose) (.roId kq)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl frameImpl
  simp only [StateT.run_mk]
  unfold lazyRO
  split <;> rename_i h
  · simp [h, idealizeFrame, auditAfter, hk]
  · simp [h, idealizeFrame, auditAfter, hk, maskKey_update_of_ne]

/-- Every internally materialized honest slope is represented in the audit.
This invariant makes the public nullifier namespace disjoint from the
secret-erased per-index namespace on a good state. -/
def FrameAuditComplete (k : F) (s : AuditedFrameSt F M) : Prop :=
  ∀ i a, s.base.roA (k, i) = some a → a ∈ s.audit.honestSlopes

/-- The programmed empty initial state has no materialized honest slopes. -/
theorem frameAuditComplete_initial (k cm : F) :
    FrameAuditComplete k
      ⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩ := by
  intro i a h
  simp [FrameSt.init] at h

/-- Updating the public nullifier cache at a non-honest slope commutes with
masking all audited honest slopes. -/
theorem maskSlopes_update_of_not_mem (f : F → Option F) (slopes : List F)
    (aq value : F) (ha : aq ∉ slopes) :
    (fun q => if q ∈ slopes then none else Function.update f aq (some value) q) =
      Function.update (fun q => if q ∈ slopes then none else f q) aq (some value) := by
  funext q
  by_cases hq : q = aq
  · subst q
    simp [ha]
  · rw [Function.update_of_ne hq, Function.update_of_ne hq]

/-- Updating a non-honest public slope cannot alter a composed honest
nullifier entry in an audit-complete state. -/
theorem update_roNf_at_honest_of_complete (k aq value : F)
    (s : AuditedFrameSt F M) (hc : FrameAuditComplete k s)
    (ha : aq ∉ s.audit.honestSlopes) (i : ℕ) :
    (s.base.roA (k, i)).bind (Function.update s.base.roNf aq (some value)) =
      (s.base.roA (k, i)).bind s.base.roNf := by
  cases h : s.base.roA (k, i) with
  | none => rfl
  | some a =>
      simp only [Option.bind_some]
      rw [Function.update_of_ne]
      intro heq
      subst a
      exact ha (hc i aq h)

/-- A public nullifier-oracle query that misses all audited honest slopes
commutes exactly with idealization on an audit-complete state. -/
theorem idealize_roNf_step (k : F) (mclose : M) (aq : F)
    (s : AuditedFrameSt F M) (hc : FrameAuditComplete k s)
    (ha : aq ∉ s.audit.honestSlopes) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.roNf aq)).run s =
      ((idealFrameImpl mclose) (.roNf aq)).run (idealizeFrame k s) := by
  unfold auditedFrameImpl idealFrameImpl frameImpl
  simp only [StateT.run_mk]
  unfold lazyRO
  split <;> rename_i h
  · simp [h, idealizeFrame, auditAfter, ha]
  · simp [h, idealizeFrame, auditAfter, ha, maskSlopes_update_of_not_mem,
      update_roNf_at_honest_of_complete, hc]

/-- The MC20 nullifier-reveal operation preserves audit completeness on every
supported outcome: a newly sampled slope is recorded, while cache hits were
already covered by the incoming invariant. -/
theorem auditedFrameImpl_nfAt_complete (k : F) (mclose : M) (i : ℕ)
    (s : AuditedFrameSt F M) (hc : FrameAuditComplete k s)
    (z : F × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) (.nfAt i)).run s)) :
    FrameAuditComplete k z.2 := by
  unfold auditedFrameImpl at hz
  obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst z
  unfold frameImpl at hp
  simp only [StateT.run_mk] at hp
  obtain ⟨ac, hac, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
  obtain ⟨nc, hnc, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
  rw [support_pure, Set.mem_singleton_iff] at hp
  subst p
  intro j a hentry
  by_cases hj : j = i
  · subst j
    change ac.2 (k, i) = some a at hentry
    have hqueried := lazyRO_support_entry s.base.roA (k, i) ac hac
    have ha : a = ac.1 := Option.some.inj (hentry.symm.trans hqueried)
    subst a
    change ac.1 ∈
      (auditAfter k (.nfAt i) s.base
        { s.base with roA := ac.2, roNf := nc.2 } s.audit).honestSlopes
    unfold auditAfter
    cases hold : s.base.roA (k, i) with
    | some old =>
        simp only [hold]
        have hvalue := lazyRO_support_value_of_entry s.base.roA (k, i) ac hac hold
        rw [hvalue]
        exact hc i old hold
    | none => simp [hold, lazyRO_support_entry s.base.roA (k, i) ac hac]
  · have hpair : (k, j) ≠ (k, i) := by
      intro h
      exact hj (congrArg Prod.snd h)
    change ac.2 (k, j) = some a at hentry
    have hold : s.base.roA (k, j) = some a := by
      rw [← hentry]
      exact (lazyRO_support_eq_of_ne s.base.roA (k, i) ac hac hpair).symm
    unfold auditAfter
    cases hi : s.base.roA (k, i) with
    | some old => simpa [hi] using hc j a hold
    | none =>
        have hnew := lazyRO_support_entry s.base.roA (k, i) ac hac
        simp [hi, hnew, hc j a hold]

/-- `spend` and legacy `close` share exactly the same slope-audit update on
an open state. -/
theorem auditAfter_signal_eq (k : F) (m : M) (op : FrameOp F M)
    (before after : FrameSt F M) (audit : FrameAudit F)
    (hop : op = .spend m ∨ op = .close) (hopen : before.closed = false) :
    auditAfter k op before after audit =
      match before.roA (k, before.idx) with
      | some _ => audit
      | none => match after.roA (k, before.idx) with
        | some slope => { audit with honestSlopes := slope :: audit.honestSlopes }
        | none => audit := by
  rcases hop with rfl | rfl <;> simp [auditAfter, hopen] <;> rfl

/-- A successful honest signal emission preserves audit completeness when
its freshly materialized slope is recorded by `auditAfter`. This common
kernel serves both `spend` and legacy `close`. -/
theorem emitSignal_audit_complete (k : F) (m : M) (op : FrameOp F M)
    (s : AuditedFrameSt F M) (hc : FrameAuditComplete k s)
    (hop : op = .spend m ∨ op = .close) (hopen : s.base.closed = false)
    (z : Signal F × FrameSt F M) (hz : z ∈ support (emitSignal k m s.base)) :
    FrameAuditComplete k
      ⟨z.2, auditAfter k op s.base z.2 s.audit⟩ := by
  unfold emitSignal at hz
  obtain ⟨xc, hxc, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  obtain ⟨ac, hac, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  obtain ⟨nc, hnc, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst z
  intro j a hentry
  by_cases hj : j = s.base.idx
  · subst j
    change ac.2 (k, s.base.idx) = some a at hentry
    have hqueried := lazyRO_support_entry s.base.roA (k, s.base.idx) ac hac
    have ha : a = ac.1 := Option.some.inj (hentry.symm.trans hqueried)
    subst a
    rw [auditAfter_signal_eq k m op s.base _ s.audit hop hopen]
    cases hold : s.base.roA (k, s.base.idx) with
    | some old =>
        simp only [hold]
        have hvalue := lazyRO_support_value_of_entry
          s.base.roA (k, s.base.idx) ac hac hold
        rw [hvalue]
        exact hc s.base.idx old hold
    | none => simp [hold, lazyRO_support_entry s.base.roA (k, s.base.idx) ac hac]
  · have hpair : (k, j) ≠ (k, s.base.idx) := by
      intro h
      exact hj (congrArg Prod.snd h)
    change ac.2 (k, j) = some a at hentry
    have hold : s.base.roA (k, j) = some a := by
      rw [← hentry]
      exact (lazyRO_support_eq_of_ne s.base.roA (k, s.base.idx) ac hac hpair).symm
    rw [auditAfter_signal_eq k m op s.base _ s.audit hop hopen]
    cases hi : s.base.roA (k, s.base.idx) with
    | some old => simpa [hi] using hc j a hold
    | none =>
        have hnew := lazyRO_support_entry s.base.roA (k, s.base.idx) ac hac
        simp [hi, hnew, hc j a hold]

end Zkpc.Games

#print axioms Zkpc.Games.frameCoupled_initial
#print axioms Zkpc.Games.frameCoupled_idealize
#print axioms Zkpc.Games.idealizeFrame_initial
#print axioms Zkpc.Games.idealize_roX_step
#print axioms Zkpc.Games.maskFirst_update_of_ne
#print axioms Zkpc.Games.update_pair_at_hidden_of_ne
#print axioms Zkpc.Games.maskKey_update_of_ne
#print axioms Zkpc.Games.idealize_roA_step
#print axioms Zkpc.Games.idealize_roE_step
#print axioms Zkpc.Games.idealize_roId_step
#print axioms Zkpc.Games.frameAuditComplete_initial
#print axioms Zkpc.Games.maskSlopes_update_of_not_mem
#print axioms Zkpc.Games.update_roNf_at_honest_of_complete
#print axioms Zkpc.Games.idealize_roNf_step
#print axioms Zkpc.Games.auditedFrameImpl_nfAt_complete
#print axioms Zkpc.Games.auditAfter_signal_eq
#print axioms Zkpc.Games.emitSignal_audit_complete
