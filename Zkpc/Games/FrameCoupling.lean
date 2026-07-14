import Zkpc.Games.FrameDeferred
import Zkpc.Games.FrameIdeal

/-!
# General-state FRAME coupling bricks (Spec.md §7 T7)

`Zkpc/Games/FrameIdeal.lean` proves the per-operation real/ideal coupling
steps for the public oracles at *arbitrary* audited states, but the honest
signal channel (`spend` / legacy `close` / `nfAt`) was covered only at the
empty initial state (`initial_spend_step_evalDist_eq`). This file
generalizes the `nfAt` channel to arbitrary audit-complete states and
introduces the two cache invariants any completion of the T7 coupling
needs:

* `HiddenSlopeInj` — distinct honest indices never share a materialized
  hidden slope. Needed because the ideal per-index nullifier cache updates
  a *single* index while the real world updates the shared `H_nf` cache at
  the slope *value*: without injectivity one real update could change the
  secret-erased image at several indices at once. On the good event
  (`¬ FrameLeakBad`) injectivity is automatic — a repeated slope is
  exactly the `honestSlopes`-duplication branch of the bad event.
* `RoNfCovered` — every populated `H_nf` cache key is either a recorded
  adversary probe or a recorded honest slope. This makes "a freshly
  sampled honest slope collides with an existing `H_nf` entry" a
  *detected* bad event (through `FrameLeakBad`'s probe-hit or duplication
  branches) rather than silent drift.

The two `idealize_nfAt_step_*` theorems below discharge the MC20
close-reveal channel at materialized slopes: together with the public
steps of `FrameIdeal.lean`, every FRAME operation except a *fresh-slope*
signal emission (`spend`/`close`/`nfAt` at an unmaterialized index) now
commutes exactly with canonical secret erasure on good states. The
fresh-slope cases require carving out the sampled-slope collision mass
(a genuine bad event, not an exact commutation) and — for `spend` at an
index whose slope was pre-materialized by `nfAt` — the eager-read
obstruction documented in `ROADMAP.md` §1.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## The two coupling invariants -/

/-- Distinct honest indices never share a materialized hidden slope
(Spec.md §3: fresh `a = H_a(k, i)` per index). On the good event this is
automatic; it is stated as a standalone invariant because the coupling
lemmas consume it directly. -/
def HiddenSlopeInj (k : F) (s : AuditedFrameSt F M) : Prop :=
  ∀ i j a, s.base.roA (k, i) = some a → s.base.roA (k, j) = some a → i = j

/-- Every populated `H_nf` cache key is a recorded adversary slope probe
or a recorded honest slope: the ghost transcript sees the whole nullifier
cache domain, so a fresh honest slope landing on an existing entry is a
recorded (hence chargeable) event. -/
def RoNfCovered (s : AuditedFrameSt F M) : Prop :=
  ∀ aq v, s.base.roNf aq = some v →
    aq ∈ s.audit.slopeProbes ∨ aq ∈ s.audit.honestSlopes

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- The programmed initial FRAME state (only `H_id(k) = cm` cached) has
injective hidden slopes: there are none. -/
theorem hiddenSlopeInj_initial (k cm : F) :
    HiddenSlopeInj k
      (⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩ : AuditedFrameSt F M) := by
  intro i j a h
  simp [FrameSt.init] at h

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- The programmed initial FRAME state has an empty `H_nf` cache, so the
coverage invariant holds vacuously. -/
theorem roNfCovered_initial (k cm : F) :
    RoNfCovered
      (⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩ : AuditedFrameSt F M) := by
  intro aq v h
  simp [FrameSt.init] at h

/-! ## `nfAt` at a materialized slope: exact commutation -/

/-- **MC20 reveal, fully cached case.** If index `i`'s hidden slope and its
nullifier are both already materialized, the `nfAt i` step is
deterministic on both sides and commutes exactly with canonical secret
erasure: the real composition `H_nf(H_a(k, i))` is precisely the ideal
per-index cache entry. -/
theorem idealize_nfAt_step_cached (k : F) (mclose : M) (i : ℕ) {a nf : F}
    (s : AuditedFrameSt F M) (ha : s.base.roA (k, i) = some a)
    (hnf : s.base.roNf a = some nf) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.nfAt i)).run s =
      ((idealFrameImpl mclose) (.nfAt i)).run (idealizeFrame k s) := by
  have hid : (idealizeFrame k s).honestNf i = some nf := by
    simp [idealizeFrame, ha, hnf]
  unfold auditedFrameImpl idealFrameImpl frameImpl
  simp only [StateT.run_mk]
  rw [lazyRO_eq_of_some ha, pure_bind, lazyRO_eq_of_some hnf, pure_bind,
    lazyRO_eq_of_some hid, pure_bind, pure_bind, map_pure]
  simp [auditAfter, ha]

/-- **MC20 reveal, fresh-nullifier case.** If index `i`'s hidden slope is
materialized but its nullifier is not, both worlds draw one fresh uniform
value; coupling the draws makes the step commute exactly with secret
erasure. Audit completeness routes the real `H_nf` update inside the
masked honest-slope namespace, and hidden-slope injectivity confines the
ideal image change to the single index `i`. -/
theorem idealize_nfAt_step_freshNf (k : F) (mclose : M) (i : ℕ) {a : F}
    (s : AuditedFrameSt F M) (ha : s.base.roA (k, i) = some a)
    (hnf : s.base.roNf a = none) (hc : FrameAuditComplete k s)
    (hinj : HiddenSlopeInj k s) :
    Prod.map id (idealizeFrame k) <$>
        ((auditedFrameImpl k mclose) (.nfAt i)).run s =
      ((idealFrameImpl mclose) (.nfAt i)).run (idealizeFrame k s) := by
  have hid : (idealizeFrame k s).honestNf i = none := by
    simp [idealizeFrame, ha, hnf]
  have hmem : a ∈ s.audit.honestSlopes := hc i a ha
  unfold auditedFrameImpl idealFrameImpl frameImpl
  simp only [StateT.run_mk]
  rw [lazyRO_eq_of_some ha, pure_bind, lazyRO_eq_of_none hnf,
    lazyRO_eq_of_none hid]
  simp only [bind_assoc, pure_bind, map_bind, map_pure]
  refine bind_congr fun nf => ?_
  refine congrArg pure (Prod.ext rfl ?_)
  change idealizeFrame k _ = _
  apply IdealFrameSt.ext
  · rfl
  · rfl
  · funext q
    simp [idealizeFrame, auditAfter, ha]
  · rfl
  · -- public `H_nf` namespace: the update happens at the masked honest slope.
    funext q
    by_cases hq : q ∈ s.audit.honestSlopes
    · simp [idealizeFrame, auditAfter, ha, hq]
    · have hqa : q ≠ a := fun h => hq (h ▸ hmem)
      simp [idealizeFrame, auditAfter, ha, hq, Function.update_of_ne hqa]
  · funext q
    simp [idealizeFrame, auditAfter, ha]
  · funext q
    simp [idealizeFrame, auditAfter, ha]
  · -- per-index nullifier namespace: only index `i` changes.
    funext j
    change (idealizeFrame k _).honestNf j =
      Function.update (idealizeFrame k s).honestNf i (some nf) j
    by_cases hj : j = i
    · subst j
      simp [idealizeFrame, auditAfter, ha]
    · rw [Function.update_of_ne hj]
      cases hb : s.base.roA (k, j) with
      | none => simp [idealizeFrame, auditAfter, ha, hb]
      | some b =>
          have hba : b ≠ a := fun h => hj (hinj j i a (h ▸ hb) ha)
          simp [idealizeFrame, auditAfter, ha, hb, Function.update_of_ne hba]

/-! ## Good-outcome preservation of the invariants -/

/-- A direct `H_a` probe preserves hidden-slope injectivity on every
outcome that stays good: a probe at the hidden secret is immediately bad,
and any other probe leaves the hidden namespace untouched. -/
theorem hiddenSlopeInj_roA_step (k : F) (mclose : M) (kq : F) (n : ℕ)
    (s : AuditedFrameSt F M) (hinj : HiddenSlopeInj k s)
    (z : F × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) (.roA kq n)).run s))
    (hgood : ¬ FrameLeakBad k z.2.audit) :
    HiddenSlopeInj k z.2 := by
  by_cases hk : kq = k
  · -- probing the secret is the immediate bad event.
    exfalso
    refine hgood ?_
    unfold auditedFrameImpl at hz
    obtain ⟨p, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst z
    subst kq
    exact auditAfter_direct_secret_bad k n s.base p.2 s.audit
  · -- probe away from the secret: hidden entries are unchanged.
    unfold auditedFrameImpl frameImpl at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst z
    simp only [StateT.run_mk] at hp
    obtain ⟨c, hcm, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst p
    intro i j a hi hj
    have hpair : ∀ m : ℕ, (k, m) ≠ (kq, n) := fun m h =>
      hk ((congrArg Prod.fst h).symm)
    refine hinj i j a ?_ ?_
    · rw [← lazyRO_support_eq_of_ne s.base.roA (kq, n) c hcm (hpair i)]
      exact hi
    · rw [← lazyRO_support_eq_of_ne s.base.roA (kq, n) c hcm (hpair j)]
      exact hj

/-- The `H_x`, `H_nf`, `H_e`, and `H_id` direct queries do not touch the
hidden `H_a` namespace, so they preserve hidden-slope injectivity
unconditionally. Stated once over the four operations. -/
theorem hiddenSlopeInj_public_step (k : F) (mclose : M) (op : FrameOp F M)
    (hop : (match op with
      | .roX _ | .roNf _ | .roE _ _ | .roId _ => True
      | _ => False))
    (s : AuditedFrameSt F M) (hinj : HiddenSlopeInj k s)
    (z : (frameSpec F M).Range op × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) op).run s)) :
    HiddenSlopeInj k z.2 := by
  unfold auditedFrameImpl frameImpl at hz
  obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst z
  cases op with
  | roX m =>
      simp only [StateT.run_mk] at hp
      obtain ⟨c, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst p
      exact hinj
  | roNf aq =>
      simp only [StateT.run_mk] at hp
      obtain ⟨c, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst p
      exact hinj
  | roE kq e =>
      simp only [StateT.run_mk] at hp
      obtain ⟨c, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst p
      exact hinj
  | roId kq =>
      simp only [StateT.run_mk] at hp
      obtain ⟨c, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst p
      exact hinj
  | spend m => exact absurd hop (by simp)
  | close => exact absurd hop (by simp)
  | nfAt i => exact absurd hop (by simp)
  | roA kq n => exact absurd hop (by simp)

/-- The MC20 reveal preserves hidden-slope injectivity on good outcomes:
a freshly materialized slope that repeated an existing hidden slope would
be an audited `honestSlopes` duplication, i.e. bad. -/
theorem hiddenSlopeInj_nfAt_step (k : F) (mclose : M) (n : ℕ)
    (s : AuditedFrameSt F M) (hc : FrameAuditComplete k s)
    (hinj : HiddenSlopeInj k s)
    (z : F × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) (.nfAt n)).run s))
    (hgood : ¬ FrameLeakBad k z.2.audit) :
    HiddenSlopeInj k z.2 := by
  unfold auditedFrameImpl frameImpl at hz
  obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst z
  simp only [StateT.run_mk] at hp
  obtain ⟨ac, hac, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
  obtain ⟨nc, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
  rw [support_pure, Set.mem_singleton_iff] at hp
  subst p
  cases hold : s.base.roA (k, n) with
  | some a₀ =>
      -- cache hit: the hidden namespace is unchanged.
      intro i j a hi hj
      have hac_eq : ac.2 = s.base.roA := by
        unfold lazyRO at hac
        rw [hold] at hac
        rw [support_pure, Set.mem_singleton_iff] at hac
        rw [hac]
      rw [hac_eq] at hi hj
      exact hinj i j a hi hj
  | none =>
      -- fresh slope at index `n`: a repeat would be a bad duplication.
      intro i j a hi hj
      have hnew := lazyRO_support_entry s.base.roA (k, n) ac hac
      by_cases hin : i = n
      · by_cases hjn : j = n
        · rw [hin, hjn]
        · -- `j ≠ n` yet shares the fresh slope: audited duplication.
          exfalso
          have hji : (k, j) ≠ (k, n) := fun h => hjn (congrArg Prod.snd h)
          have hjold : s.base.roA (k, j) = some a := by
            rw [← lazyRO_support_eq_of_ne s.base.roA (k, n) ac hac hji]
            exact hj
          rw [hin] at hi
          have hafresh : a = ac.1 :=
            Option.some.inj (hi.symm.trans hnew)
          refine hgood ?_
          change FrameLeakBad k
            (auditAfter k (.nfAt n) s.base
              { s.base with roA := ac.2, roNf := nc.2 } s.audit)
          have hi' : ac.2 (k, n) = some a := hi
          unfold auditAfter
          simp only [hold, hi']
          exact FrameLeakBad.honest_collision k a s.audit
            (Or.inr (hafresh ▸ (hafresh ▸ hc j a hjold)))
      · by_cases hjn : j = n
        · -- symmetric duplication case.
          exfalso
          have hij : (k, i) ≠ (k, n) := fun h => hin (congrArg Prod.snd h)
          have hiold : s.base.roA (k, i) = some a := by
            rw [← lazyRO_support_eq_of_ne s.base.roA (k, n) ac hac hij]
            exact hi
          rw [hjn] at hj
          have hafresh : a = ac.1 :=
            Option.some.inj (hj.symm.trans hnew)
          refine hgood ?_
          change FrameLeakBad k
            (auditAfter k (.nfAt n) s.base
              { s.base with roA := ac.2, roNf := nc.2 } s.audit)
          have hj' : ac.2 (k, n) = some a := hj
          unfold auditAfter
          simp only [hold, hj']
          exact FrameLeakBad.honest_collision k a s.audit
            (Or.inr (hafresh ▸ (hafresh ▸ hc i a hiold)))
        · -- both away from the queried index: old entries, old injectivity.
          have hij : (k, i) ≠ (k, n) := fun h => hin (congrArg Prod.snd h)
          have hjj : (k, j) ≠ (k, n) := fun h => hjn (congrArg Prod.snd h)
          refine hinj i j a ?_ ?_
          · rw [← lazyRO_support_eq_of_ne s.base.roA (k, n) ac hac hij]
            exact hi
          · rw [← lazyRO_support_eq_of_ne s.base.roA (k, n) ac hac hjj]
            exact hj


/-- A successful honest signal emission (`spend` or legacy `close`)
preserves hidden-slope injectivity on good outcomes: the freshly
materialized slope at the pre-call index repeating an existing hidden
slope is exactly an audited `honestSlopes` duplication. This is the
signal-channel companion of `hiddenSlopeInj_nfAt_step`, stated over the
shared emission kernel. -/
theorem hiddenSlopeInj_emitSignal (k : F) (m : M) (op : FrameOp F M)
    (s : AuditedFrameSt F M) (hc : FrameAuditComplete k s)
    (hinj : HiddenSlopeInj k s)
    (hop : op = .spend m ∨ op = .close) (hopen : s.base.closed = false)
    (z : Signal F × FrameSt F M) (hz : z ∈ support (emitSignal k m s.base))
    (hgood : ¬ FrameLeakBad k
      (auditAfter k op s.base z.2 s.audit)) :
    HiddenSlopeInj k ⟨z.2, auditAfter k op s.base z.2 s.audit⟩ := by
  unfold emitSignal at hz
  obtain ⟨xc, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  obtain ⟨ac, hac, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  obtain ⟨nc, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst z
  rw [auditAfter_signal_eq k m op s.base _ s.audit hop hopen] at hgood ⊢
  cases hold : s.base.roA (k, s.base.idx) with
  | some a₀ =>
      -- cache hit: the hidden namespace is unchanged.
      intro i j a hi hj
      have hac_eq : ac.2 = s.base.roA := by
        unfold lazyRO at hac
        rw [hold] at hac
        rw [support_pure, Set.mem_singleton_iff] at hac
        rw [hac]
      change ac.2 (k, i) = some a at hi
      change ac.2 (k, j) = some a at hj
      rw [hac_eq] at hi hj
      exact hinj i j a hi hj
  | none =>
      -- fresh slope at the pre-call index: a repeat is a bad duplication.
      simp only [hold] at hgood
      intro i j a hi hj
      change ac.2 (k, i) = some a at hi
      change ac.2 (k, j) = some a at hj
      have hnew := lazyRO_support_entry s.base.roA (k, s.base.idx) ac hac
      have hnewmatch : ac.2 (k, s.base.idx) = some ac.1 := hnew
      simp only [hnewmatch] at hgood
      by_cases hin : i = s.base.idx
      · by_cases hjn : j = s.base.idx
        · rw [hin, hjn]
        · exfalso
          have hji : (k, j) ≠ (k, s.base.idx) := fun h =>
            hjn (congrArg Prod.snd h)
          have hjold : s.base.roA (k, j) = some a := by
            rw [← lazyRO_support_eq_of_ne s.base.roA (k, s.base.idx) ac hac hji]
            exact hj
          rw [hin] at hi
          have hafresh : ac.1 = a := Option.some.inj (hnew.symm.trans hi)
          exact hgood (FrameLeakBad.honest_collision k ac.1 s.audit
            (Or.inr (hafresh ▸ hc j a hjold)))
      · by_cases hjn : j = s.base.idx
        · exfalso
          have hij : (k, i) ≠ (k, s.base.idx) := fun h =>
            hin (congrArg Prod.snd h)
          have hiold : s.base.roA (k, i) = some a := by
            rw [← lazyRO_support_eq_of_ne s.base.roA (k, s.base.idx) ac hac hij]
            exact hi
          rw [hjn] at hj
          have hafresh : ac.1 = a := Option.some.inj (hnew.symm.trans hj)
          exact hgood (FrameLeakBad.honest_collision k ac.1 s.audit
            (Or.inr (hafresh ▸ hc i a hiold)))
        · have hij : (k, i) ≠ (k, s.base.idx) := fun h =>
            hin (congrArg Prod.snd h)
          have hjj : (k, j) ≠ (k, s.base.idx) := fun h =>
            hjn (congrArg Prod.snd h)
          refine hinj i j a ?_ ?_
          · rw [← lazyRO_support_eq_of_ne s.base.roA (k, s.base.idx) ac hac hij]
            exact hi
          · rw [← lazyRO_support_eq_of_ne s.base.roA (k, s.base.idx) ac hac hjj]
            exact hj

end Zkpc.Games

-- F2 kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.hiddenSlopeInj_initial
#print axioms Zkpc.Games.roNfCovered_initial
#print axioms Zkpc.Games.idealize_nfAt_step_cached
#print axioms Zkpc.Games.idealize_nfAt_step_freshNf
#print axioms Zkpc.Games.hiddenSlopeInj_roA_step
#print axioms Zkpc.Games.hiddenSlopeInj_public_step
#print axioms Zkpc.Games.hiddenSlopeInj_nfAt_step
#print axioms Zkpc.Games.hiddenSlopeInj_emitSignal
