import Zkpc.Games.FrameTransfer
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.ProgramLogic.Relational.FromUnary

/-!
# The deferred-slope handler and the real-side bad-mass lane (Spec.md §7 T7)

Route B of the corrected T7 assembly (`Zkpc/Games/FrameTransfer.lean`) needs
the direct real-side bad-mass bound `FrameRealBadMassLe`. This file
implements the recorded two-stage architecture:

* **Stage 1 (this file, coupling half):** an exact identical-until-bad
  bisimulation between the audited real handler `auditedFrameImpl` and the
  *deferred-slope* handler `dsFrameImpl` below. The deferred handler answers
  all public random-oracle queries from its own public caches, draws each
  hidden honest slope lazily at its first honest touch (`dsTouch`, exactly
  when the real handler materializes `H_a(k, i)`), computes the honest line
  value as the same `y = k + a·x`, but sources honest nullifiers from a
  private per-index cache instead of the public `H_nf` cache. Every
  divergence between the two handlers *simultaneously* raises the same
  audited leakage event `FrameLeakBad` on both sides (the audit transcripts
  are equal along the coupling), so the run-level bad masses transfer.
  Crucially both handlers pin the hidden slope at first touch, so the
  eager-read obstruction that blocks a real/ghost pointwise-state coupling
  does not arise here.

* **Stage 2 (k-root counting):** with the honest nullifiers private and the
  hidden slopes read only through `y = k + a·x`, the deferred run's leakage
  mass k-averages to the first-order union bound `qb.total/|F|` (each
  leakage branch pins the uniform secret or one fresh slope to a single
  root per budget pair).

The generic absorbing-event relational rule
`relTriple_simulateQ_run_untilAbsorbing` proved here is the reusable core of
stage 1: a per-query coupling that either preserves a good relation with
equal outputs or lands both sides in absorbing bad sets extends to full
adaptive runs.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

namespace Zkpc.Games

/-! ## The generic until-absorbing relational rule -/

/-- **Relational `simulateQ` until an absorbing event.** If each coupled
oracle step from `Good`-related states either returns equal answers and
`Good`-related states, or lands both sides in their absorbing sets `B₁`/`B₂`
(each preserved by every subsequent step of its own handler), then complete
simulated runs are coupled so that they either finish `Good`-related with
equal outputs or finish with both sides absorbed. This is the identical-
until-bad rule in the exact shape of the stage-1 real/deferred-slope
coupling (Spec.md §7 T7): the leakage event fires simultaneously on both
sides and is monotone, so post-divergence behavior needs no coupling at
all. -/
theorem relTriple_simulateQ_run_untilAbsorbing
    {ι₁ ι₂ ιq : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {specq : OracleSpec ιq}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂] {σ₁ σ₂ : Type} {α : Type}
    (impl₁ : QueryImpl specq (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl specq (StateT σ₂ (OracleComp spec₂)))
    (Good : σ₁ → σ₂ → Prop) (B₁ : σ₁ → Prop) (B₂ : σ₂ → Prop)
    (habs₁ : ∀ (t : specq.Domain) (s : σ₁), B₁ s →
      ∀ z ∈ support (m := OracleComp spec₁) ((impl₁ t).run s), B₁ z.2)
    (habs₂ : ∀ (t : specq.Domain) (s : σ₂), B₂ s →
      ∀ z ∈ support (m := OracleComp spec₂) ((impl₂ t).run s), B₂ z.2)
    (hstep : ∀ (t : specq.Domain) (s₁ : σ₁) (s₂ : σ₂), Good s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => (p₁.1 = p₂.1 ∧ Good p₁.2 p₂.2) ∨ (B₁ p₁.2 ∧ B₂ p₂.2)))
    (oa : OracleComp specq α) (s₁ : σ₁) (s₂ : σ₂) (hs : Good s₁ s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run s₁)
      ((simulateQ impl₂ oa).run s₂)
      (fun z₁ z₂ => (z₁.1 = z₂.1 ∧ Good z₁.2 z₂.2) ∨ (B₁ z₁.2 ∧ B₂ z₂.2)) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨rfl, hs⟩)
  | query_bind t ob ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      refine relTriple_bind (hstep t s₁ s₂ hs) ?_
      rintro ⟨u₁, s₁'⟩ ⟨u₂, s₂'⟩ (⟨hu, hg⟩ | ⟨hb₁, hb₂⟩)
      · dsimp only at hu
        subst hu
        exact ih u₁ s₁' s₂' hg
      · refine relTriple_post_mono ?_ fun z₁ z₂ h => Or.inr h
        exact relTriple_prod
          (fun z hz => simulateQ_run_preserves_inv_of_query impl₁ B₁
            habs₁ (ob u₁) s₁' hb₁ z hz)
          (fun z hz => simulateQ_run_preserves_inv_of_query impl₂ B₂
            habs₂ (ob u₂) s₂' hb₂ z hz)

/-- One-sided bad-mass transfer from the until-absorbing coupling: if the
target event is contained in the absorbing sets' joint branch and refuted on
the good branch, the left event mass is at most the right event mass. -/
theorem probEvent_le_of_untilAbsorbing
    {ι₁ ι₂ ιq : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {specq : OracleSpec ιq}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂] {σ₁ σ₂ : Type} {α : Type}
    (impl₁ : QueryImpl specq (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl specq (StateT σ₂ (OracleComp spec₂)))
    (Good : σ₁ → σ₂ → Prop) (B₁ : σ₁ → Prop) (B₂ : σ₂ → Prop)
    (habs₁ : ∀ (t : specq.Domain) (s : σ₁), B₁ s →
      ∀ z ∈ support (m := OracleComp spec₁) ((impl₁ t).run s), B₁ z.2)
    (habs₂ : ∀ (t : specq.Domain) (s : σ₂), B₂ s →
      ∀ z ∈ support (m := OracleComp spec₂) ((impl₂ t).run s), B₂ z.2)
    (hstep : ∀ (t : specq.Domain) (s₁ : σ₁) (s₂ : σ₂), Good s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => (p₁.1 = p₂.1 ∧ Good p₁.2 p₂.2) ∨ (B₁ p₁.2 ∧ B₂ p₂.2)))
    (oa : OracleComp specq α) (s₁ : σ₁) (s₂ : σ₂) (hs : Good s₁ s₂)
    (P : α × σ₁ → Prop) (Q : α × σ₂ → Prop)
    (hPgood : ∀ (z₁ : α × σ₁) (z₂ : α × σ₂),
      z₁.1 = z₂.1 → Good z₁.2 z₂.2 → P z₁ → Q z₂)
    (hBQ : ∀ z₂ : α × σ₂, B₂ z₂.2 → Q z₂) :
    Pr[P | (simulateQ impl₁ oa).run s₁]
      ≤ Pr[Q | (simulateQ impl₂ oa).run s₂] := by
  refine probEvent_le_of_relTriple_imp
    (relTriple_simulateQ_run_untilAbsorbing impl₁ impl₂ Good B₁ B₂
      habs₁ habs₂ hstep oa s₁ s₂ hs) ?_
  rintro z₁ z₂ (⟨hu, hg⟩ | ⟨hb₁, hb₂⟩) hP
  · exact hPgood z₁ z₂ hu hg hP
  · exact hBQ z₂ hb₂

/-! ## The deferred-slope handler -/

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-- State of the deferred-slope handler: the secret-independent ideal cache
state (public random oracles plus the private per-index honest-nullifier
cache), the lazily materialized hidden slopes, and the same audit record the
real audited handler keeps. -/
structure DSFrameSt (F M : Type) where
  /-- the erasable ideal cache state -/
  ideal : IdealFrameSt F M
  /-- lazily materialized hidden slopes, pinned at first honest touch -/
  slope : ℕ → Option F
  /-- the audit transcript, with the same shape as the real side -/
  audit : FrameAudit F

/-- Initial deferred-slope state. -/
def DSFrameSt.init (F M : Type) : DSFrameSt F M :=
  ⟨IdealFrameSt.init F M, fun _ => none, FrameAudit.init⟩

/-- Good-state relation for the real and deferred-slope handlers.  The
canonical idealization erases the real handler's secret namespace; the
deferred state retains exactly that erased public state, while its private
`slope` cache records the erased entries pointwise.  Both handlers carry the
same audit transcript. -/
structure RealDSCoupled (k : F) (r : AuditedFrameSt F M)
    (d : DSFrameSt F M) : Prop where
  ideal : idealizeFrame k r = d.ideal
  hiddenSlope : ∀ i, r.base.roA (k, i) = d.slope i
  audit : r.audit = d.audit

/-- Programming the real identity cache at the honest secret is invisible
after idealization, so the programmed real initial state couples to the empty
deferred-slope state. -/
theorem realDSCoupled_initial (k cm : F) :
    RealDSCoupled k
      (⟨{ FrameSt.init F M with
          roId := Function.update (FrameSt.init F M).roId k (some cm) },
        FrameAudit.init⟩ : AuditedFrameSt F M)
      (DSFrameSt.init F M) := by
  constructor
  · exact idealizeFrame_initial k cm
  · intro i
    rfl
  · rfl

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- The recorded leakage predicate agrees exactly under the real/deferred
good-state relation; there is no additional bad-event accounting loss when
changing handler. -/
theorem frameLeakBad_iff_dsFrameLeakBad {k : F} {r : AuditedFrameSt F M}
    {d : DSFrameSt F M} (h : RealDSCoupled k r d) :
    FrameLeakBad k r.audit ↔ FrameLeakBad k d.audit := by
  rw [h.audit]

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- Goodness is likewise shared exactly by coupled states. -/
theorem not_frameLeakBad_iff_not_dsFrameLeakBad {k : F}
    {r : AuditedFrameSt F M} {d : DSFrameSt F M}
    (h : RealDSCoupled k r d) :
    (¬ FrameLeakBad k r.audit) ↔ (¬ FrameLeakBad k d.audit) :=
  not_congr (frameLeakBad_iff_dsFrameLeakBad h)

/-- Lazily materialize the hidden slope at honest index `i` and record it as
an honest slope on a first touch; a re-touch returns the pinned value with
no audit change. This mirrors exactly when the real handler's `auditAfter`
records a fresh honest slope. -/
def dsTouch (gs : ℕ → Option F) (audit : FrameAudit F) (i : ℕ) :
    ProbComp (F × (ℕ → Option F) × FrameAudit F) :=
  match gs i with
  | some a => pure (a, gs, audit)
  | none => do
      let v ← ($ᵗ F)
      pure (v, Function.update gs i (some v),
        { audit with honestSlopes := v :: audit.honestSlopes })

/-- **The deferred-slope FRAME handler.** Public random-oracle queries hit
the handler's own public caches (with no programmed `H_id(k)` entry and no
hidden `H_a(k, ·)` reads); honest signal emissions pin the hidden slope at
first touch through `dsTouch` and emit the same line value `y = k + a·x` as
the real handler; honest nullifiers come from the private per-index cache
`honestNf` instead of the public `H_nf` cache, so adversary `H_nf` probes
never read hidden slope material. Audit updates classify queries exactly as
the real `auditAfter` does. -/
def dsFrameImpl (k : F) (mclose : M) :
    QueryImpl.Stateful unifSpec (frameSpec F M) (DSFrameSt F M)
  | .spend m => StateT.mk fun g =>
      if g.ideal.closed then pure (none, g)
      else do
        let (x, cX) ← lazyROX g.ideal.roX m
        let (a, gs, aud) ← dsTouch g.slope g.audit g.ideal.idx
        let (nf, cNf) ← lazyRO g.ideal.honestNf g.ideal.idx
        pure (some ⟨x, rlnY k a x, nf⟩,
          ⟨{ g.ideal with idx := g.ideal.idx + 1, roX := cX, honestNf := cNf },
            gs, aud⟩)
  | .close => StateT.mk fun g =>
      if g.ideal.closed then pure (none, g)
      else do
        let (x, cX) ← lazyROX g.ideal.roX mclose
        let (a, gs, aud) ← dsTouch g.slope g.audit g.ideal.idx
        let (nf, cNf) ← lazyRO g.ideal.honestNf g.ideal.idx
        let ideal' : IdealFrameSt F M :=
          { g.ideal with
              idx := g.ideal.idx + 1
              closed := true
              roX := cX
              honestNf := cNf }
        pure (some ⟨x, rlnY k a x, nf⟩, ⟨ideal', gs, aud⟩)
  | .nfAt i => StateT.mk fun g => do
      let (nf, cNf) ← lazyRO g.ideal.honestNf i
      let (_, gs, aud) ← dsTouch g.slope g.audit i
      pure (nf, ⟨{ g.ideal with honestNf := cNf }, gs, aud⟩)
  | .roA kq i => StateT.mk fun g => do
      let (v, c) ← lazyRO g.ideal.roA (kq, i)
      pure (v, ⟨{ g.ideal with roA := c }, g.slope,
        { g.audit with secretProbes := kq :: g.audit.secretProbes }⟩)
  | .roX m => StateT.mk fun g => do
      let (v, c) ← lazyROX g.ideal.roX m
      pure (v, ⟨{ g.ideal with roX := c }, g.slope, g.audit⟩)
  | .roNf aq => StateT.mk fun g => do
      let (v, c) ← lazyRO g.ideal.roNf aq
      pure (v, ⟨{ g.ideal with roNf := c }, g.slope,
        { g.audit with slopeProbes := aq :: g.audit.slopeProbes }⟩)
  | .roE kq e => StateT.mk fun g => do
      let (v, c) ← lazyRO g.ideal.roE (kq, e)
      pure (v, ⟨{ g.ideal with roE := c }, g.slope,
        { g.audit with secretProbes := kq :: g.audit.secretProbes }⟩)
  | .roId kq => StateT.mk fun g => do
      let (v, c) ← lazyRO g.ideal.roId kq
      pure (v, ⟨{ g.ideal with roId := c }, g.slope,
        { g.audit with secretProbes := kq :: g.audit.secretProbes }⟩)

/-- The complete deferred-slope run of a FRAME adversary at honest secret
`k`: sample the public commitment and run the adversary against the
deferred-slope handler from the empty state. Unlike the real run, the
handler does not program `H_id(k) = cm` — the divergence on a direct
`H_id(k)` probe is a recorded (hence bad-charged) event. -/
def dsFrameRun (k : F) (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    ProbComp (Evidence F × DSFrameSt F M) := do
  let cm ← ($ᵗ F)
  (simulateQ (dsFrameImpl k mclose) (A cm)).run (DSFrameSt.init F M)

/-- Hidden-slope coverage for the deferred handler: every pinned slope is a
recorded honest slope. -/
def DSSlopesCovered (g : DSFrameSt F M) : Prop :=
  ∀ i a, g.slope i = some a → a ∈ g.audit.honestSlopes

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- A coupled deferred slope entry is exactly the corresponding hidden real
random-oracle entry. -/
theorem RealDSCoupled.hiddenSlope_iff {k : F}
    {r : AuditedFrameSt F M} {d : DSFrameSt F M}
    (h : RealDSCoupled k r d) (i : ℕ) (a : F) :
    r.base.roA (k, i) = some a ↔ d.slope i = some a := by
  rw [h.hiddenSlope i]

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- Deferred slope coverage transfers to audit completeness on the real
side.  This packages the cache invariant required by the existing
materialized-`nfAt` and public-nullifier coupling lemmas. -/
theorem RealDSCoupled.frameAuditComplete {k : F}
    {r : AuditedFrameSt F M} {d : DSFrameSt F M}
    (h : RealDSCoupled k r d) (hd : DSSlopesCovered d) :
    FrameAuditComplete k r := by
  intro i a ha
  rw [h.audit]
  exact hd i a ((h.hiddenSlope_iff i a).1 ha)

/-! ## Bad-event monotonicity for the deferred-slope handler -/

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- The initial deferred-slope state is covered. -/
theorem dsSlopesCovered_init : DSSlopesCovered (DSFrameSt.init F M) := by
  intro i a h
  simp [DSFrameSt.init] at h

omit [Field F] [DecidableEq F] in
/-- `dsTouch` support characterization: a cache hit changes nothing, a fresh
touch pins and records exactly one new slope. -/
theorem dsTouch_support (gs : ℕ → Option F) (audit : FrameAudit F) (i : ℕ)
    (z : F × (ℕ → Option F) × FrameAudit F)
    (hz : z ∈ support (dsTouch gs audit i)) :
    (gs i = some z.1 ∧ z.2 = (gs, audit)) ∨
      (gs i = none ∧
        z.2 = (Function.update gs i (some z.1),
          { audit with honestSlopes := z.1 :: audit.honestSlopes })) := by
  unfold dsTouch at hz
  split at hz
  · rename_i a h
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl ⟨h, rfl⟩
  · rename_i h
    obtain ⟨v, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inr ⟨h, rfl⟩

/-- Every supported deferred-slope step preserves an already-raised leakage
event: audit lists only grow. -/
theorem dsFrameImpl_bad_monotone (k : F) (mclose : M) (op : FrameOp F M)
    (g : DSFrameSt F M) (hbad : FrameLeakBad k g.audit)
    (z : (frameSpec F M).Range op × DSFrameSt F M)
    (hz : z ∈ support (((dsFrameImpl k mclose) op).run g)) :
    FrameLeakBad k z.2.audit := by
  cases op with
  | spend m =>
      unfold dsFrameImpl at hz
      simp only [StateT.run_mk] at hz
      by_cases hc : g.ideal.closed
      · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hbad
      · rw [if_neg hc] at hz
        obtain ⟨px, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨pt, hpt, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨pn, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        rcases dsTouch_support _ _ _ pt hpt with ⟨-, ht⟩ | ⟨-, ht⟩
        · simp only [ht]
          exact hbad
        · simp only [ht]
          exact FrameLeakBad.honest_cons k pt.1 g.audit hbad
  | close =>
      unfold dsFrameImpl at hz
      simp only [StateT.run_mk] at hz
      by_cases hc : g.ideal.closed
      · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hbad
      · rw [if_neg hc] at hz
        obtain ⟨px, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨pt, hpt, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨pn, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        rcases dsTouch_support _ _ _ pt hpt with ⟨-, ht⟩ | ⟨-, ht⟩
        · simp only [ht]
          exact hbad
        · simp only [ht]
          exact FrameLeakBad.honest_cons k pt.1 g.audit hbad
  | nfAt i =>
      unfold dsFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨pn, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨pt, hpt, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rcases dsTouch_support _ _ _ pt hpt with ⟨-, ht⟩ | ⟨-, ht⟩
      · simp only [ht]
        exact hbad
      · simp only [ht]
        exact FrameLeakBad.honest_cons k pt.1 g.audit hbad
  | roA kq i =>
      unfold dsFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.secret_cons k kq g.audit hbad
  | roX m =>
      unfold dsFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hbad
  | roNf aq =>
      unfold dsFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.slope_cons k aq g.audit hbad
  | roE kq e =>
      unfold dsFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.secret_cons k kq g.audit hbad
  | roId kq =>
      unfold dsFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.secret_cons k kq g.audit hbad

/-- Once leakage has been recorded, an arbitrary adaptive continuation of the
deferred-slope handler remains in the bad set.  This is the handler-specific
absorbing premise consumed by `relTriple_simulateQ_run_untilAbsorbing`. -/
theorem dsFrameImpl_run_bad_monotone (k : F) (mclose : M)
    {α : Type} (oa : OracleComp (frameSpec F M) α)
    (g : DSFrameSt F M) (hbad : FrameLeakBad k g.audit)
    (z : α × DSFrameSt F M)
    (hz : z ∈ support ((simulateQ (dsFrameImpl k mclose) oa).run g)) :
    FrameLeakBad k z.2.audit :=
  simulateQ_run_preserves_inv_of_query (dsFrameImpl k mclose)
    (fun st => FrameLeakBad k st.audit)
    (fun op st h st' hs => dsFrameImpl_bad_monotone k mclose op st h st' hs)
    oa g hbad z hz

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.relTriple_simulateQ_run_untilAbsorbing
#print axioms Zkpc.Games.probEvent_le_of_untilAbsorbing
#print axioms Zkpc.Games.realDSCoupled_initial
#print axioms Zkpc.Games.frameLeakBad_iff_dsFrameLeakBad
#print axioms Zkpc.Games.not_frameLeakBad_iff_not_dsFrameLeakBad
#print axioms Zkpc.Games.dsFrameImpl_bad_monotone
#print axioms Zkpc.Games.dsFrameImpl_run_bad_monotone
