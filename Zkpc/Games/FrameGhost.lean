import Zkpc.Games.FrameIdeal
import Zkpc.Games.T7

/-!
# Ghost-slope audited ideal FRAME handler (Spec.md §7 T7, k-averaged assembly)

The corrected T7 certificate is the *k-averaged* real/ideal comparison: the
pointwise form is unsatisfiable, and the identical-until-bad accounting must
happen at the run level over the uniform secret. This file provides the ideal
side of that comparison, instrumented with a **write-only ghost ornament**:

* `GhostFrameSt` extends the secret-independent `IdealFrameSt` with per-index
  ghost slopes (`ghostSlope`) and a completely `k`-free audit record
  (`GhostAudit`): the queried candidate secrets per direct channel
  (`roAProbes`/`roEProbes`/`roIdProbes`), the `H_nf` probe arguments
  (`slopeProbes`), and the ghost slope values materialized by honest signal
  emissions and first `nfAt` touches (`honestSlopes`).
* `ghostFrameImpl` behaves *exactly* like `idealFrameImpl` on the answer and
  ideal-state components — proved as the erasure theorems
  `ghostFrameImpl_erase_step` / `ghostFrameImpl_run_erase` /
  `ghostFrameEvidence_evalDist_eq` — while additionally sampling a fresh ghost
  slope at each honest signal emission and each first `nfAt` touch, and
  recording audit data on every operation. Ghost data never influences
  answers or ideal-state updates.
* `map_run_simulateQ_evalDist_eq_of_step` is the generic distributional
  transport lemma powering the erasure: a per-query distributional projection
  identity lifts to full simulations. The exact-equality projection theorem
  (`OracleComp.map_run_simulateQ_eq_of_query_map_eq`) is too strong here
  because ghost sampling adds discarded randomness.
* `support_measure_le_of_isQueryBoundP` threads `IsQueryBoundP` certificates
  through a stateful simulation support-wise; instantiated per channel it
  yields `ghostFrameImpl_run_audit_bounds`: in every supported outcome of the
  ghost run the audit lists are bounded by the adversary's structural query
  budgets (`FrameQueryBounds`).

Downstream consumers: the bad-mass lane bounds, over the ghost run followed
by a deferred uniform secret `k`, the probability of
`GhostLeakBad k audit` by `qb.total/|F|`; the coupling lane relates the real
audited run (`auditedFrameImpl`) to this ghost run off that bad event, using
`GhostSlopesComplete` (the ghost analogue of `FrameAuditComplete`) and the
monotonicity lemmas.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## The k-free ghost audit record -/

/-- Ghost audit transcript for the ideal-side handler. Entirely `k`-free:
membership of a deferred secret in the probe lists is tested only *after*
the run. Lists retain multiplicity so repeated ghost slopes are observable
as a collision. -/
structure GhostAudit (F : Type) where
  /-- arguments `kq` of direct `roA kq i` queries (candidate secrets) -/
  roAProbes : List F
  /-- arguments `kq` of direct `roE kq e` queries (candidate secrets) -/
  roEProbes : List F
  /-- arguments `kq` of direct `roId kq` queries (candidate secrets) -/
  roIdProbes : List F
  /-- arguments of direct `roNf` queries (candidate honest slopes) -/
  slopeProbes : List F
  /-- ghost slope values sampled at honest signal emissions and first
  `nfAt` touches -/
  honestSlopes : List F

/-- Empty ghost audit transcript. -/
def GhostAudit.init : GhostAudit F := ⟨[], [], [], [], []⟩

/-- All direct-secret candidate probes, across the three channels that can
test a candidate for the honest secret `k`. -/
def GhostAudit.secretProbes (a : GhostAudit F) : List F :=
  a.roAProbes ++ a.roEProbes ++ a.roIdProbes

/-- The `k`-deferred leakage event of the corrected T7 accounting: a direct
candidate probe hit the (later-drawn) secret, a slope probe matched a ghost
honest slope, or two ghost honest slopes collided. Mirrors `FrameLeakBad`
on the real side. -/
def GhostLeakBad (k : F) (a : GhostAudit F) : Prop :=
  k ∈ a.secretProbes ∨
  (∃ slope ∈ a.slopeProbes, slope ∈ a.honestSlopes) ∨
  ¬ a.honestSlopes.Nodup

instance (k : F) (a : GhostAudit F) : Decidable (GhostLeakBad k a) := by
  unfold GhostLeakBad
  infer_instance

omit [Field F] [SampleableType F] in
/-- The ghost leakage event is monotone under suffix extension of all five
audit lists: once raised, no further recording can clear it. -/
theorem GhostLeakBad.mono {k : F} {a b : GhostAudit F}
    (hA : a.roAProbes <:+ b.roAProbes) (hE : a.roEProbes <:+ b.roEProbes)
    (hId : a.roIdProbes <:+ b.roIdProbes)
    (hNf : a.slopeProbes <:+ b.slopeProbes)
    (hS : a.honestSlopes <:+ b.honestSlopes)
    (h : GhostLeakBad k a) : GhostLeakBad k b := by
  rcases h with h | ⟨s, hs1, hs2⟩ | h
  · left
    simp only [GhostAudit.secretProbes, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (hA.subset h))
    · exact Or.inl (Or.inr (hE.subset h))
    · exact Or.inr (hId.subset h)
  · exact Or.inr (Or.inl ⟨s, hNf.subset hs1, hS.subset hs2⟩)
  · exact Or.inr (Or.inr fun hnd => h (hnd.sublist hS.sublist))

/-! ## The ghost state -/

/-- State of the ghost handler: the plain ideal state decorated with lazily
materialized per-index ghost slopes and the `k`-free audit record. The
decoration is write-only: `ghostFrameImpl` never reads it when computing
answers or ideal-state updates. -/
structure GhostFrameSt (F M : Type) where
  /-- the erasable ideal-handler state -/
  ideal : IdealFrameSt F M
  /-- per-index ghost slopes, standing in for the hidden real `H_a(k, ·)`
  entries in the coupling -/
  ghostSlope : ℕ → Option F
  /-- the `k`-free audit record -/
  audit : GhostAudit F

/-- Initial ghost state: empty ideal state, no ghost slopes, empty audit. -/
def GhostFrameSt.init (F M : Type) : GhostFrameSt F M :=
  ⟨IdealFrameSt.init F M, fun _ => none, GhostAudit.init⟩

omit [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] in
/-- Erasing the initial ghost state gives the initial ideal state. -/
@[simp] theorem ghostFrameSt_init_ideal :
    (GhostFrameSt.init F M).ideal = IdealFrameSt.init F M := rfl

omit [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] in
/-- The initial ghost state carries the empty audit. -/
@[simp] theorem ghostFrameSt_init_audit :
    (GhostFrameSt.init F M).audit = GhostAudit.init := rfl

/-! ## Ghost slope materialization -/

/-- Lazily materialize the ghost slope at honest index `i`: on a first touch
sample fresh-uniform, cache the value, and record it as a ghost honest
slope; on a re-touch return the cache unchanged. This mirrors exactly when
the real handler's `auditAfter` records a fresh honest slope. -/
def ghostTouch (gs : ℕ → Option F) (audit : GhostAudit F) (i : ℕ) :
    ProbComp ((ℕ → Option F) × GhostAudit F) :=
  match gs i with
  | some _ => pure (gs, audit)
  | none => do
      let v ← ($ᵗ F)
      pure (Function.update gs i (some v),
        { audit with honestSlopes := v :: audit.honestSlopes })

omit [Field F] in
/-- Support characterization of `ghostTouch`: either the touch was a cache
hit and nothing changed, or the index was fresh and exactly one new ghost
slope was cached and recorded. -/
theorem ghostTouch_support (gs : ℕ → Option F) (audit : GhostAudit F)
    (i : ℕ) (z : (ℕ → Option F) × GhostAudit F)
    (hz : z ∈ support (ghostTouch gs audit i)) :
    z = (gs, audit) ∨
      ∃ v, gs i = none ∧
        z = (Function.update gs i (some v),
          { audit with honestSlopes := v :: audit.honestSlopes }) := by
  unfold ghostTouch at hz
  split at hz
  · rw [support_pure, Set.mem_singleton_iff] at hz
    exact Or.inl hz
  · rename_i h
    obtain ⟨v, _, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    exact Or.inr ⟨v, h, hz⟩

omit [Field F] in
/-- The ghost slope sample is answer-irrelevant discarded randomness: any
continuation that ignores the `ghostTouch` result keeps its distribution. -/
theorem evalDist_ghostTouch_bind_const {β : Type} (gs : ℕ → Option F)
    (audit : GhostAudit F) (i : ℕ) (ob : ProbComp β) :
    𝒟[ghostTouch gs audit i >>= fun _ => ob] = 𝒟[ob] := by
  unfold ghostTouch
  split
  · rw [pure_bind]
  · rw [bind_assoc]
    simp only [pure_bind]
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      ($ᵗ F) (probFailure_uniformSample F) ob

/-! ## The ghost handler -/

/-- Ghost-slope audited ideal FRAME handler. On the answer and ideal-state
components it behaves *exactly* like `idealFrameImpl` (proved by the erasure
theorems below); additionally it lazily samples a fresh ghost slope at each
honest signal emission (`spend`/legacy `close` on an open state) and at
each first `nfAt i` touch, and it records the queried candidate values of
every direct secret-testing and slope-testing oracle call. The ghost data
is a write-only ornament: it never feeds back into any response. -/
def ghostFrameImpl (mclose : M) :
    QueryImpl.Stateful unifSpec (frameSpec F M) (GhostFrameSt F M)
  | .spend m => StateT.mk fun g =>
      if g.ideal.closed then pure (none, g)
      else do
        let p ← emitIdealSignal m g.ideal
        let q ← ghostTouch g.ghostSlope g.audit g.ideal.idx
        pure (some p.1, ⟨p.2, q.1, q.2⟩)
  | .close => StateT.mk fun g =>
      if g.ideal.closed then pure (none, g)
      else do
        let p ← emitIdealSignal mclose g.ideal
        let q ← ghostTouch g.ghostSlope g.audit g.ideal.idx
        pure (some p.1, ⟨{ p.2 with closed := true }, q.1, q.2⟩)
  | .nfAt i => StateT.mk fun g => do
      let p ← lazyRO g.ideal.honestNf i
      let q ← ghostTouch g.ghostSlope g.audit i
      pure (p.1, ⟨{ g.ideal with honestNf := p.2 }, q.1, q.2⟩)
  | .roA kq i => StateT.mk fun g => do
      let p ← lazyRO g.ideal.roA (kq, i)
      pure (p.1, ⟨{ g.ideal with roA := p.2 }, g.ghostSlope,
        { g.audit with roAProbes := kq :: g.audit.roAProbes }⟩)
  | .roX m => StateT.mk fun g => do
      let p ← lazyROX g.ideal.roX m
      pure (p.1, ⟨{ g.ideal with roX := p.2 }, g.ghostSlope, g.audit⟩)
  | .roNf aq => StateT.mk fun g => do
      let p ← lazyRO g.ideal.roNf aq
      pure (p.1, ⟨{ g.ideal with roNf := p.2 }, g.ghostSlope,
        { g.audit with slopeProbes := aq :: g.audit.slopeProbes }⟩)
  | .roE kq e => StateT.mk fun g => do
      let p ← lazyRO g.ideal.roE (kq, e)
      pure (p.1, ⟨{ g.ideal with roE := p.2 }, g.ghostSlope,
        { g.audit with roEProbes := kq :: g.audit.roEProbes }⟩)
  | .roId kq => StateT.mk fun g => do
      let p ← lazyRO g.ideal.roId kq
      pure (p.1, ⟨{ g.ideal with roId := p.2 }, g.ghostSlope,
        { g.audit with roIdProbes := kq :: g.audit.roIdProbes }⟩)

/-! ## Generic distributional state transport -/

/-- **Distributional state-projection transport for `simulateQ`.** If each
oracle step of `impl₁`, after projecting the state by `f`, has *the same
distribution* as the corresponding `impl₂` step from the projected state,
then full simulations agree in distribution under the same projection.
This is the distributional weakening of
`OracleComp.map_run_simulateQ_eq_of_query_map_eq`, needed when the richer
handler consumes extra randomness that the projection discards (here: the
ghost slope samples). -/
theorem map_run_simulateQ_evalDist_eq_of_step
    {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (f : σ₁ → σ₂)
    (hstep : ∀ (q : spec.Domain) (s : σ₁),
      𝒟[Prod.map id f <$> (impl₁ q).run s] = 𝒟[(impl₂ q).run (f s)])
    {α : Type} (oa : OracleComp spec α) (s : σ₁) :
    𝒟[Prod.map id f <$> (simulateQ impl₁ oa).run s] =
      𝒟[(simulateQ impl₂ oa).run (f s)] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [Prod.map]
  | query_bind t k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map, StateT.run_bind, map_bind]
      have h1 : 𝒟[(impl₁ t).run s >>= fun p =>
            Prod.map id f <$> (simulateQ impl₁ (k p.1)).run p.2]
          = 𝒟[(impl₁ t).run s >>= fun p =>
              (simulateQ impl₂ (k p.1)).run (f p.2)] :=
        evalDist_bind_congr' _ fun p => ih p.1 p.2
      have hswap : ((impl₁ t).run s >>= fun p =>
            (simulateQ impl₂ (k p.1)).run (f p.2))
          = ((Prod.map id f <$> (impl₁ t).run s) >>= fun p =>
              (simulateQ impl₂ (k p.1)).run p.2) := by
        rw [bind_map_left]
        exact bind_congr fun p => rfl
      have h2 : 𝒟[(impl₁ t).run s >>= fun p =>
            (simulateQ impl₂ (k p.1)).run (f p.2)]
          = 𝒟[(impl₂ t).run (f s) >>= fun p =>
              (simulateQ impl₂ (k p.1)).run p.2] := by
        rw [hswap, evalDist_bind, evalDist_bind, hstep t s]
      exact h1.trans h2

/-! ## Exact ghost erasure -/

/-- **Per-step ghost erasure.** Projecting away the ghost ornament after one
ghost step gives exactly the distribution of the corresponding plain ideal
step: the ghost slope sample is independent discarded randomness and the
audit is write-only. -/
theorem ghostFrameImpl_erase_step (mclose : M) (op : FrameOp F M)
    (g : GhostFrameSt F M) :
    𝒟[Prod.map id GhostFrameSt.ideal <$> ((ghostFrameImpl mclose) op).run g] =
      𝒟[((idealFrameImpl mclose) op).run g.ideal] := by
  cases op with
  | spend m =>
      unfold ghostFrameImpl idealFrameImpl
      simp only [StateT.run_mk]
      by_cases hc : g.ideal.closed
      · simp [hc, Prod.map]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind, map_pure,
          Prod.map, id_eq]
        refine evalDist_bind_congr' (emitIdealSignal m g.ideal) fun p => ?_
        obtain ⟨sig, s'⟩ := p
        exact evalDist_ghostTouch_bind_const g.ghostSlope g.audit g.ideal.idx _
  | close =>
      unfold ghostFrameImpl idealFrameImpl
      simp only [StateT.run_mk]
      by_cases hc : g.ideal.closed
      · simp [hc, Prod.map]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind, map_pure,
          Prod.map, id_eq]
        refine evalDist_bind_congr' (emitIdealSignal mclose g.ideal) fun p => ?_
        obtain ⟨sig, s'⟩ := p
        exact evalDist_ghostTouch_bind_const g.ghostSlope g.audit g.ideal.idx _
  | nfAt i =>
      unfold ghostFrameImpl idealFrameImpl
      simp only [StateT.run_mk, map_bind, map_pure, Prod.map, id_eq]
      refine evalDist_bind_congr' (lazyRO g.ideal.honestNf i) fun p => ?_
      obtain ⟨nf, cNf⟩ := p
      exact evalDist_ghostTouch_bind_const g.ghostSlope g.audit i _
  | roA kq i =>
      unfold ghostFrameImpl idealFrameImpl
      simp only [StateT.run_mk, map_bind, map_pure, Prod.map, id_eq]
  | roX m =>
      unfold ghostFrameImpl idealFrameImpl
      simp only [StateT.run_mk, map_bind, map_pure, Prod.map, id_eq]
  | roNf aq =>
      unfold ghostFrameImpl idealFrameImpl
      simp only [StateT.run_mk, map_bind, map_pure, Prod.map, id_eq]
  | roE kq e =>
      unfold ghostFrameImpl idealFrameImpl
      simp only [StateT.run_mk, map_bind, map_pure, Prod.map, id_eq]
  | roId kq =>
      unfold ghostFrameImpl idealFrameImpl
      simp only [StateT.run_mk, map_bind, map_pure, Prod.map, id_eq]

/-- **Full-run ghost erasure.** For every adaptive FRAME computation, the
ghost run's joint answer/ideal-state distribution after erasing the ghost
ornament equals the plain ideal run's distribution. -/
theorem ghostFrameImpl_run_erase (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (g : GhostFrameSt F M) :
    𝒟[Prod.map id GhostFrameSt.ideal <$>
        (simulateQ (ghostFrameImpl mclose) oa).run g] =
      𝒟[(simulateQ (idealFrameImpl mclose) oa).run g.ideal] :=
  map_run_simulateQ_evalDist_eq_of_step (ghostFrameImpl mclose)
    (idealFrameImpl mclose) GhostFrameSt.ideal
    (ghostFrameImpl_erase_step mclose) oa g

/-- Output-only corollary of the full-run erasure: the ghost handler answers
every adaptive FRAME computation with exactly the ideal handler's output
distribution. -/
theorem ghostFrameImpl_run_output_erase (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (g : GhostFrameSt F M) :
    𝒟[(ghostFrameImpl mclose).run g oa] =
      𝒟[(idealFrameImpl mclose).run g.ideal oa] := by
  simp only [QueryImpl.Stateful.run, StateT.run'_eq, evalDist_map]
  have h := congrArg (fun d => Prod.fst <$> d)
    (ghostFrameImpl_run_erase mclose oa g)
  simp only [evalDist_map, Functor.map_map] at h
  simp only [Prod.map_fst, id_eq] at h
  exact h

/-! ## The ghost run and its evidence corollary -/

/-- The complete ghost run of a FRAME adversary: sample the (secret-free)
public commitment uniformly as in `idealFrameEvidence`, then run the
adversary against the ghost handler, keeping the final ghost state. This is
the object the bad-mass and coupling lanes reason about. -/
def ghostFrameRun (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    ProbComp (Evidence F × GhostFrameSt F M) := do
  let cm ← ($ᵗ F)
  (simulateQ (ghostFrameImpl mclose) (A cm)).run (GhostFrameSt.init F M)

/-- The ghost-run evidence generator: the output-only ghost run, in the
shape of `idealFrameEvidence`. -/
def ghostFrameEvidence (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    ProbComp (Evidence F) := do
  let cm ← ($ᵗ F)
  (ghostFrameImpl mclose).run (GhostFrameSt.init F M) (A cm)

/-- The evidence generator is literally the first projection of the paired
ghost run. -/
theorem fst_map_ghostFrameRun (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    Prod.fst <$> ghostFrameRun mclose A = ghostFrameEvidence mclose A := by
  unfold ghostFrameRun ghostFrameEvidence QueryImpl.Stateful.run
  rw [map_bind]
  refine bind_congr fun cm => ?_
  rw [StateT.run'_eq]

/-- Erasing the ghost ornament from the paired ghost run gives exactly the
paired plain ideal run from the empty ideal state. -/
theorem ghostFrameRun_erase (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    𝒟[Prod.map id GhostFrameSt.ideal <$> ghostFrameRun mclose A] =
      𝒟[do
        let cm ← ($ᵗ F)
        (simulateQ (idealFrameImpl mclose) (A cm)).run (IdealFrameSt.init F M)] := by
  unfold ghostFrameRun
  rw [map_bind]
  exact evalDist_bind_congr' ($ᵗ F) fun cm =>
    ghostFrameImpl_run_erase mclose (A cm) (GhostFrameSt.init F M)

/-- **Evidence corollary of ghost erasure.** The ghost-run evidence
distribution equals `idealFrameEvidence` — the secret-independent generator
compared against the real run in the k-averaged T7 certificate. -/
theorem ghostFrameEvidence_evalDist_eq (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    𝒟[ghostFrameEvidence mclose A] = 𝒟[idealFrameEvidence mclose A] := by
  unfold ghostFrameEvidence idealFrameEvidence
  exact evalDist_bind_congr' ($ᵗ F) fun cm =>
    ghostFrameImpl_run_output_erase mclose (A cm) (GhostFrameSt.init F M)

/-! ## Per-operation audit transitions -/

omit [Field F] in
/-- A `spend` step either leaves the audit unchanged (closed member or ghost
cache hit) or records exactly one fresh ghost honest slope. -/
theorem ghostFrameImpl_audit_spend (mclose : M) (m : M)
    (g : GhostFrameSt F M) (z : Option (Signal F) × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) (.spend m)).run g)) :
    z.2.audit = g.audit ∨
      ∃ v, z.2.audit = { g.audit with
        honestSlopes := v :: g.audit.honestSlopes } := by
  unfold ghostFrameImpl at hz
  simp only [StateT.run_mk] at hz
  by_cases hc : g.ideal.closed
  · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl
  · rw [if_neg hc] at hz
    obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    obtain ⟨q, hq, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rcases ghostTouch_support g.ghostSlope g.audit g.ideal.idx q hq with
      h | ⟨v, -, h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨v, by rw [h]⟩

omit [Field F] in
/-- A legacy `close` step either leaves the audit unchanged or records
exactly one fresh ghost honest slope. -/
theorem ghostFrameImpl_audit_close (mclose : M)
    (g : GhostFrameSt F M) (z : Option (Signal F) × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) .close).run g)) :
    z.2.audit = g.audit ∨
      ∃ v, z.2.audit = { g.audit with
        honestSlopes := v :: g.audit.honestSlopes } := by
  unfold ghostFrameImpl at hz
  simp only [StateT.run_mk] at hz
  by_cases hc : g.ideal.closed
  · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl
  · rw [if_neg hc] at hz
    obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    obtain ⟨q, hq, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rcases ghostTouch_support g.ghostSlope g.audit g.ideal.idx q hq with
      h | ⟨v, -, h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨v, by rw [h]⟩

omit [Field F] in
/-- An `nfAt` step either leaves the audit unchanged (ghost cache hit) or
records exactly one fresh ghost honest slope (first touch of index `i`). -/
theorem ghostFrameImpl_audit_nfAt (mclose : M) (i : ℕ)
    (g : GhostFrameSt F M) (z : F × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) (.nfAt i)).run g)) :
    z.2.audit = g.audit ∨
      ∃ v, z.2.audit = { g.audit with
        honestSlopes := v :: g.audit.honestSlopes } := by
  unfold ghostFrameImpl at hz
  simp only [StateT.run_mk] at hz
  obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  obtain ⟨q, hq, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rcases ghostTouch_support g.ghostSlope g.audit i q hq with h | ⟨v, -, h⟩
  · exact Or.inl (by rw [h])
  · exact Or.inr ⟨v, by rw [h]⟩

omit [Field F] in
/-- A direct `roA` query records exactly its candidate secret. -/
theorem ghostFrameImpl_audit_roA (mclose : M) (kq : F) (i : ℕ)
    (g : GhostFrameSt F M) (z : F × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) (.roA kq i)).run g)) :
    z.2.audit = { g.audit with roAProbes := kq :: g.audit.roAProbes } := by
  unfold ghostFrameImpl at hz
  simp only [StateT.run_mk] at hz
  obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

omit [Field F] in
/-- A direct `roX` query records nothing. -/
theorem ghostFrameImpl_audit_roX (mclose : M) (m : M)
    (g : GhostFrameSt F M) (z : F × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) (.roX m)).run g)) :
    z.2.audit = g.audit := by
  unfold ghostFrameImpl at hz
  simp only [StateT.run_mk] at hz
  obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

omit [Field F] in
/-- A direct `roNf` query records exactly its candidate slope. -/
theorem ghostFrameImpl_audit_roNf (mclose : M) (aq : F)
    (g : GhostFrameSt F M) (z : F × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) (.roNf aq)).run g)) :
    z.2.audit = { g.audit with slopeProbes := aq :: g.audit.slopeProbes } := by
  unfold ghostFrameImpl at hz
  simp only [StateT.run_mk] at hz
  obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

omit [Field F] in
/-- A direct `roE` query records exactly its candidate secret. -/
theorem ghostFrameImpl_audit_roE (mclose : M) (kq : F) (e : ℕ)
    (g : GhostFrameSt F M) (z : F × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) (.roE kq e)).run g)) :
    z.2.audit = { g.audit with roEProbes := kq :: g.audit.roEProbes } := by
  unfold ghostFrameImpl at hz
  simp only [StateT.run_mk] at hz
  obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

omit [Field F] in
/-- A direct `roId` query records exactly its candidate secret. -/
theorem ghostFrameImpl_audit_roId (mclose : M) (kq : F)
    (g : GhostFrameSt F M) (z : F × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) (.roId kq)).run g)) :
    z.2.audit = { g.audit with roIdProbes := kq :: g.audit.roIdProbes } := by
  unfold ghostFrameImpl at hz
  simp only [StateT.run_mk] at hz
  obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

/-! ## Audit monotonicity -/

omit [Field F] in
/-- **Audit lists only grow.** Every supported ghost step extends each of
the five audit lists by a suffix relation (in fact by at most one cons). -/
theorem ghostFrameImpl_audit_suffix_step (mclose : M) (op : FrameOp F M)
    (g : GhostFrameSt F M)
    (z : (frameSpec F M).Range op × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) op).run g)) :
    g.audit.roAProbes <:+ z.2.audit.roAProbes ∧
    g.audit.roEProbes <:+ z.2.audit.roEProbes ∧
    g.audit.roIdProbes <:+ z.2.audit.roIdProbes ∧
    g.audit.slopeProbes <:+ z.2.audit.slopeProbes ∧
    g.audit.honestSlopes <:+ z.2.audit.honestSlopes := by
  cases op with
  | spend m =>
      rcases ghostFrameImpl_audit_spend mclose m g z hz with h | ⟨v, h⟩ <;>
        simp [h, List.suffix_cons, List.suffix_refl]
  | close =>
      rcases ghostFrameImpl_audit_close mclose g z hz with h | ⟨v, h⟩ <;>
        simp [h, List.suffix_cons, List.suffix_refl]
  | nfAt i =>
      rcases ghostFrameImpl_audit_nfAt mclose i g z hz with h | ⟨v, h⟩ <;>
        simp [h, List.suffix_cons, List.suffix_refl]
  | roA kq i =>
      simp [ghostFrameImpl_audit_roA mclose kq i g z hz,
        List.suffix_cons, List.suffix_refl]
  | roX m =>
      simp [ghostFrameImpl_audit_roX mclose m g z hz, List.suffix_refl]
  | roNf aq =>
      simp [ghostFrameImpl_audit_roNf mclose aq g z hz,
        List.suffix_cons, List.suffix_refl]
  | roE kq e =>
      simp [ghostFrameImpl_audit_roE mclose kq e g z hz,
        List.suffix_cons, List.suffix_refl]
  | roId kq =>
      simp [ghostFrameImpl_audit_roId mclose kq g z hz,
        List.suffix_cons, List.suffix_refl]

omit [Field F] in
/-- The ghost leakage event, once raised, is preserved by every supported
ghost step. -/
theorem ghostFrameImpl_bad_monotone (mclose : M) (k : F) (op : FrameOp F M)
    (g : GhostFrameSt F M) (hbad : GhostLeakBad k g.audit)
    (z : (frameSpec F M).Range op × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) op).run g)) :
    GhostLeakBad k z.2.audit := by
  have hsuf := ghostFrameImpl_audit_suffix_step mclose op g z hz
  exact GhostLeakBad.mono hsuf.1 hsuf.2.1 hsuf.2.2.1 hsuf.2.2.2.1
    hsuf.2.2.2.2 hbad

omit [Field F] in
/-- Run-level bad-event monotonicity: an already-raised ghost leakage event
survives any full simulated ghost run. -/
theorem ghostFrameImpl_run_bad_monotone (mclose : M) (k : F) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (g : GhostFrameSt F M)
    (hbad : GhostLeakBad k g.audit)
    (z : α × GhostFrameSt F M)
    (hz : z ∈ support ((simulateQ (ghostFrameImpl mclose) oa).run g)) :
    GhostLeakBad k z.2.audit :=
  OracleComp.simulateQ_run_preserves_inv_of_query (ghostFrameImpl mclose)
    (fun s => GhostLeakBad k s.audit)
    (fun t s hs y hy => ghostFrameImpl_bad_monotone mclose k t s hs y hy)
    oa g hbad z hz

/-! ## Ghost-slope completeness (coupling invariant) -/

/-- Every materialized ghost slope is recorded in the ghost audit — the
ghost analogue of `FrameAuditComplete`, used by the real/ghost coupling to
keep the public nullifier namespace disjoint from the deferred honest
slopes. -/
def GhostSlopesComplete (g : GhostFrameSt F M) : Prop :=
  ∀ i v, g.ghostSlope i = some v → v ∈ g.audit.honestSlopes

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- The initial ghost state has no materialized ghost slopes. -/
theorem ghostSlopesComplete_init :
    GhostSlopesComplete (GhostFrameSt.init F M) := by
  intro i v h
  simp [GhostFrameSt.init] at h

omit [Field F] in
/-- `ghostTouch` preserves ghost-slope completeness: a fresh sample is
recorded, and cache hits were covered by the incoming invariant. -/
theorem ghostTouch_complete (gs : ℕ → Option F) (audit : GhostAudit F)
    (i : ℕ) (hg : ∀ j v, gs j = some v → v ∈ audit.honestSlopes)
    (q : (ℕ → Option F) × GhostAudit F)
    (hq : q ∈ support (ghostTouch gs audit i)) :
    ∀ j v, q.1 j = some v → v ∈ q.2.honestSlopes := by
  rcases ghostTouch_support gs audit i q hq with h | ⟨v, -, h⟩
  · subst h
    exact hg
  · subst h
    intro j w hjw
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self] at hjw
      have hvw := Option.some.inj hjw
      subst hvw
      exact List.mem_cons_self
    · rw [Function.update_of_ne hj] at hjw
      exact List.mem_cons_of_mem _ (hg j w hjw)

omit [Field F] in
/-- Every supported ghost step preserves ghost-slope completeness. -/
theorem ghostFrameImpl_ghostSlopesComplete (mclose : M) (op : FrameOp F M)
    (g : GhostFrameSt F M) (hg : GhostSlopesComplete g)
    (z : (frameSpec F M).Range op × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) op).run g)) :
    GhostSlopesComplete z.2 := by
  cases op with
  | spend m =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      by_cases hc : g.ideal.closed
      · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hg
      · rw [if_neg hc] at hz
        obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨q, hq, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ghostTouch_complete g.ghostSlope g.audit g.ideal.idx hg q hq
  | close =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      by_cases hc : g.ideal.closed
      · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hg
      · rw [if_neg hc] at hz
        obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨q, hq, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ghostTouch_complete g.ghostSlope g.audit g.ideal.idx hg q hq
  | nfAt i =>
      unfold ghostFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨q, hq, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ghostTouch_complete g.ghostSlope g.audit i hg q hq
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
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hg
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

omit [Field F] in
/-- Run-level ghost-slope completeness: it holds at every supported outcome
of a full simulated ghost run from a complete state (in particular from the
initial state). -/
theorem ghostFrameImpl_run_ghostSlopesComplete (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (g : GhostFrameSt F M)
    (hg : GhostSlopesComplete g)
    (z : α × GhostFrameSt F M)
    (hz : z ∈ support ((simulateQ (ghostFrameImpl mclose) oa).run g)) :
    GhostSlopesComplete z.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (ghostFrameImpl mclose)
    GhostSlopesComplete
    (fun t s hs y hy => ghostFrameImpl_ghostSlopesComplete mclose t s hs y hy)
    oa g hg z hz

/-! ## Support-wise audit length bounds -/

omit [Field F] in
/-- Per-step audit length accounting: each supported ghost step grows each
audit list by at most one, and only when the operation is classified by the
matching T7 budget channel (`isDirectRoAQuery`/`isDirectRoEQuery`/
`isDirectRoIdQuery`/`isDirectRoNfQuery`/`isSignalQuery`). -/
theorem ghostFrameImpl_audit_length_step (mclose : M) (op : FrameOp F M)
    (g : GhostFrameSt F M)
    (z : (frameSpec F M).Range op × GhostFrameSt F M)
    (hz : z ∈ support (((ghostFrameImpl mclose) op).run g)) :
    z.2.audit.roAProbes.length ≤ g.audit.roAProbes.length
        + (if isDirectRoAQuery op then 1 else 0) ∧
    z.2.audit.roEProbes.length ≤ g.audit.roEProbes.length
        + (if isDirectRoEQuery op then 1 else 0) ∧
    z.2.audit.roIdProbes.length ≤ g.audit.roIdProbes.length
        + (if isDirectRoIdQuery op then 1 else 0) ∧
    z.2.audit.slopeProbes.length ≤ g.audit.slopeProbes.length
        + (if isDirectRoNfQuery op then 1 else 0) ∧
    z.2.audit.honestSlopes.length ≤ g.audit.honestSlopes.length
        + (if isSignalQuery op then 1 else 0) := by
  cases op with
  | spend m =>
      rcases ghostFrameImpl_audit_spend mclose m g z hz with h | ⟨v, h⟩ <;>
        simp [h, isDirectRoAQuery, isDirectRoEQuery, isDirectRoIdQuery,
          isDirectRoNfQuery, isSignalQuery]
  | close =>
      rcases ghostFrameImpl_audit_close mclose g z hz with h | ⟨v, h⟩ <;>
        simp [h, isDirectRoAQuery, isDirectRoEQuery, isDirectRoIdQuery,
          isDirectRoNfQuery, isSignalQuery]
  | nfAt i =>
      rcases ghostFrameImpl_audit_nfAt mclose i g z hz with h | ⟨v, h⟩ <;>
        simp [h, isDirectRoAQuery, isDirectRoEQuery, isDirectRoIdQuery,
          isDirectRoNfQuery, isSignalQuery]
  | roA kq i =>
      simp [ghostFrameImpl_audit_roA mclose kq i g z hz, isDirectRoAQuery,
        isDirectRoEQuery, isDirectRoIdQuery, isDirectRoNfQuery, isSignalQuery]
  | roX m =>
      simp [ghostFrameImpl_audit_roX mclose m g z hz, isDirectRoAQuery,
        isDirectRoEQuery, isDirectRoIdQuery, isDirectRoNfQuery, isSignalQuery]
  | roNf aq =>
      simp [ghostFrameImpl_audit_roNf mclose aq g z hz, isDirectRoAQuery,
        isDirectRoEQuery, isDirectRoIdQuery, isDirectRoNfQuery, isSignalQuery]
  | roE kq e =>
      simp [ghostFrameImpl_audit_roE mclose kq e g z hz, isDirectRoAQuery,
        isDirectRoEQuery, isDirectRoIdQuery, isDirectRoNfQuery, isSignalQuery]
  | roId kq =>
      simp [ghostFrameImpl_audit_roId mclose kq g z hz, isDirectRoAQuery,
        isDirectRoEQuery, isDirectRoIdQuery, isDirectRoNfQuery, isSignalQuery]

/-- **Support induction threading an `IsQueryBoundP` certificate.** If every
supported handler step increases a state measure by at most one exactly on
`c`-classified queries, then every supported outcome of a full simulation
increases the measure by at most the `c`-query budget. -/
theorem support_measure_le_of_isQueryBoundP
    {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (μ : σ → ℕ) (c : ι → Bool)
    (hstep : ∀ (t : ι) (s : σ) (z : spec.Range t × σ),
      z ∈ support ((impl t).run s) → μ z.2 ≤ μ s + (if c t then 1 else 0))
    {α : Type} (oa : OracleComp spec α) {n : ℕ}
    (hb : OracleComp.IsQueryBoundP oa (fun t => c t = true) n)
    (s : σ) (z : α × σ)
    (hz : z ∈ support ((simulateQ impl oa).run s)) :
    μ z.2 ≤ μ s + n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact Nat.le_add_right _ _
  | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      by_cases hc : c t = true
      · have h1 : μ p.2 ≤ μ s + 1 := by simpa [hc] using hstep t s p hp
        have hn : 0 < n := by
          rcases hb.1 with h | h
          · exact absurd hc h
          · exact h
        have h2 : μ z.2 ≤ μ p.2 + (n - 1) :=
          ih p.1 (by simpa [hc] using hb.2 p.1) p.2 hz
        omega
      · have h1 : μ p.2 ≤ μ s := by simpa [hc] using hstep t s p hp
        have h2 : μ z.2 ≤ μ p.2 + n :=
          ih p.1 (by simpa [hc] using hb.2 p.1) p.2 hz
        omega

omit [Field F] in
/-- **Support-wise audit length bounds for the ghost run.** For a
query-bounded FRAME adversary, every supported outcome of the ghost run
from the initial state has per-channel audit lists bounded by the matching
structural budgets: `|roAProbes| ≤ qA`, `|roEProbes| ≤ qE`,
`|roIdProbes| ≤ qId`, `|slopeProbes| ≤ qNf`, `|honestSlopes| ≤ qSig`. -/
theorem ghostFrameImpl_run_audit_bounds (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (cm : F)
    (z : Evidence F × GhostFrameSt F M)
    (hz : z ∈ support ((simulateQ (ghostFrameImpl mclose) (A cm)).run
      (GhostFrameSt.init F M))) :
    z.2.audit.roAProbes.length ≤ qb.qA ∧
    z.2.audit.roEProbes.length ≤ qb.qE ∧
    z.2.audit.roIdProbes.length ≤ qb.qId ∧
    z.2.audit.slopeProbes.length ≤ qb.qNf ∧
    z.2.audit.honestSlopes.length ≤ qb.qSig := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := support_measure_le_of_isQueryBoundP (ghostFrameImpl mclose)
      (fun g => g.audit.roAProbes.length) isDirectRoAQuery
      (fun t s z' hz' => (ghostFrameImpl_audit_length_step mclose t s z' hz').1)
      (A cm) (qb.roA_bound cm) (GhostFrameSt.init F M) z hz
    simpa [GhostFrameSt.init, GhostAudit.init] using h
  · have h := support_measure_le_of_isQueryBoundP (ghostFrameImpl mclose)
      (fun g => g.audit.roEProbes.length) isDirectRoEQuery
      (fun t s z' hz' =>
        (ghostFrameImpl_audit_length_step mclose t s z' hz').2.1)
      (A cm) (qb.roE_bound cm) (GhostFrameSt.init F M) z hz
    simpa [GhostFrameSt.init, GhostAudit.init] using h
  · have h := support_measure_le_of_isQueryBoundP (ghostFrameImpl mclose)
      (fun g => g.audit.roIdProbes.length) isDirectRoIdQuery
      (fun t s z' hz' =>
        (ghostFrameImpl_audit_length_step mclose t s z' hz').2.2.1)
      (A cm) (qb.roId_bound cm) (GhostFrameSt.init F M) z hz
    simpa [GhostFrameSt.init, GhostAudit.init] using h
  · have h := support_measure_le_of_isQueryBoundP (ghostFrameImpl mclose)
      (fun g => g.audit.slopeProbes.length) isDirectRoNfQuery
      (fun t s z' hz' =>
        (ghostFrameImpl_audit_length_step mclose t s z' hz').2.2.2.1)
      (A cm) (qb.roNf_bound cm) (GhostFrameSt.init F M) z hz
    simpa [GhostFrameSt.init, GhostAudit.init] using h
  · have h := support_measure_le_of_isQueryBoundP (ghostFrameImpl mclose)
      (fun g => g.audit.honestSlopes.length) isSignalQuery
      (fun t s z' hz' =>
        (ghostFrameImpl_audit_length_step mclose t s z' hz').2.2.2.2)
      (A cm) (qb.signal_bound cm) (GhostFrameSt.init F M) z hz
    simpa [GhostFrameSt.init, GhostAudit.init] using h

omit [Field F] in
/-- The same audit length bounds over the support of the complete paired
ghost run (public commitment sampled inside). -/
theorem ghostFrameRun_audit_bounds (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (z : Evidence F × GhostFrameSt F M)
    (hz : z ∈ support (ghostFrameRun mclose A)) :
    z.2.audit.roAProbes.length ≤ qb.qA ∧
    z.2.audit.roEProbes.length ≤ qb.qE ∧
    z.2.audit.roIdProbes.length ≤ qb.qId ∧
    z.2.audit.slopeProbes.length ≤ qb.qNf ∧
    z.2.audit.honestSlopes.length ≤ qb.qSig := by
  unfold ghostFrameRun at hz
  obtain ⟨cm, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  exact ghostFrameImpl_run_audit_bounds mclose A qb cm z hz

omit [Field F] in
/-- Aggregate direct-secret probe bound over the paired ghost run: the
combined candidate-secret list is bounded by `qA + qE + qId`, the T7
direct-probe numerator contribution. -/
theorem ghostFrameRun_secretProbes_length (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (z : Evidence F × GhostFrameSt F M)
    (hz : z ∈ support (ghostFrameRun mclose A)) :
    z.2.audit.secretProbes.length ≤ qb.qA + qb.qE + qb.qId := by
  obtain ⟨hA, hE, hId, -, -⟩ := ghostFrameRun_audit_bounds mclose A qb z hz
  simp only [GhostAudit.secretProbes, List.length_append]
  omega

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.GhostLeakBad.mono
#print axioms Zkpc.Games.ghostTouch_support
#print axioms Zkpc.Games.evalDist_ghostTouch_bind_const
#print axioms Zkpc.Games.map_run_simulateQ_evalDist_eq_of_step
#print axioms Zkpc.Games.ghostFrameImpl_erase_step
#print axioms Zkpc.Games.ghostFrameImpl_run_erase
#print axioms Zkpc.Games.ghostFrameImpl_run_output_erase
#print axioms Zkpc.Games.fst_map_ghostFrameRun
#print axioms Zkpc.Games.ghostFrameRun_erase
#print axioms Zkpc.Games.ghostFrameEvidence_evalDist_eq
#print axioms Zkpc.Games.ghostFrameImpl_audit_suffix_step
#print axioms Zkpc.Games.ghostFrameImpl_bad_monotone
#print axioms Zkpc.Games.ghostFrameImpl_run_bad_monotone
#print axioms Zkpc.Games.ghostSlopesComplete_init
#print axioms Zkpc.Games.ghostTouch_complete
#print axioms Zkpc.Games.ghostFrameImpl_ghostSlopesComplete
#print axioms Zkpc.Games.ghostFrameImpl_run_ghostSlopesComplete
#print axioms Zkpc.Games.ghostFrameImpl_audit_length_step
#print axioms Zkpc.Games.support_measure_le_of_isQueryBoundP
#print axioms Zkpc.Games.ghostFrameImpl_run_audit_bounds
#print axioms Zkpc.Games.ghostFrameRun_audit_bounds
#print axioms Zkpc.Games.ghostFrameRun_secretProbes_length
