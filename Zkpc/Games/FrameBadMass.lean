import Zkpc.Games.FrameGhost
import Zkpc.Games.FrameGhostBounds

/-!
# The k-averaged ghost bad-mass bound (Spec.md §7 T7, bad-mass lane)

The corrected T7 accounting compares the real FRAME run against the ghost
run of `Zkpc.Games.FrameGhost` and pays the *k-averaged* probability of the
ghost leakage event `GhostLeakBad`. This file proves that budget, with the
honest secret drawn uniformly **after** the entirely `k`-free ghost run. The
completed leakage bound splits as

* **direct secret probes** — `k` lands in the recorded `roA`/`roE`/`roId`
  candidate list: at most `(qA + qE + qId)/|F|` (deferred counting, via
  `ghostFrameRun_secret_probe_bound` from `Zkpc.Games.FrameGhostBounds`);
* **slope-preimage hits** (`SlopeHit`) — some recorded `H_nf` probe equals
  some ghost honest slope: at most `qNf · qSig / |F|`;
* **slope collisions** (`SlopeCollision`) — two ghost honest slopes agree:
  at most `qSig² / |F|`.

The direct piece is elementary because the ghost run never consults `k`.
The two slope pieces need the *deferral* of the ghost slope draws: each
honest slope is sampled fresh-uniform and is never read back by the
handler (the ghost ornament is write-only), so its draw commutes past the
rest of the run. This is formalized in two moves:

1. **Value erasure** (`skelFrameImpl`): the ghost slope *cache values* are
   replaced by the placeholder `0` — only the some/none pattern of the
   cache is ever consulted (`ghostTouch` matches on it but discards the
   stored value), so the erased handler simulates the ghost handler
   exactly after projecting the cache values away
   (`skelFrameImpl_erase_step` / `probEvent_audit_ghost_eq_skel` via the
   generic transport `map_run_simulateQ_evalDist_eq_of_step`). After
   erasure, the *only* place slope values persist is the recorded
   `honestSlopes` audit list, which nothing reads during the run.
2. **Slope-tape substrate**: fresh-tape counting kernels, tape commutation,
   and the value-erased `skelFrameImpl` isolate slope values in the write-only
   audit. The adaptive induction later in this file closes both slope masses
   and yields `ghostFrameRun_leakBad_le` with no additional hypothesis.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## Components of the ghost leakage event -/

/-- Slope-preimage component of `GhostLeakBad`: some recorded direct
`H_nf` probe equals some recorded ghost honest slope. -/
def SlopeHit (a : GhostAudit F) : Prop :=
  ∃ s ∈ a.slopeProbes, s ∈ a.honestSlopes

/-- Collision component of `GhostLeakBad`: two recorded ghost honest
slopes coincide. -/
def SlopeCollision (a : GhostAudit F) : Prop :=
  ¬ a.honestSlopes.Nodup

instance (a : GhostAudit F) : Decidable (SlopeHit a) := by
  unfold SlopeHit; infer_instance

instance (a : GhostAudit F) : Decidable (SlopeCollision a) := by
  unfold SlopeCollision; infer_instance

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- The ghost leakage event is definitionally the three-way disjunction of
the deferred-secret membership and the two named slope components. -/
theorem ghostLeakBad_iff (k : F) (a : GhostAudit F) :
    GhostLeakBad k a ↔
      k ∈ a.secretProbes ∨ SlopeHit a ∨ SlopeCollision a := Iff.rfl

/-! ## Probability bridges -/

/-- Bridge between the Boolean-output and event forms of a bad-event
probability: deciding a predicate after a computation outputs `true`
exactly with the event's probability. -/
theorem probOutput_true_bind_decide_eq {α : Type} (oa : ProbComp α)
    (P : α → Prop) [DecidablePred P] :
    Pr[= true | oa >>= fun a => pure (decide (P a))] = Pr[P | oa] := by
  rw [← probEvent_eq_eq_probOutput]
  rw [show (fun a => (pure (decide (P a)) : ProbComp Bool))
      = pure ∘ (fun a => decide (P a)) from rfl]
  rw [probEvent_bind_pure_comp]
  exact probEvent_ext fun a _ => by simp

/-- Appending an unread uniform draw after a computation does not change
the probability of an event on the first component. -/
theorem probEvent_bind_pair_uniform_fst {α : Type} (W : ProbComp α)
    (P : α → Prop) [DecidablePred P] :
    Pr[fun w : α × F => P w.1 |
        W >>= fun z => ($ᵗ F) >>= fun k => pure (z, k)]
      = Pr[P | W] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun z => ?_
  have hinner : Pr[fun w : α × F => P w.1 |
      ($ᵗ F) >>= fun k => pure (z, k)] = if P z then 1 else 0 := by
    rw [show (fun k : F => (pure (z, k) : ProbComp (α × F)))
        = pure ∘ (fun k : F => (z, k)) from rfl]
    rw [probEvent_bind_pure_comp]
    by_cases hz : P z <;> simp [Function.comp_def, hz,
      probEvent_true_eq_sub, probFailure_uniformSample]
  rw [hinner]
  split_ifs <;> simp

/-! ## Deferred-tape counting kernels

`drawList ($ᵗ F) m` is the deferred ghost-slope tape: `m` independent
uniform field elements. The two kernels below are the leaf counting facts
of the slope-preimage and collision masses. -/

variable [Fintype F]

/-- A fixed field element lands in a fresh uniform tape of length `m` with
probability at most `m / |F|`. -/
theorem probEvent_drawList_mem_le (w : F) (m : ℕ) :
    Pr[fun vs : List F => w ∈ vs | drawList ($ᵗ F) m]
      ≤ (m : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  induction m with
  | zero =>
      simp [drawList]
  | succ m ih =>
      rw [show drawList ($ᵗ F) (m + 1)
          = (($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
              pure (v :: ws)) from rfl]
      rw [probEvent_bind_eq_tsum]
      have hstep : ∀ v : F,
          Pr[= v | ($ᵗ F)] * Pr[fun vs : List F => w ∈ vs |
              drawList ($ᵗ F) m >>= fun ws => pure (v :: ws)]
            ≤ Pr[= v | ($ᵗ F)] * ((if w = v then 1 else 0)
                + (m : ENNReal) * (Fintype.card F : ENNReal)⁻¹) := by
        intro v
        refine mul_le_mul_left' ?_ _
        rw [show (fun ws : List F => (pure (v :: ws) : ProbComp (List F)))
            = pure ∘ (fun ws : List F => v :: ws) from rfl]
        rw [probEvent_bind_pure_comp]
        rw [probEvent_ext (q := fun ws : List F => w = v ∨ w ∈ ws)
          fun ws _ => by simp [List.mem_cons]]
        refine le_trans (probEvent_or_le _ _ _) (add_le_add ?_ ih)
        by_cases hv : w = v
        · rw [if_pos hv]
          exact probEvent_le_one
        · rw [if_neg hv]
          rw [probEvent_ext (q := fun _ : List F => False)
            fun ws _ => iff_of_false hv not_false]
          rw [probEvent_eq_tsum_ite]
          simp
      refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
      simp only [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      have h1 : (∑' v : F, Pr[= v | ($ᵗ F)] * (if w = v then 1 else 0))
          = (Fintype.card F : ENNReal)⁻¹ := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [tsum_eq_single w (fun v hv => if_neg fun h => hv h.symm)]
        rw [if_pos rfl, probOutput_uniformSample]
      rw [h1]
      calc (Fintype.card F : ENNReal)⁻¹
            + (∑' v : F, Pr[= v | ($ᵗ F)])
              * ((m : ENNReal) * (Fintype.card F : ENNReal)⁻¹)
          ≤ (Fintype.card F : ENNReal)⁻¹
            + 1 * ((m : ENNReal) * (Fintype.card F : ENNReal)⁻¹) := by
            gcongr
            exact tsum_probOutput_le_one
        _ = ((m + 1 : ℕ) : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
            rw [one_mul]
            push_cast
            ring

/-- Some element of a fixed list lands in a fresh uniform tape of length
`m` with probability at most `m · |ps| / |F|`. -/
theorem probEvent_drawList_exists_mem_le (ps : List F) (m : ℕ) :
    Pr[fun vs : List F => ∃ q ∈ ps, q ∈ vs | drawList ($ᵗ F) m]
      ≤ ((m * ps.length : ℕ) : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  induction ps with
  | nil =>
      rw [probEvent_ext (q := fun _ : List F => False)
        fun vs _ => by simp]
      simpa using (le_refl (0 : ENNReal))
  | cons a ps ih =>
      rw [probEvent_ext
        (q := fun vs : List F => a ∈ vs ∨ ∃ q ∈ ps, q ∈ vs)
        fun vs _ => by
          constructor
          · rintro ⟨q, hq, hqv⟩
            rcases List.mem_cons.1 hq with rfl | hq
            · exact Or.inl hqv
            · exact Or.inr ⟨q, hq, hqv⟩
          · rintro (h | ⟨q, hq, hqv⟩)
            · exact ⟨a, List.mem_cons_self, h⟩
            · exact ⟨q, List.mem_cons_of_mem _ hq, hqv⟩]
      refine le_trans (probEvent_or_le _ _ _)
        (le_trans (add_le_add (probEvent_drawList_mem_le a m) ih) ?_)
      rw [← add_mul]
      refine mul_le_mul_right' (le_of_eq ?_) _
      norm_cast
      simp [Nat.mul_add, Nat.add_comm]

/-- A fresh uniform tape of length `m` repeats a value with probability at
most `m² / |F|` (a generous birthday bound). -/
theorem probEvent_drawList_not_nodup_le (m : ℕ) :
    Pr[fun vs : List F => ¬ vs.Nodup | drawList ($ᵗ F) m]
      ≤ ((m * m : ℕ) : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  induction m with
  | zero =>
      simp [drawList]
  | succ m ih =>
      rw [show drawList ($ᵗ F) (m + 1)
          = (($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
              pure (v :: ws)) from rfl]
      rw [probEvent_bind_eq_tsum]
      have hstep : ∀ v : F,
          Pr[= v | ($ᵗ F)] * Pr[fun vs : List F => ¬ vs.Nodup |
              drawList ($ᵗ F) m >>= fun ws => pure (v :: ws)]
            ≤ Pr[= v | ($ᵗ F)] *
                ((m : ENNReal) * (Fintype.card F : ENNReal)⁻¹
                  + ((m * m : ℕ) : ENNReal) * (Fintype.card F : ENNReal)⁻¹) := by
        intro v
        refine mul_le_mul_left' ?_ _
        rw [show (fun ws : List F => (pure (v :: ws) : ProbComp (List F)))
            = pure ∘ (fun ws : List F => v :: ws) from rfl]
        rw [probEvent_bind_pure_comp]
        rw [probEvent_ext (q := fun ws : List F => v ∈ ws ∨ ¬ ws.Nodup)
          fun ws _ => by
            simp only [Function.comp_apply, List.nodup_cons, not_and_or,
              not_not]]
        exact le_trans (probEvent_or_le _ _ _)
          (add_le_add (probEvent_drawList_mem_le v m) ih)
      refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
      rw [ENNReal.tsum_mul_right]
      calc (∑' v : F, Pr[= v | ($ᵗ F)]) *
            ((m : ENNReal) * (Fintype.card F : ENNReal)⁻¹
              + ((m * m : ℕ) : ENNReal) * (Fintype.card F : ENNReal)⁻¹)
          ≤ 1 * ((m : ENNReal) * (Fintype.card F : ENNReal)⁻¹
              + ((m * m : ℕ) : ENNReal) * (Fintype.card F : ENNReal)⁻¹) := by
            gcongr
            exact tsum_probOutput_le_one
        _ = ((m + m * m : ℕ) : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
            rw [one_mul, ← add_mul]
            push_cast
            ring
        _ ≤ (((m + 1) * (m + 1) : ℕ) : ENNReal) *
              (Fintype.card F : ENNReal)⁻¹ := by
            refine mul_le_mul_right' (Nat.cast_le.2 ?_) _
            nlinarith

/-! ## Tape commutation -/

/-- One more fresh draw appended to the tape fuses into a longer tape:
drawing `m` values and then one more is the length-`m + 1` tape. -/
theorem evalDist_drawList_succ_swap {β : Type} (m : ℕ)
    (k : List F → ProbComp β) :
    𝒟[drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun v => k (v :: vs)]
      = 𝒟[drawList ($ᵗ F) (m + 1) >>= k] := by
  rw [show drawList ($ᵗ F) (m + 1)
      = (($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
          pure (v :: ws)) from rfl]
  simp only [bind_assoc, pure_bind]
  exact OracleComp.DeferredSampling.evalDist_bind_comm
    (drawList ($ᵗ F) m) ($ᵗ F) fun vs v => k (v :: vs)

/-- A tape-independent oracle step commutes past the front tape: to bound
an event of a run of the form `tape >>= (step >>= continuation)` where the
step does not read the tape, it suffices to bound each continuation with
the tape re-drawn in front. -/
theorem probEvent_drawList_swap_le {γ β : Type} (m : ℕ) (core : ProbComp γ)
    (cont : γ → List F → ProbComp β) (P : β → Prop) (B : ENNReal)
    (h : ∀ c ∈ support core,
      Pr[P | drawList ($ᵗ F) m >>= fun vs => cont c vs] ≤ B) :
    Pr[P | drawList ($ᵗ F) m >>= fun vs => core >>= fun c => cont c vs]
      ≤ B := by
  have hswap := OracleComp.DeferredSampling.evalDist_bind_comm
    (drawList ($ᵗ F) m) core (fun vs c => cont c vs)
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) hswap)) ?_
  exact probEvent_bind_le_of_forall_le h

/-- A tape-independent oracle step followed by one fresh ghost-slope draw
commutes past the front tape, fusing the fresh draw into a longer tape. -/
theorem probEvent_drawList_swap_fresh_le {γ β : Type} (m : ℕ)
    (core : ProbComp γ) (cont : γ → List F → ProbComp β) (P : β → Prop)
    (B : ENNReal)
    (h : ∀ c ∈ support core,
      Pr[P | drawList ($ᵗ F) (m + 1) >>= fun vs => cont c vs] ≤ B) :
    Pr[P | drawList ($ᵗ F) m >>= fun vs => core >>= fun c =>
        ($ᵗ F) >>= fun v => cont c (v :: vs)] ≤ B := by
  have hswap := OracleComp.DeferredSampling.evalDist_bind_comm
    (drawList ($ᵗ F) m) core
    (fun vs c => ($ᵗ F) >>= fun v => cont c (v :: vs))
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) hswap)) ?_
  refine probEvent_bind_le_of_forall_le fun c hc => ?_
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_drawList_succ_swap m (cont c)))) ?_
  exact h c hc

/-! ## The value-erased skeleton handler

`ghostTouch` matches on the cache entry but never reads the stored slope
value, so replacing every stored value by the placeholder `0` leaves the
whole simulation unchanged after projecting the cache values away. In the
erased handler the only surviving occurrences of the sampled slope values
are the write-only `honestSlopes` audit records — exactly the shape the
slope-tape induction needs. -/

/-- Replace every materialized ghost slope cache value by `0`, keeping the
some/none pattern, the ideal state, and the audit (including the recorded
`honestSlopes` values) intact. -/
def eraseSlopeValues (g : GhostFrameSt F M) : GhostFrameSt F M :=
  ⟨g.ideal, fun i => (g.ghostSlope i).map fun _ => (0 : F), g.audit⟩

omit [DecidableEq F] [SampleableType F] [DecidableEq M] in
@[simp] theorem eraseSlopeValues_ideal (g : GhostFrameSt F M) :
    (eraseSlopeValues g).ideal = g.ideal := rfl

omit [DecidableEq F] [SampleableType F] [DecidableEq M] in
@[simp] theorem eraseSlopeValues_audit (g : GhostFrameSt F M) :
    (eraseSlopeValues g).audit = g.audit := rfl

omit [DecidableEq F] [SampleableType F] [DecidableEq M] in
/-- Erasure fixes the initial ghost state. -/
@[simp] theorem eraseSlopeValues_init :
    eraseSlopeValues (GhostFrameSt.init F M) = GhostFrameSt.init F M := rfl

/-- Ghost-slope materialization with the placeholder value `0` cached in
place of the sampled slope; the sampled value is still recorded in the
audit. This is `ghostTouch` after cache-value erasure. -/
def skelTouch (gs : ℕ → Option F) (audit : GhostAudit F) (i : ℕ) :
    ProbComp ((ℕ → Option F) × GhostAudit F) :=
  match gs i with
  | some _ => pure (gs, audit)
  | none => do
      let v ← ($ᵗ F)
      pure (Function.update gs i (some (0 : F)),
        { audit with honestSlopes := v :: audit.honestSlopes })

omit [Field F] [DecidableEq F] in
/-- Cache-hit branch of `ghostTouch`. -/
theorem ghostTouch_eq_of_some {gs : ℕ → Option F} {audit : GhostAudit F}
    {i : ℕ} {w : F} (h : gs i = some w) :
    ghostTouch gs audit i = pure (gs, audit) := by
  unfold ghostTouch
  rw [h]

omit [Field F] [DecidableEq F] in
/-- Cache-miss branch of `ghostTouch`. -/
theorem ghostTouch_eq_of_none {gs : ℕ → Option F} {audit : GhostAudit F}
    {i : ℕ} (h : gs i = none) :
    ghostTouch gs audit i = (($ᵗ F) >>= fun v =>
      pure (Function.update gs i (some v),
        { audit with honestSlopes := v :: audit.honestSlopes })) := by
  unfold ghostTouch
  rw [h]

omit [DecidableEq F] in
/-- Cache-hit branch of `skelTouch`. -/
theorem skelTouch_eq_of_some {gs : ℕ → Option F} {audit : GhostAudit F}
    {i : ℕ} {w : F} (h : gs i = some w) :
    skelTouch gs audit i = pure (gs, audit) := by
  unfold skelTouch
  rw [h]

omit [DecidableEq F] in
/-- Cache-miss branch of `skelTouch`. -/
theorem skelTouch_eq_of_none {gs : ℕ → Option F} {audit : GhostAudit F}
    {i : ℕ} (h : gs i = none) :
    skelTouch gs audit i = (($ᵗ F) >>= fun v =>
      pure (Function.update gs i (some (0 : F)),
        { audit with honestSlopes := v :: audit.honestSlopes })) := by
  unfold skelTouch
  rw [h]

/-- The value-erased ghost handler: identical to `ghostFrameImpl` except
that `ghostTouch` is replaced by `skelTouch`, so the ghost slope cache
stores only the placeholder `0`. Answers, ideal-state updates, and audit
records are untouched. -/
def skelFrameImpl (mclose : M) :
    QueryImpl.Stateful unifSpec (frameSpec F M) (GhostFrameSt F M)
  | .spend m => StateT.mk fun g =>
      if g.ideal.closed then pure (none, g)
      else do
        let p ← emitIdealSignal m g.ideal
        let q ← skelTouch g.ghostSlope g.audit g.ideal.idx
        pure (some p.1, ⟨p.2, q.1, q.2⟩)
  | .close => StateT.mk fun g =>
      if g.ideal.closed then pure (none, g)
      else do
        let p ← emitIdealSignal mclose g.ideal
        let q ← skelTouch g.ghostSlope g.audit g.ideal.idx
        pure (some p.1, ⟨{ p.2 with closed := true }, q.1, q.2⟩)
  | .nfAt i => StateT.mk fun g => do
      let p ← lazyRO g.ideal.honestNf i
      let q ← skelTouch g.ghostSlope g.audit i
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

omit [SampleableType F] [DecidableEq M] in
/-- Erasing an updated ghost slope cache is updating the erased cache with
the placeholder. -/
theorem eraseSlopeValues_update (gs : ℕ → Option F) (i : ℕ) (v : F) :
    (fun j => (Function.update gs i (some v) j).map fun _ => (0 : F))
      = Function.update (fun j => (gs j).map fun _ => (0 : F)) i
          (some (0 : F)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

/-- **Per-step value erasure.** Projecting the ghost slope cache values
away after one ghost step gives exactly the distribution of the erased
handler's step from the erased state: the stored value is never read, and
the audit (where the sampled value survives) is preserved verbatim. -/
theorem skelFrameImpl_erase_step (mclose : M) (op : FrameOp F M)
    (g : GhostFrameSt F M) :
    𝒟[Prod.map id eraseSlopeValues <$> ((ghostFrameImpl mclose) op).run g] =
      𝒟[((skelFrameImpl mclose) op).run (eraseSlopeValues g)] := by
  cases op with
  | spend m =>
      unfold ghostFrameImpl skelFrameImpl
      simp only [StateT.run_mk, eraseSlopeValues_ideal]
      by_cases hc : g.ideal.closed
      · simp [hc, Prod.map]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind, map_pure,
          Prod.map, id_eq]
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left
          (emitIdealSignal m g.ideal) _ _ fun p => ?_
        rcases hgs : g.ghostSlope g.ideal.idx with _ | w
        · rw [ghostTouch_eq_of_none hgs,
            skelTouch_eq_of_none
              (show (eraseSlopeValues g).ghostSlope g.ideal.idx = none by
                show (g.ghostSlope g.ideal.idx).map _ = none
                rw [hgs]; rfl)]
          simp only [bind_assoc, pure_bind]
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left
            ($ᵗ F) _ _ fun v => ?_
          rw [show eraseSlopeValues
              (⟨p.2, Function.update g.ghostSlope g.ideal.idx (some v),
                { g.audit with honestSlopes := v :: g.audit.honestSlopes }⟩ :
                  GhostFrameSt F M)
              = ⟨p.2, Function.update
                  ((eraseSlopeValues g).ghostSlope) g.ideal.idx
                  (some (0 : F)),
                { g.audit with honestSlopes := v :: g.audit.honestSlopes }⟩
            from by
              cases g
              simp [eraseSlopeValues, eraseSlopeValues_update]]
          simp [eraseSlopeValues]
        · rw [ghostTouch_eq_of_some hgs,
            skelTouch_eq_of_some
              (show (eraseSlopeValues g).ghostSlope g.ideal.idx
                  = some (0 : F) by
                show (g.ghostSlope g.ideal.idx).map _ = some 0
                rw [hgs]; rfl)]
          simp only [pure_bind]
          rfl
  | close =>
      unfold ghostFrameImpl skelFrameImpl
      simp only [StateT.run_mk, eraseSlopeValues_ideal]
      by_cases hc : g.ideal.closed
      · simp [hc, Prod.map]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind, map_pure,
          Prod.map, id_eq]
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left
          (emitIdealSignal mclose g.ideal) _ _ fun p => ?_
        rcases hgs : g.ghostSlope g.ideal.idx with _ | w
        · rw [ghostTouch_eq_of_none hgs,
            skelTouch_eq_of_none
              (show (eraseSlopeValues g).ghostSlope g.ideal.idx = none by
                show (g.ghostSlope g.ideal.idx).map _ = none
                rw [hgs]; rfl)]
          simp only [bind_assoc, pure_bind]
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left
            ($ᵗ F) _ _ fun v => ?_
          rw [show eraseSlopeValues
              (⟨{ p.2 with closed := true },
                Function.update g.ghostSlope g.ideal.idx (some v),
                { g.audit with honestSlopes := v :: g.audit.honestSlopes }⟩ :
                  GhostFrameSt F M)
              = ⟨{ p.2 with closed := true }, Function.update
                  ((eraseSlopeValues g).ghostSlope) g.ideal.idx
                  (some (0 : F)),
                { g.audit with honestSlopes := v :: g.audit.honestSlopes }⟩
            from by
              cases g
              simp [eraseSlopeValues, eraseSlopeValues_update]]
          simp [eraseSlopeValues]
        · rw [ghostTouch_eq_of_some hgs,
            skelTouch_eq_of_some
              (show (eraseSlopeValues g).ghostSlope g.ideal.idx
                  = some (0 : F) by
                show (g.ghostSlope g.ideal.idx).map _ = some 0
                rw [hgs]; rfl)]
          simp only [pure_bind]
          rfl
  | nfAt i =>
      unfold ghostFrameImpl skelFrameImpl
      simp only [StateT.run_mk, eraseSlopeValues_ideal, map_bind, map_pure,
        Prod.map, id_eq]
      refine OracleComp.DeferredSampling.evalDist_bind_congr_left
        (lazyRO g.ideal.honestNf i) _ _ fun p => ?_
      rcases hgs : g.ghostSlope i with _ | w
      · rw [ghostTouch_eq_of_none hgs,
          skelTouch_eq_of_none
            (show (eraseSlopeValues g).ghostSlope i = none by
              show (g.ghostSlope i).map _ = none
              rw [hgs]; rfl)]
        simp only [bind_assoc, pure_bind]
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left
          ($ᵗ F) _ _ fun v => ?_
        rw [show eraseSlopeValues
            (⟨{ g.ideal with honestNf := p.2 },
              Function.update g.ghostSlope i (some v),
              { g.audit with honestSlopes := v :: g.audit.honestSlopes }⟩ :
                GhostFrameSt F M)
            = ⟨{ g.ideal with honestNf := p.2 }, Function.update
                ((eraseSlopeValues g).ghostSlope) i (some (0 : F)),
              { g.audit with honestSlopes := v :: g.audit.honestSlopes }⟩
          from by
            cases g
            simp [eraseSlopeValues, eraseSlopeValues_update]]
        simp [eraseSlopeValues]
      · rw [ghostTouch_eq_of_some hgs,
          skelTouch_eq_of_some
            (show (eraseSlopeValues g).ghostSlope i = some (0 : F) by
              show (g.ghostSlope i).map _ = some 0
              rw [hgs]; rfl)]
        simp only [pure_bind]
        rfl
  | roA kq i =>
      unfold ghostFrameImpl skelFrameImpl
      simp only [StateT.run_mk, eraseSlopeValues_ideal, map_bind, map_pure,
        Prod.map, id_eq]
      rfl
  | roX m =>
      unfold ghostFrameImpl skelFrameImpl
      simp only [StateT.run_mk, eraseSlopeValues_ideal, map_bind, map_pure,
        Prod.map, id_eq]
      rfl
  | roNf aq =>
      unfold ghostFrameImpl skelFrameImpl
      simp only [StateT.run_mk, eraseSlopeValues_ideal, map_bind, map_pure,
        Prod.map, id_eq]
      rfl
  | roE kq e =>
      unfold ghostFrameImpl skelFrameImpl
      simp only [StateT.run_mk, eraseSlopeValues_ideal, map_bind, map_pure,
        Prod.map, id_eq]
      rfl
  | roId kq =>
      unfold ghostFrameImpl skelFrameImpl
      simp only [StateT.run_mk, eraseSlopeValues_ideal, map_bind, map_pure,
        Prod.map, id_eq]
      rfl

/-- **Full-run value erasure.** The ghost run and the erased run from the
erased start state agree in distribution after projecting the ghost slope
cache values away. -/
theorem skelFrameImpl_run_erase (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (g : GhostFrameSt F M) :
    𝒟[Prod.map id eraseSlopeValues <$>
        (simulateQ (ghostFrameImpl mclose) oa).run g] =
      𝒟[(simulateQ (skelFrameImpl mclose) oa).run (eraseSlopeValues g)] :=
  map_run_simulateQ_evalDist_eq_of_step (ghostFrameImpl mclose)
    (skelFrameImpl mclose) eraseSlopeValues
    (skelFrameImpl_erase_step mclose) oa g

/-- Audit events transfer between the ghost run and the erased run:
erasure preserves the audit verbatim. -/
theorem probEvent_audit_ghost_eq_skel (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (g : GhostFrameSt F M)
    (P : GhostAudit F → Prop) :
    Pr[fun z : α × GhostFrameSt F M => P z.2.audit |
        (simulateQ (ghostFrameImpl mclose) oa).run g]
      = Pr[fun z : α × GhostFrameSt F M => P z.2.audit |
          (simulateQ (skelFrameImpl mclose) oa).run (eraseSlopeValues g)] := by
  have h1 : Pr[fun z : α × GhostFrameSt F M => P z.2.audit |
      (simulateQ (ghostFrameImpl mclose) oa).run g]
      = Pr[fun z : α × GhostFrameSt F M => P z.2.audit |
          Prod.map id eraseSlopeValues <$>
            (simulateQ (ghostFrameImpl mclose) oa).run g] := by
    rw [map_eq_bind_pure_comp, probEvent_bind_pure_comp]
    exact probEvent_ext fun z _ => Iff.rfl
  rw [h1]
  exact probEvent_congr' (fun _ _ => Iff.rfl)
    (skelFrameImpl_run_erase mclose oa g)

/-! ## The slope-tape induction -/

/-- Replace the recorded honest-slope list of a ghost state, keeping
everything else. Feeding this a fresh uniform tape is the deferred-slope
form of a run start state. -/
def GhostFrameSt.withSlopes (g : GhostFrameSt F M) (vs : List F) :
    GhostFrameSt F M :=
  ⟨g.ideal, g.ghostSlope,
    ⟨g.audit.roAProbes, g.audit.roEProbes, g.audit.roIdProbes,
      g.audit.slopeProbes, vs⟩⟩

section WithSlopesSimp

omit [DecidableEq F] [SampleableType F] [DecidableEq M]

@[simp] theorem withSlopes_ideal (g : GhostFrameSt F M) (vs : List F) :
    (g.withSlopes vs).ideal = g.ideal := rfl

@[simp] theorem withSlopes_ghostSlope (g : GhostFrameSt F M) (vs : List F) :
    (g.withSlopes vs).ghostSlope = g.ghostSlope := rfl

@[simp] theorem withSlopes_audit_roAProbes (g : GhostFrameSt F M)
    (vs : List F) : (g.withSlopes vs).audit.roAProbes = g.audit.roAProbes :=
  rfl

@[simp] theorem withSlopes_audit_roEProbes (g : GhostFrameSt F M)
    (vs : List F) : (g.withSlopes vs).audit.roEProbes = g.audit.roEProbes :=
  rfl

@[simp] theorem withSlopes_audit_roIdProbes (g : GhostFrameSt F M)
    (vs : List F) :
    (g.withSlopes vs).audit.roIdProbes = g.audit.roIdProbes := rfl

@[simp] theorem withSlopes_audit_slopeProbes (g : GhostFrameSt F M)
    (vs : List F) :
    (g.withSlopes vs).audit.slopeProbes = g.audit.slopeProbes := rfl

@[simp] theorem withSlopes_audit_honestSlopes (g : GhostFrameSt F M)
    (vs : List F) : (g.withSlopes vs).audit.honestSlopes = vs := rfl

end WithSlopesSimp

/-! ## Extraction certificate and quantitative closure

The handler-specific induction has one precise target: expose the write-only
honest slopes as a fresh tape drawn after a slope-independent core run.  Once
that equality is available, the probability calculation below is completely
generic and needs no further facts about FRAME. -/

/-- Materialize the honest-slope audit of a core outcome from a fresh uniform
tape whose length is carried by that outcome. -/
noncomputable def materializeSlopeTape
    (core : ProbComp ((Evidence F × GhostFrameSt F M) × ℕ)) :
    ProbComp (Evidence F × GhostFrameSt F M) := do
  let z ← core
  let vs ← drawList ($ᵗ F) z.2
  pure (z.1.1, z.1.2.withSlopes vs)

/-- **Continuation-level slope-tape extraction certificate.**  The ghost run
is represented by a slope-independent core followed by exactly as many fresh
uniform draws as slope-cache misses.  The two support bounds are the only
quantitative information used by the closure theorem. -/
structure GhostSlopeTapeExtraction (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) where
  core : ProbComp ((Evidence F × GhostFrameSt F M) × ℕ)
  evalDist_eq :
    𝒟[ghostFrameRun mclose A] = 𝒟[materializeSlopeTape core]
  slope_count_le : ∀ z ∈ support core, z.2 ≤ qb.qSig
  slope_probes_le : ∀ z ∈ support core,
    z.1.2.audit.slopeProbes.length ≤ qb.qNf

/-! ### The canonical slope-free core

This handler performs the same ideal-oracle work as `skelFrameImpl`, but a
fresh slope-cache miss only stores the placeholder and increments a counter.
It performs no slope draw and never changes `honestSlopes`; those values are
materialized in one independent tape after the run. -/

/-- State of the canonical slope-free core. -/
structure SlopeCoreSt (F M : Type) where
  ghost : GhostFrameSt F M
  count : ℕ

/-- Initial slope-free core state. -/
def SlopeCoreSt.init (F M : Type) : SlopeCoreSt F M :=
  ⟨GhostFrameSt.init F M, 0⟩

/-- Deterministic cache-shape update used in place of a fresh slope draw. -/
def slopeCoreTouch (gs : ℕ → Option F) (i : ℕ) :
    (ℕ → Option F) × ℕ :=
  match gs i with
  | some _ => (gs, 0)
  | none => (Function.update gs i (some (0 : F)), 1)

/-- FRAME handler with every honest-slope draw erased and counted. -/
def slopeCoreFrameImpl (mclose : M) :
    QueryImpl.Stateful unifSpec (frameSpec F M) (SlopeCoreSt F M)
  | .spend m => StateT.mk fun s =>
      if s.ghost.ideal.closed then pure (none, s)
      else do
        let p ← emitIdealSignal m s.ghost.ideal
        let q := slopeCoreTouch s.ghost.ghostSlope s.ghost.ideal.idx
        pure (some p.1, ⟨⟨p.2, q.1, s.ghost.audit⟩, s.count + q.2⟩)
  | .close => StateT.mk fun s =>
      if s.ghost.ideal.closed then pure (none, s)
      else do
        let p ← emitIdealSignal mclose s.ghost.ideal
        let q := slopeCoreTouch s.ghost.ghostSlope s.ghost.ideal.idx
        pure (some p.1,
          ⟨⟨{ p.2 with closed := true }, q.1, s.ghost.audit⟩,
            s.count + q.2⟩)
  | .nfAt i => StateT.mk fun s => do
      let p ← lazyRO s.ghost.ideal.honestNf i
      let q := slopeCoreTouch s.ghost.ghostSlope i
      pure (p.1,
        ⟨⟨{ s.ghost.ideal with honestNf := p.2 }, q.1, s.ghost.audit⟩,
          s.count + q.2⟩)
  | .roA kq i => StateT.mk fun s => do
      let p ← lazyRO s.ghost.ideal.roA (kq, i)
      pure (p.1, ⟨⟨{ s.ghost.ideal with roA := p.2 }, s.ghost.ghostSlope,
        { s.ghost.audit with roAProbes := kq :: s.ghost.audit.roAProbes }⟩,
        s.count⟩)
  | .roX m => StateT.mk fun s => do
      let p ← lazyROX s.ghost.ideal.roX m
      pure (p.1, ⟨⟨{ s.ghost.ideal with roX := p.2 }, s.ghost.ghostSlope,
        s.ghost.audit⟩, s.count⟩)
  | .roNf aq => StateT.mk fun s => do
      let p ← lazyRO s.ghost.ideal.roNf aq
      pure (p.1, ⟨⟨{ s.ghost.ideal with roNf := p.2 }, s.ghost.ghostSlope,
        { s.ghost.audit with slopeProbes := aq :: s.ghost.audit.slopeProbes }⟩,
        s.count⟩)
  | .roE kq e => StateT.mk fun s => do
      let p ← lazyRO s.ghost.ideal.roE (kq, e)
      pure (p.1, ⟨⟨{ s.ghost.ideal with roE := p.2 }, s.ghost.ghostSlope,
        { s.ghost.audit with roEProbes := kq :: s.ghost.audit.roEProbes }⟩,
        s.count⟩)
  | .roId kq => StateT.mk fun s => do
      let p ← lazyRO s.ghost.ideal.roId kq
      pure (p.1, ⟨⟨{ s.ghost.ideal with roId := p.2 }, s.ghost.ghostSlope,
        { s.ghost.audit with roIdProbes := kq :: s.ghost.audit.roIdProbes }⟩,
        s.count⟩)

/-- Canonical core generator used by the extraction theorem. -/
def slopeCoreRun (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    ProbComp ((Evidence F × GhostFrameSt F M) × ℕ) := do
  let cm ← ($ᵗ F)
  let z ← (simulateQ (slopeCoreFrameImpl mclose) (A cm)).run
    (SlopeCoreSt.init F M)
  pure ((z.1, z.2.ghost), z.2.count)

/-- Per-query structural accounting for the slope-free core. -/
theorem slopeCoreFrameImpl_measure_step (mclose : M) (op : FrameOp F M)
    (s : SlopeCoreSt F M)
    (z : (frameSpec F M).Range op × SlopeCoreSt F M)
    (hz : z ∈ support (((slopeCoreFrameImpl mclose) op).run s)) :
    z.2.count ≤ s.count + (if isSignalQuery op then 1 else 0) ∧
    z.2.ghost.audit.slopeProbes.length ≤
      s.ghost.audit.slopeProbes.length +
        (if isDirectRoNfQuery op then 1 else 0) := by
  have htouch : ∀ (gs : ℕ → Option F) (i : ℕ),
      (slopeCoreTouch gs i).2 ≤ 1 := by
    intro gs i
    unfold slopeCoreTouch
    split <;> simp
  cases op with
  | spend m =>
      unfold slopeCoreFrameImpl at hz
      simp only [StateT.run_mk] at hz
      by_cases hc : s.ghost.ideal.closed
      · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        simp [isSignalQuery, isDirectRoNfQuery]
      · rw [if_neg hc] at hz
        obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        constructor
        · simpa [isSignalQuery] using
            Nat.add_le_add_left
              (htouch s.ghost.ghostSlope s.ghost.ideal.idx) s.count
        · simp [isDirectRoNfQuery]
  | close =>
      unfold slopeCoreFrameImpl at hz
      simp only [StateT.run_mk] at hz
      by_cases hc : s.ghost.ideal.closed
      · rw [if_pos hc, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        simp [isSignalQuery, isDirectRoNfQuery]
      · rw [if_neg hc] at hz
        obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        constructor
        · simpa [isSignalQuery] using
            Nat.add_le_add_left
              (htouch s.ghost.ghostSlope s.ghost.ideal.idx) s.count
        · simp [isDirectRoNfQuery]
  | nfAt i =>
      unfold slopeCoreFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      constructor
      · simpa [isSignalQuery] using
          Nat.add_le_add_left (htouch s.ghost.ghostSlope i) s.count
      · simp [isDirectRoNfQuery]
  | roA kq i =>
      unfold slopeCoreFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [isSignalQuery, isDirectRoNfQuery]

  | roX m =>
      unfold slopeCoreFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [isSignalQuery, isDirectRoNfQuery]
  | roNf aq =>
      unfold slopeCoreFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [isSignalQuery, isDirectRoNfQuery]
  | roE kq e =>
      unfold slopeCoreFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [isSignalQuery, isDirectRoNfQuery]
  | roId kq =>
      unfold slopeCoreFrameImpl at hz
      simp only [StateT.run_mk] at hz
      obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [isSignalQuery, isDirectRoNfQuery]

/-- Both query-budget support bounds for one complete canonical core run. -/
theorem slopeCoreRun_support_bounds (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A)
    (z : (Evidence F × GhostFrameSt F M) × ℕ)
    (hz : z ∈ support (slopeCoreRun mclose A)) :
    z.2 ≤ qb.qSig ∧ z.1.2.audit.slopeProbes.length ≤ qb.qNf := by
  unfold slopeCoreRun at hz
  obtain ⟨cm, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  obtain ⟨w, hw, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  constructor
  · have h := support_measure_le_of_isQueryBoundP
      (slopeCoreFrameImpl mclose) SlopeCoreSt.count isSignalQuery
      (fun t s y hy => (slopeCoreFrameImpl_measure_step mclose t s y hy).1)
      (A cm) (qb.signal_bound cm) (SlopeCoreSt.init F M) w hw
    simpa [SlopeCoreSt.init] using h
  · have h := support_measure_le_of_isQueryBoundP
      (slopeCoreFrameImpl mclose)
      (fun s => s.ghost.audit.slopeProbes.length) isDirectRoNfQuery
      (fun t s y hy => (slopeCoreFrameImpl_measure_step mclose t s y hy).2)
      (A cm) (qb.roNf_bound cm) (SlopeCoreSt.init F M) w hw
    simpa [SlopeCoreSt.init, GhostFrameSt.init, GhostAudit.init] using h

/-- The sole semantic equality left in the ghost bad-mass lane: the erased
write-only slope draws may be postponed until after the canonical core run. -/
def GhostSlopeCoreCorrect (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) : Prop :=
  𝒟[ghostFrameRun mclose A] =
    𝒟[materializeSlopeTape (slopeCoreRun mclose A)]

/-- Core correctness plus the proved query accounting constructs the complete
extraction certificate. -/
noncomputable def ghostSlopeTapeExtraction_of_core (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (hc : GhostSlopeCoreCorrect mclose A) :
    GhostSlopeTapeExtraction mclose A qb where
  core := slopeCoreRun mclose A
  evalDist_eq := hc
  slope_count_le := fun z hz => (slopeCoreRun_support_bounds mclose A qb z hz).1
  slope_probes_le := fun z hz => (slopeCoreRun_support_bounds mclose A qb z hz).2

/-- Tape extraction gives the adaptive slope-preimage bound.  Although the
probe list and tape length may both depend on the core transcript, neither can
depend on the subsequently sampled tape. -/
theorem ghostFrameRun_slope_hit_bound_of_tape (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (h : GhostSlopeTapeExtraction mclose A qb) :
    Pr[fun z => SlopeHit z.2.audit | ghostFrameRun mclose A]
      ≤ ((qb.qNf * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    h.evalDist_eq)) ?_
  unfold materializeSlopeTape
  refine probEvent_bind_le_of_forall_le fun z hz => ?_
  rw [show (fun vs : List F =>
      (pure (z.1.1, z.1.2.withSlopes vs) :
        ProbComp (Evidence F × GhostFrameSt F M))) =
      pure ∘ (fun vs => (z.1.1, z.1.2.withSlopes vs)) from rfl,
    probEvent_bind_pure_comp]
  change Pr[fun vs : List F => ∃ q ∈ z.1.2.audit.slopeProbes, q ∈ vs |
      drawList ($ᵗ F) z.2] ≤ _
  refine (probEvent_drawList_exists_mem_le z.1.2.audit.slopeProbes z.2).trans ?_
  refine mul_le_mul_right' (Nat.cast_le.2 ?_) _
  simpa [Nat.mul_comm] using
    Nat.mul_le_mul (h.slope_probes_le z hz) (h.slope_count_le z hz)

/-- Tape extraction gives the honest-slope birthday bound. -/
theorem ghostFrameRun_slope_collision_bound_of_tape (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (h : GhostSlopeTapeExtraction mclose A qb) :
    Pr[fun z => SlopeCollision z.2.audit | ghostFrameRun mclose A]
      ≤ ((qb.qSig * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    h.evalDist_eq)) ?_
  unfold materializeSlopeTape
  refine probEvent_bind_le_of_forall_le fun z hz => ?_
  rw [show (fun vs : List F =>
      (pure (z.1.1, z.1.2.withSlopes vs) :
        ProbComp (Evidence F × GhostFrameSt F M))) =
      pure ∘ (fun vs => (z.1.1, z.1.2.withSlopes vs)) from rfl,
    probEvent_bind_pure_comp]
  change Pr[fun vs : List F => ¬ vs.Nodup | drawList ($ᵗ F) z.2] ≤ _
  refine (probEvent_drawList_not_nodup_le z.2).trans ?_
  refine mul_le_mul_right' (Nat.cast_le.2 ?_) _
  exact Nat.mul_le_mul (h.slope_count_le z hz) (h.slope_count_le z hz)

/-- The extraction certificate discharges the complete slope-dependent socket
consumed by `ghostFrameRun_leak_bad_bound`. -/
theorem ghostSlopeBadBounds_of_tape (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (h : GhostSlopeTapeExtraction mclose A qb) :
    GhostSlopeBadBounds mclose A qb where
  slope_hit := by
    unfold ghostDeferredRun
    change Pr[fun z : (Evidence F × GhostFrameSt F M) × F =>
      SlopeHit z.1.2.audit | _] ≤ _
    calc
      _ = Pr[fun z : Evidence F × GhostFrameSt F M => SlopeHit z.2.audit |
          ghostFrameRun mclose A] :=
        probEvent_bind_pair_uniform_fst (F := F) (ghostFrameRun mclose A)
          (fun z => SlopeHit z.2.audit)
      _ ≤ _ := ghostFrameRun_slope_hit_bound_of_tape mclose A qb h
  honest_collision := by
    unfold ghostDeferredRun
    change Pr[fun z : (Evidence F × GhostFrameSt F M) × F =>
      SlopeCollision z.1.2.audit | _] ≤ _
    calc
      _ = Pr[fun z : Evidence F × GhostFrameSt F M => SlopeCollision z.2.audit |
          ghostFrameRun mclose A] :=
        probEvent_bind_pair_uniform_fst (F := F) (ghostFrameRun mclose A)
          (fun z => SlopeCollision z.2.audit)
      _ ≤ _ := ghostFrameRun_slope_collision_bound_of_tape mclose A qb h

end Zkpc.Games

#print axioms Zkpc.Games.probEvent_drawList_mem_le
#print axioms Zkpc.Games.probEvent_drawList_exists_mem_le
#print axioms Zkpc.Games.probEvent_drawList_not_nodup_le
#print axioms Zkpc.Games.evalDist_drawList_succ_swap
#print axioms Zkpc.Games.skelFrameImpl_erase_step
#print axioms Zkpc.Games.skelFrameImpl_run_erase
#print axioms Zkpc.Games.probEvent_audit_ghost_eq_skel
#print axioms Zkpc.Games.slopeCoreFrameImpl_measure_step
#print axioms Zkpc.Games.slopeCoreRun_support_bounds
#print axioms Zkpc.Games.ghostFrameRun_slope_hit_bound_of_tape
#print axioms Zkpc.Games.ghostFrameRun_slope_collision_bound_of_tape
#print axioms Zkpc.Games.ghostSlopeBadBounds_of_tape

/-! ## The slope-tape averaged induction

The certificate route above leaves the tape factorization as an explicit
hypothesis. The development below discharges the two slope masses
*unconditionally*: instead of exhibiting the ghost run as literally equal
to a core-then-tape factorization, the induction runs the erased handler
from a start state whose honest-slope record is itself a fresh tape, and
shows that every oracle step either commutes with the tape or fuses one
more fresh draw into it. The leaf then pays the elementary counting
kernels. Budgets are threaded through the `IsQueryBoundP` certificates. -/

namespace Zkpc.Games

set_option maxHeartbeats 300000

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

omit [Field F] [SampleableType F] in
/-- Aggregate audit shape of a tape-seeded state, for rewriting handler
steps. -/
theorem withSlopes_audit_eq (g : GhostFrameSt F M) (vs : List F) :
    (g.withSlopes vs).audit
      = ⟨g.audit.roAProbes, g.audit.roEProbes, g.audit.roIdProbes,
          g.audit.slopeProbes, vs⟩ := rfl

/-! ### Per-operation run shapes of the erased handler

The tape induction rewrites one handler step at a time while the
`simulateQ` fold of the continuation stays folded, so each operation gets
its run shape as a standalone equation. -/

section RunShapes

variable (mclose : M)

/-- Run shape of a `spend` step of the erased handler. -/
theorem skelFrameImpl_run_spend (m : M) (g : GhostFrameSt F M) :
    ((skelFrameImpl mclose) (.spend m)).run g
      = if g.ideal.closed then pure (none, g)
        else
          emitIdealSignal m g.ideal >>= fun p =>
            skelTouch g.ghostSlope g.audit g.ideal.idx >>= fun q =>
              pure (some p.1, ⟨p.2, q.1, q.2⟩) := rfl

/-- Run shape of a legacy `close` step of the erased handler. -/
theorem skelFrameImpl_run_close (g : GhostFrameSt F M) :
    ((skelFrameImpl mclose) .close).run g
      = if g.ideal.closed then pure (none, g)
        else
          emitIdealSignal mclose g.ideal >>= fun p =>
            skelTouch g.ghostSlope g.audit g.ideal.idx >>= fun q =>
              pure (some p.1, ⟨{ p.2 with closed := true }, q.1, q.2⟩) :=
  rfl

/-- Run shape of an `nfAt` step of the erased handler. -/
theorem skelFrameImpl_run_nfAt (i : ℕ) (g : GhostFrameSt F M) :
    ((skelFrameImpl mclose) (.nfAt i)).run g
      = lazyRO g.ideal.honestNf i >>= fun p =>
          skelTouch g.ghostSlope g.audit i >>= fun q =>
            pure (p.1, ⟨{ g.ideal with honestNf := p.2 }, q.1, q.2⟩) := rfl

/-- Run shape of a direct `roA` step of the erased handler. -/
theorem skelFrameImpl_run_roA (kq : F) (i : ℕ) (g : GhostFrameSt F M) :
    ((skelFrameImpl mclose) (.roA kq i)).run g
      = lazyRO g.ideal.roA (kq, i) >>= fun p =>
          pure (p.1, ⟨{ g.ideal with roA := p.2 }, g.ghostSlope,
            { g.audit with roAProbes := kq :: g.audit.roAProbes }⟩) := rfl

/-- Run shape of a direct `roX` step of the erased handler. -/
theorem skelFrameImpl_run_roX (m : M) (g : GhostFrameSt F M) :
    ((skelFrameImpl mclose) (.roX m)).run g
      = lazyROX g.ideal.roX m >>= fun p =>
          pure (p.1, ⟨{ g.ideal with roX := p.2 }, g.ghostSlope,
            g.audit⟩) := rfl

/-- Run shape of a direct `roNf` step of the erased handler. -/
theorem skelFrameImpl_run_roNf (aq : F) (g : GhostFrameSt F M) :
    ((skelFrameImpl mclose) (.roNf aq)).run g
      = lazyRO g.ideal.roNf aq >>= fun p =>
          pure (p.1, ⟨{ g.ideal with roNf := p.2 }, g.ghostSlope,
            { g.audit with slopeProbes := aq :: g.audit.slopeProbes }⟩) :=
  rfl

/-- Run shape of a direct `roE` step of the erased handler. -/
theorem skelFrameImpl_run_roE (kq : F) (e : ℕ) (g : GhostFrameSt F M) :
    ((skelFrameImpl mclose) (.roE kq e)).run g
      = lazyRO g.ideal.roE (kq, e) >>= fun p =>
          pure (p.1, ⟨{ g.ideal with roE := p.2 }, g.ghostSlope,
            { g.audit with roEProbes := kq :: g.audit.roEProbes }⟩) := rfl

/-- Run shape of a direct `roId` step of the erased handler. -/
theorem skelFrameImpl_run_roId (kq : F) (g : GhostFrameSt F M) :
    ((skelFrameImpl mclose) (.roId kq)).run g
      = lazyRO g.ideal.roId kq >>= fun p =>
          pure (p.1, ⟨{ g.ideal with roId := p.2 }, g.ghostSlope,
            { g.audit with roIdProbes := kq :: g.audit.roIdProbes }⟩) := rfl

end RunShapes

section TapeInduction

variable [Fintype F]

/-- **Slope-preimage mass of the deferred-tape run.** Running any
query-bounded FRAME computation against the erased handler from a state
whose honest-slope record is a fresh uniform tape of length `m`, the
probability that some recorded `H_nf` probe ever equals some recorded
honest slope is at most `(m + nSig) · (|slopeProbes| + nNf) / |F|`: every
probe is chosen independently of every tape entry and of every later
fresh ghost slope, so each of the at most `m + nSig` slopes meets each of
the at most `|slopeProbes| + nNf` probes with mass `1/|F|`
(Spec.md §7 T7, `H_nf`-preimage leakage term). -/
theorem skelFrameImpl_slopeHit_prob_le (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (m nNf nSig : ℕ)
    (hNf : OracleComp.IsQueryBoundP oa
      (fun t => isDirectRoNfQuery t = true) nNf)
    (hSig : OracleComp.IsQueryBoundP oa
      (fun t => isSignalQuery t = true) nSig)
    (s : GhostFrameSt F M) :
    Pr[fun z : α × GhostFrameSt F M => SlopeHit z.2.audit |
        drawList ($ᵗ F) m >>= fun vs =>
          (simulateQ (skelFrameImpl mclose) oa).run (s.withSlopes vs)]
      ≤ (((m + nSig) * (s.audit.slopeProbes.length + nNf) : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing m nNf nSig s with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure]
      rw [show (fun vs : List F =>
          (pure (x, s.withSlopes vs) : ProbComp (α × GhostFrameSt F M))) =
          pure ∘ (fun vs => (x, s.withSlopes vs)) from rfl,
        probEvent_bind_pure_comp]
      refine le_trans (le_of_eq (probEvent_ext
        (q := fun vs : List F => ∃ q ∈ s.audit.slopeProbes, q ∈ vs)
        fun vs _ => Iff.rfl)) (le_trans
          (probEvent_drawList_exists_mem_le s.audit.slopeProbes m) ?_)
      exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul
        (Nat.le_add_right m nSig) (Nat.le_add_right _ nNf))) le_rfl
  | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hNf hSig
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        monadLift_self, StateT.run_bind]
      cases t with
      | spend msg =>
          have hposSig : 0 < nSig := by
            rcases hSig.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [skelFrameImpl, StateT.run_mk, OracleQuery.cont_query,
            withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq]
          by_cases hc : s.ideal.closed
          · try simp only [hc, ↓reduceIte, pure_bind]
            refine le_trans (ih none m nNf (nSig - 1)
              (by simpa [isDirectRoNfQuery] using hNf.2 none)
              (by simpa [isSignalQuery] using hSig.2 none) s) ?_
            exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
              le_rfl)) le_rfl
          · try simp only [hc, Bool.false_eq_true, ↓reduceIte]
            rcases hgs : s.ghostSlope s.ideal.idx with _ | w
            · try simp only [skelTouch_eq_of_none hgs, bind_assoc, pure_bind]
              refine probEvent_drawList_swap_fresh_le m
                (emitIdealSignal msg s.ideal)
                (fun c ws => (simulateQ (skelFrameImpl mclose)
                  (k (some c.1))).run
                    ⟨c.2, Function.update s.ghostSlope s.ideal.idx
                        (some (0 : F)),
                      ⟨s.audit.roAProbes, s.audit.roEProbes,
                        s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
                _ _ (fun c _ => ?_)
              refine le_trans (ih (some c.1) (m + 1) nNf (nSig - 1)
                (by simpa [isDirectRoNfQuery] using hNf.2 (some c.1))
                (by simpa [isSignalQuery] using hSig.2 (some c.1))
                ⟨c.2, Function.update s.ghostSlope s.ideal.idx
                  (some (0 : F)), s.audit⟩) ?_
              exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
                le_rfl)) le_rfl
            · try simp only [skelTouch_eq_of_some hgs, bind_assoc, pure_bind]
              refine probEvent_drawList_swap_le m
                (emitIdealSignal msg s.ideal)
                (fun c ws => (simulateQ (skelFrameImpl mclose)
                  (k (some c.1))).run
                    ⟨c.2, s.ghostSlope,
                      ⟨s.audit.roAProbes, s.audit.roEProbes,
                        s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
                _ _ (fun c _ => ?_)
              refine le_trans (ih (some c.1) m nNf (nSig - 1)
                (by simpa [isDirectRoNfQuery] using hNf.2 (some c.1))
                (by simpa [isSignalQuery] using hSig.2 (some c.1))
                ⟨c.2, s.ghostSlope, s.audit⟩) ?_
              exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
                le_rfl)) le_rfl
      | close =>
          have hposSig : 0 < nSig := by
            rcases hSig.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq]
          by_cases hc : s.ideal.closed
          · simp only [hc, ↓reduceIte, pure_bind]
            refine le_trans (ih none m nNf (nSig - 1)
              (by simpa [isDirectRoNfQuery] using hNf.2 none)
              (by simpa [isSignalQuery] using hSig.2 none) s) ?_
            exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
              le_rfl)) le_rfl
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]
            rcases hgs : s.ghostSlope s.ideal.idx with _ | w
            · simp only [skelTouch_eq_of_none hgs, bind_assoc, pure_bind]
              refine probEvent_drawList_swap_fresh_le m
                (emitIdealSignal mclose s.ideal)
                (fun c ws => (simulateQ (skelFrameImpl mclose)
                  (k (some c.1))).run
                    ⟨{ c.2 with closed := true },
                      Function.update s.ghostSlope s.ideal.idx
                        (some (0 : F)),
                      ⟨s.audit.roAProbes, s.audit.roEProbes,
                        s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
                _ _ (fun c _ => ?_)
              refine le_trans (ih (some c.1) (m + 1) nNf (nSig - 1)
                (by simpa [isDirectRoNfQuery] using hNf.2 (some c.1))
                (by simpa [isSignalQuery] using hSig.2 (some c.1))
                ⟨{ c.2 with closed := true },
                  Function.update s.ghostSlope s.ideal.idx (some (0 : F)),
                  s.audit⟩) ?_
              exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
                le_rfl)) le_rfl
            · simp only [skelTouch_eq_of_some hgs, bind_assoc, pure_bind]
              refine probEvent_drawList_swap_le m
                (emitIdealSignal mclose s.ideal)
                (fun c ws => (simulateQ (skelFrameImpl mclose)
                  (k (some c.1))).run
                    ⟨{ c.2 with closed := true }, s.ghostSlope,
                      ⟨s.audit.roAProbes, s.audit.roEProbes,
                        s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
                _ _ (fun c _ => ?_)
              refine le_trans (ih (some c.1) m nNf (nSig - 1)
                (by simpa [isDirectRoNfQuery] using hNf.2 (some c.1))
                (by simpa [isSignalQuery] using hSig.2 (some c.1))
                ⟨{ c.2 with closed := true }, s.ghostSlope, s.audit⟩) ?_
              exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
                le_rfl)) le_rfl
      | nfAt i =>
          have hposSig : 0 < nSig := by
            rcases hSig.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq]
          rcases hgs : s.ghostSlope i with _ | w
          · simp only [skelTouch_eq_of_none hgs, bind_assoc, pure_bind]
            refine probEvent_drawList_swap_fresh_le m
              (lazyRO s.ideal.honestNf i)
              (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
                ⟨{ s.ideal with honestNf := c.2 },
                  Function.update s.ghostSlope i (some (0 : F)),
                  ⟨s.audit.roAProbes, s.audit.roEProbes,
                    s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
              _ _ (fun c _ => ?_)
            refine le_trans (ih c.1 (m + 1) nNf (nSig - 1)
              (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
              (by simpa [isSignalQuery] using hSig.2 c.1)
              ⟨{ s.ideal with honestNf := c.2 },
                Function.update s.ghostSlope i (some (0 : F)),
                s.audit⟩) ?_
            exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
              le_rfl)) le_rfl
          · simp only [skelTouch_eq_of_some hgs, bind_assoc, pure_bind]
            refine probEvent_drawList_swap_le m
              (lazyRO s.ideal.honestNf i)
              (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
                ⟨{ s.ideal with honestNf := c.2 }, s.ghostSlope,
                  ⟨s.audit.roAProbes, s.audit.roEProbes,
                    s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
              _ _ (fun c _ => ?_)
            refine le_trans (ih c.1 m nNf (nSig - 1)
              (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
              (by simpa [isSignalQuery] using hSig.2 c.1)
              ⟨{ s.ideal with honestNf := c.2 }, s.ghostSlope,
                s.audit⟩) ?_
            exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
              le_rfl)) le_rfl
      | roA kq i =>
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyRO s.ideal.roA (kq, i))
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roA := c.2 }, s.ghostSlope,
                ⟨kq :: s.audit.roAProbes, s.audit.roEProbes,
                  s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          exact ih c.1 m nNf nSig
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roA := c.2 }, s.ghostSlope,
              ⟨kq :: s.audit.roAProbes, s.audit.roEProbes,
                s.audit.roIdProbes, s.audit.slopeProbes,
                s.audit.honestSlopes⟩⟩
      | roX msg =>
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyROX s.ideal.roX msg)
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roX := c.2 }, s.ghostSlope,
                ⟨s.audit.roAProbes, s.audit.roEProbes,
                  s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          exact ih c.1 m nNf nSig
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roX := c.2 }, s.ghostSlope, s.audit⟩
      | roNf aq =>
          have hposNf : 0 < nNf := by
            rcases hNf.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyRO s.ideal.roNf aq)
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roNf := c.2 }, s.ghostSlope,
                ⟨s.audit.roAProbes, s.audit.roEProbes,
                  s.audit.roIdProbes, aq :: s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          refine le_trans (ih c.1 m (nNf - 1) nSig
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roNf := c.2 }, s.ghostSlope,
              ⟨s.audit.roAProbes, s.audit.roEProbes, s.audit.roIdProbes,
                aq :: s.audit.slopeProbes, s.audit.honestSlopes⟩⟩) ?_
          refine mul_le_mul' (Nat.cast_le.2 ?_) le_rfl
          show (m + nSig) *
              ((aq :: s.audit.slopeProbes).length + (nNf - 1))
              ≤ (m + nSig) * (s.audit.slopeProbes.length + nNf)
          simp only [List.length_cons]
          exact Nat.mul_le_mul le_rfl (by omega)
      | roE kq e =>
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyRO s.ideal.roE (kq, e))
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roE := c.2 }, s.ghostSlope,
                ⟨s.audit.roAProbes, kq :: s.audit.roEProbes,
                  s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          exact ih c.1 m nNf nSig
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roE := c.2 }, s.ghostSlope,
              ⟨s.audit.roAProbes, kq :: s.audit.roEProbes,
                s.audit.roIdProbes, s.audit.slopeProbes,
                s.audit.honestSlopes⟩⟩
      | roId kq =>
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyRO s.ideal.roId kq)
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roId := c.2 }, s.ghostSlope,
                ⟨s.audit.roAProbes, s.audit.roEProbes,
                  kq :: s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          exact ih c.1 m nNf nSig
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roId := c.2 }, s.ghostSlope,
              ⟨s.audit.roAProbes, s.audit.roEProbes,
                kq :: s.audit.roIdProbes, s.audit.slopeProbes,
                s.audit.honestSlopes⟩⟩

/-- **Collision mass of the deferred-tape run.** Running any query-bounded
FRAME computation against the erased handler from a state whose
honest-slope record is a fresh uniform tape of length `m`, the probability
that the final honest-slope record repeats a value is at most
`(m + nSig)² / |F|`: at most `m + nSig` slopes ever exist, each pair
colliding with mass `1/|F|` (Spec.md §7 T7, honest-slope birthday
term). -/
theorem skelFrameImpl_collision_prob_le (mclose : M) {α : Type}
    (oa : OracleComp (frameSpec F M) α) (m nSig : ℕ)
    (hSig : OracleComp.IsQueryBoundP oa
      (fun t => isSignalQuery t = true) nSig)
    (s : GhostFrameSt F M) :
    Pr[fun z : α × GhostFrameSt F M => SlopeCollision z.2.audit |
        drawList ($ᵗ F) m >>= fun vs =>
          (simulateQ (skelFrameImpl mclose) oa).run (s.withSlopes vs)]
      ≤ (((m + nSig) * (m + nSig) : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing m nSig s with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure]
      rw [show (fun vs : List F =>
          (pure (x, s.withSlopes vs) : ProbComp (α × GhostFrameSt F M))) =
          pure ∘ (fun vs => (x, s.withSlopes vs)) from rfl,
        probEvent_bind_pure_comp]
      refine le_trans (le_of_eq (probEvent_ext
        (q := fun vs : List F => ¬ vs.Nodup) fun vs _ => Iff.rfl))
        (le_trans (probEvent_drawList_not_nodup_le m) ?_)
      exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul
        (Nat.le_add_right m nSig) (Nat.le_add_right m nSig))) le_rfl
  | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hSig
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        monadLift_self, StateT.run_bind]
      cases t with
      | spend msg =>
          have hposSig : 0 < nSig := by
            rcases hSig.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq]
          by_cases hc : s.ideal.closed
          · simp only [hc, ↓reduceIte, pure_bind]
            refine le_trans (ih none m (nSig - 1)
              (by simpa [isSignalQuery] using hSig.2 none) s) ?_
            exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
              (by omega))) le_rfl
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]
            rcases hgs : s.ghostSlope s.ideal.idx with _ | w
            · simp only [skelTouch_eq_of_none hgs, bind_assoc, pure_bind]
              refine probEvent_drawList_swap_fresh_le m
                (emitIdealSignal msg s.ideal)
                (fun c ws => (simulateQ (skelFrameImpl mclose)
                  (k (some c.1))).run
                    ⟨c.2, Function.update s.ghostSlope s.ideal.idx
                        (some (0 : F)),
                      ⟨s.audit.roAProbes, s.audit.roEProbes,
                        s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
                _ _ (fun c _ => ?_)
              refine le_trans (ih (some c.1) (m + 1) (nSig - 1)
                (by simpa [isSignalQuery] using hSig.2 (some c.1))
                ⟨c.2, Function.update s.ghostSlope s.ideal.idx
                  (some (0 : F)), s.audit⟩) ?_
              exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
                (by omega))) le_rfl
            · simp only [skelTouch_eq_of_some hgs, bind_assoc, pure_bind]
              refine probEvent_drawList_swap_le m
                (emitIdealSignal msg s.ideal)
                (fun c ws => (simulateQ (skelFrameImpl mclose)
                  (k (some c.1))).run
                    ⟨c.2, s.ghostSlope,
                      ⟨s.audit.roAProbes, s.audit.roEProbes,
                        s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
                _ _ (fun c _ => ?_)
              refine le_trans (ih (some c.1) m (nSig - 1)
                (by simpa [isSignalQuery] using hSig.2 (some c.1))
                ⟨c.2, s.ghostSlope, s.audit⟩) ?_
              exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
                (by omega))) le_rfl
      | close =>
          have hposSig : 0 < nSig := by
            rcases hSig.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq]
          by_cases hc : s.ideal.closed
          · simp only [hc, ↓reduceIte, pure_bind]
            refine le_trans (ih none m (nSig - 1)
              (by simpa [isSignalQuery] using hSig.2 none) s) ?_
            exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
              (by omega))) le_rfl
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]
            rcases hgs : s.ghostSlope s.ideal.idx with _ | w
            · simp only [skelTouch_eq_of_none hgs, bind_assoc, pure_bind]
              refine probEvent_drawList_swap_fresh_le m
                (emitIdealSignal mclose s.ideal)
                (fun c ws => (simulateQ (skelFrameImpl mclose)
                  (k (some c.1))).run
                    ⟨{ c.2 with closed := true },
                      Function.update s.ghostSlope s.ideal.idx
                        (some (0 : F)),
                      ⟨s.audit.roAProbes, s.audit.roEProbes,
                        s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
                _ _ (fun c _ => ?_)
              refine le_trans (ih (some c.1) (m + 1) (nSig - 1)
                (by simpa [isSignalQuery] using hSig.2 (some c.1))
                ⟨{ c.2 with closed := true },
                  Function.update s.ghostSlope s.ideal.idx (some (0 : F)),
                  s.audit⟩) ?_
              exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
                (by omega))) le_rfl
            · simp only [skelTouch_eq_of_some hgs, bind_assoc, pure_bind]
              refine probEvent_drawList_swap_le m
                (emitIdealSignal mclose s.ideal)
                (fun c ws => (simulateQ (skelFrameImpl mclose)
                  (k (some c.1))).run
                    ⟨{ c.2 with closed := true }, s.ghostSlope,
                      ⟨s.audit.roAProbes, s.audit.roEProbes,
                        s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
                _ _ (fun c _ => ?_)
              refine le_trans (ih (some c.1) m (nSig - 1)
                (by simpa [isSignalQuery] using hSig.2 (some c.1))
                ⟨{ c.2 with closed := true }, s.ghostSlope, s.audit⟩) ?_
              exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
                (by omega))) le_rfl
      | nfAt i =>
          have hposSig : 0 < nSig := by
            rcases hSig.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq]
          rcases hgs : s.ghostSlope i with _ | w
          · simp only [skelTouch_eq_of_none hgs, bind_assoc, pure_bind]
            refine probEvent_drawList_swap_fresh_le m
              (lazyRO s.ideal.honestNf i)
              (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
                ⟨{ s.ideal with honestNf := c.2 },
                  Function.update s.ghostSlope i (some (0 : F)),
                  ⟨s.audit.roAProbes, s.audit.roEProbes,
                    s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
              _ _ (fun c _ => ?_)
            refine le_trans (ih c.1 (m + 1) (nSig - 1)
              (by simpa [isSignalQuery] using hSig.2 c.1)
              ⟨{ s.ideal with honestNf := c.2 },
                Function.update s.ghostSlope i (some (0 : F)),
                s.audit⟩) ?_
            exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
              (by omega))) le_rfl
          · simp only [skelTouch_eq_of_some hgs, bind_assoc, pure_bind]
            refine probEvent_drawList_swap_le m
              (lazyRO s.ideal.honestNf i)
              (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
                ⟨{ s.ideal with honestNf := c.2 }, s.ghostSlope,
                  ⟨s.audit.roAProbes, s.audit.roEProbes,
                    s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
              _ _ (fun c _ => ?_)
            refine le_trans (ih c.1 m (nSig - 1)
              (by simpa [isSignalQuery] using hSig.2 c.1)
              ⟨{ s.ideal with honestNf := c.2 }, s.ghostSlope,
                s.audit⟩) ?_
            exact mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul (by omega)
              (by omega))) le_rfl
      | roA kq i =>
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyRO s.ideal.roA (kq, i))
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roA := c.2 }, s.ghostSlope,
                ⟨kq :: s.audit.roAProbes, s.audit.roEProbes,
                  s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          exact ih c.1 m nSig (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roA := c.2 }, s.ghostSlope,
              ⟨kq :: s.audit.roAProbes, s.audit.roEProbes,
                s.audit.roIdProbes, s.audit.slopeProbes,
                s.audit.honestSlopes⟩⟩
      | roX msg =>
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyROX s.ideal.roX msg)
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roX := c.2 }, s.ghostSlope,
                ⟨s.audit.roAProbes, s.audit.roEProbes,
                  s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          exact ih c.1 m nSig (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roX := c.2 }, s.ghostSlope, s.audit⟩
      | roNf aq =>
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyRO s.ideal.roNf aq)
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roNf := c.2 }, s.ghostSlope,
                ⟨s.audit.roAProbes, s.audit.roEProbes,
                  s.audit.roIdProbes, aq :: s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          exact ih c.1 m nSig (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roNf := c.2 }, s.ghostSlope,
              ⟨s.audit.roAProbes, s.audit.roEProbes, s.audit.roIdProbes,
                aq :: s.audit.slopeProbes, s.audit.honestSlopes⟩⟩
      | roE kq e =>
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyRO s.ideal.roE (kq, e))
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roE := c.2 }, s.ghostSlope,
                ⟨s.audit.roAProbes, kq :: s.audit.roEProbes,
                  s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          exact ih c.1 m nSig (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roE := c.2 }, s.ghostSlope,
              ⟨s.audit.roAProbes, kq :: s.audit.roEProbes,
                s.audit.roIdProbes, s.audit.slopeProbes,
                s.audit.honestSlopes⟩⟩
      | roId kq =>
          simp only [skelFrameImpl, StateT.run_mk, withSlopes_ideal,
            withSlopes_ghostSlope, withSlopes_audit_eq, bind_assoc,
            pure_bind]
          refine probEvent_drawList_swap_le m (lazyRO s.ideal.roId kq)
            (fun c ws => (simulateQ (skelFrameImpl mclose) (k c.1)).run
              ⟨{ s.ideal with roId := c.2 }, s.ghostSlope,
                ⟨s.audit.roAProbes, s.audit.roEProbes,
                  kq :: s.audit.roIdProbes, s.audit.slopeProbes, ws⟩⟩)
            _ _ (fun c _ => ?_)
          exact ih c.1 m nSig (by simpa [isSignalQuery] using hSig.2 c.1)
            ⟨{ s.ideal with roId := c.2 }, s.ghostSlope,
              ⟨s.audit.roAProbes, s.audit.roEProbes,
                kq :: s.audit.roIdProbes, s.audit.slopeProbes,
                s.audit.honestSlopes⟩⟩

end TapeInduction

/-! ### Unconditional endpoints and the master bound -/

section Endpoints

variable [Fintype F]

/-- Per-commitment slope-preimage endpoint: the ghost run from the initial
state raises `SlopeHit` with probability at most `qNf · qSig / |F|`. -/
theorem ghostFrameImpl_run_slopeHit_le (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (cm : F) :
    Pr[fun z : Evidence F × GhostFrameSt F M => SlopeHit z.2.audit |
        (simulateQ (ghostFrameImpl mclose) (A cm)).run
          (GhostFrameSt.init F M)]
      ≤ ((qb.qNf * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  rw [probEvent_audit_ghost_eq_skel mclose (A cm) (GhostFrameSt.init F M)
    SlopeHit, eraseSlopeValues_init]
  have h0 : (drawList ($ᵗ F) 0 >>= fun vs =>
      (simulateQ (skelFrameImpl mclose) (A cm)).run
        ((GhostFrameSt.init F M).withSlopes vs))
      = (simulateQ (skelFrameImpl mclose) (A cm)).run
          (GhostFrameSt.init F M) := by
    rw [show drawList ($ᵗ F) 0 = (pure [] : ProbComp (List F)) from rfl,
      pure_bind]
    rfl
  rw [← h0]
  refine le_trans (skelFrameImpl_slopeHit_prob_le mclose (A cm) 0 qb.qNf
    qb.qSig (qb.roNf_bound cm) (qb.signal_bound cm)
    (GhostFrameSt.init F M)) ?_
  refine mul_le_mul' (Nat.cast_le.2 (le_of_eq ?_)) le_rfl
  show (0 + qb.qSig) *
      ((GhostFrameSt.init F M).audit.slopeProbes.length + qb.qNf)
      = qb.qNf * qb.qSig
  have hlen : (GhostFrameSt.init F M).audit.slopeProbes.length = 0 := rfl
  rw [hlen]
  ring

/-- Per-commitment collision endpoint: the ghost run from the initial
state raises `SlopeCollision` with probability at most `qSig² / |F|`. -/
theorem ghostFrameImpl_run_collision_le (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (cm : F) :
    Pr[fun z : Evidence F × GhostFrameSt F M => SlopeCollision z.2.audit |
        (simulateQ (ghostFrameImpl mclose) (A cm)).run
          (GhostFrameSt.init F M)]
      ≤ ((qb.qSig * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  rw [probEvent_audit_ghost_eq_skel mclose (A cm) (GhostFrameSt.init F M)
    SlopeCollision, eraseSlopeValues_init]
  have h0 : (drawList ($ᵗ F) 0 >>= fun vs =>
      (simulateQ (skelFrameImpl mclose) (A cm)).run
        ((GhostFrameSt.init F M).withSlopes vs))
      = (simulateQ (skelFrameImpl mclose) (A cm)).run
          (GhostFrameSt.init F M) := by
    rw [show drawList ($ᵗ F) 0 = (pure [] : ProbComp (List F)) from rfl,
      pure_bind]
    rfl
  rw [← h0]
  refine le_trans (skelFrameImpl_collision_prob_le mclose (A cm) 0 qb.qSig
    (qb.signal_bound cm) (GhostFrameSt.init F M)) ?_
  refine mul_le_mul' (Nat.cast_le.2 (le_of_eq ?_)) le_rfl
  ring

/-- Run-level slope-preimage mass: over the complete paired ghost run, the
`SlopeHit` component of the leakage event has probability at most
`qNf · qSig / |F|` — unconditionally. -/
theorem ghostFrameRun_slopeHit_le (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) :
    Pr[fun z : Evidence F × GhostFrameSt F M => SlopeHit z.2.audit |
        ghostFrameRun mclose A]
      ≤ ((qb.qNf * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  unfold ghostFrameRun
  exact probEvent_bind_le_of_forall_le fun cm _ =>
    ghostFrameImpl_run_slopeHit_le mclose A qb cm

/-- Run-level collision mass: over the complete paired ghost run, the
`SlopeCollision` component of the leakage event has probability at most
`qSig² / |F|` — unconditionally. -/
theorem ghostFrameRun_collision_le (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) :
    Pr[fun z : Evidence F × GhostFrameSt F M => SlopeCollision z.2.audit |
        ghostFrameRun mclose A]
      ≤ ((qb.qSig * qb.qSig : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  unfold ghostFrameRun
  exact probEvent_bind_le_of_forall_le fun cm _ =>
    ghostFrameImpl_run_collision_le mclose A qb cm

/-- **Unconditional discharge of the slope-dependent socket.** The two
hidden-slope obligations of `GhostSlopeBadBounds` hold outright for every
query-bounded FRAME adversary: the deferred secret plays no role in the
slope events, and the slope-tape induction bounds both masses. -/
theorem ghostSlopeBadBounds_holds (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) :
    GhostSlopeBadBounds mclose A qb where
  slope_hit := by
    unfold ghostDeferredRun
    change Pr[fun z : (Evidence F × GhostFrameSt F M) × F =>
      SlopeHit z.1.2.audit | _] ≤ _
    calc
      _ = Pr[fun z : Evidence F × GhostFrameSt F M => SlopeHit z.2.audit |
          ghostFrameRun mclose A] :=
        probEvent_bind_pair_uniform_fst (F := F) (ghostFrameRun mclose A)
          (fun z => SlopeHit z.2.audit)
      _ ≤ _ := ghostFrameRun_slopeHit_le mclose A qb
  honest_collision := by
    unfold ghostDeferredRun
    change Pr[fun z : (Evidence F × GhostFrameSt F M) × F =>
      SlopeCollision z.1.2.audit | _] ≤ _
    calc
      _ = Pr[fun z : Evidence F × GhostFrameSt F M =>
          SlopeCollision z.2.audit | ghostFrameRun mclose A] :=
        probEvent_bind_pair_uniform_fst (F := F) (ghostFrameRun mclose A)
          (fun z => SlopeCollision z.2.audit)
      _ ≤ _ := ghostFrameRun_collision_le mclose A qb

/-- **Master k-averaged ghost bad-mass bound (Spec.md §7 T7), event
form.** Over the complete ghost run followed by the deferred uniform
secret, the ghost leakage event has probability at most
`qb.total / |F|` — with no remaining hypotheses. -/
theorem ghostFrameRun_leakBad_le (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) :
    Pr[(fun z => GhostLeakBad z.2 z.1.2.audit) | ghostDeferredRun mclose A]
      ≤ (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹ :=
  ghostFrameRun_leak_bad_bound mclose A qb
    (ghostSlopeBadBounds_holds mclose A qb)

/-- **Master k-averaged ghost bad-mass bound (Spec.md §7 T7), Boolean
form.** Run the ghost-audited ideal FRAME experiment, then draw the
honest secret `k` uniformly: the decided ghost leakage event — a direct
`roA`/`roE`/`roId` probe hit `k`, an `H_nf` probe hit a ghost honest
slope, or two ghost honest slopes collided — outputs `true` with
probability at most `qb.total / |F|`. This is the exact bad-event budget
the k-averaged deferred-sampling certificate pays. -/
theorem ghostFrameRun_leakBad_prob_le (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) :
    Pr[= true | do
        let z ← ghostFrameRun mclose A
        let k ← ($ᵗ F)
        pure (decide (GhostLeakBad k z.2.audit))]
      ≤ (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  have hprog : (do
      let z ← ghostFrameRun mclose A
      let k ← ($ᵗ F)
      pure (decide (GhostLeakBad k z.2.audit)))
      = (ghostDeferredRun mclose A >>= fun w =>
          pure (decide (GhostLeakBad w.2 w.1.2.audit))) := by
    simp only [ghostDeferredRun, bind_assoc, pure_bind]
  rw [hprog, probOutput_true_bind_decide_eq]
  exact ghostFrameRun_leakBad_le mclose A qb

end Endpoints

end Zkpc.Games

#print axioms Zkpc.Games.skelFrameImpl_slopeHit_prob_le
#print axioms Zkpc.Games.skelFrameImpl_collision_prob_le
#print axioms Zkpc.Games.ghostFrameImpl_run_slopeHit_le
#print axioms Zkpc.Games.ghostFrameImpl_run_collision_le
#print axioms Zkpc.Games.ghostFrameRun_slopeHit_le
#print axioms Zkpc.Games.ghostFrameRun_collision_le
#print axioms Zkpc.Games.ghostSlopeBadBounds_holds
#print axioms Zkpc.Games.ghostFrameRun_leakBad_le
#print axioms Zkpc.Games.ghostFrameRun_leakBad_prob_le
