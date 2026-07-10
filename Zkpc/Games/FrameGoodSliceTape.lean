import Zkpc.Games.FrameGoodSlice
import Zkpc.Games.FrameRealBadStep

/-!
# Deferred-tape closure of the FRAME good slice

The real/deferred-slope coupling already agrees on every answer until the
audited leakage event.  Consequently the real win-and-good event injects
into the deferred-slope win event: the coupling's bad branch contradicts
the guard on the real event.

The remainder of this module postpones every `nfAt`-pinned slope until its
unique consuming signal.  Pending slopes are represented by a finite fresh
tape.  An answer-irrelevant step commutes past the tape; a first `nfAt`
touch grows it by one uniform coordinate; and a consuming `spend`/`close`
extracts the corresponding coordinate and transports it through the
bijection `a ↦ k + a*x`.  This is the run-level argument needed for pins
whose value cannot be coupled pointwise after it has been sampled.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## The good real run embeds in the deferred-slope run -/

/-- At a fixed commitment and secret, identical-until-bad transfers the
real win-and-good event to the deferred-slope win event.  In the coupling's
good branch the evidence is equal.  Its absorbing branch is impossible
under the real-side `¬ FrameLeakBad` guard. -/
theorem auditedFrameImpl_goodSlice_le_ds (k cm : F) (mclose : M)
    (oa : OracleComp (frameSpec F M) (Evidence F)) :
    Pr[fun z : Evidence F × AuditedFrameSt F M =>
        Slashes k z.1 ∧ ¬ FrameLeakBad k z.2.audit |
      (simulateQ (auditedFrameImpl k mclose) oa).run
        ⟨{ FrameSt.init F M with
            roId := Function.update (FrameSt.init F M).roId k (some cm) },
          FrameAudit.init⟩]
      ≤ Pr[fun z : Evidence F × DSFrameSt F M => Slashes k z.1 |
        (simulateQ (dsFrameImpl k mclose) oa).run (DSFrameSt.init F M)] := by
  refine probEvent_le_of_relTriple_imp
    (relTriple_simulateQ_run_untilAbsorbing
      (auditedFrameImpl k mclose) (dsFrameImpl k mclose)
      (RealDSGood k) (fun r => FrameLeakBad k r.audit)
      (fun d => FrameLeakBad k d.audit)
      (fun t s hb z hz => auditedFrameImpl_bad_monotone k mclose t s hb z hz)
      (fun t s hb z hz => dsFrameImpl_bad_monotone k mclose t s hb z hz)
      (fun t r d hg => realDSStepCoupling_holds k mclose t r d hg)
      oa _ _ (realDSGood_initial k cm)) ?_
  rintro z₁ z₂ (hgood | hbad) ⟨hslash, hnbad⟩
  · exact hgood.1 ▸ hslash
  · exact absurd hbad.1 hnbad

/-- The commitment-averaged form of
`auditedFrameImpl_goodSlice_le_ds`. -/
theorem auditedFrameRun_goodSlice_le_dsFrameRun (k : F) (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    Pr[fun z : Evidence F × AuditedFrameSt F M =>
        Slashes k z.1 ∧ ¬ FrameLeakBad k z.2.audit |
      auditedFrameRun mclose A k]
      ≤ Pr[fun z : Evidence F × DSFrameSt F M => Slashes k z.1 |
        dsFrameRun k mclose A] := by
  unfold auditedFrameRun dsFrameRun
  exact probEvent_bind_mono_of_le _ _ _ _ _ fun cm =>
    auditedFrameImpl_goodSlice_le_ds k cm mclose (A cm)

/-! ## Erasing dead deferred slopes

Only slopes at indices at or above the next honest index can ever feed a
future line value.  The audit and all earlier slope values are therefore
observationally dead.  `FutureDSSt` is the canonical deferred state that
keeps precisely the live suffix.
-/

/-- Deferred-slope state with the write-only audit and dead prefix erased. -/
structure FutureDSSt (F M : Type) where
  ideal : IdealFrameSt F M
  slope : ℕ → Option F

/-- Keep only slope entries that may still be consumed by a future honest
signal. -/
def DSFrameSt.future (d : DSFrameSt F M) : FutureDSSt F M :=
  ⟨d.ideal, fun i => if d.ideal.idx ≤ i then d.slope i else none⟩

/-- Empty canonical deferred state. -/
def FutureDSSt.init (F M : Type) : FutureDSSt F M :=
  ⟨IdealFrameSt.init F M, fun _ => none⟩

/-- Restrict a slope cache to indices that can still be consumed. -/
def liveSlopeSuffix (n : ℕ) (gs : ℕ → Option F) : ℕ → Option F :=
  fun i => if n ≤ i then gs i else none

omit [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] in
theorem liveSlopeSuffix_succ (n : ℕ) (gs : ℕ → Option F) :
    liveSlopeSuffix (n + 1) gs =
      Function.update (liveSlopeSuffix n gs) n none := by
  funext i
  by_cases hi : i = n
  · subst i
    simp [liveSlopeSuffix]
  · by_cases hin : n ≤ i
    · have hs : n + 1 ≤ i := by omega
      simp [liveSlopeSuffix, hi, hin, hs]
    · have hs : ¬ n + 1 ≤ i := by omega
      simp [liveSlopeSuffix, hi, hin, hs]

omit [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] in
theorem liveSlopeSuffix_update_of_le (n i : ℕ) (hi : n ≤ i)
    (gs : ℕ → Option F) (a : F) :
    liveSlopeSuffix n (Function.update gs i (some a)) =
      Function.update (liveSlopeSuffix n gs) i (some a) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [liveSlopeSuffix, hi]
  · by_cases hj : n ≤ j <;>
      simp [liveSlopeSuffix, hj, Function.update_of_ne hji]

omit [Field F] [DecidableEq F] [DecidableEq M] in
/-- A touch at a live index projects exactly to an ordinary lazy lookup in
the live cache. -/
theorem dsTouch_live (gs : ℕ → Option F) (audit : FrameAudit F)
    (n i : ℕ) (hi : n ≤ i) :
    𝒟[(fun q => (q.1, liveSlopeSuffix n q.2.1)) <$>
        dsTouch gs audit i] =
      𝒟[lazyRO (liveSlopeSuffix n gs) i] := by
  cases h : gs i with
  | some a =>
      have hlive : liveSlopeSuffix n gs i = some a := by
        simp [liveSlopeSuffix, hi, h]
      simp [dsTouch, lazyRO, h, hlive]
  | none =>
      have hlive : liveSlopeSuffix n gs i = none := by
        simp [liveSlopeSuffix, hi, h]
      simp only [dsTouch, lazyRO, h, hlive, map_bind, map_pure]
      refine evalDist_bind_congr' ($ᵗ F) fun a => ?_
      rw [liveSlopeSuffix_update_of_le n i hi gs a]

omit [Field F] [DecidableEq F] [DecidableEq M] in
/-- A touch below the live suffix is answer-irrelevant after projection. -/
theorem dsTouch_dead (gs : ℕ → Option F) (audit : FrameAudit F)
    (n i : ℕ) (hi : i < n) :
    𝒟[(fun q => liveSlopeSuffix n q.2.1) <$>
        dsTouch gs audit i] =
      𝒟[(pure (liveSlopeSuffix n gs) : ProbComp (ℕ → Option F))] := by
  cases h : gs i with
  | some a =>
      simp [dsTouch, h]
  | none =>
    simp only [dsTouch, h, map_bind, map_pure]
    have hconst : ∀ v : F,
        liveSlopeSuffix n (Function.update gs i (some v)) =
          liveSlopeSuffix n gs := by
      intro v
      funext j
      by_cases hj : n ≤ j
      · have hne : j ≠ i := by omega
        simp [liveSlopeSuffix, hj, Function.update_of_ne hne]
      · simp [liveSlopeSuffix, hj]
    simp_rw [hconst]
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      ($ᵗ F) (probFailure_uniformSample F) _

omit [Field F] [DecidableEq F] [DecidableEq M] in
/-- A touch at the next signal index, followed by advancing that index,
is the live lazy lookup with the consumed coordinate cleared. -/
theorem dsTouch_consume (gs : ℕ → Option F) (audit : FrameAudit F)
    (n : ℕ) :
    𝒟[(fun q => (q.1, liveSlopeSuffix (n + 1) q.2.1)) <$>
        dsTouch gs audit n] =
      𝒟[(fun q => (q.1, Function.update q.2 n none)) <$>
        lazyRO (liveSlopeSuffix n gs) n] := by
  calc
    𝒟[(fun q => (q.1, liveSlopeSuffix (n + 1) q.2.1)) <$>
        dsTouch gs audit n]
        = 𝒟[(fun q => (q.1,
            Function.update (liveSlopeSuffix n q.2.1) n none)) <$>
              dsTouch gs audit n] := by
            rw [show (fun q : F × (ℕ → Option F) × FrameAudit F =>
                (q.1, liveSlopeSuffix (n + 1) q.2.1)) =
              (fun q => (q.1,
                Function.update (liveSlopeSuffix n q.2.1) n none)) by
              funext q
              rw [liveSlopeSuffix_succ]]
    _ = 𝒟[(fun q => (q.1, Function.update q.2 n none)) <$>
          lazyRO (liveSlopeSuffix n gs) n] := by
      have hmap := congrArg (fun D => (fun q =>
          (q.1, Function.update q.2 n none)) <$> D)
        (dsTouch_live gs audit n n le_rfl)
      simpa only [← evalDist_map, Functor.map_map, Function.comp_apply] using hmap

omit [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] in
@[simp] theorem dsFrameSt_init_future :
    (DSFrameSt.init F M).future = FutureDSSt.init F M := by
  rfl

/-- Deferred handler after deleting the dead prefix after every step.
`nfAt i` below the next signal index performs no slope draw because such a
slope can never again affect an answer. -/
def futureDSFrameImpl (k : F) (mclose : M) :
    QueryImpl.Stateful unifSpec (frameSpec F M) (FutureDSSt F M)
  | .spend m => StateT.mk fun g =>
      if g.ideal.closed then pure (none, g)
      else do
        let (x, cX) ← lazyROX g.ideal.roX m
        let (a, gs) ← lazyRO g.slope g.ideal.idx
        let (nf, cNf) ← lazyRO g.ideal.honestNf g.ideal.idx
        pure (some ⟨x, rlnY k a x, nf⟩,
          ⟨{ g.ideal with
              idx := g.ideal.idx + 1
              roX := cX
              honestNf := cNf },
            Function.update gs g.ideal.idx none⟩)
  | .close => StateT.mk fun g =>
      if g.ideal.closed then pure (none, g)
      else do
        let (x, cX) ← lazyROX g.ideal.roX mclose
        let (a, gs) ← lazyRO g.slope g.ideal.idx
        let (nf, cNf) ← lazyRO g.ideal.honestNf g.ideal.idx
        pure (some ⟨x, rlnY k a x, nf⟩,
          ⟨{ g.ideal with
              idx := g.ideal.idx + 1
              closed := true
              roX := cX
              honestNf := cNf },
            Function.update gs g.ideal.idx none⟩)
  | .nfAt i => StateT.mk fun g => do
      let (nf, cNf) ← lazyRO g.ideal.honestNf i
      if i < g.ideal.idx then
        pure (nf, ⟨{ g.ideal with honestNf := cNf }, g.slope⟩)
      else do
        let (_, gs) ← lazyRO g.slope i
        pure (nf, ⟨{ g.ideal with honestNf := cNf }, gs⟩)
  | .roA kq i => StateT.mk fun g => do
      let (v, c) ← lazyRO g.ideal.roA (kq, i)
      pure (v, ⟨{ g.ideal with roA := c }, g.slope⟩)
  | .roX m => StateT.mk fun g => do
      let (v, c) ← lazyROX g.ideal.roX m
      pure (v, ⟨{ g.ideal with roX := c }, g.slope⟩)
  | .roNf aq => StateT.mk fun g => do
      let (v, c) ← lazyRO g.ideal.roNf aq
      pure (v, ⟨{ g.ideal with roNf := c }, g.slope⟩)
  | .roE kq e => StateT.mk fun g => do
      let (v, c) ← lazyRO g.ideal.roE (kq, e)
      pure (v, ⟨{ g.ideal with roE := c }, g.slope⟩)
  | .roId kq => StateT.mk fun g => do
      let (v, c) ← lazyRO g.ideal.roId kq
      pure (v, ⟨{ g.ideal with roId := c }, g.slope⟩)

/-- Erasing the dead deferred ornament after one DS query has the same
distribution as the canonical live-suffix handler. -/
theorem dsFrameImpl_future_step (k : F) (mclose : M)
    (op : FrameOp F M) (d : DSFrameSt F M) :
    𝒟[(Prod.map id DSFrameSt.future <$>
        ((dsFrameImpl k mclose) op).run d : ProbComp _)] =
      𝒟[(((futureDSFrameImpl k mclose) op).run d.future : ProbComp _)] := by
  cases op with
  | roA kq i =>
      simp [dsFrameImpl, futureDSFrameImpl, DSFrameSt.future, StateT.run_mk]
  | roX m =>
      simp [dsFrameImpl, futureDSFrameImpl, DSFrameSt.future, StateT.run_mk]
  | roNf aq =>
      simp [dsFrameImpl, futureDSFrameImpl, DSFrameSt.future, StateT.run_mk]
  | roE kq e =>
      simp [dsFrameImpl, futureDSFrameImpl, DSFrameSt.future, StateT.run_mk]
  | roId kq =>
      simp [dsFrameImpl, futureDSFrameImpl, DSFrameSt.future, StateT.run_mk]
  | spend m =>
      unfold dsFrameImpl futureDSFrameImpl
      simp only [StateT.run_mk]
      by_cases hc : d.ideal.closed
      · simp [hc, DSFrameSt.future]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind,
          map_pure, Prod.map, id_eq]
        simp only [DSFrameSt.future, hc, Bool.false_eq_true, ↓reduceIte]
        refine evalDist_bind_congr' (lazyROX d.ideal.roX m) fun px => ?_
        let C : (F × (ℕ → Option F)) →
            ProbComp (Option (Signal F) × FutureDSSt F M) := fun q => do
          let pn ← lazyRO d.ideal.honestNf d.ideal.idx
          pure (some ⟨px.1, rlnY k q.1 px.1, pn.1⟩,
            ⟨{ d.ideal with
                idx := d.ideal.idx + 1
                closed := false
                roX := px.2
                honestNf := pn.2 }, q.2⟩)
        change 𝒟[dsTouch d.slope d.audit d.ideal.idx >>= fun q =>
            C (q.1, liveSlopeSuffix (d.ideal.idx + 1) q.2.1)] =
          𝒟[lazyRO (liveSlopeSuffix d.ideal.idx d.slope) d.ideal.idx >>=
            fun q => C (q.1, Function.update q.2 d.ideal.idx none)]
        calc
          𝒟[dsTouch d.slope d.audit d.ideal.idx >>= fun q =>
              C (q.1, liveSlopeSuffix (d.ideal.idx + 1) q.2.1)] =
            𝒟[((fun q =>
                (q.1, liveSlopeSuffix (d.ideal.idx + 1) q.2.1)) <$>
              dsTouch d.slope d.audit d.ideal.idx) >>= C] := by
                rw [bind_map_left]
          _ = 𝒟[((fun q =>
                (q.1, Function.update q.2 d.ideal.idx none)) <$>
              lazyRO (liveSlopeSuffix d.ideal.idx d.slope) d.ideal.idx) >>=
                C] := by
              rw [evalDist_bind, evalDist_bind, dsTouch_consume]
          _ = 𝒟[lazyRO (liveSlopeSuffix d.ideal.idx d.slope)
                d.ideal.idx >>= fun q =>
              C (q.1, Function.update q.2 d.ideal.idx none)] := by
                rw [bind_map_left]
  | close =>
      unfold dsFrameImpl futureDSFrameImpl
      simp only [StateT.run_mk]
      by_cases hc : d.ideal.closed
      · simp [hc, DSFrameSt.future]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind,
          map_pure, Prod.map, id_eq]
        simp only [DSFrameSt.future, hc, Bool.false_eq_true, ↓reduceIte]
        refine evalDist_bind_congr' (lazyROX d.ideal.roX mclose) fun px => ?_
        let C : (F × (ℕ → Option F)) →
            ProbComp (Option (Signal F) × FutureDSSt F M) := fun q => do
          let pn ← lazyRO d.ideal.honestNf d.ideal.idx
          pure (some ⟨px.1, rlnY k q.1 px.1, pn.1⟩,
            ⟨{ d.ideal with
                idx := d.ideal.idx + 1
                closed := true
                roX := px.2
                honestNf := pn.2 }, q.2⟩)
        change 𝒟[dsTouch d.slope d.audit d.ideal.idx >>= fun q =>
            C (q.1, liveSlopeSuffix (d.ideal.idx + 1) q.2.1)] =
          𝒟[lazyRO (liveSlopeSuffix d.ideal.idx d.slope) d.ideal.idx >>=
            fun q => C (q.1, Function.update q.2 d.ideal.idx none)]
        calc
          𝒟[dsTouch d.slope d.audit d.ideal.idx >>= fun q =>
              C (q.1, liveSlopeSuffix (d.ideal.idx + 1) q.2.1)] =
            𝒟[((fun q =>
                (q.1, liveSlopeSuffix (d.ideal.idx + 1) q.2.1)) <$>
              dsTouch d.slope d.audit d.ideal.idx) >>= C] := by
                rw [bind_map_left]
          _ = 𝒟[((fun q =>
                (q.1, Function.update q.2 d.ideal.idx none)) <$>
              lazyRO (liveSlopeSuffix d.ideal.idx d.slope) d.ideal.idx) >>=
                C] := by
              rw [evalDist_bind, evalDist_bind, dsTouch_consume]
          _ = 𝒟[lazyRO (liveSlopeSuffix d.ideal.idx d.slope)
                d.ideal.idx >>= fun q =>
              C (q.1, Function.update q.2 d.ideal.idx none)] := by
                rw [bind_map_left]
  | nfAt i =>
      unfold dsFrameImpl futureDSFrameImpl
      simp only [StateT.run_mk, map_bind, map_pure, Prod.map, id_eq,
        DSFrameSt.future]
      refine evalDist_bind_congr' (lazyRO d.ideal.honestNf i) fun pn => ?_
      by_cases hi : i < d.ideal.idx
      · simp only [hi, if_pos]
        let C : (ℕ → Option F) → ProbComp (F × FutureDSSt F M) :=
          fun gs => pure (pn.1,
            ⟨{ d.ideal with honestNf := pn.2 }, gs⟩)
        change 𝒟[dsTouch d.slope d.audit i >>= fun q =>
            C (liveSlopeSuffix d.ideal.idx q.2.1)] =
          𝒟[C (liveSlopeSuffix d.ideal.idx d.slope)]
        calc
          𝒟[dsTouch d.slope d.audit i >>= fun q =>
              C (liveSlopeSuffix d.ideal.idx q.2.1)] =
            𝒟[((fun q => liveSlopeSuffix d.ideal.idx q.2.1) <$>
              dsTouch d.slope d.audit i) >>= C] := by
                rw [bind_map_left]
          _ = 𝒟[(pure (liveSlopeSuffix d.ideal.idx d.slope) :
                ProbComp (ℕ → Option F)) >>= C] := by
              rw [evalDist_bind, evalDist_bind,
                dsTouch_dead d.slope d.audit d.ideal.idx i hi]
          _ = 𝒟[C (liveSlopeSuffix d.ideal.idx d.slope)] := by
                rw [pure_bind]
      · have hle : d.ideal.idx ≤ i := Nat.le_of_not_gt hi
        simp only [hi, if_false]
        let C : (F × (ℕ → Option F)) →
            ProbComp (F × FutureDSSt F M) := fun q =>
          pure (pn.1, ⟨{ d.ideal with honestNf := pn.2 }, q.2⟩)
        change 𝒟[dsTouch d.slope d.audit i >>= fun q =>
            C (q.1, liveSlopeSuffix d.ideal.idx q.2.1)] =
          𝒟[lazyRO (liveSlopeSuffix d.ideal.idx d.slope) i >>= C]
        calc
          𝒟[dsTouch d.slope d.audit i >>= fun q =>
              C (q.1, liveSlopeSuffix d.ideal.idx q.2.1)] =
            𝒟[((fun q =>
                (q.1, liveSlopeSuffix d.ideal.idx q.2.1)) <$>
              dsTouch d.slope d.audit i) >>= C] := by
                rw [bind_map_left]
          _ = 𝒟[lazyRO (liveSlopeSuffix d.ideal.idx d.slope) i >>=
                C] := by
              rw [evalDist_bind, evalDist_bind,
                dsTouch_live d.slope d.audit d.ideal.idx i hle]

/-- Full adaptive simulations commute with deletion of the dead deferred
ornament. -/
theorem dsFrameImpl_run_future (k : F) (mclose : M) {alpha : Type}
    (oa : OracleComp (frameSpec F M) alpha) (d : DSFrameSt F M) :
    𝒟[Prod.map id DSFrameSt.future <$>
        (simulateQ (dsFrameImpl k mclose) oa).run d] =
      𝒟[(simulateQ (futureDSFrameImpl k mclose) oa).run d.future] :=
  map_run_simulateQ_evalDist_eq_of_step
    (dsFrameImpl k mclose) (futureDSFrameImpl k mclose)
    DSFrameSt.future (dsFrameImpl_future_step k mclose) oa d

/-- Evidence alone has the same distribution in the original deferred
handler and its live-suffix projection. -/
theorem dsFrameImpl_run_evidence_eq_future (k : F) (mclose : M)
    (oa : OracleComp (frameSpec F M) (Evidence F)) (d : DSFrameSt F M) :
    𝒟[Prod.fst <$> (simulateQ (dsFrameImpl k mclose) oa).run d] =
      𝒟[Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose) oa).run
        d.future] := by
  have h := congrArg (fun D => Prod.fst <$> D)
    (dsFrameImpl_run_future k mclose oa d)
  simpa only [← evalDist_map, Functor.map_map, Prod.map_apply,
    Function.comp_apply, id_eq] using h

/-! ## Pending-slope tape -/

/-- Draw independent uniform slope values for a finite list of pending
indices and materialize them as a function-backed cache. -/
noncomputable def drawPendingSlopes : List ℕ → ProbComp (ℕ → Option F)
  | [] => pure (fun _ => none)
  | i :: is => do
      let a ← ($ᵗ F)
      let gs ← drawPendingSlopes is
      pure (Function.update gs i (some a))

omit [Field F] [DecidableEq F] [DecidableEq M] in
@[simp] theorem probFailure_drawPendingSlopes (is : List ℕ) :
    Pr[⊥ | drawPendingSlopes (F := F) is] = 0 := by
  induction is with
  | nil => simp [drawPendingSlopes]
  | cons i is ih => simp [drawPendingSlopes]

omit [Field F] [DecidableEq F] [DecidableEq M] in
/-- A supported pending-slope cache is populated exactly on the named
pending indices. -/
theorem drawPendingSlopes_support_none_iff (is : List ℕ)
    (gs : ℕ → Option F) (hgs : gs ∈ support (drawPendingSlopes (F := F) is))
    (i : ℕ) : gs i = none ↔ i ∉ is := by
  induction is generalizing gs with
  | nil =>
      rw [drawPendingSlopes, support_pure, Set.mem_singleton_iff] at hgs
      subst gs
      simp
  | cons j is ih =>
      unfold drawPendingSlopes at hgs
      obtain ⟨a, -, hgs⟩ := (mem_support_bind_iff _ _ _).1 hgs
      obtain ⟨tail, htail, hgs⟩ := (mem_support_bind_iff _ _ _).1 hgs
      rw [support_pure, Set.mem_singleton_iff] at hgs
      subst gs
      by_cases hij : i = j
      · subst i
        simp
      · rw [Function.update_of_ne hij]
        simpa [hij] using ih tail htail

omit [Field F] [DecidableEq F] [DecidableEq M] in
/-- Grow the pending tape by one first-touch coordinate. -/
theorem evalDist_drawPendingSlopes_cons {beta : Type} (is : List ℕ)
    (i : ℕ) (G : (ℕ → Option F) → ProbComp beta) :
    𝒟[drawPendingSlopes (F := F) is >>= fun gs =>
        ($ᵗ F) >>= fun a => G (Function.update gs i (some a))] =
      𝒟[drawPendingSlopes (F := F) (i :: is) >>= G] := by
  rw [drawPendingSlopes]
  simp only [bind_assoc, pure_bind]
  exact OracleComp.DeferredSampling.evalDist_bind_comm
    (drawPendingSlopes (F := F) is) ($ᵗ F)
      (fun gs a => G (Function.update gs i (some a)))

omit [DecidableEq M] in
/-- Extract one pending coordinate, transport it through a bijection, and
leave an independent fresh tape for the remaining pending indices. -/
theorem evalDist_drawPendingSlopes_extract_bij [Finite F] {beta : Type}
    (is : List ℕ) (i : ℕ) (hmem : i ∈ is) (hnd : is.Nodup)
    (phi : F → F) (hphi : Function.Bijective phi)
    (G : F → (ℕ → Option F) → ProbComp beta) :
    𝒟[drawPendingSlopes (F := F) is >>= fun gs =>
        G (phi ((gs i).getD 0)) (Function.update gs i none)] =
      𝒟[($ᵗ F) >>= fun y =>
        drawPendingSlopes (F := F) (is.erase i) >>= fun gs => G y gs] := by
  induction is generalizing G with
  | nil => simp at hmem
  | cons j is ih =>
      have hnot : j ∉ is := (List.nodup_cons.mp hnd).1
      have hnd' : is.Nodup := (List.nodup_cons.mp hnd).2
      by_cases hij : i = j
      · subst i
        have hclean : ∀ gs ∈ support (drawPendingSlopes (F := F) is),
            Function.update gs j none = gs := by
          intro gs hgs
          have hjnone := (drawPendingSlopes_support_none_iff is gs hgs j).2 hnot
          funext q
          by_cases hq : q = j
          · subst q
            simp [hjnone]
          · simp [Function.update_of_ne hq]
        rw [drawPendingSlopes]
        simp only [bind_assoc, pure_bind, Function.update_self,
          Option.getD_some, Function.update_idem]
        calc
          𝒟[($ᵗ F) >>= fun a =>
              drawPendingSlopes (F := F) is >>= fun gs =>
                G (phi a) (Function.update gs j none)] =
            𝒟[($ᵗ F) >>= fun a =>
              drawPendingSlopes (F := F) is >>= fun gs => G (phi a) gs] := by
                refine evalDist_bind_congr' ($ᵗ F) fun a => ?_
                refine evalDist_bind_congr
                  (mx := drawPendingSlopes (F := F) is) fun gs hgs => ?_
                rw [hclean gs hgs]
          _ = 𝒟[($ᵗ F) >>= fun y =>
              drawPendingSlopes (F := F) is >>= fun gs => G y gs] := by
                have hp := evalDist_bind_bijective_add_right_uniform F
                  phi hphi 0 (fun y =>
                    drawPendingSlopes (F := F) is >>= fun gs => G y gs)
                simpa using hp
          _ = 𝒟[($ᵗ F) >>= fun y =>
              drawPendingSlopes (F := F) ((j :: is).erase j) >>= fun gs =>
                G y gs] := by simp [hnot]
      · have himem : i ∈ is := by simpa [hij] using hmem
        rw [drawPendingSlopes]
        simp only [bind_assoc, pure_bind]
        have hcomm : ∀ (gs : ℕ → Option F) (a : F),
            Function.update (Function.update gs j (some a)) i none =
              Function.update (Function.update gs i none) j (some a) := by
          intro gs a
          exact Function.update_comm (Ne.symm hij) (some a) none gs
        simp_rw [Function.update_of_ne hij]
        simp_rw [hcomm]
        calc
          𝒟[($ᵗ F) >>= fun a =>
              drawPendingSlopes (F := F) is >>= fun gs =>
                G (phi ((gs i).getD 0))
                  (Function.update (Function.update gs i none) j (some a))] =
            𝒟[($ᵗ F) >>= fun a => ($ᵗ F) >>= fun y =>
              drawPendingSlopes (F := F) (is.erase i) >>= fun gs =>
                G y (Function.update gs j (some a))] := by
                  refine evalDist_bind_congr' ($ᵗ F) fun a => ?_
                  exact ih himem hnd'
                    (fun y gs => G y (Function.update gs j (some a)))
          _ = 𝒟[($ᵗ F) >>= fun y => ($ᵗ F) >>= fun a =>
              drawPendingSlopes (F := F) (is.erase i) >>= fun gs =>
                G y (Function.update gs j (some a))] :=
                OracleComp.DeferredSampling.evalDist_bind_comm
                  ($ᵗ F) ($ᵗ F) _
          _ = 𝒟[($ᵗ F) >>= fun y =>
              drawPendingSlopes (F := F) ((j :: is).erase i) >>= fun gs =>
                G y gs] := by
                  refine evalDist_bind_congr' ($ᵗ F) fun y => ?_
                  rw [show (j :: is).erase i = j :: is.erase i by
                    simp only [List.erase]
                    split <;> simp_all]
                  rw [drawPendingSlopes]
                  simp only [bind_assoc, pure_bind]

/-! ## The slope-free pending-index core -/

/-- Secret-free core state: ideal caches plus the finite set (represented
without duplication as a list) of indices touched by `nfAt` but not yet
consumed by an honest signal. -/
structure PendingFrameSt (F M : Type) where
  ideal : IdealFrameSt F M
  pending : List ℕ

/-- Empty pending-index state. -/
def PendingFrameSt.init (F M : Type) : PendingFrameSt F M :=
  ⟨IdealFrameSt.init F M, []⟩

/-- The pending list is duplicate-free and every pending index can still be
consumed. -/
def PendingValid (p : PendingFrameSt F M) : Prop :=
  p.pending.Nodup ∧ ∀ i ∈ p.pending, p.ideal.idx ≤ i

omit [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] in
theorem pendingValid_init : PendingValid (PendingFrameSt.init F M) := by
  constructor <;> simp [PendingFrameSt.init]

/-- Slope-free handler.  A live first `nfAt` touch records only its index.
Signals sample their public ordinate directly and retire the current index.
All answer and ideal-cache behavior is exactly `idealFrameImpl`. -/
def pendingFrameImpl (mclose : M) :
    QueryImpl.Stateful unifSpec (frameSpec F M) (PendingFrameSt F M)
  | .spend m => StateT.mk fun p =>
      if p.ideal.closed then pure (none, p)
      else do
        let (x, cX) ← lazyROX p.ideal.roX m
        let y ← ($ᵗ F)
        let (nf, cNf) ← lazyRO p.ideal.honestNf p.ideal.idx
        pure (some ⟨x, y, nf⟩,
          ⟨{ p.ideal with
              idx := p.ideal.idx + 1
              roX := cX
              honestNf := cNf },
            p.pending.erase p.ideal.idx⟩)
  | .close => StateT.mk fun p =>
      if p.ideal.closed then pure (none, p)
      else do
        let (x, cX) ← lazyROX p.ideal.roX mclose
        let y ← ($ᵗ F)
        let (nf, cNf) ← lazyRO p.ideal.honestNf p.ideal.idx
        pure (some ⟨x, y, nf⟩,
          ⟨{ p.ideal with
              idx := p.ideal.idx + 1
              closed := true
              roX := cX
              honestNf := cNf },
            p.pending.erase p.ideal.idx⟩)
  | .nfAt i => StateT.mk fun p => do
      let (nf, cNf) ← lazyRO p.ideal.honestNf i
      let pending' :=
        if i < p.ideal.idx ∨ i ∈ p.pending then p.pending
        else i :: p.pending
      pure (nf, ⟨{ p.ideal with honestNf := cNf }, pending'⟩)
  | .roA kq i => StateT.mk fun p => do
      let (v, c) ← lazyRO p.ideal.roA (kq, i)
      pure (v, ⟨{ p.ideal with roA := c }, p.pending⟩)
  | .roX m => StateT.mk fun p => do
      let (v, c) ← lazyROX p.ideal.roX m
      pure (v, ⟨{ p.ideal with roX := c }, p.pending⟩)
  | .roNf aq => StateT.mk fun p => do
      let (v, c) ← lazyRO p.ideal.roNf aq
      pure (v, ⟨{ p.ideal with roNf := c }, p.pending⟩)
  | .roE kq e => StateT.mk fun p => do
      let (v, c) ← lazyRO p.ideal.roE (kq, e)
      pure (v, ⟨{ p.ideal with roE := c }, p.pending⟩)
  | .roId kq => StateT.mk fun p => do
      let (v, c) ← lazyRO p.ideal.roId kq
      pure (v, ⟨{ p.ideal with roId := c }, p.pending⟩)

/-- Per-step erasure of the pending-index ornament. -/
theorem pendingFrameImpl_erase_step (mclose : M) (op : FrameOp F M)
    (p : PendingFrameSt F M) :
    𝒟[Prod.map id PendingFrameSt.ideal <$>
        ((pendingFrameImpl mclose) op).run p] =
      𝒟[((idealFrameImpl mclose) op).run p.ideal] := by
  cases op with
  | spend m | close =>
      unfold pendingFrameImpl idealFrameImpl emitIdealSignal
      simp only [StateT.run_mk]
      by_cases hc : p.ideal.closed <;>
        simp [hc, map_bind, map_pure, Prod.map]
  | nfAt i | roA kq i | roX i | roNf i | roE kq i | roId i =>
      simp [pendingFrameImpl, idealFrameImpl, StateT.run_mk]

/-- Full-run erasure of the pending-index ornament. -/
theorem pendingFrameImpl_run_erase (mclose : M) {alpha : Type}
    (oa : OracleComp (frameSpec F M) alpha) (p : PendingFrameSt F M) :
    𝒟[Prod.map id PendingFrameSt.ideal <$>
        (simulateQ (pendingFrameImpl mclose) oa).run p] =
      𝒟[(simulateQ (idealFrameImpl mclose) oa).run p.ideal] :=
  map_run_simulateQ_evalDist_eq_of_step
    (pendingFrameImpl mclose) (idealFrameImpl mclose)
    PendingFrameSt.ideal (pendingFrameImpl_erase_step mclose) oa p

/-- Evidence alone is unchanged by pending-index erasure. -/
theorem pendingFrameImpl_run_evidence_eq_ideal (mclose : M)
    (oa : OracleComp (frameSpec F M) (Evidence F)) (p : PendingFrameSt F M) :
    𝒟[Prod.fst <$> (simulateQ (pendingFrameImpl mclose) oa).run p] =
      𝒟[Prod.fst <$> (simulateQ (idealFrameImpl mclose) oa).run p.ideal] := by
  have h := congrArg (fun D => Prod.fst <$> D)
    (pendingFrameImpl_run_erase mclose oa p)
  simpa only [← evalDist_map, Functor.map_map, Prod.map_apply,
    Function.comp_apply, id_eq] using h

/-! ## Run-level tape/pad induction -/

section TapeInduction

variable [Fintype F]

set_option maxHeartbeats 600000 in
/-- A front tape of independent pending slopes turns the live deferred
handler into the slope-free pending handler for every adaptive adversary
computation. -/
theorem futureDSFrameImpl_run_evidence_eq_pending (k : F) (mclose : M) :
    ∀ (oa : OracleComp (frameSpec F M) (Evidence F))
      (p : PendingFrameSt F M), PendingValid p →
      𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
        Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose) oa).run
          ⟨p.ideal, gs⟩] =
      𝒟[Prod.fst <$>
        (simulateQ (pendingFrameImpl mclose) oa).run p] := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure ev =>
      intro p hp
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (drawPendingSlopes (F := F) p.pending)
        (probFailure_drawPendingSlopes p.pending) _
  | query_bind op cont ih =>
      intro p hp
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        monadLift_self, StateT.run_bind, map_bind]
      cases op with
      | spend m =>
          simp [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk]
      | close =>
          simp [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk]
      | nfAt i =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.honestNf i
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun pn =>
                (if i < p.ideal.idx then
                    Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
                      (cont pn.1)).run
                        ⟨{ p.ideal with honestNf := pn.2 }, gs⟩
                  else lazyRO gs i >>= fun q =>
                    Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
                      (cont pn.1)).run
                        ⟨{ p.ideal with honestNf := pn.2 }, q.2⟩)] =
            𝒟[step >>= fun pn => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont pn.1)).run
                ⟨{ p.ideal with honestNf := pn.2 },
                  if i < p.ideal.idx ∨ i ∈ p.pending then p.pending
                  else i :: p.pending⟩]
          calc
            _ = 𝒟[step >>= fun pn =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  (if i < p.ideal.idx then
                      Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
                        (cont pn.1)).run
                          ⟨{ p.ideal with honestNf := pn.2 }, gs⟩
                    else lazyRO gs i >>= fun q =>
                      Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
                        (cont pn.1)).run
                          ⟨{ p.ideal with honestNf := pn.2 }, q.2⟩)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun pn => ?_
              let ideal' := { p.ideal with honestNf := pn.2 }
              let futureCont : (ℕ → Option F) → ProbComp (Evidence F) :=
                fun gs => Prod.fst <$>
                  (simulateQ (futureDSFrameImpl k mclose) (cont pn.1)).run
                    ⟨ideal', gs⟩
              by_cases hi : i < p.ideal.idx
              · simp only [hi, if_pos, true_or]
                simpa [ideal', futureCont] using ih pn.1
                  (⟨ideal', p.pending⟩ : PendingFrameSt F M) hp
              · have hle : p.ideal.idx ≤ i := Nat.le_of_not_gt hi
                by_cases hm : i ∈ p.pending
                · simp only [hi, hm, if_false, or_true, if_true]
                  calc
                    𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                        lazyRO gs i >>= fun q => futureCont q.2] =
                      𝒟[drawPendingSlopes (F := F) p.pending >>=
                        futureCont] := by
                          refine evalDist_bind_congr
                            (mx := drawPendingSlopes (F := F) p.pending)
                              fun gs hgs => ?_
                          have hn : gs i ≠ none := by
                            intro hnone
                            exact ((drawPendingSlopes_support_none_iff
                              p.pending gs hgs i).1 hnone) hm
                          cases hsi : gs i with
                          | none => exact absurd hsi hn
                          | some a => simp [lazyRO, hsi]
                    _ = 𝒟[Prod.fst <$>
                        (simulateQ (pendingFrameImpl mclose) (cont pn.1)).run
                          ⟨ideal', p.pending⟩] := by
                            simpa [futureCont] using ih pn.1
                              (⟨ideal', p.pending⟩ : PendingFrameSt F M) hp
                · simp only [hi, hm, if_false, or_false]
                  have hpcons : PendingValid
                      (⟨ideal', i :: p.pending⟩ : PendingFrameSt F M) := by
                    refine ⟨List.nodup_cons.mpr ⟨hm, hp.1⟩, ?_⟩
                    intro j hj
                    rcases List.mem_cons.mp hj with rfl | hj
                    · exact hle
                    · exact hp.2 j hj
                  calc
                    𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                        lazyRO gs i >>= fun q => futureCont q.2] =
                      𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                        ($ᵗ F) >>= fun a =>
                          futureCont (Function.update gs i (some a))] := by
                            refine evalDist_bind_congr
                              (mx := drawPendingSlopes (F := F) p.pending)
                                fun gs hgs => ?_
                            have hnone :=
                              (drawPendingSlopes_support_none_iff
                                p.pending gs hgs i).2 hm
                            simp [lazyRO, hnone]
                    _ = 𝒟[drawPendingSlopes (F := F) (i :: p.pending) >>=
                        futureCont] :=
                          evalDist_drawPendingSlopes_cons p.pending i futureCont
                    _ = 𝒟[Prod.fst <$>
                        (simulateQ (pendingFrameImpl mclose) (cont pn.1)).run
                          ⟨ideal', i :: p.pending⟩] := by
                            simpa [futureCont] using ih pn.1
                              (⟨ideal', i :: p.pending⟩ :
                                PendingFrameSt F M) hpcons
      | roA kq i =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.roA (kq, i)
          let next : (F × (F × ℕ → Option F)) ×
              (ℕ → Option F) → ProbComp (Evidence F) :=
            fun z => Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run
                ⟨{ p.ideal with roA := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roA := a.2 }, p.pending⟩]
          calc
            𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                step >>= fun a => next (a, gs)] =
              𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = 𝒟[step >>= fun a => Prod.fst <$>
                (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                  ⟨{ p.ideal with roA := a.2 }, p.pending⟩] := by
              refine evalDist_bind_congr' step fun a => ?_
              simpa [next] using ih a.1
                (⟨{ p.ideal with roA := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp
      | roX m =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyROX p.ideal.roX m
          let next : (F × (M → Option F)) × (ℕ → Option F) →
              ProbComp (Evidence F) := fun z =>
            Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run ⟨{ p.ideal with roX := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roX := a.2 }, p.pending⟩]
          calc
            𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                step >>= fun a => next (a, gs)] =
              𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun a => ?_
              simpa [next] using ih a.1
                (⟨{ p.ideal with roX := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp
      | roNf aq =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.roNf aq
          let next : (F × (F → Option F)) × (ℕ → Option F) →
              ProbComp (Evidence F) := fun z =>
            Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run ⟨{ p.ideal with roNf := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roNf := a.2 }, p.pending⟩]
          calc
            𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                step >>= fun a => next (a, gs)] =
              𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun a => ?_
              simpa [next] using ih a.1
                (⟨{ p.ideal with roNf := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp
      | roE kq e =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.roE (kq, e)
          let next : (F × (F × ℕ → Option F)) ×
              (ℕ → Option F) → ProbComp (Evidence F) := fun z =>
            Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run ⟨{ p.ideal with roE := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roE := a.2 }, p.pending⟩]
          calc
            𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                step >>= fun a => next (a, gs)] =
              𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun a => ?_
              simpa [next] using ih a.1
                (⟨{ p.ideal with roE := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp
      | roId kq =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.roId kq
          let next : (F × (F → Option F)) × (ℕ → Option F) →
              ProbComp (Evidence F) := fun z =>
            Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run ⟨{ p.ideal with roId := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roId := a.2 }, p.pending⟩]
          calc
            𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                step >>= fun a => next (a, gs)] =
              𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun a => ?_
              simpa [next] using ih a.1
                (⟨{ p.ideal with roId := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp

end TapeInduction

end Zkpc.Games
