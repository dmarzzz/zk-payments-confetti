import Zkpc.Games.FrameDSCount

/-!
# Adaptive seeded-shadow induction for deferred FRAME counting

This module closes `DSBadMassLe` directly.  It strengthens the seeded
shadow invariant with the missing cache-pattern ownership fact, then
inducts over the adversary computation while keeping the secret and the
unrevealed-slope tape under uniform binders.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Fintype F]
variable {M : Type} [DecidableEq M]

/-- The seeded invariant plus ownership of every symbolic cache entry by
the shadow audit.  Ownership is what makes a single-coordinate tape
reindexing stable at every cache slot other than the consumed hole. -/
structure DSShadowInvStrong (sigma : DSShadowSt F M) (m : Nat) : Prop
    extends DSShadowInv sigma m where
  hpat_mem : forall i e, sigma.pat i = some e -> e ∈ sigma.shadow

/-- Extensionality helper for concrete deferred-slope states. -/
omit [Field F] [DecidableEq F] [SampleableType F] [Fintype F]
    [DecidableEq M] in
private theorem dsFrameSt_ext {s t : DSFrameSt F M}
    (hideal : s.ideal = t.ideal) (hslope : s.slope = t.slope)
    (haudit : s.audit = t.audit) : s = t := by
  cases s
  cases t
  simp_all

/-- Empty symbolic state corresponding to `DSFrameSt.init`. -/
def dsShadowInit (F M : Type) : DSShadowSt F M :=
  ⟨IdealFrameSt.init F M, fun _ => none, [], [], []⟩

@[simp] theorem dsShadowInit_seed (k : F) (vs : List F) :
    (dsShadowInit F M).seed k vs = DSFrameSt.init F M := by
  rfl

/-- The empty symbolic state satisfies the strong invariant at tape length
zero. -/
theorem dsShadowInvStrong_init : DSShadowInvStrong (dsShadowInit F M) 0 := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [dsShadowInit]
    · simp [dsShadowInit]
    · simp [dsShadowInit, entryCoords]
    · simp [dsShadowInit, entryCoords]
    · simpa [dsShadowInit, IdealFrameSt.init] using
        (roXCacheNonzero_init (F := F) (M := M))
    · simp [dsShadowInit]
    · simp [dsShadowInit]
    · simp [dsShadowInit]
  · simp [dsShadowInit]

/-- Insert a newly materialized symbolic slope at an unused index and at
the head of the audit shadow. -/
def DSShadowSt.insertEntry (sigma : DSShadowSt F M) (i : Nat)
    (e : DSEntry F) : DSShadowSt F M :=
  { sigma with
    pat := Function.update sigma.pat i (some e)
    shadow := e :: sigma.shadow }

/-- Consume the unique pending hole at an index.  The pattern entry is
updated at that index and the matching audit entry is updated in place. -/
def DSShadowSt.consumeHole (sigma : DSShadowSt F M) (i j : Nat) (x : F) :
    DSShadowSt F M :=
  { sigma with
    pat := Function.update sigma.pat i (some (.tline j x))
    shadow := sigma.shadow.map (replaceHole j x) }

/-- Record a direct-secret probe in the symbolic audit. -/
def DSShadowSt.addSecretProbe (sigma : DSShadowSt F M) (q : F) :
    DSShadowSt F M :=
  { sigma with secretProbes := q :: sigma.secretProbes }

/-- Record a candidate-slope probe in the symbolic audit. -/
def DSShadowSt.addSlopeProbe (sigma : DSShadowSt F M) (q : F) :
    DSShadowSt F M :=
  { sigma with slopeProbes := q :: sigma.slopeProbes }

/-- Replace only the public ideal-cache component. -/
def DSShadowSt.setIdeal (sigma : DSShadowSt F M) (ideal : IdealFrameSt F M) :
    DSShadowSt F M :=
  { sigma with ideal := ideal }

@[simp] theorem DSShadowSt.seed_setIdeal (sigma : DSShadowSt F M)
    (ideal : IdealFrameSt F M) (k : F) (vs : List F) :
    (sigma.setIdeal ideal).seed k vs =
      { sigma.seed k vs with ideal := ideal } := by
  rfl

@[simp] theorem dsBudget_setIdeal (sigma : DSShadowSt F M)
    (ideal : IdealFrameSt F M) (nA nE nId nNf nSig : Nat) :
    dsBudget (sigma.setIdeal ideal) nA nE nId nNf nSig =
      dsBudget sigma nA nE nId nNf nSig := by
  rfl

omit [SampleableType F] [Fintype F] in
/-- A cache-pattern entry has the structural properties carried by its
owning shadow entry. -/
theorem DSShadowInvStrong.pat_xne0 {sigma : DSShadowSt F M} {m i : Nat}
    {e : DSEntry F} (h : DSShadowInvStrong sigma m)
    (he : sigma.pat i = some e) : e.XNe0 :=
  h.hx e (h.hpat_mem i e he)

omit [SampleableType F] [Fintype F] in
/-- A cache-pattern coordinate lies inside the current tape. -/
theorem DSShadowInvStrong.pat_coord_lt {sigma : DSShadowSt F M} {m i j : Nat}
    {e : DSEntry F} (h : DSShadowInvStrong sigma m)
    (he : sigma.pat i = some e) (hc : e.coord = some j) : j < m := by
  apply h.hlt j
  simp only [entryCoords, List.mem_filterMap]
  exact ⟨e, h.hpat_mem i e he, hc⟩

omit [SampleableType F] [Fintype F] in
/-- No shadow entry distinct from the owned hole can use its tape
coordinate. -/
theorem DSShadowInvStrong.coord_ne_of_mem_of_ne_hole
    {sigma : DSShadowSt F M} {m i j : Nat}
    (h : DSShadowInvStrong sigma m) (hi : sigma.pat i = some (.hole j))
    {e : DSEntry F} (he : e ∈ sigma.shadow) (hne : e ≠ .hole j) :
    forall q, e.coord = some q -> q ≠ j := by
  intro q hq hqj
  subst q
  have hh : DSEntry.hole j ∈ sigma.shadow := h.hpat i j hi
  apply hne
  clear hne
  induction sigma.shadow with
  | nil => simp at he
  | cons a rest ih =>
      cases hca : a.coord with
      | none =>
          have hnd : (entryCoords rest).Nodup := by
            simpa [entryCoords, hca] using h.hnd
          rcases List.mem_cons.1 he with rfl | he
          · simp [hca] at hq
          rcases List.mem_cons.1 hh with rfl | hh
          · simp [hca]
          exact ih hnd he hh
      | some l =>
          have hnd : (l :: entryCoords rest).Nodup := by
            simpa [entryCoords, hca] using h.hnd
          rw [List.nodup_cons] at hnd
          rcases hnd with ⟨hl, hnd⟩
          rcases List.mem_cons.1 he with rfl | he
          · rcases List.mem_cons.1 hh with rfl | hh
            · rfl
            · exfalso
              apply hl
              simp only [entryCoords, List.mem_filterMap]
              refine ⟨.hole j, hh, rfl⟩
          · rcases List.mem_cons.1 hh with rfl | hh
            · exfalso
              apply hl
              simp only [entryCoords, List.mem_filterMap]
              exact ⟨e, he, hq⟩
            · exact ih hnd he hh

omit [SampleableType F] [Fintype F] in
/-- Replacing public caches without changing the honest counter preserves
the symbolic invariant, provided the nonzero digest-cache invariant is
supplied for the replacement. -/
theorem DSShadowInvStrong.setIdeal_sameIdx {sigma : DSShadowSt F M} {m : Nat}
    (h : DSShadowInvStrong sigma m) (ideal : IdealFrameSt F M)
    (hidx : ideal.idx = sigma.ideal.idx) (hroX : RoXCacheNonzero ideal.roX) :
    DSShadowInvStrong (sigma.setIdeal ideal) m := by
  refine ⟨?_, ?_⟩
  · refine ⟨h.hx, h.hsep, h.hlt, h.hnd, hroX, h.hpat, h.hpatinj, ?_⟩
    intro i hi e he
    apply h.hfresh i
    · simpa [DSShadowSt.setIdeal, hidx] using hi
    · exact he
  · exact h.hpat_mem

omit [SampleableType F] [Fintype F] in
/-- Merely recording a direct-secret probe preserves the invariant. -/
theorem DSShadowInvStrong.addSecretProbe {sigma : DSShadowSt F M} {m : Nat}
    (h : DSShadowInvStrong sigma m) (q : F) :
    DSShadowInvStrong (sigma.addSecretProbe q) m := by
  refine ⟨?_, ?_⟩
  · simpa [DSShadowSt.addSecretProbe] using h.toDSShadowInv
  · simpa [DSShadowSt.addSecretProbe] using h.hpat_mem

omit [SampleableType F] [Fintype F] in
/-- Merely recording a slope probe preserves the invariant. -/
theorem DSShadowInvStrong.addSlopeProbe {sigma : DSShadowSt F M} {m : Nat}
    (h : DSShadowInvStrong sigma m) (q : F) :
    DSShadowInvStrong (sigma.addSlopeProbe q) m := by
  refine ⟨?_, ?_⟩
  · simpa [DSShadowSt.addSlopeProbe] using h.toDSShadowInv
  · simpa [DSShadowSt.addSlopeProbe] using h.hpat_mem

omit [SampleableType F] [Fintype F] in
/-- Seeding after appending the draw of a fresh pending hole is exactly the
concrete `dsTouch` state update. -/
theorem seed_insertHole (sigma : DSShadowSt F M) (m i : Nat) (k v : F)
    (vs : List F) (hInv : DSShadowInvStrong sigma m)
    (hlen : vs.length = m) (hi : sigma.pat i = none) :
    (sigma.insertEntry i (.hole m)).seed k (vs ++ [v]) =
      ⟨sigma.ideal,
        Function.update (sigma.seed k vs).slope i (some v),
        { (sigma.seed k vs).audit with
          honestSlopes := v :: (sigma.seed k vs).audit.honestSlopes }⟩ := by
  apply dsFrameSt_ext
  · rfl
  · funext q
    by_cases hqi : q = i
    · subst q
      simp [DSShadowSt.seed, DSShadowSt.insertEntry, hi, DSEntry.eval,
        List.getD, hlen]
    · rw [Function.update_of_ne hqi, Function.update_of_ne hqi]
      simp only [DSShadowSt.seed_slope, DSShadowSt.insertEntry]
      rw [Function.update_of_ne hqi]
      cases hq : sigma.pat q with
      | none => simp [hq]
      | some e =>
          simp only [hq, Option.map_some]
          apply DSEntry.eval_append_lt
          intro j hj
          rw [hlen]
          exact hInv.pat_coord_lt hq hj
  · simp only [DSShadowSt.seed_audit, DSShadowSt.insertEntry, List.map_cons]
    congr 2
    refine List.map_congr_left fun e he => ?_
    apply DSEntry.eval_append_lt
    intro j hj
    rw [hlen]
    apply hInv.hlt j
    simp only [entryCoords, List.mem_filterMap]
    exact ⟨e, he, hj⟩

omit [SampleableType F] [Fintype F] in
/-- Allocating the next tape coordinate to a fresh hole preserves the
strong invariant. -/
theorem DSShadowInvStrong.insertHole {sigma : DSShadowSt F M} {m i : Nat}
    (h : DSShadowInvStrong sigma m) (hi : sigma.pat i = none) :
    DSShadowInvStrong (sigma.insertEntry i (.hole m)) (m + 1) := by
  have hnom : forall q, sigma.pat q ≠ some (.hole m) := by
    intro q hq
    have hm := h.hlt m (by
      simp only [entryCoords, List.mem_filterMap]
      exact ⟨.hole m, h.hpat q m hq, rfl⟩)
    omega
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, h.hroX, ?_, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · trivial
      · exact h.hx e he
    · change (DSEntry.hole m :: sigma.shadow).Pairwise DSEntry.Sep
      rw [List.pairwise_cons]
      exact ⟨by intro e _; trivial, h.hsep⟩
    · intro j hj
      simp only [DSShadowSt.insertEntry, entryCoords, List.filterMap_cons,
        DSEntry.coord, List.mem_cons] at hj
      rcases hj with rfl | hj
      · omega
      · exact Nat.lt.step (h.hlt j hj)
    · simp only [DSShadowSt.insertEntry, entryCoords, List.filterMap_cons,
        DSEntry.coord, List.nodup_cons]
      refine ⟨?_, h.hnd⟩
      intro hm
      exact (Nat.lt_irrefl m) (h.hlt m hm)
    · intro q j hq
      by_cases hqi : q = i
      · subst q
        simp only [DSShadowSt.insertEntry, Function.update_self] at hq
        have : j = m := by simpa using (Option.some.inj hq).symm
        subst j
        exact List.mem_cons_self
      · simp only [DSShadowSt.insertEntry, Function.update_of_ne hqi] at hq
        exact List.mem_cons_of_mem _ (h.hpat q j hq)
    · intro q q' j hq hq'
      by_cases hqi : q = i
      · subst q
        simp only [DSShadowSt.insertEntry, Function.update_self] at hq
          have hj : j = m := by simpa using (Option.some.inj hq).symm
        subst j
        by_cases hq'i : q' = i
        · exact hq'i.symm
        · simp only [DSShadowSt.insertEntry, Function.update_of_ne hq'i] at hq'
          exact (hnom q' hq').elim
      · simp only [DSShadowSt.insertEntry, Function.update_of_ne hqi] at hq
        by_cases hq'i : q' = i
        · subst q'
          simp only [DSShadowSt.insertEntry, Function.update_self] at hq'
          have hj : j = m := by simpa using (Option.some.inj hq').symm
          subst j
          exact (hnom q hq).elim
        · simp only [DSShadowSt.insertEntry, Function.update_of_ne hq'i] at hq'
          exact h.hpatinj q q' j hq hq'
    · intro q hidx e hq
      by_cases hqi : q = i
      · subst q
        simp only [DSShadowSt.insertEntry, Function.update_self] at hq
        have he : e = .hole m := (Option.some.inj hq).symm
        exact ⟨m, he⟩
      · simp only [DSShadowSt.insertEntry, Function.update_of_ne hqi] at hq
        exact h.hfresh q hidx e hq
  · intro q e hq
    by_cases hqi : q = i
    · subst q
      simp only [DSShadowSt.insertEntry, Function.update_self] at hq
      have he : e = .hole m := (Option.some.inj hq).symm
      subst e
      exact List.mem_cons_self
    · simp only [DSShadowSt.insertEntry, Function.update_of_ne hqi] at hq
      exact List.mem_cons_of_mem _ (h.hpat_mem q e hq)

omit [Field F] [SampleableType F] [Fintype F] in
/-- Avoiding the listed equal-abscissa ordinates is exactly what is needed
to cons a separated concrete line. -/
theorem line_sep_of_not_mem_dupTargets (x y : F) (shadow : List (DSEntry F))
    (hy : y ∉ dupTargets x shadow) :
    forall e, e ∈ shadow -> DSEntry.Sep (.line x y) e := by
  intro e he
  cases e with
  | line x' y' =>
      intro hxx hyy
      subst x'
      subst y'
      apply hy
      unfold dupTargets
      simp only [List.mem_filterMap]
      exact ⟨.line x y, he, by simp⟩
  | hole j => trivial
  | tline j x' => trivial

omit [SampleableType F] [Fintype F] in
/-- A successful fresh emission advances the honest counter, inserts its
concrete line, and preserves the strong invariant off the duplicate target
event. -/
theorem DSShadowInvStrong.insertLine_advance
    {sigma : DSShadowSt F M} {m : Nat} (h : DSShadowInvStrong sigma m)
    (ideal : IdealFrameSt F M) (x y : F)
    (hi : sigma.pat sigma.ideal.idx = none)
    (hidx : ideal.idx = sigma.ideal.idx + 1)
    (hroX : RoXCacheNonzero ideal.roX) (hx : x ≠ 0)
    (hy : y ∉ dupTargets x sigma.shadow) :
    DSShadowInvStrong
      ((sigma.insertEntry sigma.ideal.idx (.line x y)).setIdeal ideal) m := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, hroX, ?_, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hx
      · exact h.hx e he
    · change (DSEntry.line x y :: sigma.shadow).Pairwise DSEntry.Sep
      rw [List.pairwise_cons]
      exact ⟨line_sep_of_not_mem_dupTargets x y sigma.shadow hy, h.hsep⟩
    · intro j hj
      change j ∈ entryCoords (DSEntry.line x y :: sigma.shadow) at hj
      simpa [entryCoords] using h.hlt j hj
    · change (entryCoords (DSEntry.line x y :: sigma.shadow)).Nodup
      simpa [entryCoords] using h.hnd
    · intro q j hq
      by_cases hqi : q = sigma.ideal.idx
      · subst q
        simp [DSShadowSt.setIdeal, DSShadowSt.insertEntry] at hq
      · simp only [DSShadowSt.setIdeal, DSShadowSt.insertEntry,
          Function.update_of_ne hqi] at hq
        exact List.mem_cons_of_mem _ (h.hpat q j hq)
    · intro q q' j hq hq'
      have hqi : q ≠ sigma.ideal.idx := by
        intro heq
        subst q
        simp [DSShadowSt.setIdeal, DSShadowSt.insertEntry] at hq
      have hq'i : q' ≠ sigma.ideal.idx := by
        intro heq
        subst q'
        simp [DSShadowSt.setIdeal, DSShadowSt.insertEntry] at hq'
      simp only [DSShadowSt.setIdeal, DSShadowSt.insertEntry,
        Function.update_of_ne hqi] at hq
      simp only [DSShadowSt.setIdeal, DSShadowSt.insertEntry,
        Function.update_of_ne hq'i] at hq'
      exact h.hpatinj q q' j hq hq'
    · intro q hq e he
      have hqi : q ≠ sigma.ideal.idx := by
        intro heq
        subst q
        change ideal.idx ≤ sigma.ideal.idx at hq
        rw [hidx] at hq
        omega
      simp only [DSShadowSt.setIdeal, DSShadowSt.insertEntry,
        Function.update_of_ne hqi] at he
      apply h.hfresh q
      · change sigma.ideal.idx ≤ q
        change ideal.idx ≤ q at hq
        omega
      · exact he
  · intro q e he
    by_cases hqi : q = sigma.ideal.idx
    · subst q
      simp only [DSShadowSt.setIdeal, DSShadowSt.insertEntry,
        Function.update_self] at he
      have : e = .line x y := (Option.some.inj he).symm
      subst e
      exact List.mem_cons_self
    · simp only [DSShadowSt.setIdeal, DSShadowSt.insertEntry,
        Function.update_of_ne hqi] at he
      exact List.mem_cons_of_mem _ (h.hpat_mem q e he)

/-- Consuming the current pending hole and advancing the honest counter
preserves the strong invariant. -/
theorem DSShadowInvStrong.consumeHole_advance
    {sigma : DSShadowSt F M} {m j : Nat} (h : DSShadowInvStrong sigma m)
    (ideal : IdealFrameSt F M) (x : F)
    (hi : sigma.pat sigma.ideal.idx = some (.hole j))
    (hidx : ideal.idx = sigma.ideal.idx + 1)
    (hroX : RoXCacheNonzero ideal.roX) (hx : x ≠ 0) :
    DSShadowInvStrong
      ((sigma.consumeHole sigma.ideal.idx j x).setIdeal ideal) m := by
  have hhole : DSEntry.hole j ∈ sigma.shadow :=
    h.hpat sigma.ideal.idx j hi
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, hroX, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact xne0_replaceHole j x hx e0 (h.hx e0 he0)
    · change (sigma.shadow.map (replaceHole j x)).Pairwise DSEntry.Sep
      rw [List.pairwise_map]
      exact h.hsep.imp fun hab => sep_replaceHole j x _ _ hab
    · change ∀ q, q ∈ entryCoords (sigma.shadow.map (replaceHole j x)) -> q < m
      rw [entryCoords_map_replaceHole]
      exact h.hlt
    · change (entryCoords (sigma.shadow.map (replaceHole j x))).Nodup
      rw [entryCoords_map_replaceHole]
      exact h.hnd
    · intro q l hq
      have hqi : q ≠ sigma.ideal.idx := by
        intro heq
        subst q
        simp [DSShadowSt.setIdeal, DSShadowSt.consumeHole] at hq
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHole,
        Function.update_of_ne hqi] at hq
      have hlj : l ≠ j := by
        intro heq
        subst l
        exact hqi (h.hpatinj q sigma.ideal.idx j hq hi)
      refine List.mem_map.2 ⟨.hole l, h.hpat q l hq, ?_⟩
      simp [replaceHole, hlj]
    · intro q q' l hq hq'
      have hqi : q ≠ sigma.ideal.idx := by
        intro heq
        subst q
        simp [DSShadowSt.setIdeal, DSShadowSt.consumeHole] at hq
      have hq'i : q' ≠ sigma.ideal.idx := by
        intro heq
        subst q'
        simp [DSShadowSt.setIdeal, DSShadowSt.consumeHole] at hq'
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHole,
        Function.update_of_ne hqi] at hq
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHole,
        Function.update_of_ne hq'i] at hq'
      exact h.hpatinj q q' l hq hq'
    · intro q hq e he
      have hqi : q ≠ sigma.ideal.idx := by
        intro heq
        subst q
        change ideal.idx ≤ sigma.ideal.idx at hq
        rw [hidx] at hq
        omega
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHole,
        Function.update_of_ne hqi] at he
      apply h.hfresh q
      · change sigma.ideal.idx ≤ q
        change ideal.idx ≤ q at hq
        omega
      · exact he
  · intro q e he
    by_cases hqi : q = sigma.ideal.idx
    · subst q
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHole,
        Function.update_self] at he
      have heq : e = .tline j x := (Option.some.inj he).symm
      subst e
      refine List.mem_map.2 ⟨.hole j, hhole, ?_⟩
      simp [replaceHole]
    · simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHole,
        Function.update_of_ne hqi] at he
      have hne : e ≠ .hole j := by
        intro heq
        subst e
        exact hqi (h.hpatinj q sigma.ideal.idx j he hi)
      refine List.mem_map.2 ⟨e, h.hpat_mem q e he, ?_⟩
      simp [replaceHole, hne]

omit [SampleableType F] [Fintype F] in
/-- Seeding a fresh concrete line stores exactly its reconstructed slope
and records that slope at the head of the audit. -/
theorem seed_insertLine (sigma : DSShadowSt F M) (i : Nat) (k x y : F)
    (vs : List F) (hi : sigma.pat i = none) :
    (sigma.insertEntry i (.line x y)).seed k vs =
      ⟨sigma.ideal,
        Function.update (sigma.seed k vs).slope i (some ((y - k) / x)),
        { (sigma.seed k vs).audit with
          honestSlopes := (y - k) / x ::
            (sigma.seed k vs).audit.honestSlopes }⟩ := by
  apply dsFrameSt_ext
  · rfl
  · funext q
    by_cases hqi : q = i
    · subst q
      simp [DSShadowSt.seed, DSShadowSt.insertEntry, hi, DSEntry.eval]
    · simp [DSShadowSt.seed, DSShadowSt.insertEntry,
        Function.update_of_ne hqi]
  · rfl

omit [SampleableType F] [Fintype F] in
/-- Reindexing the owned hole coordinate by the RLN pad and replacing its
symbolic entry by a tape-line leaves the concrete seeded state unchanged.
The transformed coordinate is the public ordinate returned to the
adversary; the tape-line evaluation reconstructs the old cached slope. -/
theorem seed_consumeHole (sigma : DSShadowSt F M) (m i j : Nat)
    (k x : F) (vs : List F) (hInv : DSShadowInvStrong sigma m)
    (hlen : vs.length = m) (hi : sigma.pat i = some (.hole j))
    (hx : x ≠ 0) :
    (sigma.consumeHole i j x).seed k
        (vs.set j (k + vs.getD j 0 * x)) = sigma.seed k vs := by
  have hjm : j < m := hInv.pat_coord_lt hi rfl
  have hjv : j < vs.length := by simpa [hlen] using hjm
  apply dsFrameSt_ext
  · rfl
  · funext q
    by_cases hqi : q = i
    · subst q
      simp only [DSShadowSt.seed_slope, DSShadowSt.consumeHole,
        Function.update_self, Option.map_some, DSEntry.eval]
      rw [List.getD_set (by simpa using hjv)]
      simp only [hi, Option.map_some, DSEntry.eval]
      rw [add_sub_cancel_left, mul_div_cancel_right₀ _ hx]
    · simp only [DSShadowSt.seed_slope, DSShadowSt.consumeHole,
        Function.update_of_ne hqi]
      cases hq : sigma.pat q with
      | none => simp [hq]
      | some e =>
          simp only [hq, Option.map_some]
          have hne : e ≠ .hole j := by
            intro he
            subst e
            exact hqi (hInv.hpatinj q i j hq hi)
          apply DSEntry.eval_set_ne
          exact hInv.coord_ne_of_mem_of_ne_hole hi
            (hInv.hpat_mem q e hq) hne
  · simp only [DSShadowSt.seed_audit, DSShadowSt.consumeHole, List.map_map]
    congr 1
    refine List.map_congr_left fun e he => ?_
    by_cases heq : e = .hole j
    · subst e
      simp only [Function.comp_apply, replaceHole, if_pos rfl, DSEntry.eval]
      rw [List.getD_set (by simpa using hjv)]
      rw [add_sub_cancel_left, mul_div_cancel_right₀ _ hx]
    · simp only [Function.comp_apply]
      rw [eval_replaceHole_of_ne j x k _ e heq]
      apply DSEntry.eval_set_ne
      exact hInv.coord_ne_of_mem_of_ne_hole hi he heq

/-! ## Budget algebra -/

theorem choose_succ_two (n : Nat) : Nat.choose (n + 1) 2 = n + Nat.choose n 2 := by
  simpa [Nat.choose_one_right] using Nat.choose_succ_succ' n 1

/-- Spending one signal query without growing the shadow only lowers the
potential. -/
theorem dsBudget_signal_same_le (sigma : DSShadowSt F M)
    (nA nE nId nNf nSig : Nat) :
    dsBudget sigma nA nE nId nNf nSig ≤
      dsBudget sigma nA nE nId nNf (nSig + 1) := by
  simp only [dsBudget, choose_succ_two]
  omega

/-- A fresh deferred hole consumes one remaining signal query and preserves
the potential exactly. -/
theorem dsBudget_insertHole (sigma : DSShadowSt F M) (i j : Nat)
    (nA nE nId nNf nSig : Nat) :
    dsBudget (sigma.insertEntry i (.hole j)) nA nE nId nNf nSig =
      dsBudget sigma nA nE nId nNf (nSig + 1) := by
  simp only [dsBudget, DSShadowSt.insertEntry, List.length_cons,
    scCount_hole_cons, choose_succ_two]
  ring

/-- The duplicate-target mass plus the good fresh-line successor potential
is exactly the predecessor potential. -/
theorem dsBudget_insertLine_add_dupTargets (sigma : DSShadowSt F M)
    (i : Nat) (x y : F) (nA nE nId nNf nSig : Nat) :
    (dupTargets x sigma.shadow).length +
        dsBudget (sigma.insertEntry i (.line x y)) nA nE nId nNf nSig =
      dsBudget sigma nA nE nId nNf (nSig + 1) := by
  have hc := scCount_line_cons x y sigma.shadow
  simp only [dsBudget, DSShadowSt.insertEntry, List.length_cons,
    choose_succ_two]
  omega

/-- Consuming a hole preserves the existing shadow size and pair count, so
after spending a signal query its potential only decreases. -/
theorem dsBudget_consumeHole_le (sigma : DSShadowSt F M) (i j : Nat) (x : F)
    (nA nE nId nNf nSig : Nat) :
    dsBudget (sigma.consumeHole i j x) nA nE nId nNf nSig ≤
      dsBudget sigma nA nE nId nNf (nSig + 1) := by
  have hc := scCount_map_replaceHole j x sigma.shadow
  have hl : (sigma.shadow.map (replaceHole j x)).length = sigma.shadow.length :=
    List.length_map _
  simp only [dsBudget, DSShadowSt.consumeHole, hl, hc, choose_succ_two]
  omega

/-- Recording a direct probe while decrementing its matching budget leaves
the aggregate direct term unchanged. -/
theorem dsBudget_addSecretProbe_roA (sigma : DSShadowSt F M) (q : F)
    (nA nE nId nNf nSig : Nat) :
    dsBudget (sigma.addSecretProbe q) nA nE nId nNf nSig =
      dsBudget sigma (nA + 1) nE nId nNf nSig := by
  simp [dsBudget, DSShadowSt.addSecretProbe]
  omega

theorem dsBudget_addSecretProbe_roE (sigma : DSShadowSt F M) (q : F)
    (nA nE nId nNf nSig : Nat) :
    dsBudget (sigma.addSecretProbe q) nA nE nId nNf nSig =
      dsBudget sigma nA (nE + 1) nId nNf nSig := by
  simp [dsBudget, DSShadowSt.addSecretProbe]
  omega

theorem dsBudget_addSecretProbe_roId (sigma : DSShadowSt F M) (q : F)
    (nA nE nId nNf nSig : Nat) :
    dsBudget (sigma.addSecretProbe q) nA nE nId nNf nSig =
      dsBudget sigma nA nE (nId + 1) nNf nSig := by
  simp [dsBudget, DSShadowSt.addSecretProbe]
  omega

theorem dsBudget_addSlopeProbe (sigma : DSShadowSt F M) (q : F)
    (nA nE nId nNf nSig : Nat) :
    dsBudget (sigma.addSlopeProbe q) nA nE nId nNf nSig =
      dsBudget sigma nA nE nId (nNf + 1) nSig := by
  simp [dsBudget, DSShadowSt.addSlopeProbe]
  ring

/-! ## Seeded probability experiment -/

/-- Run a computation from a symbolic state under the deferred uniform
secret and uniform pending-slope tape, retaining the secret for the final
leakage predicate. -/
noncomputable def dsSeededRun {alpha : Type} (mclose : M)
    (oa : OracleComp (frameSpec F M) alpha) (sigma : DSShadowSt F M)
    (m : Nat) : ProbComp (F × (alpha × DSFrameSt F M)) := do
  let k ← ($ᵗ F)
  let vs ← drawList ($ᵗ F) m
  let z ← (simulateQ (dsFrameImpl k mclose) oa).run (sigma.seed k vs)
  pure (k, z)

/-- Leakage predicate on a seeded run result. -/
def dsSeededBad {alpha : Type} (w : F × (alpha × DSFrameSt F M)) : Prop :=
  FrameLeakBad w.1 w.2.2.audit

instance {alpha : Type} (w : F × (alpha × DSFrameSt F M)) :
    Decidable (dsSeededBad w) := by
  unfold dsSeededBad
  infer_instance

/-- Terminal case of the master induction: after swapping the independent
secret and tape draws, this is exactly `dsShadow_leaf_le`. -/
theorem dsSeededRun_pure_bad_le {alpha : Type} (mclose : M) (a : alpha)
    (sigma : DSShadowSt F M) (m : Nat) (h : DSShadowInvStrong sigma m) :
    Pr[dsSeededBad | dsSeededRun mclose (pure a) sigma m]
      ≤ (dsBudget sigma 0 0 0 0 0 : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  have hswap :
      𝒟[($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
          pure (k, (a, sigma.seed k vs))]
        = 𝒟[drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun k =>
            pure (k, (a, sigma.seed k vs))] :=
    OracleComp.DeferredSampling.evalDist_bind_comm
      ($ᵗ F) (drawList ($ᵗ F) m)
        (fun k vs => pure (k, (a, sigma.seed k vs)))
  unfold dsSeededRun
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) hswap)) ?_
  change Pr[fun w : F × (alpha × DSFrameSt F M) =>
      FrameLeakBad w.1 w.2.2.audit |
      drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun k =>
        pure (k, (a, sigma.seed k vs))] ≤ _
  have hleaf := dsShadow_leaf_le sigma.secretProbes sigma.slopeProbes
    sigma.shadow m h.hx h.hsep h.hlt h.hnd
  have hleaf' := hleaf
  simpa [dsBudget] using hleaf'

end Zkpc.Games
