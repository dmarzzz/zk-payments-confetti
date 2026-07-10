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

omit [Field F] [DecidableEq F] [SampleableType F] [Fintype F]
    [DecidableEq M] in
/-- Extensionality helper for concrete deferred-slope states. -/
theorem dsFrameSt_ext {s t : DSFrameSt F M}
    (hideal : s.ideal = t.ideal) (hslope : s.slope = t.slope)
    (haudit : s.audit = t.audit) : s = t := by
  cases s
  cases t
  simp_all

omit [Field F] [DecidableEq F] [SampleableType F] [Fintype F]
    [DecidableEq M] in
/-- Extensionality helper for FRAME audit records. -/
theorem frameAudit_ext {s t : FrameAudit F}
    (hsecret : s.secretProbes = t.secretProbes)
    (hslope : s.slopeProbes = t.slopeProbes)
    (hhonest : s.honestSlopes = t.honestSlopes) : s = t := by
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

/-- Replace a consumed pending hole by the concrete public line that the
adversary receives.  Unlike `consumeHole`, this representation no longer
uses tape coordinate `j`; leaving that coordinate as an unread dummy is what
allows the public ordinate to be extracted as an independent uniform draw. -/
def replaceHoleLine (j : Nat) (x y : F) (e : DSEntry F) : DSEntry F :=
  if e = .hole j then .line x y else e

/-- Symbolic state update for consuming an owned pending hole into a concrete
public line.  The update is in place, so the order of the honest-slope audit
is unchanged. -/
def DSShadowSt.consumeHoleLine (sigma : DSShadowSt F M) (i j : Nat)
    (x y : F) : DSShadowSt F M :=
  { sigma with
    pat := Function.update sigma.pat i (some (.line x y))
    shadow := sigma.shadow.map (replaceHoleLine j x y) }

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
/-- Replacing a hole by a concrete line preserves the nonzero-abscissa
condition when the consuming line has nonzero abscissa. -/
theorem xne0_replaceHoleLine (j : Nat) (x y : F) (hx : x ≠ 0)
    (e : DSEntry F) (he : e.XNe0) :
    (replaceHoleLine j x y e).XNe0 := by
  unfold replaceHoleLine
  split_ifs with h
  · exact hx
  · exact he

omit [Field F] [SampleableType F] [Fintype F] in
/-- Every coordinate retained by `replaceHoleLine` was already a coordinate
of the original entry. -/
theorem coord_replaceHoleLine_some (j : Nat) (x y : F) (e : DSEntry F)
    (q : Nat) (h : (replaceHoleLine j x y e).coord = some q) :
    e.coord = some q := by
  unfold replaceHoleLine at h
  split at h <;> simp_all [DSEntry.coord]

omit [Field F] [SampleableType F] [Fintype F] in
/-- Every coordinate in the concrete-line successor occurred in the original
shadow. -/
theorem mem_entryCoords_of_mem_map_replaceHoleLine
    (shadow : List (DSEntry F)) (j : Nat) (x y : F) (q : Nat)
    (hq : q ∈ entryCoords (shadow.map (replaceHoleLine j x y))) :
    q ∈ entryCoords shadow := by
  simp only [entryCoords, List.mem_filterMap] at hq ⊢
  obtain ⟨e', he', hc⟩ := hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
  exact ⟨e, he, coord_replaceHoleLine_some j x y e q hc⟩

omit [Field F] [SampleableType F] [Fintype F] in
theorem entryCoords_tail_nodup (e : DSEntry F) (rest : List (DSEntry F))
    (h : (entryCoords (e :: rest)).Nodup) :
    (entryCoords rest).Nodup := by
  cases e with
  | line x y => simpa [entryCoords] using h
  | hole q =>
      change (q :: entryCoords rest).Nodup at h
      exact (List.nodup_cons.mp h).2
  | tline q x =>
      change (q :: entryCoords rest).Nodup at h
      exact (List.nodup_cons.mp h).2

omit [Field F] [SampleableType F] [Fintype F] in
/-- Deleting holes from the coordinate projection preserves coordinate
uniqueness. -/
theorem nodup_entryCoords_map_replaceHoleLine
    (shadow : List (DSEntry F)) (j : Nat) (x y : F)
    (hnd : (entryCoords shadow).Nodup) :
    (entryCoords (shadow.map (replaceHoleLine j x y))).Nodup := by
  induction shadow with
  | nil => simp [entryCoords]
  | cons e rest ih =>
      have hndRest := entryCoords_tail_nodup e rest hnd
      have hi := ih hndRest
      rw [List.map_cons]
      cases e with
      | line x' y' =>
          rw [show replaceHoleLine j x y (.line x' y') = .line x' y' by
            simp [replaceHoleLine]]
          change (entryCoords (rest.map (replaceHoleLine j x y))).Nodup
          exact hi
      | hole q =>
          by_cases hqj : q = j
          · subst q
            rw [show replaceHoleLine j x y (.hole j) = .line x y by
              simp [replaceHoleLine]]
            change (entryCoords (rest.map (replaceHoleLine j x y))).Nodup
            exact hi
          · have hqold : q ∉ entryCoords rest := by
              change (q :: entryCoords rest).Nodup at hnd
              exact (List.nodup_cons.mp hnd).1
            have hqnew :
                q ∉ entryCoords (rest.map (replaceHoleLine j x y)) := by
              intro hqm
              exact hqold
                (mem_entryCoords_of_mem_map_replaceHoleLine rest j x y q hqm)
            rw [show replaceHoleLine j x y (.hole q) = .hole q by
              simp [replaceHoleLine, hqj]]
            change (q :: entryCoords
              (rest.map (replaceHoleLine j x y))).Nodup
            exact List.nodup_cons.mpr ⟨hqnew, hi⟩
      | tline q x' =>
          have hqold : q ∉ entryCoords rest := by
            change (q :: entryCoords rest).Nodup at hnd
            exact (List.nodup_cons.mp hnd).1
          have hqnew :
              q ∉ entryCoords (rest.map (replaceHoleLine j x y)) := by
            intro hqm
            exact hqold
              (mem_entryCoords_of_mem_map_replaceHoleLine rest j x y q hqm)
          rw [show replaceHoleLine j x y (.tline q x') = .tline q x' by
            simp [replaceHoleLine]]
          change (q :: entryCoords
            (rest.map (replaceHoleLine j x y))).Nodup
          exact List.nodup_cons.mpr ⟨hqnew, hi⟩

omit [Field F] [SampleableType F] [Fintype F] in
/-- If every old entry at `j` is the consumed hole, the concrete-line
successor no longer mentions `j`. -/
theorem not_mem_entryCoords_map_replaceHoleLine
    (shadow : List (DSEntry F)) (j : Nat) (x y : F)
    (honly : ∀ e, e ∈ shadow → e.coord = some j → e = .hole j) :
    j ∉ entryCoords (shadow.map (replaceHoleLine j x y)) := by
  intro hj
  simp only [entryCoords, List.mem_filterMap] at hj
  obtain ⟨e', he', hc⟩ := hj
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
  have hec := coord_replaceHoleLine_some j x y e j hc
  have heq := honly e he hec
  subst e
  simp [replaceHoleLine, DSEntry.coord] at hc

omit [Field F] [SampleableType F] in
/-- Replacing the unique owned hole by a nonduplicating public line preserves
pairwise line separation. -/
theorem pairwise_sep_map_replaceHoleLine (shadow : List (DSEntry F))
    (j : Nat) (x y : F) (hsep : shadow.Pairwise DSEntry.Sep)
    (hnd : (entryCoords shadow).Nodup) (hy : y ∉ dupTargets x shadow) :
    (shadow.map (replaceHoleLine j x y)).Pairwise DSEntry.Sep := by
  induction shadow with
  | nil => simp
  | cons e rest ih =>
      rw [List.pairwise_cons] at hsep
      have hndRest := entryCoords_tail_nodup e rest hnd
      have hyRest : y ∉ dupTargets x rest := by
        intro hyr
        apply hy
        rw [dupTargets_cons]
        exact List.mem_append.2 (Or.inr hyr)
      have htail := ih hsep.2 hndRest hyRest
      rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, htail⟩
      intro b' hb'
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
      have heb := hsep.1 b hb
      cases e with
      | line x' y' =>
          cases b with
          | line xb yb =>
              simpa [replaceHoleLine] using heb
          | hole q =>
              by_cases hq : q = j
              · subst q
                simp only [replaceHoleLine, if_pos rfl, DSEntry.Sep]
                intro hxx hyy
                apply hy
                simp [dupTargets, hxx.symm, hyy]
              · simp [replaceHoleLine, hq, DSEntry.Sep]
          | tline q xb => simp [replaceHoleLine, DSEntry.Sep]
      | hole q =>
          by_cases hq : q = j
          · subst q
            have hjrest : j ∉ entryCoords rest := by
              change (j :: entryCoords rest).Nodup at hnd
              exact (List.nodup_cons.mp hnd).1
            cases b with
            | line xb yb =>
                simp only [replaceHoleLine, if_pos rfl, DSEntry.Sep]
                intro hxx hyy
                apply hy
                simp only [dupTargets, List.mem_filterMap]
                refine ⟨DSEntry.line xb yb,
                  List.mem_cons_of_mem _ hb, ?_⟩
                simp [hxx, hyy]
            | hole qb =>
                have hqb : qb ≠ j := by
                  intro heq
                  subst qb
                  apply hjrest
                  simp only [entryCoords, List.mem_filterMap]
                  exact ⟨DSEntry.hole j, hb, rfl⟩
                simp [replaceHoleLine, hqb, DSEntry.Sep]
            | tline qb xb => simp [replaceHoleLine, DSEntry.Sep]
          · simp [replaceHoleLine, hq, DSEntry.Sep]
      | tline q x' => simp [replaceHoleLine, DSEntry.Sep]

omit [Field F] [SampleableType F] [Fintype F] in
theorem map_replaceHoleLine_eq_self_of_not_mem (shadow : List (DSEntry F))
    (j : Nat) (x y : F) (h : DSEntry.hole j ∉ shadow) :
    shadow.map (replaceHoleLine j x y) = shadow := by
  induction shadow with
  | nil => rfl
  | cons e rest ih =>
      have he : e ≠ DSEntry.hole j := by
        intro heq
        apply h
        subst e
        exact List.mem_cons_self
      have hr : DSEntry.hole j ∉ rest := by
        intro hm
        exact h (List.mem_cons_of_mem e hm)
      simp [replaceHoleLine, he, ih hr]

omit [Field F] [SampleableType F] [Fintype F] in
/-- A tape-line, like a hole, contributes one charge against every existing
entry. -/
theorem scCount_tline_cons (j : Nat) (x : F) (shadow : List (DSEntry F)) :
    scCount (DSEntry.tline j x :: shadow) =
      shadow.length + scCount shadow := by
  have h : (shadow.map (fun e' =>
      if (DSEntry.tline j x).clash e' then 0 else 1)).sum = shadow.length := by
    induction shadow with
    | nil => rfl
    | cons e rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih]
        cases e <;> simp [DSEntry.clash] <;> omega
  simp [scCount, h]

/-- The head-against-tail contribution used by `scCount` for a concrete
line. -/
def lineCharge (x y : F) (shadow : List (DSEntry F)) : Nat :=
  (shadow.map fun e => if (DSEntry.line x y).clash e then 0 else 1).sum

omit [Field F] [SampleableType F] [Fintype F] in
theorem lineCharge_replaceHoleLine_of_ne (x₀ y₀ x y : F) (j : Nat)
    (hxx : x₀ ≠ x) (shadow : List (DSEntry F)) :
    lineCharge x₀ y₀ (shadow.map (replaceHoleLine j x y)) =
      lineCharge x₀ y₀ shadow := by
  unfold lineCharge
  rw [List.map_map]
  refine congrArg List.sum ?_
  refine List.map_congr_left fun e _ => ?_
  cases e with
  | line x' y' => simp [Function.comp_apply, replaceHoleLine]
  | hole q =>
      by_cases hq : q = j
      · subst q
        simp [Function.comp_apply, replaceHoleLine, DSEntry.clash, hxx]
      · simp [Function.comp_apply, replaceHoleLine, DSEntry.clash, hq]
  | tline q x' => simp [Function.comp_apply, replaceHoleLine]

omit [Field F] [SampleableType F] [Fintype F] in
/-- At the same abscissa, replacing the unique hole removes exactly its one
head-pair charge. -/
theorem lineCharge_replaceHoleLine_add_one (x y₀ y : F) (j : Nat)
    (shadow : List (DSEntry F)) (hmem : DSEntry.hole j ∈ shadow)
    (hnd : (entryCoords shadow).Nodup) :
    lineCharge x y₀ (shadow.map (replaceHoleLine j x y)) + 1 =
      lineCharge x y₀ shadow := by
  induction shadow with
  | nil => simp at hmem
  | cons e rest ih =>
      have hndRest := entryCoords_tail_nodup e rest hnd
      by_cases he : e = DSEntry.hole j
      · subst e
        have hjrest : j ∉ entryCoords rest := by
          change (j :: entryCoords rest).Nodup at hnd
          exact (List.nodup_cons.mp hnd).1
        have hnot : DSEntry.hole j ∉ rest := by
          intro hm
          apply hjrest
          simp only [entryCoords, List.mem_filterMap]
          exact ⟨DSEntry.hole j, hm, rfl⟩
        have hmap := map_replaceHoleLine_eq_self_of_not_mem rest j x y hnot
        simp [lineCharge, replaceHoleLine, hmap, DSEntry.clash]
        omega
      · have hmrest : DSEntry.hole j ∈ rest := by
          rcases List.mem_cons.mp hmem with h | h
          · exact (he h.symm).elim
          · exact h
        have hi := ih hmrest hndRest
        simp only [lineCharge, List.map_cons, List.map_map,
          Function.comp_apply, List.sum_cons] at hi ⊢
        rw [show replaceHoleLine j x y e = e by
          simp [replaceHoleLine, he]]
        omega

omit [Field F] [SampleableType F] in
/-- Replacing the unique hole by a concrete line removes exactly the
same-abscissa concrete-line charges listed by `dupTargets`. -/
theorem scCount_map_replaceHoleLine_add_dupTargets
    (shadow : List (DSEntry F)) (j : Nat) (x y : F)
    (hmem : DSEntry.hole j ∈ shadow) (hnd : (entryCoords shadow).Nodup) :
    scCount (shadow.map (replaceHoleLine j x y)) +
        (dupTargets x shadow).length = scCount shadow := by
  induction shadow with
  | nil => simp at hmem
  | cons e rest ih =>
      have hndRest := entryCoords_tail_nodup e rest hnd
      by_cases he : e = DSEntry.hole j
      · subst e
        have hjrest : j ∉ entryCoords rest := by
          change (j :: entryCoords rest).Nodup at hnd
          exact (List.nodup_cons.mp hnd).1
        have hnot : DSEntry.hole j ∉ rest := by
          intro hm
          apply hjrest
          simp only [entryCoords, List.mem_filterMap]
          exact ⟨DSEntry.hole j, hm, rfl⟩
        have hmap := map_replaceHoleLine_eq_self_of_not_mem rest j x y hnot
        simpa [replaceHoleLine, hmap, dupTargets_cons,
          scCount_hole_cons] using scCount_line_cons x y rest
      · have hmrest : DSEntry.hole j ∈ rest := by
          rcases List.mem_cons.mp hmem with h | h
          · exact (he h.symm).elim
          · exact h
        have hi := ih hmrest hndRest
        cases e with
        | line x₀ y₀ =>
            by_cases hxx : x₀ = x
            · subst x₀
              have hc := lineCharge_replaceHoleLine_add_one
                x y₀ y j rest hmrest hndRest
              simp only [List.map_cons, scCount]
              change lineCharge x y₀
                    (rest.map (replaceHoleLine j x y)) +
                  scCount (rest.map (replaceHoleLine j x y)) +
                  (dupTargets x (DSEntry.line x y₀ :: rest)).length = _
              rw [dupTargets_cons]
              simp only [if_pos rfl, List.length_append, List.length_cons,
                List.length_nil]
              change _ + _ + (1 + (dupTargets x rest).length) =
                lineCharge x y₀ rest + scCount rest
              omega
            · have hc := lineCharge_replaceHoleLine_of_ne
                x₀ y₀ x y j hxx rest
              simp only [List.map_cons, scCount]
              change lineCharge x₀ y₀
                    (rest.map (replaceHoleLine j x y)) +
                  scCount (rest.map (replaceHoleLine j x y)) +
                  (dupTargets x (DSEntry.line x₀ y₀ :: rest)).length = _
              rw [dupTargets_cons]
              simp only [if_neg (Ne.symm hxx), List.nil_append]
              change _ + _ + (dupTargets x rest).length =
                lineCharge x₀ y₀ rest + scCount rest
              omega
        | hole q =>
            have hq : q ≠ j := by
              intro hqj
              apply he
              subst q
              rfl
            simp only [List.map_cons]
            rw [show replaceHoleLine j x y (.hole q) = .hole q by
              simp [replaceHoleLine, hq]]
            rw [scCount_hole_cons, scCount_hole_cons, dupTargets_cons]
            simp only [List.length_map, List.nil_append]
            omega
        | tline q x₀ =>
            simp only [List.map_cons]
            rw [show replaceHoleLine j x y (.tline q x₀) = .tline q x₀ by
              simp [replaceHoleLine]]
            rw [scCount_tline_cons, scCount_tline_cons, dupTargets_cons]
            simp only [List.length_map, List.nil_append]
            omega

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
theorem entry_eq_of_coord_nodup {shadow : List (DSEntry F)}
    (hnd : (entryCoords shadow).Nodup) {a b : DSEntry F}
    (ha : a ∈ shadow) (hb : b ∈ shadow) {j : Nat}
    (hca : a.coord = some j) (hcb : b.coord = some j) : a = b := by
  induction shadow generalizing a b j with
  | nil => simp at ha
  | cons e rest ih =>
      cases hec : e.coord with
      | none =>
          have hr : (entryCoords rest).Nodup := by
            simpa [entryCoords, hec] using hnd
          rcases List.mem_cons.1 ha with rfl | ha
          · simp [hec] at hca
          rcases List.mem_cons.1 hb with rfl | hb
          · simp [hec] at hcb
          exact ih hr ha hb hca hcb
      | some q =>
          have hc : (q :: entryCoords rest).Nodup := by
            simpa [entryCoords, hec] using hnd
          rw [List.nodup_cons] at hc
          rcases hc with ⟨hq, hr⟩
          rcases List.mem_cons.1 ha with rfl | ha
          · rcases List.mem_cons.1 hb with rfl | hb
            · rfl
            · exfalso
              apply hq
              simp only [entryCoords, List.mem_filterMap]
              refine ⟨b, hb, ?_⟩
              have hqj : q = j := by
                exact Option.some.inj (hec.symm.trans hca)
              simpa [hqj] using hcb
          · have haj : j ∈ entryCoords rest := by
              simp only [entryCoords, List.mem_filterMap]
              exact ⟨a, ha, hca⟩
            rcases List.mem_cons.1 hb with rfl | hb
            · exfalso
              apply hq
              have hqj : q = j := by
                exact Option.some.inj (hec.symm.trans hcb)
              simpa [hqj] using haj
            · exact ih hr ha hb hca hcb

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
  exact hne (entry_eq_of_coord_nodup h.hnd he hh hq rfl)

omit [SampleableType F] [Fintype F] in
/-- The consumed coordinate is an unread dummy in the concrete-line
successor. -/
theorem DSShadowInvStrong.consumeHoleLine_coord_unused
    {sigma : DSShadowSt F M} {m i j : Nat}
    (h : DSShadowInvStrong sigma m)
    (hi : sigma.pat i = some (.hole j)) (x y : F) :
    j ∉ entryCoords (sigma.consumeHoleLine i j x y).shadow := by
  apply not_mem_entryCoords_map_replaceHoleLine
  intro e he hc
  have hh : DSEntry.hole j ∈ sigma.shadow := h.hpat i j hi
  exact entry_eq_of_coord_nodup h.hnd he hh hc rfl

omit [SampleableType F] [Fintype F] in
/-- If a coordinate is absent from the owned shadow, changing that dummy
tape coordinate does not change the seeded concrete state. -/
theorem DSShadowInvStrong.seed_set_of_coord_not_mem
    {sigma : DSShadowSt F M} {m j : Nat}
    (h : DSShadowInvStrong sigma m) (hj : j ∉ entryCoords sigma.shadow)
    (k w : F) (vs : List F) :
    sigma.seed k (vs.set j w) = sigma.seed k vs := by
  apply dsFrameSt_ext
  · rfl
  · funext i
    simp only [DSShadowSt.seed_slope]
    cases hi : sigma.pat i with
    | none => simp [hi]
    | some e =>
        simp only [hi, Option.map_some]
        congr 1
        apply DSEntry.eval_set_ne
        intro q hq hqj
        subst q
        apply hj
        simp only [entryCoords, List.mem_filterMap]
        exact ⟨e, h.hpat_mem i e hi, hq⟩
  · apply frameAudit_ext
    · rfl
    · rfl
    · simp only [DSShadowSt.seed_audit]
      refine List.map_congr_left fun e he => ?_
      apply DSEntry.eval_set_ne
      intro q hq hqj
      subst q
      apply hj
      simp only [entryCoords, List.mem_filterMap]
      exact ⟨e, he, hq⟩

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
  · exact ⟨h.hx, h.hsep, h.hlt, h.hnd, h.hroX, h.hpat,
      h.hpatinj, h.hfresh⟩
  · exact h.hpat_mem

omit [SampleableType F] [Fintype F] in
/-- Merely recording a slope probe preserves the invariant. -/
theorem DSShadowInvStrong.addSlopeProbe {sigma : DSShadowSt F M} {m : Nat}
    (h : DSShadowInvStrong sigma m) (q : F) :
    DSShadowInvStrong (sigma.addSlopeProbe q) m := by
  refine ⟨?_, ?_⟩
  · exact ⟨h.hx, h.hsep, h.hlt, h.hnd, h.hroX, h.hpat,
      h.hpatinj, h.hfresh⟩
  · exact h.hpat_mem

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
    simp only [DSShadowSt.seed_slope]
    by_cases hqi : q = i
    · subst q
      simp [DSShadowSt.seed, DSShadowSt.insertEntry, hi, DSEntry.eval,
        List.getD, hlen]
    · simp only [DSShadowSt.insertEntry, Function.update_of_ne hqi]
      change (sigma.pat q).map (DSEntry.eval k (vs ++ [v])) =
        (sigma.pat q).map (DSEntry.eval k vs)
      cases hq : sigma.pat q with
      | none => simp [hq]
      | some e =>
          simp only [hq, Option.map_some]
          congr 1
          apply DSEntry.eval_append_lt
          intro j hj
          rw [hlen]
          exact hInv.pat_coord_lt hq hj
  · apply frameAudit_ext
    · rfl
    · rfl
    · simp only [DSShadowSt.seed_audit, DSShadowSt.insertEntry,
        List.map_cons]
      congr 1
      · simp [DSEntry.eval, List.getD, hlen]
      · refine List.map_congr_left fun e he => ?_
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
      exact h.hsep.imp fun {a b} hab => sep_replaceHole j x a b hab
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

/-- Consuming the current pending hole into its concrete public line and
advancing the honest counter preserves the strong invariant away from the
listed duplicate ordinates.  Coordinate `j` becomes unused. -/
theorem DSShadowInvStrong.consumeHoleLine_advance
    {sigma : DSShadowSt F M} {m j : Nat} (h : DSShadowInvStrong sigma m)
    (ideal : IdealFrameSt F M) (x y : F)
    (hi : sigma.pat sigma.ideal.idx = some (.hole j))
    (hidx : ideal.idx = sigma.ideal.idx + 1)
    (hroX : RoXCacheNonzero ideal.roX) (hx : x ≠ 0)
    (hy : y ∉ dupTargets x sigma.shadow) :
    DSShadowInvStrong
      ((sigma.consumeHoleLine sigma.ideal.idx j x y).setIdeal ideal) m := by
  have hhole : DSEntry.hole j ∈ sigma.shadow :=
    h.hpat sigma.ideal.idx j hi
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, hroX, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact xne0_replaceHoleLine j x y hx e0 (h.hx e0 he0)
    · exact pairwise_sep_map_replaceHoleLine sigma.shadow j x y
        h.hsep h.hnd hy
    · intro q hq
      exact h.hlt q
        (mem_entryCoords_of_mem_map_replaceHoleLine
          sigma.shadow j x y q hq)
    · exact nodup_entryCoords_map_replaceHoleLine
        sigma.shadow j x y h.hnd
    · intro q l hq
      have hqi : q ≠ sigma.ideal.idx := by
        intro heq
        subst q
        simp [DSShadowSt.setIdeal, DSShadowSt.consumeHoleLine] at hq
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHoleLine,
        Function.update_of_ne hqi] at hq
      have hlj : l ≠ j := by
        intro heq
        subst l
        exact hqi (h.hpatinj q sigma.ideal.idx j hq hi)
      refine List.mem_map.2 ⟨.hole l, h.hpat q l hq, ?_⟩
      simp [replaceHoleLine, hlj]
    · intro q q' l hq hq'
      have hqi : q ≠ sigma.ideal.idx := by
        intro heq
        subst q
        simp [DSShadowSt.setIdeal, DSShadowSt.consumeHoleLine] at hq
      have hq'i : q' ≠ sigma.ideal.idx := by
        intro heq
        subst q'
        simp [DSShadowSt.setIdeal, DSShadowSt.consumeHoleLine] at hq'
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHoleLine,
        Function.update_of_ne hqi] at hq
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHoleLine,
        Function.update_of_ne hq'i] at hq'
      exact h.hpatinj q q' l hq hq'
    · intro q hq e he
      have hqi : q ≠ sigma.ideal.idx := by
        intro heq
        subst q
        change ideal.idx ≤ sigma.ideal.idx at hq
        rw [hidx] at hq
        omega
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHoleLine,
        Function.update_of_ne hqi] at he
      apply h.hfresh q
      · change sigma.ideal.idx ≤ q
        change ideal.idx ≤ q at hq
        omega
      · exact he
  · intro q e he
    by_cases hqi : q = sigma.ideal.idx
    · subst q
      simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHoleLine,
        Function.update_self] at he
      have heq : e = .line x y := (Option.some.inj he).symm
      subst e
      refine List.mem_map.2 ⟨.hole j, hhole, ?_⟩
      simp [replaceHoleLine]
    · simp only [DSShadowSt.setIdeal, DSShadowSt.consumeHoleLine,
        Function.update_of_ne hqi] at he
      have hne : e ≠ .hole j := by
        intro heq
        subst e
        exact hqi (h.hpatinj q sigma.ideal.idx j he hi)
      refine List.mem_map.2 ⟨e, h.hpat_mem q e he, ?_⟩
      simp [replaceHoleLine, hne]

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
  have hget :
      (vs.set j (k + vs.getD j 0 * x)).getD j 0 =
        k + vs.getD j 0 * x := by
    simp [List.getD, hjv]
  apply dsFrameSt_ext
  · rfl
  · funext q
    by_cases hqi : q = i
    · subst q
      simp only [DSShadowSt.seed_slope, DSShadowSt.consumeHole,
        Function.update_self, Option.map_some, DSEntry.eval]
      rw [hget]
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
          apply congrArg some
          apply DSEntry.eval_set_ne
          exact hInv.coord_ne_of_mem_of_ne_hole hi
            (hInv.hpat_mem q e hq) hne
  · apply frameAudit_ext
    · rfl
    · rfl
    · simp only [DSShadowSt.seed_audit, DSShadowSt.consumeHole,
        List.map_map]
      refine List.map_congr_left fun e he => ?_
      by_cases heq : e = .hole j
      · subst e
        simp only [Function.comp_apply]
        rw [show replaceHole j x (.hole j) = .tline j x by
          simp [replaceHole]]
        simp only [DSEntry.eval]
        simp [List.getD, hjv]
        rw [mul_div_cancel_right₀ _ hx]
      · simp only [Function.comp_apply]
        rw [show replaceHole j x e = e by simp [replaceHole, heq]]
        apply DSEntry.eval_set_ne
        exact hInv.coord_ne_of_mem_of_ne_hole hi he heq

omit [SampleableType F] [Fintype F] in
/-- Replacing an owned hole by the concrete line actually returned by the
handler leaves the seeded slope cache and audit unchanged. -/
theorem seed_consumeHoleLine (sigma : DSShadowSt F M) (i j : Nat)
    (k x : F) (vs : List F) (hi : sigma.pat i = some (.hole j))
    (hx : x ≠ 0) :
    (sigma.consumeHoleLine i j x (rlnY k (vs.getD j 0) x)).seed k vs =
      sigma.seed k vs := by
  apply dsFrameSt_ext
  · rfl
  · funext q
    by_cases hqi : q = i
    · subst q
      simp only [DSShadowSt.seed_slope, DSShadowSt.consumeHoleLine,
        Function.update_self, Option.map_some, DSEntry.eval]
      rw [hi]
      simp only [Option.map_some, DSEntry.eval, rlnY]
      rw [add_sub_cancel_left, mul_div_cancel_right₀ _ hx]
    · simp [DSShadowSt.seed_slope, DSShadowSt.consumeHoleLine,
        Function.update_of_ne hqi]
  · apply frameAudit_ext
    · rfl
    · rfl
    · simp only [DSShadowSt.seed_audit, DSShadowSt.consumeHoleLine,
        List.map_map]
      refine List.map_congr_left fun e he => ?_
      by_cases heq : e = .hole j
      · subst e
        simp only [Function.comp_apply]
        rw [show replaceHoleLine j x (rlnY k (vs.getD j 0) x) (.hole j) =
            .line x (rlnY k (vs.getD j 0) x) by
          simp [replaceHoleLine]]
        simp only [DSEntry.eval, rlnY]
        rw [add_sub_cancel_left, mul_div_cancel_right₀ _ hx]
      · simp [Function.comp_apply, replaceHoleLine, heq]

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
  ring_nf <;> omega

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
  ring_nf at hc ⊢
  omega

/-- The potential of an inserted concrete line depends on its abscissa but
not on its ordinate. -/
theorem dsBudget_insertLine_y_eq (sigma : DSShadowSt F M) (i : Nat)
    (x y y' : F) (nA nE nId nNf nSig : Nat) :
    dsBudget (sigma.insertEntry i (.line x y)) nA nE nId nNf nSig =
      dsBudget (sigma.insertEntry i (.line x y')) nA nE nId nNf nSig := by
  have h := scCount_line_cons x y sigma.shadow
  have h' := scCount_line_cons x y' sigma.shadow
  simp only [dsBudget, DSShadowSt.insertEntry, List.length_cons]
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
  ring_nf
  omega

/-- Exact potential delta for concrete-line hole consumption.  The
`dupTargets` charge plus the good successor leaves the unused signal-query
margin: all prior slope probes, one cross-pair per existing shadow entry, and
one cross-pair per future signal. -/
theorem dsBudget_consumeHoleLine_delta (sigma : DSShadowSt F M)
    (i j : Nat) (x y : F) (nA nE nId nNf nSig : Nat)
    (hmem : DSEntry.hole j ∈ sigma.shadow)
    (hnd : (entryCoords sigma.shadow).Nodup) :
    (dupTargets x sigma.shadow).length +
        dsBudget (sigma.consumeHoleLine i j x y) nA nE nId nNf nSig +
        (sigma.slopeProbes.length + nNf + sigma.shadow.length + nSig) =
      dsBudget sigma nA nE nId nNf (nSig + 1) := by
  have hc := scCount_map_replaceHoleLine_add_dupTargets
    sigma.shadow j x y hmem hnd
  have hl : (sigma.shadow.map (replaceHoleLine j x y)).length =
      sigma.shadow.length := List.length_map _
  simp only [dsBudget, DSShadowSt.consumeHoleLine, hl, choose_succ_two]
  ring_nf at hc ⊢
  omega

/-- The duplicate-ordinate union-bound charge and the good concrete-line
successor fit inside the predecessor signal-query potential. -/
theorem dsBudget_consumeHoleLine_add_dupTargets_le
    (sigma : DSShadowSt F M) (i j : Nat) (x y : F)
    (nA nE nId nNf nSig : Nat) (hmem : DSEntry.hole j ∈ sigma.shadow)
    (hnd : (entryCoords sigma.shadow).Nodup) :
    (dupTargets x sigma.shadow).length +
        dsBudget (sigma.consumeHoleLine i j x y) nA nE nId nNf nSig ≤
      dsBudget sigma nA nE nId nNf (nSig + 1) := by
  have hdelta := dsBudget_consumeHoleLine_delta sigma i j x y
    nA nE nId nNf nSig hmem hnd
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
  simp [dsBudget, DSShadowSt.addSlopeProbe, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm]

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
  refine le_trans (probEvent_bind_mono_of_le
    (drawList ($ᵗ F) m)
    (fun vs => ($ᵗ F) >>= fun k =>
      pure (k, (a, sigma.seed k vs)))
    (fun vs => ($ᵗ F) >>= fun k => pure (vs, k))
    (fun w : F × (alpha × DSFrameSt F M) =>
      FrameLeakBad w.1 w.2.2.audit)
    (fun w : List F × F =>
      FrameLeakBad w.2
        ⟨sigma.secretProbes, sigma.slopeProbes,
          sigma.shadow.map (DSEntry.eval w.2 w.1)⟩)
    (fun vs => ?_)) ?_
  · refine probEvent_bind_mono_of_le ($ᵗ F)
      (fun k => pure (k, (a, sigma.seed k vs)))
      (fun k => pure (vs, k)) _ _ (fun k => ?_)
    simp [DSShadowSt.seed_audit]
    exact le_rfl
  · simpa [dsBudget] using hleaf

/-! ## Adaptive master induction -/

theorem dsBudget_base_le (sigma : DSShadowSt F M)
    (nA nE nId nNf nSig : Nat) :
    dsBudget sigma 0 0 0 0 0 ≤ dsBudget sigma nA nE nId nNf nSig := by
  simp [dsBudget]
  ring_nf
  omega

/-- A freshly sampled slope can be reparameterized by its public line
ordinate at any fixed nonzero abscissa. -/
theorem rlnY_bijective (k x : F) (hx : x ≠ 0) :
    Function.Bijective (fun a : F => rlnY k a x) := by
  constructor
  · intro a b hab
    simp only [rlnY, add_left_inj] at hab
    exact mul_right_cancel₀ hx hab
  · intro y
    refine ⟨(y - k) / x, ?_⟩
    simp only [rlnY]
    rw [div_mul_cancel₀ _ hx]
    ring

/-- A freshly sampled slope can be reparameterized by its public line
ordinate at any fixed nonzero abscissa. -/
theorem evalDist_rlnY_uniform {beta : Type} (k x : F) (hx : x ≠ 0)
    (G : F → ProbComp beta) :
    𝒟[($ᵗ F) >>= fun a => G (rlnY k a x)] =
      𝒟[($ᵗ F) >>= G] := by
  calc
    𝒟[($ᵗ F) >>= fun a => G (rlnY k a x)] =
        𝒟[($ᵗ F) >>= fun a => G (a * x + k)] := by
          refine evalDist_bind_congr' ($ᵗ F) fun a => ?_
          simp [rlnY, add_comm]
    _ = 𝒟[($ᵗ F) >>= G] :=
      evalDist_bind_bijective_add_right_uniform F
        (fun a : F => a * x) (mulRight_bijective₀ x hx) k G

/-- Extract a tape coordinate through a bijection while replacing that
coordinate by an independent fresh dummy.  The result exposes the extracted
value as an independent uniform draw and leaves a fresh tape of the same
length. -/
theorem evalDist_drawList_extract_replace {beta : Type} (m j : Nat)
    (hj : j < m) (phi : F → F) (hphi : Function.Bijective phi)
    (G : F → List F → ProbComp beta) :
    𝒟[drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun w =>
        G (phi (vs.getD j 0)) (vs.set j w)] =
      𝒟[($ᵗ F) >>= fun y => drawList ($ᵗ F) m >>= fun vs =>
        G y vs] := by
  induction m generalizing j G with
  | zero => omega
  | succ m ih =>
      rw [show drawList ($ᵗ F) (m + 1) =
          (($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
            pure (v :: ws)) from rfl]
      simp only [bind_assoc, pure_bind]
      cases j with
      | zero =>
          calc
            𝒟[($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
                ($ᵗ F) >>= fun w =>
                  G (phi ((v :: ws).getD 0 0)) ((v :: ws).set 0 w)] =
              𝒟[($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
                ($ᵗ F) >>= fun w => G (phi v) (w :: ws)] := by
                  refine evalDist_bind_congr' ($ᵗ F) fun v => ?_
                  refine evalDist_bind_congr' (drawList ($ᵗ F) m)
                    fun ws => ?_
                  simp
            _ = 𝒟[($ᵗ F) >>= fun v => ($ᵗ F) >>= fun w =>
                drawList ($ᵗ F) m >>= fun ws => G (phi v) (w :: ws)] := by
                  refine evalDist_bind_congr' ($ᵗ F) fun v => ?_
                  exact OracleComp.DeferredSampling.evalDist_bind_comm
                    (drawList ($ᵗ F) m) ($ᵗ F)
                      (fun ws w => G (phi v) (w :: ws))
            _ = 𝒟[($ᵗ F) >>= fun y => ($ᵗ F) >>= fun w =>
                drawList ($ᵗ F) m >>= fun ws => G y (w :: ws)] := by
                  have hpad := evalDist_bind_bijective_add_right_uniform F
                    phi hphi 0 (fun y => ($ᵗ F) >>= fun w =>
                      drawList ($ᵗ F) m >>= fun ws => G y (w :: ws))
                  simpa using hpad
      | succ j =>
          calc
            𝒟[($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
                ($ᵗ F) >>= fun w =>
                  G (phi ((v :: ws).getD (j + 1) 0))
                    ((v :: ws).set (j + 1) w)] =
              𝒟[($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
                ($ᵗ F) >>= fun w =>
                  G (phi (ws.getD j 0)) (v :: ws.set j w)] := by
                    refine evalDist_bind_congr' ($ᵗ F) fun v => ?_
                    refine evalDist_bind_congr' (drawList ($ᵗ F) m)
                      fun ws => ?_
                    simp
            _ = 𝒟[($ᵗ F) >>= fun v => ($ᵗ F) >>= fun y =>
                drawList ($ᵗ F) m >>= fun ws => G y (v :: ws)] := by
                  refine evalDist_bind_congr' ($ᵗ F) fun v => ?_
                  exact ih j (by omega) (fun y ws => G y (v :: ws))
            _ = 𝒟[($ᵗ F) >>= fun y => ($ᵗ F) >>= fun v =>
                drawList ($ᵗ F) m >>= fun ws => G y (v :: ws)] :=
                  OracleComp.DeferredSampling.evalDist_bind_comm
                    ($ᵗ F) ($ᵗ F)
                      (fun v y => drawList ($ᵗ F) m >>= fun ws =>
                        G y (v :: ws))

/-- Concrete-line hole-consumption potential is independent of the public
ordinate once the owned-hole hypotheses are fixed. -/
theorem dsBudget_consumeHoleLine_y_eq (sigma : DSShadowSt F M)
    (i j : Nat) (x y y' : F) (nA nE nId nNf nSig : Nat)
    (hmem : DSEntry.hole j ∈ sigma.shadow)
    (hnd : (entryCoords sigma.shadow).Nodup) :
    dsBudget (sigma.consumeHoleLine i j x y) nA nE nId nNf nSig =
      dsBudget (sigma.consumeHoleLine i j x y') nA nE nId nNf nSig := by
  have h := dsBudget_consumeHoleLine_delta sigma i j x y
    nA nE nId nNf nSig hmem hnd
  have h' := dsBudget_consumeHoleLine_delta sigma i j x y'
    nA nE nId nNf nSig hmem hnd
  omega

/-- Seed insensitivity needs only pattern ownership and coordinate absence;
separation is irrelevant.  This raw form is used before splitting off the
duplicate-ordinate event. -/
theorem DSShadowSt.seed_set_of_coord_not_mem_raw
    (sigma : DSShadowSt F M) (j : Nat)
    (hpat : forall i e, sigma.pat i = some e -> e ∈ sigma.shadow)
    (hj : j ∉ entryCoords sigma.shadow) (k w : F) (vs : List F) :
    sigma.seed k (vs.set j w) = sigma.seed k vs := by
  apply dsFrameSt_ext
  · rfl
  · funext i
    simp only [DSShadowSt.seed_slope]
    cases hi : sigma.pat i with
    | none => simp [hi]
    | some e =>
        simp only [hi, Option.map_some]
        apply congrArg some
        apply DSEntry.eval_set_ne
        intro q hq hqj
        subst q
        apply hj
        simp only [entryCoords, List.mem_filterMap]
        exact ⟨e, hpat i e hi, hq⟩
  · apply frameAudit_ext
    · rfl
    · rfl
    · simp only [DSShadowSt.seed_audit]
      refine List.map_congr_left fun e he => ?_
      apply DSEntry.eval_set_ne
      intro q hq hqj
      subst q
      apply hj
      simp only [entryCoords, List.mem_filterMap]
      exact ⟨e, he, hq⟩

omit [SampleableType F] [Fintype F] in
/-- Pattern ownership is preserved when the owned hole is replaced by a
concrete line, independently of the line's separation side condition. -/
theorem DSShadowInvStrong.hpat_mem_consumeHoleLine
    {sigma : DSShadowSt F M} {m i j : Nat}
    (h : DSShadowInvStrong sigma m)
    (hi : sigma.pat i = some (.hole j)) (x y : F) :
    forall q e, (sigma.consumeHoleLine i j x y).pat q = some e ->
      e ∈ (sigma.consumeHoleLine i j x y).shadow := by
  intro q e he
  have hhole : DSEntry.hole j ∈ sigma.shadow := h.hpat i j hi
  by_cases hqi : q = i
  · subst q
    simp only [DSShadowSt.consumeHoleLine, Function.update_self] at he
    have heq : e = .line x y := (Option.some.inj he).symm
    subst e
    refine List.mem_map.2 ⟨.hole j, hhole, ?_⟩
    simp [replaceHoleLine]
  · simp only [DSShadowSt.consumeHoleLine,
      Function.update_of_ne hqi] at he
    have hne : e ≠ .hole j := by
      intro heq
      subst e
      exact hqi (h.hpatinj q i j he hi)
    refine List.mem_map.2 ⟨e, h.hpat_mem q e he, ?_⟩
    simp [replaceHoleLine, hne]

omit [SampleableType F] [Fintype F] in
/-- After extracting the public ordinate, the replacement tape coordinate
is a dummy: seeding the concrete-line successor still gives the original
concrete state. -/
theorem seed_consumeHoleLine_set_dummy (sigma : DSShadowSt F M)
    (m i j : Nat) (k x w : F) (vs : List F)
    (h : DSShadowInvStrong sigma m)
    (hi : sigma.pat i = some (.hole j)) (hx : x ≠ 0) :
    (sigma.consumeHoleLine i j x (rlnY k (vs.getD j 0) x)).seed k
        (vs.set j w) = sigma.seed k vs := by
  rw [DSShadowSt.seed_set_of_coord_not_mem_raw
    (sigma.consumeHoleLine i j x (rlnY k (vs.getD j 0) x)) j
    (h.hpat_mem_consumeHoleLine hi x (rlnY k (vs.getD j 0) x))
    (h.consumeHoleLine_coord_unused hi x (rlnY k (vs.getD j 0) x))
    k w vs]
  exact seed_consumeHoleLine sigma i j k x vs hi hx

/-- Seeded-shadow master bound for an arbitrary query-bounded FRAME
computation. -/
theorem dsFrameImpl_seeded_bad_le (mclose : M) {alpha : Type}
    (oa : OracleComp (frameSpec F M) alpha) (sigma : DSShadowSt F M)
    (m nA nE nId nNf nSig : Nat) (hInv : DSShadowInvStrong sigma m)
    (hA : OracleComp.IsQueryBoundP oa
      (fun t => isDirectRoAQuery t = true) nA)
    (hE : OracleComp.IsQueryBoundP oa
      (fun t => isDirectRoEQuery t = true) nE)
    (hId : OracleComp.IsQueryBoundP oa
      (fun t => isDirectRoIdQuery t = true) nId)
    (hNf : OracleComp.IsQueryBoundP oa
      (fun t => isDirectRoNfQuery t = true) nNf)
    (hSig : OracleComp.IsQueryBoundP oa
      (fun t => isSignalQuery t = true) nSig) :
    Pr[dsSeededBad | dsSeededRun mclose oa sigma m]
      ≤ (dsBudget sigma nA nE nId nNf nSig : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing
      sigma m nA nE nId nNf nSig with
  | pure a =>
      refine (dsSeededRun_pure_bad_le mclose a sigma m hInv).trans ?_
      exact mul_le_mul_right' (Nat.cast_le.2
        (dsBudget_base_le sigma nA nE nId nNf nSig)) _
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at hA hE hId hNf hSig
      simp only [dsSeededRun, simulateQ_query_bind,
        OracleQuery.input_query, monadLift_self, StateT.run_bind]
      cases t with
      | spend msg =>
          have hposSig : 0 < nSig := by
            rcases hSig.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [dsFrameImpl, StateT.run_mk, DSShadowSt.seed_ideal]
          by_cases hc : sigma.ideal.closed = true
          · simp only [hc, if_pos, pure_bind, OracleQuery.cont_query]
            have hih := ih none sigma m nA nE nId nNf (nSig - 1) hInv
              (by simpa [isDirectRoAQuery] using hA.2 none)
              (by simpa [isDirectRoEQuery] using hE.2 none)
              (by simpa [isDirectRoIdQuery] using hId.2 none)
              (by simpa [isDirectRoNfQuery] using hNf.2 none)
              (by simpa [isSignalQuery] using hSig.2 none)
            refine le_trans (by simpa [dsSeededRun] using hih) ?_
            refine mul_le_mul_right' (Nat.cast_le.2 ?_) _
            simpa [Nat.sub_add_cancel hposSig] using
              (dsBudget_signal_same_le sigma nA nE nId nNf (nSig - 1))
          · simp only [hc, if_neg]
            cases hi : sigma.pat sigma.ideal.idx with
            | none =>
                rw [DSShadowSt.seed_slope, hi]
                simp only [Option.map_none, dsTouch, bind_assoc, pure_bind,
                  DSShadowSt.seed_audit, OracleQuery.cont_query]
                refine probEvent_kTape_core_swap_le m
                  (lazyROX sigma.ideal.roX msg) _ dsSeededBad _ ?_
                intro xc hxc
                have hx := lazyROX_support_nonzero hInv.hroX msg xc hxc
                let cF : ENNReal := (Fintype.card F : ENNReal)⁻¹
                let goodBudget : ENNReal :=
                  (dsBudget
                    (sigma.insertEntry sigma.ideal.idx (.line xc.1 0))
                    nA nE nId nNf (nSig - 1) : ENNReal) * cF
                let dupBudget : ENNReal :=
                  ((dupTargets xc.1 sigma.shadow).length : ENNReal) * cF
                have hcanon :
                    Pr[dsSeededBad | ($ᵗ F) >>= fun k =>
                      drawList ($ᵗ F) m >>= fun vs =>
                      ($ᵗ F) >>= fun y =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, y, nc.1⟩))).run
                          (((sigma.insertEntry sigma.ideal.idx
                            (.line xc.1 y)).setIdeal
                              { sigma.ideal with
                                idx := sigma.ideal.idx + 1
                                roX := xc.2
                                honestNf := nc.2 }).seed k vs) >>= fun z =>
                            pure (k, z)] ≤
                      (dsBudget sigma nA nE nId nNf nSig : ENNReal) * cF := by
                  refine le_trans (probEvent_kTape_core_split_le m ($ᵗ F)
                    (fun k vs y =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, y, nc.1⟩))).run
                          (((sigma.insertEntry sigma.ideal.idx
                            (.line xc.1 y)).setIdeal
                              { sigma.ideal with
                                idx := sigma.ideal.idx + 1
                                roX := xc.2
                                honestNf := nc.2 }).seed k vs) >>= fun z =>
                            pure (k, z))
                    dsSeededBad (fun y => y ∈ dupTargets xc.1 sigma.shadow)
                    goodBudget dupBudget
                    (by
                      dsimp [dupBudget, cF]
                      exact probEvent_uniform_mem_list_le _)
                    (fun y _ hy => ?_)) ?_
                  · refine probEvent_kTape_core_swap_le m
                      (lazyRO sigma.ideal.honestNf sigma.ideal.idx)
                      (fun k vs nc =>
                        (simulateQ (dsFrameImpl k mclose)
                          (cont (some ⟨xc.1, y, nc.1⟩))).run
                            (((sigma.insertEntry sigma.ideal.idx
                              (.line xc.1 y)).setIdeal
                                { sigma.ideal with
                                  idx := sigma.ideal.idx + 1
                                  roX := xc.2
                                  honestNf := nc.2 }).seed k vs) >>= fun z =>
                              pure (k, z)) dsSeededBad goodBudget ?_
                    intro nc hnc
                    let ideal' : IdealFrameSt F M :=
                      { sigma.ideal with
                        idx := sigma.ideal.idx + 1
                        roX := xc.2
                        honestNf := nc.2 }
                    let sigma' := (sigma.insertEntry sigma.ideal.idx
                      (.line xc.1 y)).setIdeal ideal'
                    have hinv : DSShadowInvStrong sigma' m :=
                      hInv.insertLine_advance ideal' xc.1 y hi rfl hx.2 hx.1 hy
                    have hih := ih (some ⟨xc.1, y, nc.1⟩) sigma' m
                      nA nE nId nNf (nSig - 1) hinv
                      (by simpa [isDirectRoAQuery] using
                        hA.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoEQuery] using
                        hE.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoIdQuery] using
                        hId.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoNfQuery] using
                        hNf.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isSignalQuery] using
                        hSig.2 (some ⟨xc.1, y, nc.1⟩))
                    have hbud := dsBudget_insertLine_y_eq sigma
                      sigma.ideal.idx xc.1 y 0 nA nE nId nNf (nSig - 1)
                    dsimp [sigma', ideal', goodBudget, cF] at hih ⊢
                    rw [dsBudget_setIdeal, hbud] at hih
                    simpa [dsSeededRun] using hih
                  · dsimp [dupBudget, goodBudget, cF]
                    have hsum := dsBudget_insertLine_add_dupTargets sigma
                      sigma.ideal.idx xc.1 0 nA nE nId nNf (nSig - 1)
                    rw [Nat.sub_add_cancel hposSig] at hsum
                    rw [← Nat.cast_add, hsum]
                refine le_trans (le_of_eq ?_) hcanon
                refine probEvent_bind_congr_inner ($ᵗ F) _ _ dsSeededBad
                  (fun k => ?_)
                refine probEvent_bind_congr_inner (drawList ($ᵗ F) m)
                  _ _ dsSeededBad (fun vs => ?_)
                refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
                let G : F → ProbComp (F × (alpha × DSFrameSt F M)) :=
                  fun y =>
                    lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                    (simulateQ (dsFrameImpl k mclose)
                      (cont (some ⟨xc.1, y, nc.1⟩))).run
                        (((sigma.insertEntry sigma.ideal.idx
                          (.line xc.1 y)).setIdeal
                            { sigma.ideal with
                              idx := sigma.ideal.idx + 1
                              roX := xc.2
                              honestNf := nc.2 }).seed k vs) >>= fun z =>
                          pure (k, z)
                calc
                  𝒟[($ᵗ F) >>= fun a =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, rlnY k a xc.1, nc.1⟩))).run
                          ⟨{ sigma.ideal with
                              idx := sigma.ideal.idx + 1
                              roX := xc.2
                              honestNf := nc.2 },
                            Function.update (sigma.seed k vs).slope
                              sigma.ideal.idx (some a),
                            { (sigma.seed k vs).audit with
                              honestSlopes := a ::
                                (sigma.seed k vs).audit.honestSlopes }⟩
                            >>= fun z => pure (k, z)] =
                      𝒟[($ᵗ F) >>= fun a => G (rlnY k a xc.1)] := by
                        refine evalDist_bind_congr' ($ᵗ F) fun a => ?_
                        dsimp [G]
                        refine evalDist_bind_congr'
                          (lazyRO sigma.ideal.honestNf sigma.ideal.idx)
                          fun nc => ?_
                        rw [DSShadowSt.seed_setIdeal,
                          seed_insertLine sigma sigma.ideal.idx k xc.1
                            (rlnY k a xc.1) vs hi]
                        simp [rlnY, hx.1]
                    _ = 𝒟[($ᵗ F) >>= G] :=
                      evalDist_rlnY_uniform k xc.1 hx.1 G
            | some e =>
                have hehole := hInv.hfresh sigma.ideal.idx le_rfl e hi
                rcases hehole with ⟨j, rfl⟩
                simp only [DSShadowSt.seed_slope, hi, Option.map_some,
                  DSEntry.eval, dsTouch, bind_assoc, pure_bind,
                  DSShadowSt.seed_audit,
                  OracleQuery.cont_query]
                refine probEvent_kTape_core_swap_le m
                  (lazyROX sigma.ideal.roX msg) _ dsSeededBad _ ?_
                intro xc hxc
                have hx := lazyROX_support_nonzero hInv.hroX msg xc hxc
                have hhole : DSEntry.hole j ∈ sigma.shadow :=
                  hInv.hpat sigma.ideal.idx j hi
                have hjm : j < m := hInv.pat_coord_lt hi rfl
                let cF : ENNReal := (Fintype.card F : ENNReal)⁻¹
                let goodBudget : ENNReal :=
                  (dsBudget
                    (sigma.consumeHoleLine sigma.ideal.idx j xc.1 0)
                    nA nE nId nNf (nSig - 1) : ENNReal) * cF
                let dupBudget : ENNReal :=
                  ((dupTargets xc.1 sigma.shadow).length : ENNReal) * cF
                have hcanon :
                    Pr[dsSeededBad | ($ᵗ F) >>= fun k =>
                      drawList ($ᵗ F) m >>= fun vs =>
                      ($ᵗ F) >>= fun y =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, y, nc.1⟩))).run
                          (((sigma.consumeHoleLine sigma.ideal.idx j xc.1 y)
                            .setIdeal
                              { sigma.ideal with
                                idx := sigma.ideal.idx + 1
                                roX := xc.2
                                honestNf := nc.2 }).seed k vs) >>= fun z =>
                            pure (k, z)] ≤
                      (dsBudget sigma nA nE nId nNf nSig : ENNReal) * cF := by
                  refine le_trans (probEvent_kTape_core_split_le m ($ᵗ F)
                    (fun k vs y =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, y, nc.1⟩))).run
                          (((sigma.consumeHoleLine sigma.ideal.idx j xc.1 y)
                            .setIdeal
                              { sigma.ideal with
                                idx := sigma.ideal.idx + 1
                                roX := xc.2
                                honestNf := nc.2 }).seed k vs) >>= fun z =>
                            pure (k, z))
                    dsSeededBad (fun y => y ∈ dupTargets xc.1 sigma.shadow)
                    goodBudget dupBudget
                    (by
                      dsimp [dupBudget, cF]
                      exact probEvent_uniform_mem_list_le _)
                    (fun y _ hy => ?_)) ?_
                  · refine probEvent_kTape_core_swap_le m
                      (lazyRO sigma.ideal.honestNf sigma.ideal.idx)
                      (fun k vs nc =>
                        (simulateQ (dsFrameImpl k mclose)
                          (cont (some ⟨xc.1, y, nc.1⟩))).run
                            (((sigma.consumeHoleLine sigma.ideal.idx j xc.1 y)
                              .setIdeal
                                { sigma.ideal with
                                  idx := sigma.ideal.idx + 1
                                  roX := xc.2
                                  honestNf := nc.2 }).seed k vs) >>= fun z =>
                              pure (k, z)) dsSeededBad goodBudget ?_
                    intro nc hnc
                    let ideal' : IdealFrameSt F M :=
                      { sigma.ideal with
                        idx := sigma.ideal.idx + 1
                        roX := xc.2
                        honestNf := nc.2 }
                    let sigma' := (sigma.consumeHoleLine sigma.ideal.idx
                      j xc.1 y).setIdeal ideal'
                    have hinv : DSShadowInvStrong sigma' m :=
                      hInv.consumeHoleLine_advance ideal' xc.1 y hi rfl
                        hx.2 hx.1 hy
                    have hih := ih (some ⟨xc.1, y, nc.1⟩) sigma' m
                      nA nE nId nNf (nSig - 1) hinv
                      (by simpa [isDirectRoAQuery] using
                        hA.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoEQuery] using
                        hE.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoIdQuery] using
                        hId.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoNfQuery] using
                        hNf.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isSignalQuery] using
                        hSig.2 (some ⟨xc.1, y, nc.1⟩))
                    have hbud := dsBudget_consumeHoleLine_y_eq sigma
                      sigma.ideal.idx j xc.1 y 0 nA nE nId nNf
                        (nSig - 1) hhole hInv.hnd
                    dsimp [sigma', ideal', goodBudget, cF] at hih ⊢
                    rw [dsBudget_setIdeal, hbud] at hih
                    simpa [dsSeededRun] using hih
                  · dsimp [dupBudget, goodBudget, cF]
                    have hsum :=
                      dsBudget_consumeHoleLine_add_dupTargets_le sigma
                        sigma.ideal.idx j xc.1 0 nA nE nId nNf
                        (nSig - 1) hhole hInv.hnd
                    rw [Nat.sub_add_cancel hposSig] at hsum
                    rw [← add_mul, ← Nat.cast_add]
                    exact mul_le_mul_right' (Nat.cast_le.2 hsum) _
                refine le_trans (le_of_eq ?_) hcanon
                refine probEvent_bind_congr_inner ($ᵗ F) _ _ dsSeededBad
                  (fun k => ?_)
                let G : F → List F →
                    ProbComp (F × (alpha × DSFrameSt F M)) :=
                  fun y vs =>
                    lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                    (simulateQ (dsFrameImpl k mclose)
                      (cont (some ⟨xc.1, y, nc.1⟩))).run
                        (((sigma.consumeHoleLine sigma.ideal.idx j xc.1 y)
                          .setIdeal
                            { sigma.ideal with
                              idx := sigma.ideal.idx + 1
                              roX := xc.2
                              honestNf := nc.2 }).seed k vs) >>= fun z =>
                          pure (k, z)
                calc
                  𝒟[drawList ($ᵗ F) m >>= fun vs =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some
                          ⟨xc.1, rlnY k (vs.getD j 0) xc.1, nc.1⟩))).run
                          ⟨{ sigma.ideal with
                              idx := sigma.ideal.idx + 1
                              roX := xc.2
                              honestNf := nc.2 },
                            (sigma.seed k vs).slope,
                            (sigma.seed k vs).audit⟩ >>= fun z => pure (k, z)] =
                      𝒟[drawList ($ᵗ F) m >>= fun vs =>
                        ($ᵗ F) >>= fun w =>
                          G (rlnY k (vs.getD j 0) xc.1) (vs.set j w)] := by
                    refine evalDist_bind_congr' (drawList ($ᵗ F) m)
                      fun vs => ?_
                    have hconst : forall w : F,
                        G (rlnY k (vs.getD j 0) xc.1) (vs.set j w) =
                          (lazyRO sigma.ideal.honestNf
                            sigma.ideal.idx >>= fun nc =>
                            (simulateQ (dsFrameImpl k mclose)
                              (cont (some ⟨xc.1,
                                rlnY k (vs.getD j 0) xc.1, nc.1⟩))).run
                              ⟨{ sigma.ideal with
                                  idx := sigma.ideal.idx + 1
                                  roX := xc.2
                                  honestNf := nc.2 },
                                (sigma.seed k vs).slope,
                                (sigma.seed k vs).audit⟩ >>= fun z =>
                                  pure (k, z)) := by
                      intro w
                      dsimp [G]
                      refine bind_congr fun nc => ?_
                      rw [DSShadowSt.seed_setIdeal,
                        seed_consumeHoleLine_set_dummy sigma m
                          sigma.ideal.idx j k xc.1 w vs hInv hi hx.1]
                    simp_rw [hconst]
                    exact
                      (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                        ($ᵗ F) (probFailure_uniformSample F) _).symm
                  _ = 𝒟[($ᵗ F) >>= fun y =>
                      drawList ($ᵗ F) m >>= fun vs => G y vs] :=
                    evalDist_drawList_extract_replace m j hjm
                      (fun a : F => rlnY k a xc.1)
                      (rlnY_bijective k xc.1 hx.1) G
                  _ = 𝒟[drawList ($ᵗ F) m >>= fun vs =>
                      ($ᵗ F) >>= fun y => G y vs] :=
                    OracleComp.DeferredSampling.evalDist_bind_comm
                      ($ᵗ F) (drawList ($ᵗ F) m) G
      | close =>
          have hposSig : 0 < nSig := by
            rcases hSig.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [dsFrameImpl, StateT.run_mk, DSShadowSt.seed_ideal]
          by_cases hc : sigma.ideal.closed = true
          · simp only [hc, if_pos, pure_bind, OracleQuery.cont_query]
            have hih := ih none sigma m nA nE nId nNf (nSig - 1) hInv
              (by simpa [isDirectRoAQuery] using hA.2 none)
              (by simpa [isDirectRoEQuery] using hE.2 none)
              (by simpa [isDirectRoIdQuery] using hId.2 none)
              (by simpa [isDirectRoNfQuery] using hNf.2 none)
              (by simpa [isSignalQuery] using hSig.2 none)
            refine le_trans (by simpa [dsSeededRun] using hih) ?_
            refine mul_le_mul_right' (Nat.cast_le.2 ?_) _
            simpa [Nat.sub_add_cancel hposSig] using
              (dsBudget_signal_same_le sigma nA nE nId nNf (nSig - 1))
          · simp only [hc, if_neg]
            cases hi : sigma.pat sigma.ideal.idx with
            | none =>
                rw [DSShadowSt.seed_slope, hi]
                simp only [Option.map_none, dsTouch, bind_assoc, pure_bind,
                  DSShadowSt.seed_audit, OracleQuery.cont_query]
                refine probEvent_kTape_core_swap_le m
                  (lazyROX sigma.ideal.roX mclose) _ dsSeededBad _ ?_
                intro xc hxc
                have hx := lazyROX_support_nonzero hInv.hroX mclose xc hxc
                let cF : ENNReal := (Fintype.card F : ENNReal)⁻¹
                let goodBudget : ENNReal :=
                  (dsBudget
                    (sigma.insertEntry sigma.ideal.idx (.line xc.1 0))
                    nA nE nId nNf (nSig - 1) : ENNReal) * cF
                let dupBudget : ENNReal :=
                  ((dupTargets xc.1 sigma.shadow).length : ENNReal) * cF
                have hcanon :
                    Pr[dsSeededBad | ($ᵗ F) >>= fun k =>
                      drawList ($ᵗ F) m >>= fun vs =>
                      ($ᵗ F) >>= fun y =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, y, nc.1⟩))).run
                          (((sigma.insertEntry sigma.ideal.idx
                            (.line xc.1 y)).setIdeal
                              { sigma.ideal with
                                idx := sigma.ideal.idx + 1
                                closed := true
                                roX := xc.2
                                honestNf := nc.2 }).seed k vs) >>= fun z =>
                            pure (k, z)] ≤
                      (dsBudget sigma nA nE nId nNf nSig : ENNReal) * cF := by
                  refine le_trans (probEvent_kTape_core_split_le m ($ᵗ F)
                    (fun k vs y =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, y, nc.1⟩))).run
                          (((sigma.insertEntry sigma.ideal.idx
                            (.line xc.1 y)).setIdeal
                              { sigma.ideal with
                                idx := sigma.ideal.idx + 1
                                closed := true
                                roX := xc.2
                                honestNf := nc.2 }).seed k vs) >>= fun z =>
                            pure (k, z))
                    dsSeededBad (fun y => y ∈ dupTargets xc.1 sigma.shadow)
                    goodBudget dupBudget
                    (by
                      dsimp [dupBudget, cF]
                      exact probEvent_uniform_mem_list_le _)
                    (fun y _ hy => ?_)) ?_
                  · refine probEvent_kTape_core_swap_le m
                      (lazyRO sigma.ideal.honestNf sigma.ideal.idx)
                      (fun k vs nc =>
                        (simulateQ (dsFrameImpl k mclose)
                          (cont (some ⟨xc.1, y, nc.1⟩))).run
                            (((sigma.insertEntry sigma.ideal.idx
                              (.line xc.1 y)).setIdeal
                                { sigma.ideal with
                                  idx := sigma.ideal.idx + 1
                                  closed := true
                                  roX := xc.2
                                  honestNf := nc.2 }).seed k vs) >>= fun z =>
                              pure (k, z)) dsSeededBad goodBudget ?_
                    intro nc hnc
                    let ideal' : IdealFrameSt F M :=
                      { sigma.ideal with
                        idx := sigma.ideal.idx + 1
                        closed := true
                        roX := xc.2
                        honestNf := nc.2 }
                    let sigma' := (sigma.insertEntry sigma.ideal.idx
                      (.line xc.1 y)).setIdeal ideal'
                    have hinv : DSShadowInvStrong sigma' m :=
                      hInv.insertLine_advance ideal' xc.1 y hi rfl hx.2 hx.1 hy
                    have hih := ih (some ⟨xc.1, y, nc.1⟩) sigma' m
                      nA nE nId nNf (nSig - 1) hinv
                      (by simpa [isDirectRoAQuery] using
                        hA.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoEQuery] using
                        hE.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoIdQuery] using
                        hId.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoNfQuery] using
                        hNf.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isSignalQuery] using
                        hSig.2 (some ⟨xc.1, y, nc.1⟩))
                    have hbud := dsBudget_insertLine_y_eq sigma
                      sigma.ideal.idx xc.1 y 0 nA nE nId nNf (nSig - 1)
                    dsimp [sigma', ideal', goodBudget, cF] at hih ⊢
                    rw [dsBudget_setIdeal, hbud] at hih
                    simpa [dsSeededRun] using hih
                  · dsimp [dupBudget, goodBudget, cF]
                    have hsum := dsBudget_insertLine_add_dupTargets sigma
                      sigma.ideal.idx xc.1 0 nA nE nId nNf (nSig - 1)
                    rw [Nat.sub_add_cancel hposSig] at hsum
                    rw [← Nat.cast_add, hsum]
                refine le_trans (le_of_eq ?_) hcanon
                refine probEvent_bind_congr_inner ($ᵗ F) _ _ dsSeededBad
                  (fun k => ?_)
                refine probEvent_bind_congr_inner (drawList ($ᵗ F) m)
                  _ _ dsSeededBad (fun vs => ?_)
                refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
                let G : F → ProbComp (F × (alpha × DSFrameSt F M)) :=
                  fun y =>
                    lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                    (simulateQ (dsFrameImpl k mclose)
                      (cont (some ⟨xc.1, y, nc.1⟩))).run
                        (((sigma.insertEntry sigma.ideal.idx
                          (.line xc.1 y)).setIdeal
                            { sigma.ideal with
                              idx := sigma.ideal.idx + 1
                              closed := true
                              roX := xc.2
                              honestNf := nc.2 }).seed k vs) >>= fun z =>
                          pure (k, z)
                calc
                  𝒟[($ᵗ F) >>= fun a =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, rlnY k a xc.1, nc.1⟩))).run
                          ⟨{ sigma.ideal with
                              idx := sigma.ideal.idx + 1
                              closed := true
                              roX := xc.2
                              honestNf := nc.2 },
                            Function.update (sigma.seed k vs).slope
                              sigma.ideal.idx (some a),
                            { (sigma.seed k vs).audit with
                              honestSlopes := a ::
                                (sigma.seed k vs).audit.honestSlopes }⟩
                            >>= fun z => pure (k, z)] =
                      𝒟[($ᵗ F) >>= fun a => G (rlnY k a xc.1)] := by
                        refine evalDist_bind_congr' ($ᵗ F) fun a => ?_
                        dsimp [G]
                        refine evalDist_bind_congr'
                          (lazyRO sigma.ideal.honestNf sigma.ideal.idx)
                          fun nc => ?_
                        rw [DSShadowSt.seed_setIdeal,
                          seed_insertLine sigma sigma.ideal.idx k xc.1
                            (rlnY k a xc.1) vs hi]
                        simp [rlnY, hx.1]
                    _ = 𝒟[($ᵗ F) >>= G] :=
                      evalDist_rlnY_uniform k xc.1 hx.1 G
            | some e =>
                have hehole := hInv.hfresh sigma.ideal.idx le_rfl e hi
                rcases hehole with ⟨j, rfl⟩
                simp only [DSShadowSt.seed_slope, hi, Option.map_some,
                  DSEntry.eval, dsTouch, bind_assoc, pure_bind,
                  DSShadowSt.seed_audit,
                  OracleQuery.cont_query]
                refine probEvent_kTape_core_swap_le m
                  (lazyROX sigma.ideal.roX mclose) _ dsSeededBad _ ?_
                intro xc hxc
                have hx := lazyROX_support_nonzero hInv.hroX mclose xc hxc
                have hhole : DSEntry.hole j ∈ sigma.shadow :=
                  hInv.hpat sigma.ideal.idx j hi
                have hjm : j < m := hInv.pat_coord_lt hi rfl
                let cF : ENNReal := (Fintype.card F : ENNReal)⁻¹
                let goodBudget : ENNReal :=
                  (dsBudget
                    (sigma.consumeHoleLine sigma.ideal.idx j xc.1 0)
                    nA nE nId nNf (nSig - 1) : ENNReal) * cF
                let dupBudget : ENNReal :=
                  ((dupTargets xc.1 sigma.shadow).length : ENNReal) * cF
                have hcanon :
                    Pr[dsSeededBad | ($ᵗ F) >>= fun k =>
                      drawList ($ᵗ F) m >>= fun vs =>
                      ($ᵗ F) >>= fun y =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, y, nc.1⟩))).run
                          (((sigma.consumeHoleLine sigma.ideal.idx j xc.1 y)
                            .setIdeal
                              { sigma.ideal with
                                idx := sigma.ideal.idx + 1
                                closed := true
                                roX := xc.2
                                honestNf := nc.2 }).seed k vs) >>= fun z =>
                            pure (k, z)] ≤
                      (dsBudget sigma nA nE nId nNf nSig : ENNReal) * cF := by
                  refine le_trans (probEvent_kTape_core_split_le m ($ᵗ F)
                    (fun k vs y =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some ⟨xc.1, y, nc.1⟩))).run
                          (((sigma.consumeHoleLine sigma.ideal.idx j xc.1 y)
                            .setIdeal
                              { sigma.ideal with
                                idx := sigma.ideal.idx + 1
                                closed := true
                                roX := xc.2
                                honestNf := nc.2 }).seed k vs) >>= fun z =>
                            pure (k, z))
                    dsSeededBad (fun y => y ∈ dupTargets xc.1 sigma.shadow)
                    goodBudget dupBudget
                    (by
                      dsimp [dupBudget, cF]
                      exact probEvent_uniform_mem_list_le _)
                    (fun y _ hy => ?_)) ?_
                  · refine probEvent_kTape_core_swap_le m
                      (lazyRO sigma.ideal.honestNf sigma.ideal.idx)
                      (fun k vs nc =>
                        (simulateQ (dsFrameImpl k mclose)
                          (cont (some ⟨xc.1, y, nc.1⟩))).run
                            (((sigma.consumeHoleLine sigma.ideal.idx j xc.1 y)
                              .setIdeal
                                { sigma.ideal with
                                  idx := sigma.ideal.idx + 1
                                  closed := true
                                  roX := xc.2
                                  honestNf := nc.2 }).seed k vs) >>= fun z =>
                              pure (k, z)) dsSeededBad goodBudget ?_
                    intro nc hnc
                    let ideal' : IdealFrameSt F M :=
                      { sigma.ideal with
                        idx := sigma.ideal.idx + 1
                        closed := true
                        roX := xc.2
                        honestNf := nc.2 }
                    let sigma' := (sigma.consumeHoleLine sigma.ideal.idx
                      j xc.1 y).setIdeal ideal'
                    have hinv : DSShadowInvStrong sigma' m :=
                      hInv.consumeHoleLine_advance ideal' xc.1 y hi rfl
                        hx.2 hx.1 hy
                    have hih := ih (some ⟨xc.1, y, nc.1⟩) sigma' m
                      nA nE nId nNf (nSig - 1) hinv
                      (by simpa [isDirectRoAQuery] using
                        hA.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoEQuery] using
                        hE.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoIdQuery] using
                        hId.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isDirectRoNfQuery] using
                        hNf.2 (some ⟨xc.1, y, nc.1⟩))
                      (by simpa [isSignalQuery] using
                        hSig.2 (some ⟨xc.1, y, nc.1⟩))
                    have hbud := dsBudget_consumeHoleLine_y_eq sigma
                      sigma.ideal.idx j xc.1 y 0 nA nE nId nNf
                        (nSig - 1) hhole hInv.hnd
                    dsimp [sigma', ideal', goodBudget, cF] at hih ⊢
                    rw [dsBudget_setIdeal, hbud] at hih
                    simpa [dsSeededRun] using hih
                  · dsimp [dupBudget, goodBudget, cF]
                    have hsum :=
                      dsBudget_consumeHoleLine_add_dupTargets_le sigma
                        sigma.ideal.idx j xc.1 0 nA nE nId nNf
                        (nSig - 1) hhole hInv.hnd
                    rw [Nat.sub_add_cancel hposSig] at hsum
                    rw [← add_mul, ← Nat.cast_add]
                    exact mul_le_mul_right' (Nat.cast_le.2 hsum) _
                refine le_trans (le_of_eq ?_) hcanon
                refine probEvent_bind_congr_inner ($ᵗ F) _ _ dsSeededBad
                  (fun k => ?_)
                let G : F → List F →
                    ProbComp (F × (alpha × DSFrameSt F M)) :=
                  fun y vs =>
                    lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                    (simulateQ (dsFrameImpl k mclose)
                      (cont (some ⟨xc.1, y, nc.1⟩))).run
                        (((sigma.consumeHoleLine sigma.ideal.idx j xc.1 y)
                          .setIdeal
                            { sigma.ideal with
                              idx := sigma.ideal.idx + 1
                              closed := true
                              roX := xc.2
                              honestNf := nc.2 }).seed k vs) >>= fun z =>
                          pure (k, z)
                calc
                  𝒟[drawList ($ᵗ F) m >>= fun vs =>
                      lazyRO sigma.ideal.honestNf sigma.ideal.idx >>= fun nc =>
                      (simulateQ (dsFrameImpl k mclose)
                        (cont (some
                          ⟨xc.1, rlnY k (vs.getD j 0) xc.1, nc.1⟩))).run
                          ⟨{ sigma.ideal with
                              idx := sigma.ideal.idx + 1
                              closed := true
                              roX := xc.2
                              honestNf := nc.2 },
                            (sigma.seed k vs).slope,
                            (sigma.seed k vs).audit⟩ >>= fun z => pure (k, z)] =
                      𝒟[drawList ($ᵗ F) m >>= fun vs =>
                        ($ᵗ F) >>= fun w =>
                          G (rlnY k (vs.getD j 0) xc.1) (vs.set j w)] := by
                    refine evalDist_bind_congr' (drawList ($ᵗ F) m)
                      fun vs => ?_
                    have hconst : forall w : F,
                        G (rlnY k (vs.getD j 0) xc.1) (vs.set j w) =
                          (lazyRO sigma.ideal.honestNf
                            sigma.ideal.idx >>= fun nc =>
                            (simulateQ (dsFrameImpl k mclose)
                              (cont (some ⟨xc.1,
                                rlnY k (vs.getD j 0) xc.1, nc.1⟩))).run
                              ⟨{ sigma.ideal with
                                  idx := sigma.ideal.idx + 1
                                  closed := true
                                  roX := xc.2
                                  honestNf := nc.2 },
                                (sigma.seed k vs).slope,
                                (sigma.seed k vs).audit⟩ >>= fun z =>
                                  pure (k, z)) := by
                      intro w
                      dsimp [G]
                      refine bind_congr fun nc => ?_
                      rw [DSShadowSt.seed_setIdeal,
                        seed_consumeHoleLine_set_dummy sigma m
                          sigma.ideal.idx j k xc.1 w vs hInv hi hx.1]
                    simp_rw [hconst]
                    exact
                      (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                        ($ᵗ F) (probFailure_uniformSample F) _).symm
                  _ = 𝒟[($ᵗ F) >>= fun y =>
                      drawList ($ᵗ F) m >>= fun vs => G y vs] :=
                    evalDist_drawList_extract_replace m j hjm
                      (fun a : F => rlnY k a xc.1)
                      (rlnY_bijective k xc.1 hx.1) G
                  _ = 𝒟[drawList ($ᵗ F) m >>= fun vs =>
                      ($ᵗ F) >>= fun y => G y vs] :=
                    OracleComp.DeferredSampling.evalDist_bind_comm
                      ($ᵗ F) (drawList ($ᵗ F) m) G
      | nfAt i =>
          have hposSig : 0 < nSig := by
            rcases hSig.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [dsFrameImpl, StateT.run_mk, DSShadowSt.seed_ideal,
            DSShadowSt.seed_slope, DSShadowSt.seed_audit,
            OracleQuery.cont_query]
          cases hi : sigma.pat i with
          | none =>
              rw [DSShadowSt.seed_slope, hi]
              simp only [Option.map_none, dsTouch, bind_assoc, pure_bind]
              refine probEvent_kTape_core_swap_le m
                (lazyRO sigma.ideal.honestNf i) _ dsSeededBad _ ?_
              intro c hc
              let sigma' := (sigma.insertEntry i (.hole m)).setIdeal
                { sigma.ideal with honestNf := c.2 }
              have hinv : DSShadowInvStrong sigma' (m + 1) :=
                (hInv.insertHole hi).setIdeal_sameIdx _ rfl hInv.hroX
              have hih := ih c.1 sigma' (m + 1) nA nE nId nNf
                (nSig - 1) hinv
                (by simpa [isDirectRoAQuery] using hA.2 c.1)
                (by simpa [isDirectRoEQuery] using hE.2 c.1)
                (by simpa [isDirectRoIdQuery] using hId.2 c.1)
                (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
                (by simpa [isSignalQuery] using hSig.2 c.1)
              have hcanon :
                  Pr[dsSeededBad | ($ᵗ F) >>= fun k =>
                    drawList ($ᵗ F) m >>= fun vs =>
                    ($ᵗ F) >>= fun v =>
                    (simulateQ (dsFrameImpl k mclose) (cont c.1)).run
                      (sigma'.seed k (vs ++ [v])) >>= fun z => pure (k, z)]
                    ≤ (dsBudget sigma nA nE nId nNf nSig : ENNReal) *
                        (Fintype.card F : ENNReal)⁻¹ := by
                refine probEvent_kTape_snoc_le m
                  (fun k vs =>
                    (simulateQ (dsFrameImpl k mclose) (cont c.1)).run
                      (sigma'.seed k vs) >>= fun z => pure (k, z))
                  dsSeededBad _ ?_
                simpa [dsSeededRun, sigma', dsBudget_setIdeal,
                  dsBudget_insertHole, Nat.sub_add_cancel hposSig] using hih
              refine le_trans (le_of_eq ?_) hcanon
              refine probEvent_bind_congr_inner ($ᵗ F) _ _ dsSeededBad
                (fun k => ?_)
              apply probEvent_bind_congr_support (drawList ($ᵗ F) m)
              intro vs hvs
              have hlen := drawList_support_length m vs hvs
              refine bind_congr fun v => ?_
              rw [seed_insertHole sigma m i k v vs hInv hlen hi]
              rfl
          | some e =>
              rw [DSShadowSt.seed_slope, hi]
              simp only [Option.map_some, dsTouch, bind_assoc, pure_bind]
              refine probEvent_kTape_core_swap_le m
                (lazyRO sigma.ideal.honestNf i) _ dsSeededBad _ ?_
              intro c hc
              let sigma' := sigma.setIdeal
                { sigma.ideal with honestNf := c.2 }
              have hinv : DSShadowInvStrong sigma' m :=
                hInv.setIdeal_sameIdx _ rfl hInv.hroX
              have hih := ih c.1 sigma' m nA nE nId nNf (nSig - 1)
                hinv
                (by simpa [isDirectRoAQuery] using hA.2 c.1)
                (by simpa [isDirectRoEQuery] using hE.2 c.1)
                (by simpa [isDirectRoIdQuery] using hId.2 c.1)
                (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
                (by simpa [isSignalQuery] using hSig.2 c.1)
              have hstep :
                  Pr[dsSeededBad | dsSeededRun mclose (cont c.1) sigma' m]
                    ≤ (dsBudget sigma' nA nE nId nNf (nSig - 1) : ENNReal) *
                        (Fintype.card F : ENNReal)⁻¹ := hih
              refine le_trans (by simpa [dsSeededRun, sigma'] using hstep) ?_
              refine mul_le_mul_right' (Nat.cast_le.2 ?_) _
              simpa [Nat.sub_add_cancel hposSig] using
                (dsBudget_signal_same_le sigma nA nE nId nNf (nSig - 1))
      | roA kq i =>
          have hposA : 0 < nA := by
            rcases hA.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [dsFrameImpl, StateT.run_mk, DSShadowSt.seed_ideal,
            DSShadowSt.seed_slope, DSShadowSt.seed_audit, bind_assoc,
            pure_bind, OracleQuery.cont_query]
          refine probEvent_kTape_core_swap_le m
            (lazyRO sigma.ideal.roA (kq, i))
            (fun k vs c =>
              (simulateQ (dsFrameImpl k mclose) (cont c.1)).run
                (((sigma.addSecretProbe kq).setIdeal
                  { sigma.ideal with roA := c.2 }).seed k vs) >>= fun z =>
                    pure (k, z)) dsSeededBad _ ?_
          intro c hc
          have hinv := (hInv.addSecretProbe kq).setIdeal_sameIdx
            { sigma.ideal with roA := c.2 } rfl hInv.hroX
          have hih := ih c.1
            ((sigma.addSecretProbe kq).setIdeal
              { sigma.ideal with roA := c.2 }) m (nA - 1) nE nId nNf nSig
            hinv
            (by simpa [isDirectRoAQuery] using hA.2 c.1)
            (by simpa [isDirectRoEQuery] using hE.2 c.1)
            (by simpa [isDirectRoIdQuery] using hId.2 c.1)
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
          simpa [dsSeededRun, dsBudget_setIdeal,
            dsBudget_addSecretProbe_roA, Nat.sub_add_cancel hposA] using hih
      | roX msg =>
          simp only [dsFrameImpl, StateT.run_mk, DSShadowSt.seed_ideal,
            DSShadowSt.seed_slope, DSShadowSt.seed_audit, bind_assoc,
            pure_bind, OracleQuery.cont_query]
          refine probEvent_kTape_core_swap_le m
            (lazyROX sigma.ideal.roX msg)
            (fun k vs c =>
              (simulateQ (dsFrameImpl k mclose) (cont c.1)).run
                ((sigma.setIdeal { sigma.ideal with roX := c.2 }).seed k vs)
                  >>= fun z => pure (k, z)) dsSeededBad _ ?_
          intro c hc
          have hx := lazyROX_support_nonzero hInv.hroX msg c hc
          have hinv := hInv.setIdeal_sameIdx
            { sigma.ideal with roX := c.2 } rfl hx.2
          have hih := ih c.1
            (sigma.setIdeal { sigma.ideal with roX := c.2 }) m
            nA nE nId nNf nSig hinv
            (by simpa [isDirectRoAQuery] using hA.2 c.1)
            (by simpa [isDirectRoEQuery] using hE.2 c.1)
            (by simpa [isDirectRoIdQuery] using hId.2 c.1)
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
          simpa [dsSeededRun, dsBudget_setIdeal] using hih
      | roNf aq =>
          have hposNf : 0 < nNf := by
            rcases hNf.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [dsFrameImpl, StateT.run_mk, DSShadowSt.seed_ideal,
            DSShadowSt.seed_slope, DSShadowSt.seed_audit, bind_assoc,
            pure_bind, OracleQuery.cont_query]
          refine probEvent_kTape_core_swap_le m
            (lazyRO sigma.ideal.roNf aq)
            (fun k vs c =>
              (simulateQ (dsFrameImpl k mclose) (cont c.1)).run
                (((sigma.addSlopeProbe aq).setIdeal
                  { sigma.ideal with roNf := c.2 }).seed k vs) >>= fun z =>
                    pure (k, z)) dsSeededBad _ ?_
          intro c hc
          have hinv := (hInv.addSlopeProbe aq).setIdeal_sameIdx
            { sigma.ideal with roNf := c.2 } rfl hInv.hroX
          have hih := ih c.1
            ((sigma.addSlopeProbe aq).setIdeal
              { sigma.ideal with roNf := c.2 }) m nA nE nId
            (nNf - 1) nSig hinv
            (by simpa [isDirectRoAQuery] using hA.2 c.1)
            (by simpa [isDirectRoEQuery] using hE.2 c.1)
            (by simpa [isDirectRoIdQuery] using hId.2 c.1)
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
          simpa [dsSeededRun, dsBudget_setIdeal, dsBudget_addSlopeProbe,
            Nat.sub_add_cancel hposNf] using hih
      | roE kq e =>
          have hposE : 0 < nE := by
            rcases hE.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [dsFrameImpl, StateT.run_mk, DSShadowSt.seed_ideal,
            DSShadowSt.seed_slope, DSShadowSt.seed_audit, bind_assoc,
            pure_bind, OracleQuery.cont_query]
          refine probEvent_kTape_core_swap_le m
            (lazyRO sigma.ideal.roE (kq, e))
            (fun k vs c =>
              (simulateQ (dsFrameImpl k mclose) (cont c.1)).run
                (((sigma.addSecretProbe kq).setIdeal
                  { sigma.ideal with roE := c.2 }).seed k vs) >>= fun z =>
                    pure (k, z)) dsSeededBad _ ?_
          intro c hc
          have hinv := (hInv.addSecretProbe kq).setIdeal_sameIdx
            { sigma.ideal with roE := c.2 } rfl hInv.hroX
          have hih := ih c.1
            ((sigma.addSecretProbe kq).setIdeal
              { sigma.ideal with roE := c.2 }) m nA (nE - 1) nId nNf nSig
            hinv
            (by simpa [isDirectRoAQuery] using hA.2 c.1)
            (by simpa [isDirectRoEQuery] using hE.2 c.1)
            (by simpa [isDirectRoIdQuery] using hId.2 c.1)
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
          simpa [dsSeededRun, dsBudget_setIdeal,
            dsBudget_addSecretProbe_roE, Nat.sub_add_cancel hposE] using hih
      | roId kq =>
          have hposId : 0 < nId := by
            rcases hId.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [dsFrameImpl, StateT.run_mk, DSShadowSt.seed_ideal,
            DSShadowSt.seed_slope, DSShadowSt.seed_audit, bind_assoc,
            pure_bind, OracleQuery.cont_query]
          refine probEvent_kTape_core_swap_le m
            (lazyRO sigma.ideal.roId kq)
            (fun k vs c =>
              (simulateQ (dsFrameImpl k mclose) (cont c.1)).run
                (((sigma.addSecretProbe kq).setIdeal
                  { sigma.ideal with roId := c.2 }).seed k vs) >>= fun z =>
                    pure (k, z)) dsSeededBad _ ?_
          intro c hc
          have hinv := (hInv.addSecretProbe kq).setIdeal_sameIdx
            { sigma.ideal with roId := c.2 } rfl hInv.hroX
          have hih := ih c.1
            ((sigma.addSecretProbe kq).setIdeal
              { sigma.ideal with roId := c.2 }) m nA nE (nId - 1) nNf nSig
            hinv
            (by simpa [isDirectRoAQuery] using hA.2 c.1)
            (by simpa [isDirectRoEQuery] using hE.2 c.1)
            (by simpa [isDirectRoIdQuery] using hId.2 c.1)
            (by simpa [isDirectRoNfQuery] using hNf.2 c.1)
            (by simpa [isSignalQuery] using hSig.2 c.1)
          simpa [dsSeededRun, dsBudget_setIdeal,
            dsBudget_addSecretProbe_roId, Nat.sub_add_cancel hposId] using hih

/-- The adaptive seeded-shadow induction discharges the deferred-slope
counting obligation for the public commitment family.  The commitment draw
is independent of the secret/tape seed, so it can be moved outside the
seeded experiment and the five per-commitment query certificates instantiate
the master bound. -/
theorem dsBadMassLe_of_queryBounds (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) : DSBadMassLe mclose A qb := by
  unfold DSBadMassLe dsFrameJoint dsFrameRun
  have hswap :
      𝒟[($ᵗ F) >>= fun k => ($ᵗ F) >>= fun cm =>
          (simulateQ (dsFrameImpl k mclose) (A cm)).run (DSFrameSt.init F M)
            >>= fun z => pure (k, z)] =
        𝒟[($ᵗ F) >>= fun cm => dsSeededRun mclose (A cm)
          (dsShadowInit F M) 0] := by
    unfold dsSeededRun
    rw [show drawList ($ᵗ F) 0 = (pure [] : ProbComp (List F)) from rfl]
    simp only [pure_bind, dsShadowInit_seed]
    exact OracleComp.DeferredSampling.evalDist_bind_comm
      ($ᵗ F) ($ᵗ F)
      (fun k cm => (simulateQ (dsFrameImpl k mclose) (A cm)).run
        (DSFrameSt.init F M) >>= fun z => pure (k, z))
  simp only [bind_assoc]
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) hswap)) ?_
  refine probEvent_bind_le_of_forall_le fun cm _ => ?_
  have h := dsFrameImpl_seeded_bad_le mclose (A cm) (dsShadowInit F M) 0
    qb.qA qb.qE qb.qId qb.qNf qb.qSig dsShadowInvStrong_init
    (qb.roA_bound cm) (qb.roE_bound cm) (qb.roId_bound cm)
    (qb.roNf_bound cm) (qb.signal_bound cm)
  have hbudget :
      dsBudget (dsShadowInit F M) qb.qA qb.qE qb.qId qb.qNf qb.qSig ≤
        qb.total := by
    have hc : Nat.choose qb.qSig 2 ≤ qb.qSig * qb.qSig := by
      simpa [pow_two] using Nat.choose_le_pow qb.qSig 2
    simp only [dsBudget, dsShadowInit, List.length_nil, zero_add, zero_mul,
      scCount, FrameQueryBounds.total]
    omega
  refine le_trans (by simpa [dsSeededBad] using h) ?_
  exact mul_le_mul_right' (Nat.cast_le.2 hbudget) _

/-- Public stage-2 endpoint: the deferred FRAME leakage mass satisfies the
declared aggregate query budget. -/
theorem dsBadMassLe_holds (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) : DSBadMassLe mclose A qb :=
  dsBadMassLe_of_queryBounds mclose A qb

end Zkpc.Games
