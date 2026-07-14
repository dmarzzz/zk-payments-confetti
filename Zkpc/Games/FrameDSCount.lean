import Zkpc.Games.FrameRealBadTransfer
import Zkpc.Games.FrameBadMass

/-!
# Stage-2 counting for the deferred-slope run (Spec.md §7 T7, `DSBadMassLe`)

This file executes the recorded stage-2 plan of `ROADMAP.md` §1: the
k-averaged leakage mass of the deferred-slope joint experiment
`dsFrameJoint` is at most `qb.total/|F|`.  The strategy re-parameterizes
the deferred run into an entirely `k`-free *shadow transcript*:

* every fresh honest emission `y = k + a·x` is rewritten through the
  one-time-pad bijection `a ↦ k + a·x` (`x ≠ 0` by digest normalization),
  so the emitted line value is a fresh uniform draw and the recorded slope
  becomes the deterministic root `(y − k)/x` of a concrete public line;
* every pinned-but-unconsumed `nfAt` slope is deferred onto an explicit
  uniform tape (mirroring `FrameBadMass`), with tape coordinates tracked
  positionally so a later consumption can re-parameterize its coordinate
  by the same pad bijection;
* the honest secret `k` never enters the rewritten run, so it may be
  sampled last, where every leakage branch pins it to one algebraic root
  per budget pair, and the residual tape events pay the elementary
  fresh-tape kernels.

This first section provides the positional tape kernels: coordinate
marginals, coordinate-pair collision bounds, a per-coordinate bijective
re-indexing rule, and the back-append (`snoc`) fusion used when a fresh
pin joins the tape.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]

/-! ## Generic union bound over a list of events -/

/-- Union bound over a list of parameterized events: the probability that
some listed event fires is at most the sum of the individual masses. -/
theorem probEvent_exists_mem_le {α β : Type} (oa : ProbComp α)
    (l : List β) (P : β → α → Prop) (B : β → ENNReal)
    (h : ∀ b ∈ l, Pr[P b | oa] ≤ B b) :
    Pr[fun a => ∃ b ∈ l, P b a | oa] ≤ (l.map B).sum := by
  induction l with
  | nil =>
      rw [probEvent_ext (q := fun _ : α => False) (fun a _ => by simp)]
      simp
  | cons b l ih =>
      rw [probEvent_ext
        (q := fun a : α => P b a ∨ ∃ b' ∈ l, P b' a)
        (fun a _ => by
          constructor
          · rintro ⟨b', hb', hP⟩
            rcases List.mem_cons.1 hb' with rfl | hb'
            · exact Or.inl hP
            · exact Or.inr ⟨b', hb', hP⟩
          · rintro (hP | ⟨b', hb', hP⟩)
            · exact ⟨b, List.mem_cons_self, hP⟩
            · exact ⟨b', List.mem_cons_of_mem _ hb', hP⟩)]
      refine le_trans (probEvent_or_le _ _ _) ?_
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h b List.mem_cons_self)
        (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

section TapeKernels

variable [Fintype F]

/-- Coordinate marginal of a fresh uniform tape: any single coordinate of
`drawList ($ᵗ F) m` lands in a fixed target list with probability at most
`|ts|/|F|`. -/
theorem probEvent_drawList_getD_mem_le (j m : ℕ) (hj : j < m) (ts : List F) :
    Pr[fun vs : List F => vs.getD j 0 ∈ ts | drawList ($ᵗ F) m]
      ≤ (ts.length : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  induction m generalizing j with
  | zero => omega
  | succ m ih =>
      rw [show drawList ($ᵗ F) (m + 1)
          = (($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
              pure (v :: ws)) from rfl]
      cases j with
      | zero =>
          rw [probEvent_bind_eq_tsum]
          have hstep : ∀ v : F,
              Pr[= v | ($ᵗ F)] * Pr[fun vs : List F => vs.getD 0 0 ∈ ts |
                  drawList ($ᵗ F) m >>= fun ws => pure (v :: ws)]
                ≤ Pr[= v | ($ᵗ F)] * (if v ∈ ts then 1 else 0) := by
            intro v
            refine mul_le_mul_left' ?_ _
            rw [show (fun ws : List F => (pure (v :: ws) : ProbComp (List F)))
                = pure ∘ (fun ws : List F => v :: ws) from rfl,
              probEvent_bind_pure_comp]
            by_cases hv : v ∈ ts
            · rw [if_pos hv]
              exact probEvent_le_one
            · rw [if_neg hv]
              rw [probEvent_ext (q := fun _ : List F => False)
                (fun ws _ => by simp [Function.comp_apply, hv])]
              simp [probEvent_eq_tsum_ite]
          refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
          have hsum : (∑' v : F, Pr[= v | ($ᵗ F)] * (if v ∈ ts then 1 else 0))
              = Pr[fun v : F => v ∈ ts | ($ᵗ F)] := by
            rw [probEvent_eq_tsum_ite]
            refine tsum_congr fun v => ?_
            by_cases hv : v ∈ ts <;> simp [hv]
          rw [hsum]
          exact probEvent_uniform_mem_list_le ts
      | succ j =>
          refine probEvent_bind_le_of_forall_le fun v _ => ?_
          rw [show (fun ws : List F => (pure (v :: ws) : ProbComp (List F)))
              = pure ∘ (fun ws : List F => v :: ws) from rfl]
          rw [probEvent_bind_pure_comp]
          rw [probEvent_ext (q := fun ws : List F => ws.getD j 0 ∈ ts)
            (fun ws _ => by simp)]
          exact ih j (by omega)

/-- Coordinate-pair collision of a fresh uniform tape: two distinct
coordinates agree with probability at most `1/|F|`. -/
theorem probEvent_drawList_getD_eq_le (i j m : ℕ) (hij : i ≠ j)
    (hi : i < m) (hj : j < m) :
    Pr[fun vs : List F => vs.getD i 0 = vs.getD j 0 | drawList ($ᵗ F) m]
      ≤ (Fintype.card F : ENNReal)⁻¹ := by
  induction m generalizing i j with
  | zero => omega
  | succ m ih =>
      rw [show drawList ($ᵗ F) (m + 1)
          = (($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
              pure (v :: ws)) from rfl]
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · -- coordinate 0 versus a strictly later coordinate
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        refine probEvent_bind_le_of_forall_le fun v _ => ?_
        rw [show (fun ws : List F => (pure (v :: ws) : ProbComp (List F)))
            = pure ∘ (fun ws : List F => v :: ws) from rfl,
          probEvent_bind_pure_comp]
        rw [probEvent_ext (q := fun ws : List F => ws.getD j' 0 = v)
          (fun ws _ => by simp [eq_comm])]
        have := probEvent_drawList_getD_mem_le (F := F) j' m (by omega) [v]
        refine le_trans (le_of_eq (probEvent_ext
          (q := fun ws : List F => ws.getD j' 0 ∈ [v])
          (fun ws _ => by simp))) (le_trans this ?_)
        simp
      · rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          refine probEvent_bind_le_of_forall_le fun v _ => ?_
          rw [show (fun ws : List F => (pure (v :: ws) : ProbComp (List F)))
              = pure ∘ (fun ws : List F => v :: ws) from rfl,
            probEvent_bind_pure_comp]
          rw [probEvent_ext (q := fun ws : List F => ws.getD i' 0 = v)
            (fun ws _ => by simp)]
          have := probEvent_drawList_getD_mem_le (F := F) i' m (by omega) [v]
          refine le_trans (le_of_eq (probEvent_ext
            (q := fun ws : List F => ws.getD i' 0 ∈ [v])
            (fun ws _ => by simp))) (le_trans this ?_)
          simp
        · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          refine probEvent_bind_le_of_forall_le fun v _ => ?_
          rw [show (fun ws : List F => (pure (v :: ws) : ProbComp (List F)))
              = pure ∘ (fun ws : List F => v :: ws) from rfl,
            probEvent_bind_pure_comp]
          rw [probEvent_ext
            (q := fun ws : List F => ws.getD i' 0 = ws.getD j' 0)
            (fun ws _ => by simp)]
          exact ih i' j' (by omega) (by omega) (by omega)

end TapeKernels

/-! ## Tape re-indexing and back-append fusion -/

omit [DecidableEq F] in
/-- Applying a bijection to one fixed coordinate of a fresh uniform tape
leaves the observed distribution unchanged. -/
theorem evalDist_drawList_set_bij {β : Type} (m j : ℕ) (hj : j < m)
    (φ : F → F) (hφ : Function.Bijective φ) (G : List F → ProbComp β) :
    𝒟[drawList ($ᵗ F) m >>= fun vs => G (vs.set j (φ (vs.getD j 0)))]
      = 𝒟[drawList ($ᵗ F) m >>= G] := by
  induction m generalizing j G with
  | zero => omega
  | succ m ih =>
      rw [show drawList ($ᵗ F) (m + 1)
          = (($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
              pure (v :: ws)) from rfl]
      simp only [bind_assoc, pure_bind]
      cases j with
      | zero =>
          have hφ0 : ∀ v : F, φ v = φ v + 0 := fun v => (add_zero _).symm
          calc 𝒟[($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
                G ((v :: ws).set 0 (φ ((v :: ws).getD 0 0)))]
              = 𝒟[($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
                  G (φ v :: ws)] := by
                refine OracleComp.DeferredSampling.evalDist_bind_congr_left
                  ($ᵗ F) _ _ fun v => ?_
                simp
            _ = 𝒟[($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
                  G (v :: ws)] := by
                have := evalDist_bind_bijective_add_right_uniform (α := F)
                  φ hφ 0 (fun y => drawList ($ᵗ F) m >>= fun ws =>
                    G (y :: ws))
                simpa using this
      | succ j =>
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left
            ($ᵗ F) _ _ fun v => ?_
          have hset : ∀ ws : List F,
              (v :: ws).set (j + 1) (φ ((v :: ws).getD (j + 1) 0))
                = v :: ws.set j (φ (ws.getD j 0)) := by
            intro ws
            simp
          calc 𝒟[drawList ($ᵗ F) m >>= fun ws =>
                G ((v :: ws).set (j + 1) (φ ((v :: ws).getD (j + 1) 0)))]
              = 𝒟[drawList ($ᵗ F) m >>= fun ws =>
                  (fun ws' => G (v :: ws')) (ws.set j (φ (ws.getD j 0)))] := by
                refine OracleComp.DeferredSampling.evalDist_bind_congr_left
                  (drawList ($ᵗ F) m) _ _ fun ws => by rw [hset]
            _ = 𝒟[drawList ($ᵗ F) m >>= fun ws => G (v :: ws)] :=
                ih j (by omega) (fun ws => G (v :: ws))

omit [Field F] [DecidableEq F] in
/-- Back-append fusion: a tape of length `m` followed by one more fresh
draw appended at the *end* is the tape of length `m + 1`.  Appending at the
back keeps all existing coordinate positions stable. -/
theorem evalDist_drawList_snoc {β : Type} (m : ℕ)
    (G : List F → ProbComp β) :
    𝒟[drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun v => G (vs ++ [v])]
      = 𝒟[drawList ($ᵗ F) (m + 1) >>= G] := by
  induction m generalizing G with
  | zero =>
      rw [show drawList ($ᵗ F) 0 = (pure [] : ProbComp (List F)) from rfl,
        show drawList ($ᵗ F) 1
          = (($ᵗ F) >>= fun v => drawList ($ᵗ F) 0 >>= fun ws =>
              pure (v :: ws)) from rfl,
        show drawList ($ᵗ F) 0 = (pure [] : ProbComp (List F)) from rfl]
      simp
  | succ m ih =>
      rw [show drawList ($ᵗ F) (m + 1)
          = (($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
              pure (v :: ws)) from rfl,
        show drawList ($ᵗ F) (m + 1 + 1)
          = (($ᵗ F) >>= fun v => drawList ($ᵗ F) (m + 1) >>= fun ws =>
              pure (v :: ws)) from rfl]
      simp only [bind_assoc, pure_bind]
      refine OracleComp.DeferredSampling.evalDist_bind_congr_left
        ($ᵗ F) _ _ fun w => ?_
      have := ih (fun vs => G (w :: vs))
      simpa [List.cons_append] using this

/-! ## The k-free shadow transcript

A shadow entry describes one recorded honest slope without consulting the
secret: a `line` is a consumed fresh emission with concrete public
coordinates (its slope is the root `(y − k)/x`); a `hole` is a
pinned-but-unconsumed `nfAt` slope, deferred to tape coordinate `j`; a
`tline` is a consumed pinned slope, whose public line ordinate is tape
coordinate `j` at abscissa `x` (its slope is `(vs_j − k)/x`). -/
inductive DSEntry (F : Type) where
  | line (x y : F)
  | hole (j : ℕ)
  | tline (j : ℕ) (x : F)
  deriving DecidableEq

namespace DSEntry

/-- Evaluate a shadow entry to the recorded honest slope, given the secret
and the hole tape. -/
def eval (k : F) (vs : List F) : DSEntry F → F
  | .line x y => (y - k) / x
  | .hole j => vs.getD j 0
  | .tline j x => (vs.getD j 0 - k) / x

/-- The tape coordinate referenced by an entry, if any. -/
def coord : DSEntry F → Option ℕ
  | .line _ _ => none
  | .hole j => some j
  | .tline j _ => some j

/-- The nonzero-abscissa side condition of an entry. -/
def XNe0 : DSEntry F → Prop
  | .line x _ => x ≠ 0
  | .hole _ => True
  | .tline _ x => x ≠ 0

/-- Two entries clash when they are concrete lines at the same abscissa:
such a pair either never collides (distinct ordinates) or was already
charged in-run at emission time, so it is the only pair the leaf counting
does not pay. -/
def clash [DecidableEq F] : DSEntry F → DSEntry F → Bool
  | .line x _, .line x' _ => decide (x = x')
  | _, _ => false

/-- Separation of two entries: they are not equal-abscissa equal-ordinate
concrete lines.  Maintained in-run by charging the fresh emission draw. -/
def Sep : DSEntry F → DSEntry F → Prop
  | .line x y, .line x' y' => x = x' → y ≠ y'
  | _, _ => True

end DSEntry

/-! ### Pair and probe charges -/

variable [DecidableEq F]

/-- Secret roots charged to an entry pair (given the tape): every
collision between the two evaluated slopes forces the secret onto this
list, except for the pair shapes routed to the tape events. -/
def pairKRoots (vs : List F) : DSEntry F → DSEntry F → List F
  | .line x y, .line x' y' =>
      if x = x' then [] else [slopeCollisionRoot x y x' y']
  | .line x y, .hole j => [slopeHitRoot x y (vs.getD j 0)]
  | .line x y, .tline j x' =>
      if x = x' then [] else [slopeCollisionRoot x y x' (vs.getD j 0)]
  | .hole i, .line x y => [slopeHitRoot x y (vs.getD i 0)]
  | .hole _, .hole _ => []
  | .hole i, .tline j x => [slopeHitRoot x (vs.getD j 0) (vs.getD i 0)]
  | .tline i x, .line x' y' =>
      if x = x' then [] else [slopeCollisionRoot x (vs.getD i 0) x' y']
  | .tline i x, .hole j => [slopeHitRoot x (vs.getD i 0) (vs.getD j 0)]
  | .tline i x, .tline j x' =>
      if x = x' then []
      else [slopeCollisionRoot x (vs.getD i 0) x' (vs.getD j 0)]

/-- Tape-membership targets charged to an entry pair: an equal-abscissa
line/tape-line pair collides exactly when the tape ordinate hits the
concrete ordinate. -/
def pairVsMem : DSEntry F → DSEntry F → List (ℕ × List F)
  | .line x y, .tline j x' => if x = x' then [(j, [y])] else []
  | .tline i x, .line x' y' => if x = x' then [(i, [y'])] else []
  | _, _ => []

/-- Tape coordinate-equality pairs charged to an entry pair: two holes, or
two equal-abscissa tape-lines, collide exactly when their coordinates
agree. -/
def pairVsEq : DSEntry F → DSEntry F → List (ℕ × ℕ)
  | .hole i, .hole j => [(i, j)]
  | .tline i x, .tline j x' => if x = x' then [(i, j)] else []
  | _, _ => []

/-- Secret roots charged to a probe list against one entry. -/
def probeKRoots (P vs : List F) : DSEntry F → List F
  | .line x y => P.map (slopeHitRoot x y)
  | .hole _ => []
  | .tline j x => P.map (slopeHitRoot x (vs.getD j 0))

/-- Tape-membership targets charged to a probe list against one entry. -/
def probeVsMem (P : List F) : DSEntry F → List (ℕ × List F)
  | .hole j => [(j, P)]
  | _ => []

/-! ### Aggregates over the shadow -/

/-- All secret roots of a shadow: probe charges plus ordered pair charges,
head against tail. -/
def shadowKRoots (P vs : List F) : List (DSEntry F) → List F
  | [] => []
  | e :: rest =>
      probeKRoots P vs e ++ rest.flatMap (pairKRoots vs e)
        ++ shadowKRoots P vs rest

/-- All tape-membership assignments of a shadow. -/
def shadowVsMem (P : List F) : List (DSEntry F) → List (ℕ × List F)
  | [] => []
  | e :: rest =>
      probeVsMem P e ++ rest.flatMap (pairVsMem e) ++ shadowVsMem P rest

/-- All tape coordinate-equality pairs of a shadow. -/
def shadowVsEq : List (DSEntry F) → List (ℕ × ℕ)
  | [] => []
  | e :: rest => rest.flatMap (pairVsEq e) ++ shadowVsEq rest

/-- Number of leaf-chargeable unordered entry pairs of a shadow (all pairs
except equal-abscissa concrete-line pairs). -/
def scCount : List (DSEntry F) → ℕ
  | [] => 0
  | e :: rest =>
      (rest.map (fun e' => if e.clash e' then 0 else 1)).sum + scCount rest

/-- Total size of a tape-membership assignment list. -/
def asgSize (l : List (ℕ × List F)) : ℕ := (l.map (fun b => b.2.length)).sum

/-- A tape-membership assignment fires when some listed coordinate hits
its target list. -/
def VsMemFires (vs : List F) (l : List (ℕ × List F)) : Prop :=
  ∃ b ∈ l, vs.getD b.1 0 ∈ b.2

/-- A coordinate-equality list fires when some listed pair of coordinates
agrees. -/
def VsEqFires (vs : List F) (l : List (ℕ × ℕ)) : Prop :=
  ∃ b ∈ l, vs.getD b.1 0 = vs.getD b.2 0

/-! ### Per-pair exact accounting -/

/-- Each entry pair contributes exactly one charge (a secret root, one
tape target, or one coordinate pair) unless it clashes. -/
theorem pair_charge_count (vs : List F) (e e' : DSEntry F) :
    (pairKRoots vs e e').length + asgSize (pairVsMem e e')
        + (pairVsEq e e').length
      = if e.clash e' then 0 else 1 := by
  cases e <;> cases e' <;>
    simp only [pairKRoots, pairVsMem, pairVsEq, DSEntry.clash, asgSize] <;>
    split_ifs <;> simp_all

/-- Each probe list contributes exactly `|P|` charges per entry. -/
theorem probe_charge_count (P vs : List F) (e : DSEntry F) :
    (probeKRoots P vs e).length + asgSize (probeVsMem P e) = P.length := by
  cases e <;> simp [probeKRoots, probeVsMem, asgSize]

/-- Head-against-tail exact accounting: the pair charges of one entry
against a list have total size equal to the number of non-clashing
partners. -/
theorem pairs_charge_count (vs : List F) (e : DSEntry F)
    (rest : List (DSEntry F)) :
    (rest.flatMap (pairKRoots vs e)).length
        + asgSize (rest.flatMap (pairVsMem e))
        + (rest.flatMap (pairVsEq e)).length
      = (rest.map (fun e' => if e.clash e' then 0 else 1)).sum := by
  induction rest with
  | nil => simp [asgSize]
  | cons e' rest' ih =>
      simp only [List.flatMap_cons, List.length_append, asgSize,
        List.map_append, List.sum_append, List.map_cons,
        List.sum_cons] at ih ⊢
      have hc := pair_charge_count vs e e'
      simp only [asgSize] at hc
      omega

/-- Exact aggregate accounting: the three shadow charge lists together
have total size `|P| · t + scCount`. -/
theorem shadow_charge_count (P vs : List F) (shadow : List (DSEntry F)) :
    (shadowKRoots P vs shadow).length + asgSize (shadowVsMem P shadow)
        + (shadowVsEq shadow).length
      = P.length * shadow.length + scCount shadow := by
  induction shadow with
  | nil => simp [shadowKRoots, shadowVsMem, shadowVsEq, scCount, asgSize]
  | cons e rest ih =>
      have hpairs := pairs_charge_count vs e rest
      simp only [shadowKRoots, shadowVsMem, shadowVsEq, scCount,
        List.length_append, asgSize, List.map_append, List.sum_append,
        List.length_cons]
      have hprobe := probe_charge_count P vs e
      simp only [asgSize] at hprobe hpairs ih
      have hmul : P.length * (rest.length + 1)
          = P.length * rest.length + P.length := by ring
      omega

/-! ### The collision implication -/

variable [Fintype F]

/-- One-pair semantic charge: if two separated entries with nonzero
abscissas evaluate to the same slope, the pair's charge fires. -/
theorem pair_eval_eq_charged (k : F) (vs : List F) (e e' : DSEntry F)
    (hx : e.XNe0) (hx' : e'.XNe0) (hsep : e.Sep e')
    (heq : e.eval k vs = e'.eval k vs) :
    k ∈ pairKRoots vs e e' ∨ VsMemFires vs (pairVsMem e e')
      ∨ VsEqFires vs (pairVsEq e e') := by
  cases e with
  | line x y =>
      cases e' with
      | line x' y' =>
          by_cases hxx : x = x'
          · exfalso
            subst hxx
            apply hsep rfl
            simp only [DSEntry.eval] at heq
            have h2 := mul_right_cancel₀ hx ((div_eq_div_iff hx hx).1 heq)
            exact sub_left_inj.mp h2
          · refine Or.inl ?_
            simp only [pairKRoots, if_neg hxx, List.mem_singleton]
            exact ((reconstructedSlopes_eq_iff_secret_eq_collisionRoot
              x y x' y' k hx hx' hxx).1 heq)
      | hole j =>
          refine Or.inl ?_
          simp only [pairKRoots, List.mem_singleton]
          exact (reconstructedSlope_eq_iff_secret_eq_root x y
            (vs.getD j 0) k hx).1 heq
      | tline j x' =>
          by_cases hxx : x = x'
          · refine Or.inr (Or.inl ?_)
            subst hxx
            refine ⟨(j, [y]), by simp [pairVsMem], ?_⟩
            simp only [DSEntry.eval] at heq
            have h2 := mul_right_cancel₀ hx ((div_eq_div_iff hx hx).1 heq)
            have hy : vs.getD j 0 = y := (sub_left_inj.mp h2).symm
            simpa using hy
          · refine Or.inl ?_
            simp only [pairKRoots, if_neg hxx, List.mem_singleton]
            exact ((reconstructedSlopes_eq_iff_secret_eq_collisionRoot
              x y x' (vs.getD j 0) k hx hx' hxx).1 heq)
  | hole i =>
      cases e' with
      | line x y =>
          refine Or.inl ?_
          simp only [pairKRoots, List.mem_singleton]
          exact (reconstructedSlope_eq_iff_secret_eq_root x y
            (vs.getD i 0) k hx').1 heq.symm
      | hole j =>
          exact Or.inr (Or.inr ⟨(i, j), by simp [pairVsEq], heq⟩)
      | tline j x =>
          refine Or.inl ?_
          simp only [pairKRoots, List.mem_singleton]
          exact (reconstructedSlope_eq_iff_secret_eq_root x
            (vs.getD j 0) (vs.getD i 0) k hx').1 heq.symm
  | tline i x =>
      cases e' with
      | line x' y' =>
          by_cases hxx : x = x'
          · refine Or.inr (Or.inl ?_)
            subst hxx
            refine ⟨(i, [y']), by simp [pairVsMem], ?_⟩
            simp only [DSEntry.eval] at heq
            have h2 := mul_right_cancel₀ hx ((div_eq_div_iff hx hx).1 heq)
            have hy : vs.getD i 0 = y' := sub_left_inj.mp h2
            simpa using hy
          · refine Or.inl ?_
            simp only [pairKRoots, if_neg hxx, List.mem_singleton]
            exact ((reconstructedSlopes_eq_iff_secret_eq_collisionRoot
              x (vs.getD i 0) x' y' k hx hx' hxx).1 heq)
      | hole j =>
          refine Or.inl ?_
          simp only [pairKRoots, List.mem_singleton]
          exact (reconstructedSlope_eq_iff_secret_eq_root x
            (vs.getD i 0) (vs.getD j 0) k hx).1 heq
      | tline j x' =>
          by_cases hxx : x = x'
          · refine Or.inr (Or.inr ?_)
            subst hxx
            refine ⟨(i, j), by simp [pairVsEq], ?_⟩
            simp only [DSEntry.eval] at heq
            have h2 := mul_right_cancel₀ hx ((div_eq_div_iff hx hx).1 heq)
            exact sub_left_inj.mp h2
          · refine Or.inl ?_
            simp only [pairKRoots, if_neg hxx, List.mem_singleton]
            exact ((reconstructedSlopes_eq_iff_secret_eq_collisionRoot
              x (vs.getD i 0) x' (vs.getD j 0) k hx hx' hxx).1 heq)

/-- One-probe semantic charge: a probe hitting an evaluated slope fires
the probe charge of that entry. -/
theorem probe_eval_charged (k : F) (P vs : List F) (e : DSEntry F)
    (hx : e.XNe0) {p : F} (hp : p ∈ P) (heq : p = e.eval k vs) :
    k ∈ probeKRoots P vs e ∨ VsMemFires vs (probeVsMem P e) := by
  cases e with
  | line x y =>
      refine Or.inl ?_
      simp only [probeKRoots, List.mem_map]
      exact ⟨p, hp, ((reconstructedSlope_eq_iff_secret_eq_root x y p k
        hx).1 heq.symm).symm⟩
  | hole j =>
      simp only [DSEntry.eval] at heq
      exact Or.inr ⟨(j, P), by simp [probeVsMem], heq ▸ hp⟩
  | tline j x =>
      refine Or.inl ?_
      simp only [probeKRoots, List.mem_map]
      exact ⟨p, hp, ((reconstructedSlope_eq_iff_secret_eq_root x
        (vs.getD j 0) p k hx).1 heq.symm).symm⟩

/-- **The leaf implication.**  If the reconstructed audit raises the FRAME
leakage event, then either the secret hits the shadow root list or a tape
event fires (Spec.md §7 T7, deferred-run union-bound skeleton). -/
theorem frameLeakBad_shadow_charged (k : F) (vs D P : List F)
    (shadow : List (DSEntry F))
    (hx : ∀ e ∈ shadow, e.XNe0)
    (hsep : shadow.Pairwise DSEntry.Sep)
    (hbad : FrameLeakBad k
      ⟨D, P, shadow.map (DSEntry.eval k vs)⟩) :
    k ∈ D ++ shadowKRoots P vs shadow
      ∨ VsMemFires vs (shadowVsMem P shadow)
      ∨ VsEqFires vs (shadowVsEq shadow) := by
  induction shadow with
  | nil =>
      rcases hbad with h | ⟨p, _, hp⟩ | h
      · exact Or.inl (List.mem_append.2 (Or.inl h))
      · simp at hp
      · simp at h
  | cons e rest ih =>
      have hxe := hx e List.mem_cons_self
      have hxr : ∀ e' ∈ rest, DSEntry.XNe0 e' :=
        fun e' he' => hx e' (List.mem_cons_of_mem _ he')
      have hsepr := (List.pairwise_cons.1 hsep).2
      have hsepe := (List.pairwise_cons.1 hsep).1
      -- helper to push a rest-level charge up to the cons level
      have lift : (k ∈ D ++ shadowKRoots P vs rest
            ∨ VsMemFires vs (shadowVsMem P rest)
            ∨ VsEqFires vs (shadowVsEq rest)) →
          k ∈ D ++ shadowKRoots P vs (e :: rest)
            ∨ VsMemFires vs (shadowVsMem P (e :: rest))
            ∨ VsEqFires vs (shadowVsEq (e :: rest)) := by
        rintro (h | ⟨b, hb, hfire⟩ | ⟨b, hb, hfire⟩)
        · refine Or.inl ?_
          rcases List.mem_append.1 h with h | h
          · exact List.mem_append.2 (Or.inl h)
          · refine List.mem_append.2 (Or.inr ?_)
            simp only [shadowKRoots, List.mem_append]
            exact Or.inr h
        · refine Or.inr (Or.inl ⟨b, ?_, hfire⟩)
          simp only [shadowVsMem, List.mem_append]
          exact Or.inr hb
        · refine Or.inr (Or.inr ⟨b, ?_, hfire⟩)
          simp only [shadowVsEq, List.mem_append]
          exact Or.inr hb
      rcases hbad with h | ⟨p, hpP, hp⟩ | h
      · exact Or.inl (List.mem_append.2 (Or.inl h))
      · -- probe hit: either the head slope or a tail slope
        simp only [List.map_cons, List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases probe_eval_charged k P vs e hxe hpP hp with h | h
          · refine Or.inl (List.mem_append.2 (Or.inr ?_))
            simp only [shadowKRoots, List.mem_append]
            exact Or.inl (Or.inl h)
          · rcases h with ⟨b, hb, hfire⟩
            refine Or.inr (Or.inl ⟨b, ?_, hfire⟩)
            simp only [shadowVsMem, List.mem_append]
            exact Or.inl (Or.inl hb)
        · exact lift (ih hxr hsepr (Or.inr (Or.inl ⟨p, hpP, hp⟩)))
      · -- collision: head against tail, or inside the tail
        simp only [List.map_cons, List.nodup_cons, not_and_or, not_not] at h
        rcases h with h | h
        · obtain ⟨e', he', heq⟩ := List.mem_map.1 h
          rcases pair_eval_eq_charged k vs e e' hxe (hxr e' he')
              (hsepe e' he') heq.symm with hc | hc | hc
          · refine Or.inl (List.mem_append.2 (Or.inr ?_))
            simp only [shadowKRoots, List.mem_append]
            exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨e', he', hc⟩))
          · rcases hc with ⟨b, hb, hfire⟩
            refine Or.inr (Or.inl ⟨b, ?_, hfire⟩)
            simp only [shadowVsMem, List.mem_append]
            exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨e', he', hb⟩))
          · rcases hc with ⟨b, hb, hfire⟩
            refine Or.inr (Or.inr ⟨b, ?_, hfire⟩)
            simp only [shadowVsEq, List.mem_append]
            exact Or.inl (List.mem_flatMap.2 ⟨e', he', hb⟩)
        · exact lift (ih hxr hsepr (Or.inr (Or.inr h)))

/-! ### Coordinate hygiene of the charge lists -/

/-- All tape coordinates referenced by a shadow, in order. -/
def entryCoords (shadow : List (DSEntry F)) : List ℕ :=
  shadow.filterMap DSEntry.coord

omit [Field F] [SampleableType F] [Fintype F] in
/-- A pair coordinate-equality charge names the two entries' coordinates. -/
theorem pairVsEq_mem_spec {e e' : DSEntry F} {b : ℕ × ℕ}
    (hb : b ∈ pairVsEq e e') :
    e.coord = some b.1 ∧ e'.coord = some b.2 := by
  cases e <;> cases e' <;> simp only [pairVsEq] at hb
  all_goals (try split_ifs at hb)
  all_goals simp_all [DSEntry.coord]

omit [Field F] [SampleableType F] [Fintype F] in
/-- A pair tape-membership charge names one of the two entries'
coordinates. -/
theorem pairVsMem_mem_spec {e e' : DSEntry F} {b : ℕ × List F}
    (hb : b ∈ pairVsMem e e') :
    e.coord = some b.1 ∨ e'.coord = some b.1 := by
  cases e <;> cases e' <;> simp only [pairVsMem] at hb
  all_goals (try split_ifs at hb)
  all_goals simp_all [DSEntry.coord]

omit [Field F] [SampleableType F] [Fintype F] in
/-- Every tape-membership charge of a shadow references a shadow
coordinate. -/
theorem shadowVsMem_coord_spec (P : List F) (shadow : List (DSEntry F)) :
    ∀ b ∈ shadowVsMem P shadow, b.1 ∈ entryCoords shadow := by
  induction shadow with
  | nil => simp [shadowVsMem]
  | cons e rest ih =>
      intro b hb
      have hmem : ∀ {j : ℕ}, DSEntry.coord e = some j →
          j ∈ entryCoords (e :: rest) := by
        intro j hj
        simp [entryCoords, List.filterMap_cons, hj]
      have hrest : ∀ {j : ℕ}, j ∈ entryCoords rest →
          j ∈ entryCoords (e :: rest) := by
        intro j hj
        simp only [entryCoords, List.filterMap_cons]
        cases hce : DSEntry.coord e
        · exact hj
        · exact List.mem_cons_of_mem _ hj
      simp only [shadowVsMem, List.mem_append] at hb
      rcases hb with (hb | hb) | hb
      · -- probe charge on the head
        cases e <;> simp only [probeVsMem] at hb
        · cases hb
        · rw [List.mem_singleton] at hb
          subst hb
          exact hmem rfl
        · cases hb
      · obtain ⟨e', he', hb⟩ := List.mem_flatMap.1 hb
        rcases pairVsMem_mem_spec hb with h | h
        · exact hmem h
        · refine hrest ?_
          simp only [entryCoords, List.mem_filterMap]
          exact ⟨e', he', h⟩
      · exact hrest (ih b hb)

omit [Field F] [SampleableType F] [Fintype F] in
/-- Every coordinate-equality charge of a shadow references two distinct
shadow coordinates, provided the shadow coordinates are distinct. -/
theorem shadowVsEq_coord_spec (shadow : List (DSEntry F))
    (hnd : (entryCoords shadow).Nodup) :
    ∀ b ∈ shadowVsEq shadow,
      b.1 ∈ entryCoords shadow ∧ b.2 ∈ entryCoords shadow ∧ b.1 ≠ b.2 := by
  induction shadow with
  | nil => simp [shadowVsEq]
  | cons e rest ih =>
      intro b hb
      have hmem : ∀ {j : ℕ}, DSEntry.coord e = some j →
          j ∈ entryCoords (e :: rest) := by
        intro j hj
        simp [entryCoords, List.filterMap_cons, hj]
      have hrest : ∀ {j : ℕ}, j ∈ entryCoords rest →
          j ∈ entryCoords (e :: rest) := by
        intro j hj
        simp only [entryCoords, List.filterMap_cons]
        cases hce : DSEntry.coord e
        · exact hj
        · exact List.mem_cons_of_mem _ hj
      have hndr : (entryCoords rest).Nodup := by
        simp only [entryCoords, List.filterMap_cons] at hnd
        cases hce : DSEntry.coord e <;> rw [hce] at hnd
        · exact hnd
        · exact (List.nodup_cons.1 hnd).2
      simp only [shadowVsEq, List.mem_append] at hb
      rcases hb with hb | hb
      · obtain ⟨e', he', hb⟩ := List.mem_flatMap.1 hb
        obtain ⟨h1, h2⟩ := pairVsEq_mem_spec hb
        have hb2 : b.2 ∈ entryCoords rest := by
          simp only [entryCoords, List.mem_filterMap]
          exact ⟨e', he', h2⟩
        refine ⟨hmem h1, hrest hb2, ?_⟩
        -- head coordinate is fresh relative to the tail coordinates
        simp only [entryCoords, List.filterMap_cons, h1] at hnd
        intro hcontra
        exact (List.nodup_cons.1 hnd).1 (hcontra ▸ hb2)
      · obtain ⟨h1, h2, h3⟩ := ih hndr b hb
        exact ⟨hrest h1, hrest h2, h3⟩

/-! ### The leaf probability bound -/

omit [Field F] [DecidableEq F] [SampleableType F] [Fintype F] in
/-- Sum of a constant map. -/
theorem list_sum_map_const {β : Type} (l : List β) (c : ENNReal) :
    (l.map fun _ => c).sum = (l.length : ℕ) * c := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
      push_cast
      ring

omit [Field F] [DecidableEq F] [SampleableType F] [Fintype F] in
/-- Sum of a mapped constant multiple. -/
theorem list_sum_map_mul_const {β : Type} (l : List β) (f : β → ℕ)
    (c : ENNReal) :
    (l.map (fun b => (f b : ENNReal) * c)).sum
      = ((l.map f).sum : ℕ) * c := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      push_cast
      ring

/-- **Leaf bound (Spec.md §7 T7).** With the shadow transcript fixed, a
fresh hole tape and a last-sampled deferred secret raise the reconstructed
FRAME leakage event with probability at most
`(|D| + |P|·t + scCount)/|F|`: every branch pins the secret to one root
per charge, or fires one elementary tape event. -/
theorem dsShadow_leaf_le (D P : List F) (shadow : List (DSEntry F)) (m : ℕ)
    (hx : ∀ e ∈ shadow, e.XNe0)
    (hsep : shadow.Pairwise DSEntry.Sep)
    (hlt : ∀ j ∈ entryCoords shadow, j < m)
    (hnd : (entryCoords shadow).Nodup) :
    Pr[fun w : List F × F =>
        FrameLeakBad w.2 ⟨D, P, shadow.map (DSEntry.eval w.2 w.1)⟩ |
        drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun k => pure (vs, k)]
      ≤ ((D.length + P.length * shadow.length + scCount shadow : ℕ) : ENNReal)
          * (Fintype.card F : ENNReal)⁻¹ := by
  classical
  set c : ENNReal := (Fintype.card F : ENNReal)⁻¹ with hc
  set asg := shadowVsMem P shadow with hasg
  set eqs := shadowVsEq shadow with heqs
  -- monotone pass to the charged form
  have hmono : Pr[fun w : List F × F =>
        FrameLeakBad w.2 ⟨D, P, shadow.map (DSEntry.eval w.2 w.1)⟩ |
        drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun k => pure (vs, k)]
      ≤ Pr[fun w : List F × F =>
          (w.2 ∈ D ++ shadowKRoots P w.1 shadow)
            ∨ (VsMemFires w.1 asg ∨ VsEqFires w.1 eqs) |
          drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun k => pure (vs, k)] := by
    refine probEvent_mono fun w _ hbad => ?_
    rcases frameLeakBad_shadow_charged w.2 w.1 D P shadow hx hsep hbad with
      h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine le_trans hmono ?_
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add le_rfl (probEvent_or_le _ _ _)) ?_
  -- the deferred-secret root mass, uniformly over the tape
  have hk : Pr[fun w : List F × F => w.2 ∈ D ++ shadowKRoots P w.1 shadow |
        drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun k => pure (vs, k)]
      ≤ ((D.length + P.length * shadow.length + scCount shadow
            - asgSize asg - eqs.length : ℕ) : ENNReal) * c := by
    refine probEvent_bind_le_of_forall_le fun vs _ => ?_
    rw [show (fun k : F => (pure (vs, k) : ProbComp (List F × F)))
        = pure ∘ (fun k : F => (vs, k)) from rfl, probEvent_bind_pure_comp]
    refine le_trans (le_of_eq (probEvent_ext
      (q := fun k : F => k ∈ D ++ shadowKRoots P vs shadow)
      (fun k _ => Iff.rfl))) ?_
    refine le_trans (probEvent_uniform_mem_list_le _) ?_
    refine mul_le_mul_right' (Nat.cast_le.2 ?_) _
    have hcount := shadow_charge_count P vs shadow
    rw [← hasg, ← heqs] at hcount
    simp only [List.length_append]
    omega
  -- the tape-membership mass
  have hasgmass : Pr[fun w : List F × F => VsMemFires w.1 asg |
        drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun k => pure (vs, k)]
      ≤ ((asgSize asg : ℕ) : ENNReal) * c := by
    rw [probEvent_bind_pair_uniform_fst (F := F) (drawList ($ᵗ F) m)
      (fun vs => VsMemFires vs asg)]
    refine le_trans (probEvent_exists_mem_le (drawList ($ᵗ F) m) asg
      (fun b vs => vs.getD b.1 0 ∈ b.2)
      (fun b => (b.2.length : ENNReal) * c) ?_) ?_
    · intro b hb
      exact probEvent_drawList_getD_mem_le b.1 m
        (hlt b.1 (shadowVsMem_coord_spec P shadow b hb)) b.2
    · rw [list_sum_map_mul_const asg (fun b => b.2.length) c]
      exact le_of_eq rfl
  -- the coordinate-equality mass
  have heqmass : Pr[fun w : List F × F => VsEqFires w.1 eqs |
        drawList ($ᵗ F) m >>= fun vs => ($ᵗ F) >>= fun k => pure (vs, k)]
      ≤ ((eqs.length : ℕ) : ENNReal) * c := by
    rw [probEvent_bind_pair_uniform_fst (F := F) (drawList ($ᵗ F) m)
      (fun vs => VsEqFires vs eqs)]
    refine le_trans (probEvent_exists_mem_le (drawList ($ᵗ F) m) eqs
      (fun b vs => vs.getD b.1 0 = vs.getD b.2 0)
      (fun _ => c) ?_) ?_
    · intro b hb
      obtain ⟨h1, h2, h3⟩ := shadowVsEq_coord_spec shadow hnd b hb
      exact probEvent_drawList_getD_eq_le b.1 b.2 m h3 (hlt _ h1) (hlt _ h2)
    · rw [list_sum_map_const eqs c]
  refine le_trans (add_le_add hk (add_le_add hasgmass heqmass)) ?_
  have hle : asgSize asg + eqs.length
      ≤ D.length + P.length * shadow.length + scCount shadow := by
    have hcount := shadow_charge_count P ([] : List F) shadow
    rw [← hasg, ← heqs] at hcount
    omega
  rw [← add_mul, ← add_mul]
  refine mul_le_mul_right' (le_of_eq ?_) _
  norm_cast
  omega

/-! ## Plumbing for the seeded master induction -/

omit [Field F] [DecidableEq F] in
/-- Every supported tape of `drawList` has the announced length. -/
theorem drawList_support_length (m : ℕ) (vs : List F)
    (hvs : vs ∈ support (drawList ($ᵗ F) m)) : vs.length = m := by
  induction m generalizing vs with
  | zero =>
      rw [show drawList ($ᵗ F) 0 = (pure [] : ProbComp (List F)) from rfl,
        support_pure, Set.mem_singleton_iff] at hvs
      subst hvs
      rfl
  | succ m ih =>
      rw [show drawList ($ᵗ F) (m + 1)
          = (($ᵗ F) >>= fun v => drawList ($ᵗ F) m >>= fun ws =>
              pure (v :: ws)) from rfl] at hvs
      obtain ⟨v, -, hvs⟩ := (mem_support_bind_iff _ _ _).1 hvs
      obtain ⟨ws, hws, hvs⟩ := (mem_support_bind_iff _ _ _).1 hvs
      rw [support_pure, Set.mem_singleton_iff] at hvs
      subst hvs
      simp [ih ws hws]

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- Bind congruence restricted to the support of the sampler. -/
theorem probEvent_bind_congr_support {α β : Type} (oa : ProbComp α)
    (f g : α → ProbComp β) (P : β → Prop)
    (h : ∀ a ∈ support oa, f a = g a) :
    Pr[P | oa >>= f] = Pr[P | oa >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ support oa
  · rw [h a ha]
  · rw [probOutput_eq_zero_of_not_mem_support ha]
    simp

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- Split a bind bound through a bad event on the sampled value: pay the
bad-event mass, and bound the continuation on the good outcomes. -/
theorem probEvent_bind_le_probEvent_add {α β : Type} (oa : ProbComp α)
    (f : α → ProbComp β) (P : β → Prop) (Q : α → Prop) (B B' : ENNReal)
    (hQ : Pr[Q | oa] ≤ B')
    (h : ∀ a ∈ support oa, ¬ Q a → Pr[P | f a] ≤ B) :
    Pr[P | oa >>= f] ≤ B' + B := by
  classical
  rw [probEvent_bind_eq_tsum]
  have hterm : ∀ a : α,
      Pr[= a | oa] * Pr[P | f a]
        ≤ (if Q a then Pr[= a | oa] else 0)
          + (if Q a then 0 else Pr[= a | oa] * B) := by
    intro a
    by_cases hqa : Q a
    · simp only [hqa, if_true, add_zero]
      exact le_trans (mul_le_mul_left' probEvent_le_one _) (by simp)
    · simp only [hqa, if_false, zero_add]
      by_cases ha : a ∈ support oa
      · exact mul_le_mul_left' (h a ha hqa) _
      · rw [probOutput_eq_zero_of_not_mem_support ha]
        simp
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add ?_ ?_
  · refine le_trans (le_of_eq ?_) hQ
    rw [probEvent_eq_tsum_ite]
  · calc (∑' a : α, if Q a then 0 else Pr[= a | oa] * B)
        ≤ ∑' a : α, Pr[= a | oa] * B := by
          refine ENNReal.tsum_le_tsum fun a => ?_
          by_cases hqa : Q a <;> simp [hqa]
      _ = (∑' a : α, Pr[= a | oa]) * B := ENNReal.tsum_mul_right
      _ ≤ 1 * B := mul_le_mul_right' tsum_probOutput_le_one _
      _ = B := one_mul B

section MasterPlumbing

/-- Commute a secret/tape-independent core sampler in front of the secret
and hole tape. -/
theorem probEvent_kTape_core_swap_le {γ β : Type} (m : ℕ)
    (core : ProbComp γ) (cont : F → List F → γ → ProbComp β)
    (P : β → Prop) (B : ENNReal)
    (h : ∀ c ∈ support core,
      Pr[P | ($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
        cont k vs c] ≤ B) :
    Pr[P | ($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
        core >>= fun c => cont k vs c] ≤ B := by
  have h1 : 𝒟[($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
        core >>= fun c => cont k vs c]
      = 𝒟[core >>= fun c => ($ᵗ F) >>= fun k =>
          drawList ($ᵗ F) m >>= fun vs => cont k vs c] := by
    calc 𝒟[($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
          core >>= fun c => cont k vs c]
        = 𝒟[($ᵗ F) >>= fun k => core >>= fun c =>
            drawList ($ᵗ F) m >>= fun vs => cont k vs c] := by
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left
            ($ᵗ F) _ _ fun k => ?_
          exact OracleComp.DeferredSampling.evalDist_bind_comm
            (drawList ($ᵗ F) m) core (fun vs c => cont k vs c)
      _ = 𝒟[core >>= fun c => ($ᵗ F) >>= fun k =>
            drawList ($ᵗ F) m >>= fun vs => cont k vs c] :=
          OracleComp.DeferredSampling.evalDist_bind_comm
            ($ᵗ F) core (fun k c => drawList ($ᵗ F) m >>= fun vs =>
              cont k vs c)
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) h1)) ?_
  exact probEvent_bind_le_of_forall_le h

/-- Commute a core sampler out, then split on a bad event of its outcome:
pay the bad mass and bound the good continuations. -/
theorem probEvent_kTape_core_split_le {γ β : Type} (m : ℕ)
    (core : ProbComp γ) (cont : F → List F → γ → ProbComp β)
    (P : β → Prop) (Q : γ → Prop) (B B' : ENNReal)
    (hQ : Pr[Q | core] ≤ B')
    (h : ∀ c ∈ support core, ¬ Q c →
      Pr[P | ($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
        cont k vs c] ≤ B) :
    Pr[P | ($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
        core >>= fun c => cont k vs c] ≤ B' + B := by
  have h1 : 𝒟[($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
        core >>= fun c => cont k vs c]
      = 𝒟[core >>= fun c => ($ᵗ F) >>= fun k =>
          drawList ($ᵗ F) m >>= fun vs => cont k vs c] := by
    calc 𝒟[($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
          core >>= fun c => cont k vs c]
        = 𝒟[($ᵗ F) >>= fun k => core >>= fun c =>
            drawList ($ᵗ F) m >>= fun vs => cont k vs c] := by
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left
            ($ᵗ F) _ _ fun k => ?_
          exact OracleComp.DeferredSampling.evalDist_bind_comm
            (drawList ($ᵗ F) m) core (fun vs c => cont k vs c)
      _ = _ :=
          OracleComp.DeferredSampling.evalDist_bind_comm
            ($ᵗ F) core (fun k c => drawList ($ᵗ F) m >>= fun vs =>
              cont k vs c)
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) h1)) ?_
  exact probEvent_bind_le_probEvent_add core _ P Q B B' hQ h

/-- Fuse one fresh draw appended at the back of the tape into a longer
tape, under the secret binder. -/
theorem probEvent_kTape_snoc_le {β : Type} (m : ℕ)
    (cont : F → List F → ProbComp β) (P : β → Prop) (B : ENNReal)
    (h : Pr[P | ($ᵗ F) >>= fun k => drawList ($ᵗ F) (m + 1) >>= fun vs =>
      cont k vs] ≤ B) :
    Pr[P | ($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
        ($ᵗ F) >>= fun v => cont k (vs ++ [v])] ≤ B := by
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) ?_)) h
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left
    ($ᵗ F) _ _ fun k => ?_
  exact evalDist_drawList_snoc m (cont k)

/-- Re-parameterize one tape coordinate by the pad bijection
`v ↦ k + v·x` under the secret binder: the observed distribution is
unchanged. -/
theorem probEvent_kTape_reindex {β : Type} (m j : ℕ) (hj : j < m)
    (x : F) (hx : x ≠ 0) (cont : F → List F → ProbComp β) (P : β → Prop) :
    Pr[P | ($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
        cont k (vs.set j (k + (vs.getD j 0) * x))]
      = Pr[P | ($ᵗ F) >>= fun k => drawList ($ᵗ F) m >>= fun vs =>
          cont k vs] := by
  refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left
    ($ᵗ F) _ _ fun k => ?_
  have hbij : Function.Bijective (fun v : F => k + v * x) := by
    have h1 : Function.Bijective (fun v : F => v * x) :=
      mulRight_bijective₀ x hx
    have h2 : Function.Bijective (fun w : F => k + w) :=
      (Equiv.addLeft k).bijective
    exact h2.comp h1
  exact evalDist_drawList_set_bij m j hj (fun v => k + v * x) hbij (cont k)

end MasterPlumbing

/-! ## The seeded shadow state -/

variable {M : Type} [DecidableEq M]

/-- The k-free shadow description of a deferred-slope handler state: the
ideal caches, the per-index slope-cache pattern, the two adversary probe
transcripts, and the shadow of the recorded honest slopes. -/
structure DSShadowSt (F M : Type) where
  /-- the ideal (public) cache state -/
  ideal : IdealFrameSt F M
  /-- per-index slope-cache pattern -/
  pat : ℕ → Option (DSEntry F)
  /-- recorded direct secret probes -/
  secretProbes : List F
  /-- recorded direct `H_nf` probes -/
  slopeProbes : List F
  /-- shadow of the recorded honest slopes -/
  shadow : List (DSEntry F)

/-- Reify a shadow state at a concrete secret and hole tape. -/
def DSShadowSt.seed (σ : DSShadowSt F M) (k : F) (vs : List F) :
    DSFrameSt F M :=
  ⟨σ.ideal, fun i => (σ.pat i).map (DSEntry.eval k vs),
    ⟨σ.secretProbes, σ.slopeProbes, σ.shadow.map (DSEntry.eval k vs)⟩⟩

@[simp] theorem DSShadowSt.seed_ideal (σ : DSShadowSt F M) (k : F)
    (vs : List F) : (σ.seed k vs).ideal = σ.ideal := rfl

@[simp] theorem DSShadowSt.seed_slope (σ : DSShadowSt F M) (k : F)
    (vs : List F) (i : ℕ) :
    (σ.seed k vs).slope i = (σ.pat i).map (DSEntry.eval k vs) := rfl

@[simp] theorem DSShadowSt.seed_audit (σ : DSShadowSt F M) (k : F)
    (vs : List F) :
    (σ.seed k vs).audit
      = ⟨σ.secretProbes, σ.slopeProbes,
          σ.shadow.map (DSEntry.eval k vs)⟩ := rfl

/-- Structural invariants of a shadow state against a tape of length `m`
(Spec.md §7 T7, deferred-run bookkeeping). -/
structure DSShadowInv (σ : DSShadowSt F M) (m : ℕ) : Prop where
  hx : ∀ e ∈ σ.shadow, e.XNe0
  hsep : σ.shadow.Pairwise DSEntry.Sep
  hlt : ∀ j ∈ entryCoords σ.shadow, j < m
  hnd : (entryCoords σ.shadow).Nodup
  hroX : RoXCacheNonzero σ.ideal.roX
  hpat : ∀ i j, σ.pat i = some (.hole j) → DSEntry.hole j ∈ σ.shadow
  hpatinj : ∀ i i' j, σ.pat i = some (.hole j) →
    σ.pat i' = some (.hole j) → i = i'
  hfresh : ∀ i, σ.ideal.idx ≤ i → ∀ e, σ.pat i = some e →
    ∃ j, e = DSEntry.hole j

/-- The budget potential of a shadow state: direct probes, probe/slope
cross pairs, and the chargeable slope pairs (past, cross, and future). -/
def dsBudget (σ : DSShadowSt F M) (nA nE nId nNf nSig : ℕ) : ℕ :=
  (σ.secretProbes.length + (nA + nE + nId))
    + (σ.slopeProbes.length + nNf) * (σ.shadow.length + nSig)
    + (scCount σ.shadow + nSig * σ.shadow.length + Nat.choose nSig 2)

/-! ## Shadow update algebra -/

/-- Concrete ordinates of same-abscissa lines: the in-run duplication
targets of a fresh emission. -/
def dupTargets (x : F) (shadow : List (DSEntry F)) : List F :=
  shadow.filterMap fun e =>
    match e with
    | .line x' y' => if x = x' then some y' else none
    | _ => none

omit [Field F] [SampleableType F] in
/-- A cons of a hole charges every existing entry. -/
theorem scCount_hole_cons (j : ℕ) (shadow : List (DSEntry F)) :
    scCount (DSEntry.hole j :: shadow) = shadow.length + scCount shadow := by
  have h : (shadow.map (fun e' =>
      if (DSEntry.hole j).clash e' then 0 else 1)).sum = shadow.length := by
    induction shadow with
    | nil => simp
    | cons e rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih]
        cases e <;> simp [DSEntry.clash] <;> omega
  simp only [scCount, h]

omit [Field F] [SampleableType F] in
/-- `dupTargets` cons computation. -/
theorem dupTargets_cons (x : F) (e : DSEntry F) (rest : List (DSEntry F)) :
    dupTargets x (e :: rest)
      = (match e with
          | DSEntry.line x' y' => if x = x' then [y'] else []
          | _ => []) ++ dupTargets x rest := by
  cases e with
  | line x' y' =>
      by_cases hx : x = x' <;> simp [dupTargets, hx]
  | hole j => simp [dupTargets]
  | tline j x' => simp [dupTargets]

omit [Field F] [SampleableType F] in
/-- A cons of a concrete line charges every existing entry except the
same-abscissa lines, which are exactly the duplication targets. -/
theorem scCount_line_cons (x y : F) (shadow : List (DSEntry F)) :
    scCount (DSEntry.line x y :: shadow) + (dupTargets x shadow).length
      = shadow.length + scCount shadow := by
  have h : (shadow.map (fun e' =>
        if (DSEntry.line x y).clash e' then 0 else 1)).sum
      + (dupTargets x shadow).length = shadow.length := by
    induction shadow with
    | nil => simp [dupTargets]
    | cons e rest ih =>
        rw [dupTargets_cons]
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          List.length_append]
        cases e with
        | line x' y' =>
            by_cases hx : x = x'
            · subst hx
              rw [if_pos (by simp [DSEntry.clash])]
              simp only [List.length_append, if_true, List.length_cons,
                List.length_nil]
              omega
            · rw [if_neg (by simp [DSEntry.clash, hx])]
              simp only [if_neg hx, List.length_nil, List.length_append]
              omega
        | hole j =>
            have hcl : (DSEntry.line x y).clash (DSEntry.hole j)
                = false := rfl
            simp only [hcl, Bool.false_eq_true, if_false, List.length_nil]
            omega
        | tline j x' =>
            have hcl : (DSEntry.line x y).clash (DSEntry.tline j x')
                = false := rfl
            simp only [hcl, Bool.false_eq_true, if_false, List.length_nil]
            omega
  simp only [scCount]
  omega

/-- Replace the (unique) hole at coordinate `j` by its consumed tape-line
form. -/
def replaceHole (j : ℕ) (x : F) (e : DSEntry F) : DSEntry F :=
  if e = DSEntry.hole j then DSEntry.tline j x else e

section ReplaceHole

variable (j : ℕ) (x : F)

omit [Field F] [SampleableType F] in
theorem replaceHole_clash (a b : DSEntry F) :
    (replaceHole j x a).clash (replaceHole j x b) = a.clash b := by
  cases a <;> cases b <;> unfold replaceHole <;>
    split_ifs <;> simp_all [DSEntry.clash]

omit [Field F] [SampleableType F] in
theorem scCount_map_replaceHole (shadow : List (DSEntry F)) :
    scCount (shadow.map (replaceHole j x)) = scCount shadow := by
  induction shadow with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.map_cons, scCount, ih, List.map_map]
      congr 1
      refine congrArg List.sum ?_
      refine List.map_congr_left fun e' _ => ?_
      simp [Function.comp_apply, replaceHole_clash]

omit [Field F] [SampleableType F] in
theorem coord_replaceHole (e : DSEntry F) :
    (replaceHole j x e).coord = e.coord := by
  unfold replaceHole
  split_ifs with h
  · subst h; rfl
  · rfl

theorem entryCoords_map_replaceHole (shadow : List (DSEntry F)) :
    entryCoords (shadow.map (replaceHole j x)) = entryCoords shadow := by
  unfold entryCoords
  rw [List.filterMap_map]
  refine List.filterMap_congr fun e _ => ?_
  exact congrArg id (coord_replaceHole j x e)

omit [SampleableType F] in
theorem xne0_replaceHole (hx : x ≠ 0) (e : DSEntry F) (he : e.XNe0) :
    (replaceHole j x e).XNe0 := by
  unfold replaceHole
  split_ifs with h
  · exact hx
  · exact he

omit [Field F] [SampleableType F] in
theorem sep_replaceHole (a b : DSEntry F) (h : a.Sep b) :
    (replaceHole j x a).Sep (replaceHole j x b) := by
  unfold replaceHole
  split_ifs <;> first
    | trivial
    | (cases a <;> cases b <;> simp_all [DSEntry.Sep])

omit [SampleableType F] in
/-- Off the replaced hole, evaluation is unchanged. -/
theorem eval_replaceHole_of_ne (k : F) (vs : List F) (e : DSEntry F)
    (he : e ≠ DSEntry.hole j) :
    DSEntry.eval k vs (replaceHole j x e) = DSEntry.eval k vs e := by
  unfold replaceHole
  rw [if_neg he]

end ReplaceHole

omit [Field F] [SampleableType F] in
/-- The in-run duplication targets never exceed the shadow size. -/
theorem dupTargets_length_le (x : F) (shadow : List (DSEntry F)) :
    (dupTargets x shadow).length ≤ shadow.length := by
  unfold dupTargets
  exact List.length_filterMap_le _ _

/-! ## Evaluation stability of shadow entries -/

omit [SampleableType F] [Fintype F] in
/-- Appending one value at the back of the tape does not change the
evaluation of an entry whose coordinate lies inside the tape. -/
theorem DSEntry.eval_append_lt (k v : F) (vs : List F) (e : DSEntry F)
    (he : ∀ j, e.coord = some j → j < vs.length) :
    DSEntry.eval k (vs ++ [v]) e = DSEntry.eval k vs e := by
  have hget : ∀ j, j < vs.length → (vs ++ [v])[j]? = vs[j]? := by
    intro j hj
    exact List.getElem?_append_left hj
  cases e with
  | line x y => rfl
  | hole j =>
      have hj := he j rfl
      simp [DSEntry.eval, List.getD, hget j hj]
  | tline j x =>
      have hj := he j rfl
      simp [DSEntry.eval, List.getD, hget j hj]

omit [SampleableType F] [Fintype F] in
/-- Setting a foreign coordinate does not change the evaluation of an
entry. -/
theorem DSEntry.eval_set_ne (k w : F) (vs : List F) (j : ℕ) (e : DSEntry F)
    (he : ∀ i, e.coord = some i → i ≠ j) :
    DSEntry.eval k (vs.set j w) e = DSEntry.eval k vs e := by
  cases e with
  | line x y => rfl
  | hole i =>
      have hij := he i rfl
      simp [DSEntry.eval, List.getD, List.getElem?_set_ne (Ne.symm hij)]
  | tline i x =>
      have hij := he i rfl
      simp [DSEntry.eval, List.getD, List.getElem?_set_ne (Ne.symm hij)]

omit [Field F] [DecidableEq F] [SampleableType F] [Fintype F] in
/-- Inner probability congruence through a sampling prefix. -/
theorem probEvent_bind_congr_inner {α β : Type} (oa : ProbComp α)
    (f g : α → ProbComp β) (P : β → Prop)
    (h : ∀ a, Pr[P | f a] = Pr[P | g a]) :
    Pr[P | oa >>= f] = Pr[P | oa >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact tsum_congr fun a => by rw [h a]

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.probEvent_exists_mem_le
#print axioms Zkpc.Games.probEvent_drawList_getD_mem_le
#print axioms Zkpc.Games.probEvent_drawList_getD_eq_le
#print axioms Zkpc.Games.evalDist_drawList_set_bij
#print axioms Zkpc.Games.evalDist_drawList_snoc
#print axioms Zkpc.Games.shadow_charge_count
#print axioms Zkpc.Games.pair_eval_eq_charged
#print axioms Zkpc.Games.probe_eval_charged
#print axioms Zkpc.Games.frameLeakBad_shadow_charged
#print axioms Zkpc.Games.shadowVsMem_coord_spec
#print axioms Zkpc.Games.shadowVsEq_coord_spec
#print axioms Zkpc.Games.dsShadow_leaf_le
