import Zkpc.Chain.V2.Close
import VCVio

/-!
# The chain collision bound, proven (ROADMAP obligation 2(a))

`Zkpc/Chain/Collision.lean` and `Zkpc/Chain/V2/Close.lean` consume chain
collision-freedom as the hypothesis `Function.Injective nul`, and their
docstrings cite a lazy-random-oracle collision probability of at most
`n²/|N|` — until now docstring-only. This module proves the bound, in the
tighter birthday form `n(n-1) / (2|N|)`.

**The model.** Lazy random-oracle semantics for the chain
`N₁ = H(cid, c)`, `N_{j+1} = H(N_j, c)`: as long as no collision has
occurred, every query slot is fresh, so each new chain value is an
independent uniform sample — the first `n` links are an iid uniform draw
`v : Fin n → N`. This is exactly the idealization declared in
`Zkpc/Chain/Collision.lean`'s modeling conventions; here it is made a real
sampling statement (`$ᵗ (Fin n → N)`, VCV-io) instead of prose. The
theorems downstream inspect `nul` only at finitely many positions
(revealed indices `≤ msgs`, exhibited indices `≤ len + 2`), so
instantiating their `Function.Injective nul` hypothesis from an injective
finite prefix of length `m ≥ msgs + 2` is a finite matter; the
probabilistic content is all here.

**The counting.** Non-injective draws are covered by the pairwise collider
sets over strictly increasing index pairs; each collider has exactly
`|N|^(n-1)` members (`colliderEquiv`), and there are `C(n,2)` pairs, so
the collision event has probability at most
`C(n,2) · |N|^(n-1) / |N|^n = n(n-1) / (2|N|)`.
-/

open OracleComp Finset
open scoped ENNReal NNReal

namespace Zkpc.Chain.V2

variable {N : Type} [DecidableEq N] [Fintype N]

/-- Draws colliding at the (distinct) positions `i, j` are exactly the
functions on the remaining `n - 1` positions: drop the value at `j`
(recoverable as the value at `i`). -/
def colliderEquiv (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    {v : Fin n → N // v i = v j} ≃ ({k : Fin n // k ≠ j} → N) where
  toFun v k := v.1 k.1
  invFun f :=
    ⟨fun k => if h : k = j then f ⟨i, hij⟩ else f ⟨k, h⟩, by
      simp [hij]⟩
  left_inv v := by
    apply Subtype.ext
    funext k
    by_cases h : k = j
    · subst h
      simpa using v.2
    · simp [h]
  right_inv f := by
    funext k
    rcases k with ⟨k, hk⟩
    simp [hk]

/-- Each pairwise collider set has exactly `|N|^(n-1)` members. -/
lemma card_collider (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (univ.filter fun v : Fin n → N => v i = v j).card
      = Fintype.card N ^ (n - 1) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (colliderEquiv n i j hij),
    Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem
    (mem_univ j), Finset.card_univ, Fintype.card_fin]

/-- **Counting form of the birthday bound**: at most
`C(n,2) · |N|^(n-1)` of the `|N|^n` draws are non-injective. -/
lemma card_not_injective_le (n : ℕ) :
    (univ.filter fun v : Fin n → N => ¬ Function.Injective v).card
      ≤ n.choose 2 * Fintype.card N ^ (n - 1) := by
  have hsub : (univ.filter fun v : Fin n → N => ¬ Function.Injective v) ⊆
      (univ.filter fun p : Fin n × Fin n => p.1 < p.2).biUnion
        (fun p => univ.filter fun v : Fin n → N => v p.1 = v p.2) := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    rw [Function.not_injective_iff] at hv
    obtain ⟨i, j, hvij, hij⟩ := hv
    rcases lt_or_gt_of_ne hij with h | h
    · exact mem_biUnion.2 ⟨(i, j), by simp [h], by simp [hvij]⟩
    · exact mem_biUnion.2 ⟨(j, i), by simp [h], by simp [hvij.symm]⟩
  calc (univ.filter fun v : Fin n → N => ¬ Function.Injective v).card
      ≤ ((univ.filter fun p : Fin n × Fin n => p.1 < p.2).biUnion
          (fun p => univ.filter fun v : Fin n → N => v p.1 = v p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
          (univ.filter fun v : Fin n → N => v p.1 = v p.2).card :=
        Finset.card_biUnion_le
    _ = ∑ _p ∈ univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
          Fintype.card N ^ (n - 1) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        simp only [mem_filter] at hp
        exact card_collider n p.1 p.2 (ne_of_lt hp.2)
    _ = n.choose 2 * Fintype.card N ^ (n - 1) := by
        rw [Finset.sum_const, Finset.card_filter_fst_lt_snd, smul_eq_mul]

variable [SampleableType N]

/-- **The chain collision bound** (discharges the docstring-only claim of
`Zkpc/Chain/Collision.lean`, tighter): the first `n` links of a lazily
sampled chain fail collision-freedom (`Function.Injective`) with
probability at most `n(n-1) / (2|N|)`. Everything downstream that assumes
`Function.Injective nul` — `honest_close_unchallengeable`,
`ghost_no_evidence`, `safe_iff`, `canonical_safe`, the machine bridges —
holds except on this event. -/
theorem probEvent_chain_collision_le (n : ℕ) :
    Pr[fun v : Fin n → N => ¬ Function.Injective v | $ᵗ (Fin n → N)]
      ≤ ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card N) := by
  -- degenerate domains: on `Fin 0` and `Fin 1` every draw is injective
  rcases le_or_gt n 1 with hn1 | hn1
  · have hempty :
        (univ.filter fun v : Fin n → N => ¬ Function.Injective v) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun v _ => ?_
      have : Subsingleton (Fin n) := by
        interval_cases n <;> infer_instance
      exact not_not_intro (Function.injective_of_subsingleton v)
    rw [probEvent_uniformSample, hempty]
    simp
  -- degenerate range: `n ≥ 2` and `|N| = 0` sends the bound to `⊤`
  rcases Nat.eq_zero_or_pos (Fintype.card N) with hN | hN
  · have h2 : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (by omega) (by omega)).ne'
    rw [hN, Nat.cast_zero, mul_zero, ENNReal.div_zero h2]
    exact le_top
  -- main case
  rw [probEvent_uniformSample]
  have hcard : Fintype.card (Fin n → N) = Fintype.card N ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hcard]
  have hNe0 : (Fintype.card N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNeT : (Fintype.card N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ((univ.filter fun v : Fin n → N => ¬ Function.Injective v).card
          : ℝ≥0∞) / ((Fintype.card N ^ n : ℕ) : ℝ≥0∞)
      ≤ ((n.choose 2 * Fintype.card N ^ (n - 1) : ℕ) : ℝ≥0∞)
          / ((Fintype.card N ^ n : ℕ) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast card_not_injective_le n
    _ = (n.choose 2 : ℝ≥0∞) *
          (((Fintype.card N ^ (n - 1) : ℕ) : ℝ≥0∞)
            / ((Fintype.card N ^ n : ℕ) : ℝ≥0∞)) := by
        push_cast
        rw [mul_div_assoc]
    _ ≤ (n.choose 2 : ℝ≥0∞) * (Fintype.card N : ℝ≥0∞)⁻¹ := by
        gcongr
        have hsplit : (Fintype.card N ^ n : ℕ)
            = Fintype.card N ^ (n - 1) * Fintype.card N := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hsplit]
        push_cast
        rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by positivity))
          (Or.inl (ENNReal.pow_ne_top hNeT))]
        rw [mul_comm ((Fintype.card N : ℝ≥0∞) ^ (n - 1))⁻¹ _,
          mul_assoc, ENNReal.inv_mul_cancel (by positivity)
            (ENNReal.pow_ne_top hNeT), mul_one]
    _ ≤ (((n * (n - 1) : ℕ) : ℝ≥0∞) / 2) * (Fintype.card N : ℝ≥0∞)⁻¹ := by
        gcongr
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
          (Or.inl (by norm_num))]
        have := Nat.div_mul_le_self (n * (n - 1)) 2
        calc (n.choose 2 : ℝ≥0∞) * 2
            = ((n.choose 2 * 2 : ℕ) : ℝ≥0∞) := by push_cast; ring
          _ ≤ ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
              exact_mod_cast Nat.choose_two_right n ▸ this
    _ = ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card N) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
          ← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inr hNe0)]

end Zkpc.Chain.V2

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.V2.card_collider
#print axioms Zkpc.Chain.V2.card_not_injective_le
#print axioms Zkpc.Chain.V2.probEvent_chain_collision_le
