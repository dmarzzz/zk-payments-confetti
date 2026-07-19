import Zkpc.Chain.V2.CollisionBound

/-!
# Chain non-frameability: the hidden-target kernel (ROADMAP obligation 3, stage 1)

Spec-v2 §5 makes a challenge witness valid only if its payment proof
verifies, and the chain equation `N_{j+1} = H(N_j, c)` inside R_pay (A5)
is what should make witnesses unforgeable: after an honest close publishes
the opening of the closed state's next-nullifier, a challenger without the
chain secret `c` cannot author a message revealing it (Spec-v2 §7,
"Non-frameability"). This module proves the **hidden-target kernel** of
that claim, staged exactly as the rev-11 T7 campaign was: the
secret-averaged guessing bound first (this file, the analogue of
`T7_frame_bound` + `fsProgramCollisionBound`'s hidden-target kernels), the
adaptive shared-oracle composition second (the analogue of the
`FrameDeferred*`/`FrameComplete` apparatus; recorded as stage 2 in
`ROADMAP.md`).

**The game.** Honest Alice's channel: chain secret `c ← C` uniform; the
framing target is the *unrevealed* committed next-nullifier of her closing
state — in the lazy-RO model of `Zkpc/Chain/V2/CollisionBound.lean` a
fresh-uniform value `y ← N`, independent of the adversary's whole view
(every revealed nullifier is an earlier, distinct chain slot; balances and
cid sit inside hiding commitments). The adversary (Bob with the full
transcript) is summarized secret-averaged, as the repo's certificates
require: a list of hash-probe candidates for the chain secret (each probe
`H(N_parent, c')` tests one candidate `c'`; the parent-reveal is public,
so a probe is exactly a `c`-guess) and a fallback direct guess at `y`.

* A probe hitting `c` is **conservatively awarded the win** — with `c` the
  adversary can recompute the whole chain, so the kernel does not model
  what he does afterwards.
* Otherwise he wins only by blind-guessing the fresh-uniform `y`.

`chainFrame_bound`: the win probability is at most `q/|C| + 1/|N|`.

**Anti-vacuity** (the calibration discipline of `Zkpc/Games/Calibration.lean`):
a scheme that leaks the committed next-nullifier is framed with
probability 1 (`chainFrame_leaky_loses`), and an enumerable secret space
is ground out with probability 1 (`chainFrame_grind_loses`) — the two
degenerate schemes the bound must catch, witnessing that both terms of
`q/|C| + 1/|N|` are load-bearing.
-/

open OracleComp Finset
open scoped ENNReal NNReal

namespace Zkpc.Chain.V2

variable {C N : Type} [DecidableEq C] [Fintype C] [DecidableEq N] [Fintype N]

/-- A secret-averaged framing adversary: `probes` are the chain-secret
candidates tested by its hash queries (at the public parent-reveal), and
`fallback` is its direct guess at the unrevealed committed
next-nullifier. -/
structure FrameGuess (C N : Type) where
  probes : List C
  fallback : N

/-- The (conservative) win predicate: some probe hits the chain secret, or
the fallback guesses the fresh target. -/
def ChainFrameWins (A : FrameGuess C N) (c : C) (y : N) : Prop :=
  c ∈ A.probes ∨ A.fallback = y

instance (A : FrameGuess C N) (c : C) (y : N) :
    Decidable (ChainFrameWins A c y) := by
  unfold ChainFrameWins
  infer_instance

/-- Counting form: at most `q·|N| + |C|` of the `|C|·|N|` secret/target
pairs are winning. -/
lemma card_chainFrameWins_le (A : FrameGuess C N) :
    (univ.filter fun p : C × N => ChainFrameWins A p.1 p.2).card
      ≤ A.probes.length * Fintype.card N + Fintype.card C := by
  have hsub : (univ.filter fun p : C × N => ChainFrameWins A p.1 p.2) ⊆
      (univ.filter fun p : C × N => p.1 ∈ A.probes) ∪
        (univ.filter fun p : C × N => A.fallback = p.2) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    rcases hp with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
  gcongr
  · -- probe hits: contained in probes.toFinset ×ˢ univ
    have : (univ.filter fun p : C × N => p.1 ∈ A.probes) ⊆
        A.probes.toFinset ×ˢ (univ : Finset N) := by
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      exact Finset.mem_product.2 ⟨List.mem_toFinset.2 hp, Finset.mem_univ _⟩
    refine le_trans (Finset.card_le_card this) ?_
    rw [Finset.card_product, Finset.card_univ]
    exact Nat.mul_le_mul_right _ (A.probes.toFinset_card_le)
  · -- fallback hits: contained in univ ×ˢ {fallback}
    have : (univ.filter fun p : C × N => A.fallback = p.2) ⊆
        (univ : Finset C) ×ˢ {A.fallback} := by
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_singleton.2 hp.symm⟩
    refine le_trans (Finset.card_le_card this) ?_
    rw [Finset.card_product, Finset.card_univ, Finset.card_singleton, mul_one]

variable [Inhabited C] [Inhabited N] [SampleableType C] [SampleableType N]

/-- **The chain-frame kernel bound** (Spec-v2 §7 non-frameability, stage 1):
a `q`-probe secret-averaged adversary frames an honest close with
probability at most `q/|C| + 1/|N|`. -/
theorem chainFrame_bound (A : FrameGuess C N) :
    Pr[fun p : C × N => ChainFrameWins A p.1 p.2 | $ᵗ (C × N)]
      ≤ (A.probes.length : ℝ≥0∞) / Fintype.card C
        + (Fintype.card N : ℝ≥0∞)⁻¹ := by
  have hC : 0 < Fintype.card C := Fintype.card_pos
  have hN : 0 < Fintype.card N := Fintype.card_pos
  have hCe : (Fintype.card C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hCt : (Fintype.card C : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hNe : (Fintype.card N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (Fintype.card N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [probEvent_uniformSample, Fintype.card_prod]
  calc ((univ.filter fun p : C × N => ChainFrameWins A p.1 p.2).card : ℝ≥0∞)
        / ((Fintype.card C * Fintype.card N : ℕ) : ℝ≥0∞)
      ≤ ((A.probes.length * Fintype.card N + Fintype.card C : ℕ) : ℝ≥0∞)
        / ((Fintype.card C * Fintype.card N : ℕ) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast card_chainFrameWins_le A
    _ = ((A.probes.length * Fintype.card N : ℕ) : ℝ≥0∞)
          / ((Fintype.card C * Fintype.card N : ℕ) : ℝ≥0∞)
        + ((Fintype.card C : ℕ) : ℝ≥0∞)
          / ((Fintype.card C * Fintype.card N : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same]
        push_cast
        ring_nf
    _ = (A.probes.length : ℝ≥0∞) / Fintype.card C
        + (Fintype.card N : ℝ≥0∞)⁻¹ := by
        congr 1
        · push_cast
          rw [mul_comm (A.probes.length : ℝ≥0∞) (Fintype.card N : ℝ≥0∞),
            mul_comm (Fintype.card C : ℝ≥0∞) (Fintype.card N : ℝ≥0∞),
            ENNReal.mul_div_mul_left _ _ hNe hNt]
        · push_cast
          rw [ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl hCe) (Or.inl hCt),
            mul_comm ((Fintype.card C : ℝ≥0∞))⁻¹ _, mul_assoc,
            ENNReal.inv_mul_cancel hCe hCt, mul_one]

/-! ## Anti-vacuity calibrations (must-lose degenerate schemes) -/

/-- **Leaky scheme loses**: if the committed next-nullifier is disclosed to
the adversary (a scheme that reveals it early, or a non-hiding joint
commitment — the break A5/Q5 exists to prevent), the trivial adversary that
echoes it frames every honest close: win probability `1`. -/
theorem chainFrame_leaky_loses :
    Pr[fun p : C × N => ChainFrameWins ⟨[], p.2⟩ p.1 p.2 | $ᵗ (C × N)]
      = 1 := by
  rw [probEvent_uniformSample]
  have hall : (univ.filter fun p : C × N => ChainFrameWins ⟨[], p.2⟩ p.1 p.2)
      = univ :=
    Finset.filter_eq_self.2 fun p _ => Or.inr rfl
  rw [hall, Finset.card_univ, ENNReal.div_self
    (by exact_mod_cast (Fintype.card_pos (α := C × N)).ne')
    (ENNReal.natCast_ne_top _)]

/-- **Grindable secret space loses**: an adversary that can afford `|C|`
hash probes enumerates the chain-secret space and frames every honest
close: win probability `1`. The `q/|C|` term of the bound is exactly what
priced this out. -/
theorem chainFrame_grind_loses (y0 : N) :
    Pr[fun p : C × N =>
        ChainFrameWins ⟨(univ : Finset C).toList, y0⟩ p.1 p.2
      | $ᵗ (C × N)] = 1 := by
  rw [probEvent_uniformSample]
  have hall : (univ.filter fun p : C × N =>
      ChainFrameWins ⟨(univ : Finset C).toList, y0⟩ p.1 p.2)
      = univ :=
    Finset.filter_eq_self.2 fun p _ =>
      Or.inl (by simp [Finset.mem_toList])
  rw [hall, Finset.card_univ, ENNReal.div_self
    (by exact_mod_cast (Fintype.card_pos (α := C × N)).ne')
    (ENNReal.natCast_ne_top _)]

end Zkpc.Chain.V2

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.V2.card_chainFrameWins_le
#print axioms Zkpc.Chain.V2.chainFrame_bound
#print axioms Zkpc.Chain.V2.chainFrame_leaky_loses
#print axioms Zkpc.Chain.V2.chainFrame_grind_loses
