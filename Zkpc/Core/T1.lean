import Zkpc.Core.State

/-!
# T1 — No overspend, and the honest-signal invariants (tasks D2, part of D1)

`T1_no_overspend` is Spec.md §7 T1, flat-ticket, single honest payee
(equivalently `L = 0`): at every reachable state, the accepted value
attributed to any secret `k` is at most the deposit `D`.

`honest_never_slashed` is the symbolic form of the shared exculpability
lemma (Spec.md T3 second clause / T7 algebraic core): a protocol-following
payer emits at most one signal per index — spend signals strictly below its
counter, the close signal exactly once at its recorded index — so `Dispute`
evidence against it cannot exist in the model. The probabilistic statement
backing the symbolic move (the adversary cannot mint signals for honest
secrets) is `single_signal_hiding`, proved in the game layer (T7).
-/

namespace Zkpc.Core

open Finset

variable {K M : Type} [DecidableEq K] [DecidableEq M]
variable {C D τ : ℕ} {honest : K → Prop} {mclose : M}

/-- Safety invariant on the accepted set: per-`(k,i)` nullifier uniqueness
(check 6's freshness) and per-ticket solvency (R_spend conjunct 2). -/
def SafeAcc (C D : ℕ) (s : St K M) : Prop :=
  (∀ k i m m', (k, i, m) ∈ s.acc → (k, i, m') ∈ s.acc → m = m') ∧
  (∀ k i m, (k, i, m) ∈ s.acc → (i + 1) * C ≤ D)

/-- Honest-payer signal invariant: spend signals sit strictly below the
counter and never use the close message; close signals exist only with a
matching close record; the recorded close index is the counter at close
time; per-index signal uniqueness; and honest channels are never slashed. -/
def HonestSig (honest : K → Prop) (mclose : M) (s : St K M) : Prop :=
  (∀ k i m, honest k → (k, i, m) ∈ s.sigs → m ≠ mclose → i < s.emittedCnt k) ∧
  (∀ k i, honest k → (k, i, mclose) ∈ s.sigs → ∃ t, s.closedAt k = some (i, t)) ∧
  (∀ k j t, honest k → s.closedAt k = some (j, t) → j = s.emittedCnt k) ∧
  (∀ k i m m', honest k → (k, i, m) ∈ s.sigs → (k, i, m') ∈ s.sigs → m = m') ∧
  (∀ k, honest k → s.slashedAt k = none)

/-- No signal of an honest payer sits at its current counter value: spend
signals are strictly below (by the index bound) and the close signal's
index equals the counter only when the channel is already closed. -/
private lemma no_sig_at_counter {s : St K M}
    (hIdx : ∀ k i m, honest k → (k, i, m) ∈ s.sigs → m ≠ mclose → i < s.emittedCnt k)
    (hCloseSig : ∀ k i, honest k → (k, i, mclose) ∈ s.sigs → ∃ t, s.closedAt k = some (i, t))
    {k : K} (hh : honest k) (hcl : s.closedAt k = none) (m' : M) :
    (k, s.emittedCnt k, m') ∉ s.sigs := by
  intro hmem
  by_cases hmc : m' = mclose
  · subst hmc
    obtain ⟨t, hct⟩ := hCloseSig k (s.emittedCnt k) hh hmem
    rw [hcl] at hct
    simp at hct
  · exact Nat.lt_irrefl _ (hIdx k (s.emittedCnt k) m' hh hmem hmc)

/-- The two invariants hold at every reachable state. -/
theorem reach_inv {s : St K M}
    (h : Reach C D τ honest mclose s) :
    SafeAcc C D s ∧ HonestSig honest mclose s := by
  induction h with
  | init =>
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [Zkpc.Core.init, SafeAcc, HonestSig]
  | step hprev hstep ih =>
    obtain ⟨⟨hFresh, hSolv⟩, hIdx, hCloseSig, hCloseIdx, hUniq, hNoSlash⟩ := ih
    cases hstep with
    | tick =>
      exact ⟨⟨hFresh, hSolv⟩, hIdx, hCloseSig, hCloseIdx, hUniq, hNoSlash⟩
    | openCh k hnew =>
      exact ⟨⟨hFresh, hSolv⟩, hIdx, hCloseSig, hCloseIdx, hUniq, hNoSlash⟩
    | emitHonest k m hh hlive hm hsolv =>
      obtain ⟨hop, hsl, hcl⟩ := hlive
      refine ⟨⟨hFresh, hSolv⟩, ?_, ?_, ?_, ?_, hNoSlash⟩
      · -- spend-signal index bound
        intro k' i' m' hh' hmem hmc
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | hold
        · simp [Function.update_apply]
        · rcases eq_or_ne k' k with rfl | hkk
          · simp only [Function.update_apply, if_pos rfl]
            exact Nat.lt_succ_of_lt (hIdx k' i' m' hh' hold hmc)
          · simpa [Function.update_apply, hkk] using hIdx k' i' m' hh' hold hmc
      · -- close signals unchanged
        intro k' i' hh' hmem
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, hmm⟩ | hold
        · exact absurd hmm.symm hm
        · exact hCloseSig k' i' hh' hold
      · -- close-index vs counter: counter only moves while unclosed
        intro k' j t hh' hct
        rcases eq_or_ne k' k with rfl | hkk
        · rw [hcl] at hct
          simp at hct
        · simpa [Function.update_apply, hkk] using hCloseIdx k' j t hh' hct
      · -- per-index uniqueness: the new signal's index is fresh
        intro k' i' m1 m2 hh' h1 h2
        simp only [Finset.mem_insert, Prod.mk.injEq] at h1 h2
        rcases h1 with ⟨rfl, rfl, rfl⟩ | h1old
        · rcases h2 with ⟨-, -, rfl⟩ | h2old
          · rfl
          · exact absurd h2old (no_sig_at_counter hIdx hCloseSig hh' hcl m2)
        · rcases h2 with ⟨rfl, hi2, rfl⟩ | h2old
          · exact absurd (hi2 ▸ h1old)
              (no_sig_at_counter hIdx hCloseSig hh' hcl m1)
          · exact hUniq k' i' m1 m2 hh' h1old h2old
    | emitAdv k i m hadv =>
      refine ⟨⟨hFresh, hSolv⟩, ?_, ?_, hCloseIdx, ?_, hNoSlash⟩
      · intro k' i' m' hh' hmem hmc
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | hold
        · exact absurd hh' hadv
        · exact hIdx k' i' m' hh' hold hmc
      · intro k' i' hh' hmem
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, hmm⟩ | hold
        · exact absurd hh' hadv
        · exact hCloseSig k' i' hh' hold
      · intro k' i' m1 m2 hh' h1 h2
        simp only [Finset.mem_insert, Prod.mk.injEq] at h1 h2
        rcases h1 with ⟨rfl, rfl, rfl⟩ | h1old
        · exact absurd hh' hadv
        · rcases h2 with ⟨rfl, rfl, rfl⟩ | h2old
          · exact absurd hh' hadv
          · exact hUniq k' i' m1 m2 hh' h1old h2old
    | accept k i m hsig hm hlive hsolv hfresh =>
      refine ⟨⟨?_, ?_⟩, hIdx, hCloseSig, hCloseIdx, hUniq, hNoSlash⟩
      · intro k' i' m1 m2 h1 h2
        simp only [Finset.mem_insert, Prod.mk.injEq] at h1 h2
        rcases h1 with ⟨rfl, rfl, rfl⟩ | h1old
        · rcases h2 with ⟨-, -, rfl⟩ | h2old
          · rfl
          · exact absurd h2old (hfresh m2)
        · rcases h2 with ⟨rfl, rfl, rfl⟩ | h2old
          · exact absurd h1old (hfresh m1)
          · exact hFresh k' i' m1 m2 h1old h2old
      · intro k' i' m' hmem
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | hold
        · exact hsolv
        · exact hSolv k' i' m' hold
    | slash k i m m' h1 h2 hne hopen hns =>
      refine ⟨⟨hFresh, hSolv⟩, hIdx, hCloseSig, hCloseIdx, hUniq, ?_⟩
      intro k' hh'
      rcases eq_or_ne k' k with rfl | hkk
      · exact absurd (hUniq k' i m m' hh' h1 h2) hne
      · simpa [Function.update_apply, hkk] using hNoSlash k' hh'
    | payerClose k j hlive hj =>
      obtain ⟨hop, hsl, hcl⟩ := hlive
      refine ⟨⟨hFresh, hSolv⟩, ?_, ?_, ?_, ?_, hNoSlash⟩
      · intro k' i' m' hh' hmem hmc
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, hmm⟩ | hold
        · exact absurd hmm hmc
        · exact hIdx k' i' m' hh' hold hmc
      · intro k' i' hh' hmem
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases eq_or_ne k' k with rfl | hkk
        · rcases hmem with ⟨-, rfl, -⟩ | hold
          · simp
          · obtain ⟨t, hct⟩ := hCloseSig k' i' hh' hold
            rw [hcl] at hct
            simp at hct
        · rcases hmem with ⟨hk, -, -⟩ | hold
          · exact absurd hk hkk
          · simpa [Function.update_apply, hkk] using hCloseSig k' i' hh' hold
      · intro k' j' t hh' hct
        rcases eq_or_ne k' k with rfl | hkk
        · simp at hct
          exact hct.1 ▸ hj hh'
        · simp only [Function.update_apply, if_neg hkk] at hct
          exact hCloseIdx k' j' t hh' hct
      · intro k' i' m1 m2 hh' h1 h2
        simp only [Finset.mem_insert, Prod.mk.injEq] at h1 h2
        rcases h1 with ⟨rfl, rfl, rfl⟩ | h1old
        · rcases h2 with ⟨-, -, rfl⟩ | h2old
          · rfl
          · rw [hj hh'] at h2old
            exact absurd h2old (no_sig_at_counter hIdx hCloseSig hh' hcl m2)
        · rcases h2 with ⟨rfl, hi2, rfl⟩ | h2old
          · rw [hj hh'] at hi2
            rw [hi2] at h1old
            exact absurd h1old (no_sig_at_counter hIdx hCloseSig hh' hcl m1)
          · exact hUniq k' i' m1 m2 hh' h1old h2old
    | settleClose k j t hc hexp hns hnotYet =>
      exact ⟨⟨hFresh, hSolv⟩, hIdx, hCloseSig, hCloseIdx, hUniq, hNoSlash⟩
    | sweepOne k i m hacc hdedup hwin =>
      exact ⟨⟨hFresh, hSolv⟩, hIdx, hCloseSig, hCloseIdx, hUniq, hNoSlash⟩

/-- **T1 — No overspend (Spec.md §7 T1, flat ticket, `L = 0`).**
For every reachable state of the single-honest-payee machine — the
adversary controlling all payers, all messages, all scheduling — and every
member secret `k`: the flat-price value of accepted tickets attributed to
`k` never exceeds the deposit `D`. In symbols:
`C · |{accepted tickets attributed to k}| ≤ D`.

Proof shape: check-6 freshness makes the accepted indices of `k` pairwise
distinct; the solvency guard bounds each accepted index by `D/C`; so the
count is at most `⌊D/C⌋` and the value at most `C·⌊D/C⌋ ≤ D`. -/
theorem T1_no_overspend {s : St K M}
    (h : Reach C D τ honest mclose s) (k : K) :
    s.valueOf k C ≤ D := by
  rcases Nat.eq_zero_or_pos C with hC | hC
  · simp [St.valueOf, hC]
  obtain ⟨⟨hFresh, hSolv⟩, -⟩ := reach_inv h
  have hinj : Set.InjOn (fun t : K × ℕ × M => t.2.1) ↑(s.accOf k) := by
    intro t1 h1 t2 h2 heq
    simp only [Finset.mem_coe, St.accOf, Finset.mem_filter] at h1 h2
    obtain ⟨h1a, h1k⟩ := h1
    obtain ⟨h2a, h2k⟩ := h2
    obtain ⟨k1, i1, m1⟩ := t1
    obtain ⟨k2, i2, m2⟩ := t2
    have hk1 : k1 = k := h1k
    have hk2 : k2 = k := h2k
    have hii : i1 = i2 := heq
    have hkk : k1 = k2 := hk1.trans hk2.symm
    have h2a' : (k1, i1, m2) ∈ s.acc := by rw [hkk, hii]; exact h2a
    have hm : m1 = m2 := hFresh k1 i1 m1 m2 h1a h2a'
    simp [hkk, hii, hm]
  have hcard : (s.accOf k).card = ((s.accOf k).image (fun t => t.2.1)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : (s.accOf k).image (fun t => t.2.1) ⊆ Finset.range (D / C) := by
    intro i hi
    simp only [Finset.mem_image] at hi
    obtain ⟨t, ht, hti⟩ := hi
    obtain ⟨htacc, -⟩ := Finset.mem_filter.mp ht
    obtain ⟨k1, i1, m1⟩ := t
    obtain rfl : i1 = i := hti
    have hsolv := hSolv k1 i1 m1 htacc
    rw [Finset.mem_range]
    have hle : i1 + 1 ≤ D / C := (Nat.le_div_iff_mul_le hC).mpr hsolv
    omega
  have hle : (s.accOf k).card ≤ D / C := by
    rw [hcard]
    simpa using Finset.card_le_card hsub
  calc s.valueOf k C = C * (s.accOf k).card := rfl
    _ ≤ C * (D / C) := Nat.mul_le_mul (Nat.le_refl C) hle
    _ = (D / C) * C := Nat.mul_comm _ _
    _ ≤ D := Nat.div_mul_le_self D C

/-- **Shared exculpability lemma, symbolic form (Spec.md T3 second clause;
T7's algebraic core in the model).** A protocol-following payer is never
slashed, in any reachable state, against any adversary — because it emits
at most one signal per index (spend signals strictly below its counter, the
close signal once), so the conflicting pair `Dispute` requires cannot
exist. The probabilistic complement (an adversary cannot *mint* a second
point on an honest line) is T7 in the game layer. -/
theorem honest_never_slashed {s : St K M}
    (h : Reach C D τ honest mclose s) (k : K) (hk : honest k) :
    s.slashedAt k = none :=
  (reach_inv h).2.2.2.2.2 k hk

end Zkpc.Core
