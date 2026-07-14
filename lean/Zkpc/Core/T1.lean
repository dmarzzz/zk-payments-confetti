import Zkpc.Core.State

/-!
# T1 — No overspend, and the honest-payer invariants (tasks D2, part of D1; Spec.md rev-7)

`T1_no_overspend` is Spec.md §7 T1, flat-ticket, single honest payee
(equivalently `L = 0`): at every reachable state, the accepted value
attributed to any secret `k` is at most the deposit `D`.

`honest_never_slashed` is the symbolic form of the shared exculpability
lemma (Spec.md T3 second clause / T7 algebraic core): a protocol-following
payer emits at most one signal per index, so `Dispute` evidence against it
cannot exist in the model; and under MC20 its close emits **no** signal —
only PRF-fresh unused-nullifier reveals with no line point — so the close
opens no new evidence surface (Spec.md T3, rev-7 wording). The
probabilistic statement backing the symbolic move (the adversary cannot
mint signals for honest secrets) is `single_signal_hiding`, proved in the
game layer (T7).

`honest_close_undisputable` is the MC20 facet of exculpability: an honest
closer's window allows no valid close-dispute (Spec.md T5, rev-7: its
claimed-unused indices were genuinely never used, so no acceptance can
bit-match against them). Symbolically: every accepted ticket of an honest
`k` sits strictly below its emission counter, while its claimed set `U`
sits at or above it.
-/

namespace Zkpc.Core

open Finset

variable {K M : Type} [DecidableEq K] [DecidableEq M]
variable {C D τ : ℕ} {honest : K → Prop}

/-- Safety invariant on the accepted set: per-`(k,i)` nullifier uniqueness
(check 6's freshness), per-ticket solvency (R_spend conjunct 2), every
accepted ticket has an emitted witness (the knowledge-soundness guard of
`accept` — `acc ⊆ sigs`), and every swept nullifier traces to an accepted
ticket (MC16: sweeps only of redeemed tuples — the clause the rev-8
two-sided bar's void branch reasons from). -/
def SafeAcc (C D : ℕ) (s : St K M) : Prop :=
  (∀ k i m m', (k, i, m) ∈ s.acc → (k, i, m') ∈ s.acc → m = m') ∧
  (∀ k i m, (k, i, m) ∈ s.acc → (i + 1) * C ≤ D) ∧
  (∀ k i m, (k, i, m) ∈ s.acc → (k, i, m) ∈ s.sigs) ∧
  (∀ p ∈ s.swept, ∃ m : M, (p.1, p.2, m) ∈ s.acc)

/-- Honest-payer invariant (rev-7, MC20): every signal of an honest payer
sits strictly below its counter (the close emits no signal, so no
exemption is needed); per-index signal uniqueness; an honest payer's
recorded close set is exactly its unused indices
`{i | emittedCnt ≤ i < ⌊D/C⌋}` (the `payerClose` honest guard, frozen
thereafter because emission requires a live channel); and honest channels
are never slashed — by `Dispute` or by `closeDispute`. -/
def HonestSig (C D : ℕ) (honest : K → Prop) (s : St K M) : Prop :=
  (∀ k i m, honest k → (k, i, m) ∈ s.sigs → i < s.emittedCnt k) ∧
  (∀ k i m m', honest k → (k, i, m) ∈ s.sigs → (k, i, m') ∈ s.sigs → m = m') ∧
  (∀ k U t, honest k → s.closedAt k = some (U, t) →
    U = (Finset.range (D / C)).filter (fun i => s.emittedCnt k ≤ i)) ∧
  (∀ k, honest k → s.slashedAt k = none)

/-- No signal of an honest payer sits at its current counter value. -/
private lemma no_sig_at_counter {s : St K M}
    (hIdx : ∀ k i m, honest k → (k, i, m) ∈ s.sigs → i < s.emittedCnt k)
    {k : K} (hh : honest k) (m' : M) :
    (k, s.emittedCnt k, m') ∉ s.sigs :=
  fun hmem => Nat.lt_irrefl _ (hIdx k (s.emittedCnt k) m' hh hmem)

/-- The two invariants hold at every reachable state. -/
theorem reach_inv {s : St K M}
    (h : Reach C D τ honest s) :
    SafeAcc C D s ∧ HonestSig C D honest s := by
  induction h with
  | init =>
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [Zkpc.Core.init, SafeAcc, HonestSig]
  | step hprev hstep ih =>
    obtain ⟨⟨hFresh, hSolv, hAccSig, hSweptAcc⟩, hIdx, hUniq, hClosedU, hNoSlash⟩ := ih
    cases hstep with
    | tick =>
      exact ⟨⟨hFresh, hSolv, hAccSig, hSweptAcc⟩, hIdx, hUniq, hClosedU, hNoSlash⟩
    | openCh k hnew =>
      exact ⟨⟨hFresh, hSolv, hAccSig, hSweptAcc⟩, hIdx, hUniq, hClosedU, hNoSlash⟩
    | emitHonest k m hh hlive hsolv =>
      obtain ⟨hop, hsl, hcl⟩ := hlive
      refine ⟨⟨hFresh, hSolv, ?_, hSweptAcc⟩, ?_, ?_, ?_, hNoSlash⟩
      · -- acc ⊆ sigs: the signal set only grows
        intro k' i' m' hmem
        exact Finset.mem_insert_of_mem (hAccSig k' i' m' hmem)
      · -- spend-signal index bound
        intro k' i' m' hh' hmem
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | hold
        · simp [Function.update_apply]
        · rcases eq_or_ne k' k with rfl | hkk
          · simp only [Function.update_apply, if_pos rfl]
            exact Nat.lt_succ_of_lt (hIdx k' i' m' hh' hold)
          · simpa [Function.update_apply, hkk] using hIdx k' i' m' hh' hold
      · -- per-index uniqueness: the new signal's index is fresh
        intro k' i' m1 m2 hh' h1 h2
        simp only [Finset.mem_insert, Prod.mk.injEq] at h1 h2
        rcases h1 with ⟨rfl, rfl, rfl⟩ | h1old
        · rcases h2 with ⟨-, -, rfl⟩ | h2old
          · rfl
          · exact absurd h2old (no_sig_at_counter hIdx hh' m2)
        · rcases h2 with ⟨rfl, hi2, rfl⟩ | h2old
          · exact absurd (hi2 ▸ h1old) (no_sig_at_counter hIdx hh' m1)
          · exact hUniq k' i' m1 m2 hh' h1old h2old
      · -- close-set clause: the counter only moves while unclosed
        intro k' U t hh' hct
        rcases eq_or_ne k' k with rfl | hkk
        · rw [hcl] at hct
          simp at hct
        · simpa [Function.update_apply, hkk] using hClosedU k' U t hh' hct
    | emitAdv k i m hadv =>
      refine ⟨⟨hFresh, hSolv, ?_, hSweptAcc⟩, ?_, ?_, hClosedU, hNoSlash⟩
      · intro k' i' m' hmem
        exact Finset.mem_insert_of_mem (hAccSig k' i' m' hmem)
      · intro k' i' m' hh' hmem
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | hold
        · exact absurd hh' hadv
        · exact hIdx k' i' m' hh' hold
      · intro k' i' m1 m2 hh' h1 h2
        simp only [Finset.mem_insert, Prod.mk.injEq] at h1 h2
        rcases h1 with ⟨rfl, rfl, rfl⟩ | h1old
        · exact absurd hh' hadv
        · rcases h2 with ⟨rfl, rfl, rfl⟩ | h2old
          · exact absurd hh' hadv
          · exact hUniq k' i' m1 m2 hh' h1old h2old
    | accept k i m hsig hlive hsolv hfresh =>
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hIdx, hUniq, hClosedU, hNoSlash⟩
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
      · intro k' i' m' hmem
        simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | hold
        · exact hsig
        · exact hAccSig k' i' m' hold
      · intro p hp
        obtain ⟨m', hm'⟩ := hSweptAcc p hp
        exact ⟨m', Finset.mem_insert_of_mem hm'⟩
    | slash k i m m' h1 h2 hne hopen hns =>
      refine ⟨⟨hFresh, hSolv, hAccSig, hSweptAcc⟩, hIdx, hUniq, hClosedU, ?_⟩
      intro k' hh'
      rcases eq_or_ne k' k with rfl | hkk
      · exact absurd (hUniq k' i m m' hh' h1 h2) hne
      · simpa [Function.update_apply, hkk] using hNoSlash k' hh'
    | payerClose k U hlive hUlt hUeq =>
      refine ⟨⟨hFresh, hSolv, hAccSig, hSweptAcc⟩, hIdx, hUniq, ?_, hNoSlash⟩
      intro k' U' t hh' hct
      rcases eq_or_ne k' k with rfl | hkk
      · simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hct
        obtain ⟨rfl, -⟩ := hct
        exact hUeq hh'
      · simp only [Function.update_apply, if_neg hkk] at hct
        exact hClosedU k' U' t hh' hct
    | closeDispute k i m U t hc hiU hacc hwin hnotYet =>
      refine ⟨⟨hFresh, hSolv, hAccSig, hSweptAcc⟩, hIdx, hUniq, hClosedU, ?_⟩
      intro k' hh'
      rcases eq_or_ne k' k with rfl | hkk
      · -- an honest closer's claimed-unused indices were never accepted:
        -- the accepted index is below the counter, the claimed set above it
        exfalso
        have h1 := hIdx k' i m hh' (hAccSig k' i m hacc)
        have hU := hClosedU k' U t hh' hc
        subst hU
        have h2 := (Finset.mem_filter.mp hiU).2
        omega
      · simpa [Function.update_apply, hkk] using hNoSlash k' hh'
    | settleClose k U t hc hexp hns hswbar hnotYet =>
      exact ⟨⟨hFresh, hSolv, hAccSig, hSweptAcc⟩, hIdx, hUniq, hClosedU, hNoSlash⟩
    | sweepOne k i m hacc hdedup hwin hbar =>
      refine ⟨⟨hFresh, hSolv, hAccSig, ?_⟩, hIdx, hUniq, hClosedU, hNoSlash⟩
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact ⟨m, hacc⟩
      · exact hSweptAcc p hp'
    | settleVoid k U t hc hexp hns hnotYet hover =>
      refine ⟨⟨hFresh, hSolv, hAccSig, hSweptAcc⟩, hIdx, hUniq, hClosedU, ?_⟩
      intro k' hh'
      rcases eq_or_ne k' k with rfl | hkk
      · -- an honest closer's claimed-unused set never overlaps the swept
        -- nullifiers: swept ⇒ accepted ⇒ emitted ⇒ below the counter,
        -- while an honest U sits at or above it (rev-8 two-sided bar)
        exfalso
        obtain ⟨i, hiU, hisw⟩ := hover
        obtain ⟨m, hm⟩ := hSweptAcc (k', i) hisw
        have h1 := hIdx k' i m hh' (hAccSig k' i m hm)
        have hU := hClosedU k' U t hh' hc
        subst hU
        have h2 := (Finset.mem_filter.mp hiU).2
        omega
      · simpa [Function.update_apply, hkk] using hNoSlash k' hh'

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
    (h : Reach C D τ honest s) (k : K) :
    s.valueOf k C ≤ D := by
  rcases Nat.eq_zero_or_pos C with hC | hC
  · simp [St.valueOf, hC]
  obtain ⟨⟨hFresh, hSolv, -, -⟩, -⟩ := reach_inv h
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
slashed, in any reachable state, against any adversary — by `Dispute`,
because it emits at most one signal per index so the conflicting pair
cannot exist; and by `closeDispute`, because its claimed-unused set never
meets its accepted indices (see `honest_close_undisputable`). Under MC20
the close emits no signal at all, so closing opens no evidence surface.
The probabilistic complement (an adversary cannot *mint* a second point on
an honest line) is T7 in the game layer. -/
theorem honest_never_slashed {s : St K M}
    (h : Reach C D τ honest s) (k : K) (hk : honest k) :
    s.slashedAt k = none :=
  (reach_inv h).2.2.2.2 k hk

/-- An honest payer's recorded close claims only genuinely-unused indices:
everything in its claimed set `U` is at or above its emission counter
(the coordinate-wise form of `HonestSig`'s close-set clause; the facet the
MC20 exculpability argument uses). -/
theorem honest_close_claims_unused {s : St K M}
    (h : Reach C D τ honest s) (k : K) (hk : honest k)
    {U : Finset ℕ} {t : ℕ} (hc : s.closedAt k = some (U, t)) :
    ∀ i ∈ U, s.emittedCnt k ≤ i := by
  intro i hiU
  have hU := (reach_inv h).2.2.2.1 k U t hk hc
  subst hU
  exact (Finset.mem_filter.mp hiU).2

/-- **MC20 exculpability facet (Spec.md §7 T5 "an honest closer's window
allows no valid dispute"; §2 Close A honest-closer protection).** No
accepted ticket of an honest payer bit-matches its claimed-unused set:
for honest `k` with recorded close `(U, t)` and any `i ∈ U`, no
`(k, i, m)` is in the accepted set — so the `closeDispute` action is
never enabled against an honest closer. Symbolic content: accepted
indices sit strictly below the emission counter (`acc ⊆ sigs` + the
index bound), while an honest `U` sits at or above it. -/
theorem honest_close_undisputable {s : St K M}
    (h : Reach C D τ honest s) (k : K) (hk : honest k)
    {U : Finset ℕ} {t i : ℕ} {m : M}
    (hc : s.closedAt k = some (U, t)) (hiU : i ∈ U) :
    (k, i, m) ∉ s.acc := by
  intro hacc
  obtain ⟨⟨-, -, hAccSig, -⟩, hIdx, -, -, -⟩ := reach_inv h
  have h1 : i < s.emittedCnt k := hIdx k i m hk (hAccSig k i m hacc)
  have h2 : s.emittedCnt k ≤ i := honest_close_claims_unused h k hk hc i hiU
  omega

/-- **Rev-8 two-sided bar, honest side (Spec.md §2 Close A, rev-7 F7-2).**
An honest closer's claimed-unused set never overlaps the swept
nullifiers, so the settlement-time bar check always passes for it and the
`settleVoid` branch never fires: a swept nullifier traces to an accepted
ticket (`SafeAcc`), no accepted ticket of an honest payer sits in its
claimed set (`honest_close_undisputable`). The honest settlement path of
T3/T5 is therefore undisturbed by the void branch. -/
theorem honest_settleVoid_never {s : St K M}
    (h : Reach C D τ honest s) (k : K) (hk : honest k)
    {U : Finset ℕ} {t : ℕ} (hc : s.closedAt k = some (U, t)) :
    ∀ i ∈ U, (k, i) ∉ s.swept := by
  intro i hiU hsw
  obtain ⟨⟨-, -, -, hSweptAcc⟩, -⟩ := reach_inv h
  obtain ⟨m, hm⟩ := hSweptAcc (k, i) hsw
  exact honest_close_undisputable h k hk hc hiU hm

end Zkpc.Core
