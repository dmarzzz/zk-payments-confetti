import Zkpc.Fleet.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring

/-!
# T6 — Priced divergence (task G2; Spec.md §7 T6, fleet, instantiation A)

`T6_priced_divergence` is Spec.md §7 T6 clause (i) on the fleet machine of
`Zkpc.Fleet.Basic`: over every execution whose honest infrastructure meets
the reconciliation guarantee (`FleetFair`, the MC11/MC17 hypothesis), the
total value of accepted tickets attributed to the corrupted member is at
most

  `⌊D/C⌋·C + f(L)`  with  `f(L) = N·b·(⌈L/T_e⌉ + 1)·C`.

`T6_slash_within_L` is clause (ii): a member with two conflicting accepted
signals is slashed — fleet-wide — within `L` of the second acceptance.

GATE-NOTE (ticket-count form needs `0 < C`): Spec.md states T6 over
*value*, and `T6_priced_divergence` proves exactly that, for every `C`
(at `C = 0` the value bound is trivially true). The sharper *count* form
`T6_accept_count` (`#accepts ≤ ⌊D/C⌋ + N·b·(⌈L/T_e⌉+1)`), which the value
form is derived from, requires `0 < C`: with `C = 0` the solvency conjunct
`(i+1)·C ≤ D` holds for every index, so a zero-price fleet accepts
unboundedly many distinct-index tickets without any conflict and the count
bound is false (counterexample: `C = 0`, accept indices
`0, 1, …, ⌊D/0⌋ + N·b·(⌈L/T_e⌉+1)` at one gateway across enough epochs —
every guard passes, no pair conflicts, no slash is ever due). A flat
*price* is positive; the spec's value statement never notices.

GATE-NOTE (`0 < T_e` hypothesis): both theorems assume the epoch length is
positive. Spec.md treats `T_e` as a wall-clock duration (§1), so this is
implicit there; it is load-bearing here because `⌈L/T_e⌉` and the epoch
map `t ↦ t / T_e` are meaningless at `T_e = 0`.

No other hypotheses are added and none of Spec.md's are dropped: the
adversary schedules everything (`tick`/`accept`/`slash` interleaving is
unconstrained), chooses gateways, indices, messages, and timing, and the
only things it cannot do are forge proofs (knowledge soundness, absorbed
symbolically — see `Zkpc.Fleet.Basic`) and delay honest reconciliation
(`FleetFair`, a model guarantee per Spec.md §6).

## Proof shape (Spec.md §7 T6 "Why the bound has this shape", followed exactly)

All value beyond the solvency entitlement comes from conflicting
acceptances: within one gateway an index is never accepted twice
(check 6), and across gateways a reused index conflicts by MC14. So

- accepts strictly before `t₀` — the completion time of the earliest
  conflicting pair — have pairwise-distinct indices, each solvent, hence
  number at most `⌊D/C⌋` (`card_le_solvency_of_conflictFree`);
- from `t₀`, `FleetFair` lands an effective slash by `t₀ + L`, and no
  acceptance postdates the slash, so every remaining accept sits in the
  window `[t₀, t₀ + L]`; the member's epoch pseudonym counters cap that
  window at `b` per gateway per epoch, the window meets at most
  `⌈L/T_e⌉ + 1` epochs (`epochs_in_window`), and there are `N` gateways —
  at most `N·b·(⌈L/T_e⌉ + 1)` accepts (`card_le_rate_window`).
-/

namespace Zkpc.Fleet

open Finset

variable {N : ℕ} {P : Type} [DecidableEq P]

omit [DecidableEq P] in
/-- Counting lemma, solvency part (Spec.md §7 T6 proof shape, first half):
any conflict-free subset of the accepted log has pairwise-distinct spend
indices — within a gateway by check-6 freshness, across gateways because a
shared index with gateway-bound messages (MC14) would *be* a conflict —
and each accepted index satisfies `(i+1)·C ≤ D`, so the subset has at most
`⌊D/C⌋` elements. This is the fleet form of T1's counting argument. -/
theorem card_le_solvency_of_conflictFree {C D b Te : ℕ} {s : FSt N P}
    (hC : 0 < C) (inv : Inv C D b Te s)
    {A : Finset (Ev N P)} (hA : A ⊆ s.log)
    (hcf : ∀ e₁ ∈ A, ∀ e₂ ∈ A, ¬ Conflict e₁ e₂) :
    A.card ≤ D / C := by
  have hinj : Set.InjOn Ev.idx (A : Set (Ev N P)) := by
    intro e₁ h₁ e₂ h₂ hidx
    simp only [Finset.mem_coe] at h₁ h₂
    by_cases hgw : e₁.gw = e₂.gw
    · exact inv.idx_uniq e₁ (hA h₁) e₂ (hA h₂) hgw hidx
    · exact absurd ⟨hidx, fun hmsg => hgw (by
        rw [← inv.gw_bound e₁ (hA h₁), ← inv.gw_bound e₂ (hA h₂), hmsg])⟩
        (hcf e₁ h₁ e₂ h₂)
  have hsub : A.image Ev.idx ⊆ Finset.range (D / C) := by
    intro i hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    have hsolv := inv.solvent e (hA he)
    have h1 : e.idx + 1 ≤ D / C := (Nat.le_div_iff_mul_le hC).mpr hsolv
    rw [Finset.mem_range]
    omega
  calc A.card = (A.image Ev.idx).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (D / C)).card := Finset.card_le_card hsub
    _ = D / C := Finset.card_range _

omit [DecidableEq P] in
/-- Counting lemma, rate part (Spec.md §7 T6 proof shape, second half):
any subset of the accepted log whose timestamps sit in a window
`[t₀, t₀ + L]` has at most `N·b·(⌈L/T_e⌉ + 1)` elements — fiber the subset
over `(gateway, epoch)`: the budget invariant caps each fiber at `b`
(check 5 counts accepts of the member's epoch pseudonym, identical at
every gateway, MC3), and the window meets at most `⌈L/T_e⌉ + 1` epochs
(`epochs_in_window`) at each of the `N` gateways. -/
theorem card_le_rate_window {C D b Te : ℕ} (hTe : 0 < Te) {s : FSt N P}
    (inv : Inv C D b Te s)
    {A : Finset (Ev N P)} (hA : A ⊆ s.log) (t₀ L : ℕ)
    (hlo : ∀ e ∈ A, t₀ ≤ e.time) (hhi : ∀ e ∈ A, e.time ≤ t₀ + L) :
    A.card ≤ N * b * (ceilDiv L Te + 1) := by
  set T : Finset (Fin N × ℕ) :=
    (Finset.univ : Finset (Fin N)) ×ˢ Finset.Icc (t₀ / Te) ((t₀ + L) / Te)
    with hT
  have hmaps : ∀ e ∈ A, (e.gw, e.time / Te) ∈ T := by
    intro e he
    rw [hT, Finset.mem_product]
    exact ⟨Finset.mem_univ _, Finset.mem_Icc.mpr
      ⟨Nat.div_le_div_right (hlo e he), Nat.div_le_div_right (hhi e he)⟩⟩
  have hfib : ∀ p ∈ T, (A.filter fun e => (e.gw, e.time / Te) = p).card ≤ b := by
    intro p _
    have hsubf : (A.filter fun e => (e.gw, e.time / Te) = p) ⊆
        s.log.filter fun e => e.gw = p.1 ∧ e.time / Te = p.2 := by
      intro e he
      obtain ⟨heA, hep⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr
        ⟨hA heA, congrArg Prod.fst hep, congrArg Prod.snd hep⟩
    exact le_trans (Finset.card_le_card hsubf) (inv.rate_le p.1 p.2)
  have hTcard : T.card ≤ N * (ceilDiv L Te + 1) := by
    rw [hT, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul (Nat.le_refl N) (epochs_in_window hTe t₀ L)
  calc A.card
      = ∑ p ∈ T, (A.filter fun e => (e.gw, e.time / Te) = p).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ T.card • b := Finset.sum_le_card_nsmul T _ b hfib
    _ = T.card * b := nsmul_eq_mul _ _
    _ ≤ (N * (ceilDiv L Te + 1)) * b := Nat.mul_le_mul hTcard (Nat.le_refl b)
    _ = N * b * (ceilDiv L Te + 1) := by ring

/-- **T6, ticket-count form** (Spec.md §7 T6 clause (i), counting accepts
rather than value; see the file GATE-NOTE for why this form carries
`0 < C`). For every reachable state of the fleet machine — the adversary
controlling the member and all scheduling — that satisfies the honest-
infrastructure guarantee `FleetFair L`: the total number of accepted
tickets over the entire execution is at most

  `⌊D/C⌋ + N·b·(⌈L/T_e⌉ + 1)`.

(`s.log.card` is exactly the number of `accept` actions of the execution,
by `FStep.log_growth`.) -/
theorem T6_accept_count {C D b Te L : ℕ} {s : FSt N P}
    (h : FReach C D b Te s) (hC : 0 < C) (hTe : 0 < Te)
    (hff : FleetFair L s) :
    s.log.card ≤ D / C + N * b * (ceilDiv L Te + 1) := by
  have inv := fleet_inv h
  by_cases hconf : ∃ e₁ ∈ s.log, ∃ e₂ ∈ s.log, Conflict e₁ e₂
  case neg =>
    -- No conflicting pair ever: every accept is inside the solvency
    -- entitlement (the L = 0 / T1 situation).
    have h1 : s.log.card ≤ D / C := by
      refine card_le_solvency_of_conflictFree hC inv subset_rfl ?_
      intro e₁ h₁ e₂ h₂ hc
      exact hconf ⟨e₁, h₁, e₂, h₂, hc⟩
    omega
  case pos =>
    -- The set of conflict completion times, and t₀ its minimum: the time
    -- at which the first conflicting pair became complete.
    set CT : Finset ℕ :=
      ((s.log ×ˢ s.log).filter fun p => Conflict p.1 p.2).image
        fun p => max p.1.time p.2.time with hCT
    have hCTne : CT.Nonempty := by
      obtain ⟨e₁, h₁, e₂, h₂, hc⟩ := hconf
      exact ⟨max e₁.time e₂.time, Finset.mem_image.mpr
        ⟨(e₁, e₂), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨h₁, h₂⟩, hc⟩, rfl⟩⟩
    set t₀ := CT.min' hCTne with ht₀
    -- t₀ is realized by an actual conflicting pair q.
    obtain ⟨q, hq, hqt⟩ := Finset.mem_image.mp (CT.min'_mem hCTne)
    obtain ⟨hqmem, hqc⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqmem
    -- Every acceptance of the whole execution happened by t₀ + L: either
    -- the clock never passed the deadline, or FleetFair produced an
    -- effective slash by t₀ + L and no acceptance postdates a slash.
    have hub : ∀ e ∈ s.log, e.time ≤ t₀ + L := by
      intro e he
      by_cases hclk : s.clock ≤ t₀ + L
      · exact le_trans (inv.time_le_clock e he) hclk
      · obtain ⟨ts, hsl, hts⟩ := hff q.1 hq1 q.2 hq2 hqc (by omega)
        have := inv.time_le_slash e he ts hsl
        omega
    -- Accepts strictly before t₀ are conflict-free (t₀ is the *first*
    -- conflict completion time).
    have hpre : ∀ e₁ ∈ s.log.filter (fun e => e.time < t₀),
        ∀ e₂ ∈ s.log.filter (fun e => e.time < t₀), ¬ Conflict e₁ e₂ := by
      intro e₁ h₁ e₂ h₂ hc
      obtain ⟨h₁l, h₁t⟩ := Finset.mem_filter.mp h₁
      obtain ⟨h₂l, h₂t⟩ := Finset.mem_filter.mp h₂
      have hmem : max e₁.time e₂.time ∈ CT := Finset.mem_image.mpr
        ⟨(e₁, e₂), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨h₁l, h₂l⟩, hc⟩, rfl⟩
      have := CT.min'_le _ hmem
      omega
    have h1 : (s.log.filter fun e => e.time < t₀).card ≤ D / C :=
      card_le_solvency_of_conflictFree hC inv (Finset.filter_subset _ _) hpre
    have h2 : (s.log.filter fun e => ¬ e.time < t₀).card ≤
        N * b * (ceilDiv L Te + 1) := by
      refine card_le_rate_window hTe inv (Finset.filter_subset _ _) t₀ L ?_ ?_
      · intro e he
        have := (Finset.mem_filter.mp he).2
        omega
      · intro e he
        exact hub e (Finset.mem_filter.mp he).1
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := s.log) (p := fun e => e.time < t₀)
    omega

/-- **T6 — Priced divergence, clause (i)** (Spec.md §7 T6, fleet,
instantiation A). For every execution of the `N`-gateway fleet machine —
one corrupted member with secret `k` and deposit `D`, adversarial choice
of gateways, indices, messages, and timing — satisfying the honest-fleet
reconciliation guarantee (`FleetFair L`: MC11 end-to-end lag + MC17
merge-time evidence, a guarantee of honest infrastructure per §6), and
positive epoch length: the total value of accepted tickets attributed to
`k` over the entire execution is at most

  `⌊D/C⌋·C + f(L)`,  `f(L) = N·b·(⌈L/T_e⌉ + 1)·C`,

i.e. the solvency entitlement plus one lag-window's worth of rate-limited
divergence. The deployment condition `f(L) < D` (bounding the burst by one
deposit) and the remainder-capped recovery discussion are Spec.md-level
consequences of this bound and of clause (ii) (`T6_slash_within_L`); this
theorem claims neither attacker unprofitability nor universal recovery,
per the spec's own scoping. -/
theorem T6_priced_divergence {C D b Te L : ℕ} {s : FSt N P}
    (h : FReach C D b Te s) (hTe : 0 < Te) (hff : FleetFair L s) :
    s.acceptedValue C ≤ D / C * C + N * b * (ceilDiv L Te + 1) * C := by
  rcases Nat.eq_zero_or_pos C with hC | hC
  · simp [FSt.acceptedValue, hC]
  · have hcount := T6_accept_count h hC hTe hff
    calc s.acceptedValue C = C * s.log.card := rfl
      _ ≤ C * (D / C + N * b * (ceilDiv L Te + 1)) :=
          Nat.mul_le_mul (Nat.le_refl C) hcount
      _ = D / C * C + N * b * (ceilDiv L Te + 1) * C := by ring

omit [DecidableEq P] in
/-- **T6 — slash clause (ii)** (Spec.md §7 T6): if two conflicting signals
(same nullifier/index, different messages) are both accepted by honest
gateways, the member is slashed — evicted fleet-wide, `accept` disabled
everywhere from the slash time on — within `L` of the second acceptance,
in every execution meeting the honest-infrastructure guarantee. Under
`FleetFair` this is quantifier unfolding once the deadline is reached —
deliberately so: the *content* of clause (ii) is the honest fleet's
reconciliation duty (MC11/MC17), which is an assumption of the model, not
a theorem about the adversary; stating it separately keeps that boundary
visible (and `Inv.slash_sound` gives the converse: a slash implies a real
conflicting pair). -/
theorem T6_slash_within_L {L : ℕ} {s : FSt N P}
    (hff : FleetFair L s) {e₁ e₂ : Ev N P}
    (h₁ : e₁ ∈ s.log) (h₂ : e₂ ∈ s.log) (hc : Conflict e₁ e₂)
    (hdue : max e₁.time e₂.time + L ≤ s.clock) :
    ∃ ts, s.slashed = some ts ∧ ts ≤ max e₁.time e₂.time + L :=
  hff e₁ h₁ e₂ h₂ hc hdue

end Zkpc.Fleet
