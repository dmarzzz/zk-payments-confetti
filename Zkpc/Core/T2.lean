import Zkpc.Core.T1

/-!
# T2 — Payee balance security (task D3; Spec.md §7 T2, statement A, N = 1)

Two halves, per Spec.md T2-A:

* **Upper bound (unconditional):** the ledger's `nf`-dedup and per-ticket
  price cap the gateway's settled total — `paidGw = C · |swept|`, every
  swept nullifier traces to an accepted ticket, so
  `paidGw ≤ C · #(distinct accepted nullifiers)`. No payer behavior can
  overpay the payee, and no accepted ticket is ever paid twice.
* **Collectability (the "exactly" direction):** from any reachable state,
  every accepted-but-unswept ticket whose sweep window is still open is
  sweepable *now* (`sweepOne_enabled`), and a finite sequence of sweeps —
  no time passing, no payer cooperation — settles all of them
  (`T2_collectable`). When no window has closed on the payee,
  the result is settlement of exactly `C · |T|` (`T2_settles_exactly`).

GATE-NOTE (deltas between Spec.md T2-A and these statements):
1. *Deadlines.* Spec.md states a deadline `t_done ≥ last sweep + Δ` (+ the
   dispute-window close where a slash intervened). The machine folds the
   ledger's `Δ`-inclusion to instantaneous inclusion at the action's clock
   (State.lean header), so the deadline clause becomes: sweeps are *enabled
   now* and settle *at the action*, with no ticks needed
   (`SweepStar` contains no `tick`). The `Δ` re-enters as prose when
   interpreting machine time, exactly as for T5.
2. *Monitoring duty (MC16).* "Follows the sweep protocol including the
   monitoring duty" is formalized as the `sweepOpen` side condition: a
   ticket of a slashed member is collectable while `clock ≤ slash + τ`.
   The theorems guarantee the sweep is enabled throughout that window;
   sweeping within it is the duty. A ticket whose window the payee let
   expire is *not* covered — that is the content of the duty, not a
   weakening (Spec.md conditions T2 on the duty being followed).
3. *Aggregation.* `paidGw` is the gateway's cumulative revenue and `s.acc`
   is its whole accepted set; at `N = 1` the set `T` of Spec.md is `s.acc`,
   so "exactly `C · |T|`" is stated against `s.acc.card`. No per-payer
   split is needed (and pre-slash, none is possible — nullifiers are
   unattributable by design, Spec.md MC16).
-/

namespace Zkpc.Core

open Finset

variable {K M : Type} [DecidableEq K] [DecidableEq M]
variable {C D τ : ℕ} {honest : K → Prop} {mclose : M}

/-- The sweep window for `k` is open: either `k` was never slashed, or the
gateway-priority dispute window (Spec.md §2 Dispute, MC4/MC16) has not yet
expired. This is exactly the `hwin` guard of `Step.sweepOne`. -/
def sweepOpen (τ : ℕ) (s : St K M) (k : K) : Prop :=
  ∀ ts, s.slashedAt k = some ts → s.clock ≤ ts + τ

instance sweepOpen.decidable (τ : ℕ) (s : St K M) (k : K) :
    Decidable (sweepOpen τ s k) := by
  unfold sweepOpen
  cases h : s.slashedAt k with
  | none => exact isTrue (fun ts hts => nomatch hts)
  | some t0 =>
    by_cases hle : s.clock ≤ t0 + τ
    · exact isTrue (fun ts hts => (Option.some.inj hts) ▸ hle)
    · exact isFalse (fun hall => hle (hall t0 rfl))

/-- T2 safety invariant: the gateway's settled revenue is exactly `C` per
swept nullifier (the ledger pays `C` per fresh `nf`, Spec.md §2 Close), and
every swept nullifier is the nullifier of an accepted ticket (only the
gateway's accepted tuples are sweepable, MC16). -/
def SweepInv (C : ℕ) (s : St K M) : Prop :=
  s.paidGw = C * s.swept.card ∧
  ∀ p ∈ s.swept, ∃ m : M, (p.1, p.2, m) ∈ s.acc

/-- The T2 safety invariant holds at every reachable state. -/
theorem sweep_inv {s : St K M} (h : Reach C D τ honest mclose s) :
    SweepInv C s := by
  induction h with
  | init => exact ⟨by simp [Zkpc.Core.init], by simp [Zkpc.Core.init]⟩
  | step hprev hstep ih =>
    obtain ⟨hpaid, hsub⟩ := ih
    cases hstep with
    | tick => exact ⟨hpaid, hsub⟩
    | openCh k hnew => exact ⟨hpaid, hsub⟩
    | emitHonest k m hh hlive hm hsolv => exact ⟨hpaid, hsub⟩
    | emitAdv k i m hadv => exact ⟨hpaid, hsub⟩
    | accept k i m hsig hm hlive hsolv hfresh =>
      refine ⟨hpaid, fun p hp => ?_⟩
      obtain ⟨m', hm'⟩ := hsub p hp
      exact ⟨m', Finset.mem_insert_of_mem hm'⟩
    | slash k i m m' h1 h2 hne hopen hns => exact ⟨hpaid, hsub⟩
    | payerClose k j hlive hj => exact ⟨hpaid, hsub⟩
    | settleClose k j t hc hexp hns hnotYet => exact ⟨hpaid, hsub⟩
    | sweepOne k i m hacc hdedup hwin =>
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Finset.card_insert_of_notMem hdedup, hpaid, Nat.mul_add,
          Nat.mul_one]
      · rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact ⟨m, hacc⟩
        · exact hsub p hp'

/-- **T2, dedup half (Spec.md §7 T2-A, "exactly ... the upper bound holds
unconditionally").** In every reachable state, the honest payee's settled
sweep revenue is exactly `C` per swept nullifier: `paidGw = C · |swept|`.
Combined with `T2_swept_accepted`, each accepted ticket is paid at most
once — the ledger's `nf`-dedup (MC16). -/
theorem T2_paid_exact {s : St K M} (h : Reach C D τ honest mclose s) :
    s.paidGw = C * s.swept.card :=
  (sweep_inv h).1

/-- **T2, attribution half.** Every swept nullifier `(k, i)` is the
nullifier of some ticket the honest payee actually accepted: sweeps only
ever pay for redeemed tuples (Spec.md §2 Close, MC16 — the sweep verifier
checks the tuple against `R_spend`). -/
theorem T2_swept_accepted {s : St K M} (h : Reach C D τ honest mclose s) :
    ∀ p ∈ s.swept, ∃ m : M, (p.1, p.2, m) ∈ s.acc :=
  (sweep_inv h).2

/-- **T2 upper bound (Spec.md §7 T2-A).** The payee's settled total never
exceeds `C` times the number of *distinct accepted nullifiers*: the payee
is never overpaid, regardless of payer or scheduler behavior. -/
theorem T2_upper {s : St K M} (h : Reach C D τ honest mclose s) :
    s.paidGw ≤ C * (s.acc.image (fun t => (t.1, t.2.1))).card := by
  obtain ⟨hpaid, hsub⟩ := sweep_inv h
  have hss : s.swept ⊆ s.acc.image (fun t => (t.1, t.2.1)) := by
    intro p hp
    obtain ⟨m, hm⟩ := hsub p hp
    exact Finset.mem_image.mpr ⟨(p.1, p.2, m), hm, rfl⟩
  rw [hpaid]
  exact Nat.mul_le_mul (Nat.le_refl C) (Finset.card_le_card hss)

/-- Weaker corollary of `T2_upper`: settled total at most `C · |acc|`. -/
theorem T2_upper' {s : St K M} (h : Reach C D τ honest mclose s) :
    s.paidGw ≤ C * s.acc.card :=
  le_trans (T2_upper h)
    (Nat.mul_le_mul (Nat.le_refl C) Finset.card_image_le)

/-- **T2 enabledness (Spec.md §7 T2-A collectability; MC16 monitoring
duty).** Any accepted, not-yet-swept ticket whose sweep window is still
open — never slashed, or within the post-slash gateway-priority window —
is sweepable *right now*, unilaterally, with no payer cooperation: the
`sweepOne` step is enabled. The honest sweep protocol's monitoring duty
(Spec.md MC16) is precisely "invoke this while `sweepOpen` still holds";
the machine guarantees the sweep is available throughout that window and
pays `C`. -/
theorem sweepOne_enabled (s : St K M) (k : K) (i : ℕ) (m : M)
    (hacc : (k, i, m) ∈ s.acc) (hdedup : (k, i) ∉ s.swept)
    (hwin : sweepOpen τ s k) :
    Step C D τ honest mclose s (.sweepOne k i m)
      { s with swept := insert (k, i) s.swept, paidGw := s.paidGw + C } :=
  Step.sweepOne s k i m hacc hdedup hwin

/-- A finite sequence of `sweepOne` steps and nothing else — the honest
payee's unilateral sweep strategy. No `tick` occurs, so the entire
settlement happens at one machine time (Spec.md T5 payee half: sweeps have
no window). -/
inductive SweepStar (C D τ : ℕ) (honest : K → Prop) (mclose : M) :
    St K M → St K M → Prop
  | refl (s : St K M) : SweepStar C D τ honest mclose s s
  | step {s s₁ s₂ : St K M} {k : K} {i : ℕ} {m : M} :
      Step C D τ honest mclose s (.sweepOne k i m) s₁ →
      SweepStar C D τ honest mclose s₁ s₂ →
      SweepStar C D τ honest mclose s s₂

/-- A sweep sequence starting from a reachable state ends in a reachable
state. -/
theorem SweepStar.reach {s s' : St K M} :
    SweepStar C D τ honest mclose s s' →
    Reach C D τ honest mclose s → Reach C D τ honest mclose s' := by
  intro hs
  induction hs with
  | refl => exact id
  | step hstep _ ih => exact fun h => ih (Reach.step h hstep)

/-- Sweep sequences compose. -/
theorem SweepStar.trans {s₁ s₂ s₃ : St K M} :
    SweepStar C D τ honest mclose s₁ s₂ →
    SweepStar C D τ honest mclose s₂ s₃ →
    SweepStar C D τ honest mclose s₁ s₃ := by
  intro h₁
  induction h₁ with
  | refl => exact id
  | step hstep _ ih => exact fun h₂ => .step hstep (ih h₂)

/-- Frame conditions of a pure sweep sequence: the clock, the accepted set
and the slash record are untouched (sweeping is ledger bookkeeping only),
and the swept set only grows. -/
theorem SweepStar.frame {s s' : St K M}
    (hs : SweepStar C D τ honest mclose s s') :
    s'.clock = s.clock ∧ s'.acc = s.acc ∧ s'.slashedAt = s.slashedAt ∧
      s.swept ⊆ s'.swept := by
  induction hs with
  | refl => exact ⟨rfl, rfl, rfl, Finset.Subset.refl _⟩
  | step hstep _ ih =>
    cases hstep with
    | sweepOne k i m hacc hdedup hwin =>
      obtain ⟨hc, ha, hsl, hw⟩ := ih
      exact ⟨hc, ha, hsl, (Finset.subset_insert _ _).trans hw⟩

/-- Sweep strategy over an explicit finite target set: every targeted
accepted ticket with an open window gets swept by some pure-sweep
sequence. Auxiliary to `T2_collectable`. -/
theorem sweep_targets {s : St K M} (T : Finset (K × ℕ × M))
    (hT : ∀ t ∈ T, t ∈ s.acc ∧ sweepOpen τ s t.1) :
    ∃ s', SweepStar C D τ honest mclose s s' ∧
      ∀ t ∈ T, (t.1, t.2.1) ∈ s'.swept := by
  induction T using Finset.induction_on with
  | empty => exact ⟨s, .refl s, by simp⟩
  | @insert t T' htn ih =>
    obtain ⟨s₁, hstar₁, hcov₁⟩ := ih (fun u hu => hT u (Finset.mem_insert_of_mem hu))
    obtain ⟨ht_acc, ht_open⟩ := hT t (Finset.mem_insert_self _ _)
    obtain ⟨hclock, hacc, hslash, hswept⟩ := SweepStar.frame hstar₁
    obtain ⟨k, i, m⟩ := t
    by_cases hsw : (k, i) ∈ s₁.swept
    · refine ⟨s₁, hstar₁, fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact hsw
      · exact hcov₁ u hu'
    · have ht_acc₁ : (k, i, m) ∈ s₁.acc := by rw [hacc]; exact ht_acc
      have hopen₁ : sweepOpen τ s₁ k := by
        intro ts hts
        rw [hslash] at hts
        rw [hclock]
        exact ht_open ts hts
      have hstep := Step.sweepOne (C := C) (D := D) (τ := τ) (honest := honest)
        (mclose := mclose) s₁ k i m ht_acc₁ hsw hopen₁
      refine ⟨_, hstar₁.trans (.step hstep (.refl _)), fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hcov₁ u hu')

/-- **T2 collectability (Spec.md §7 T2-A, the "exactly" direction as a
strategy theorem).** From any reachable state the honest payee can, by a
finite sequence of unilateral `sweepOne` steps — no ticks, no payer
cooperation, no counterparty transactions — reach a state in which every
currently-sweepable accepted ticket (unswept, window open per `sweepOpen`)
is swept, and its settled revenue is exactly `C` per swept nullifier.
This formalizes "an honest payee that follows the sweep protocol,
including the MC16 monitoring duty, settles what it is owed": the duty is
to sweep before the window closes, and the machine guarantees those sweeps
are enabled and each pays `C` (see GATE-NOTE 1–2 in the file header for
the `Δ`-deadline delta). -/
theorem T2_collectable {s : St K M} (h : Reach C D τ honest mclose s) :
    ∃ s', SweepStar C D τ honest mclose s s' ∧
      Reach C D τ honest mclose s' ∧
      s'.clock = s.clock ∧
      (∀ k i m, (k, i, m) ∈ s.acc → sweepOpen τ s k → (k, i) ∈ s'.swept) ∧
      s'.paidGw = C * s'.swept.card := by
  obtain ⟨s', hstar, hcov⟩ := sweep_targets (s := s)
    (T := s.acc.filter (fun t => sweepOpen τ s t.1))
    (fun t ht => Finset.mem_filter.mp ht)
  have hreach' : Reach C D τ honest mclose s' := hstar.reach h
  refine ⟨s', hstar, hreach', (SweepStar.frame hstar).1, ?_, (sweep_inv hreach').1⟩
  intro k i m hm hopen
  exact hcov (k, i, m) (Finset.mem_filter.mpr ⟨hm, hopen⟩)

/-- **T2 exact settlement (Spec.md §7 T2-A, "settled from the ledger
exactly `C · |T|`").** If no sweep window has closed on the payee — every
accepted ticket's member is unslashed or still inside its dispute window,
i.e. the payee performed its MC16 duty in time — then the sweep strategy
of `T2_collectable` settles exactly `C · |acc|`: one price per accepted
ticket, none missed, none double-paid, regardless of payer behavior. -/
theorem T2_settles_exactly {s : St K M} (h : Reach C D τ honest mclose s)
    (hall : ∀ k i m, (k, i, m) ∈ s.acc → sweepOpen τ s k) :
    ∃ s', SweepStar C D τ honest mclose s s' ∧
      Reach C D τ honest mclose s' ∧
      s'.paidGw = C * s.acc.card := by
  obtain ⟨s', hstar, hreach', hclock, hcov, hpaid⟩ := T2_collectable h
  have hacc' : s'.acc = s.acc := (SweepStar.frame hstar).2.1
  have hswept_eq : s'.swept = s.acc.image (fun t => (t.1, t.2.1)) := by
    apply Finset.Subset.antisymm
    · intro p hp
      obtain ⟨m, hm⟩ := (sweep_inv hreach').2 p hp
      rw [hacc'] at hm
      exact Finset.mem_image.mpr ⟨(p.1, p.2, m), hm, rfl⟩
    · intro p hp
      obtain ⟨t, htmem, htp⟩ := Finset.mem_image.mp hp
      obtain ⟨k, i, m⟩ := t
      subst htp
      exact hcov k i m htmem (hall k i m htmem)
  obtain ⟨⟨hFresh, -⟩, -⟩ := reach_inv h
  have hinj : Set.InjOn (fun t : K × ℕ × M => (t.1, t.2.1)) ↑s.acc := by
    rintro ⟨k1, i1, m1⟩ h1 ⟨k2, i2, m2⟩ h2 heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hmm : m1 = m2 :=
      hFresh k1 i1 m1 m2 (Finset.mem_coe.mp h1) (Finset.mem_coe.mp h2)
    simp [hmm]
  have hcard : (s.acc.image (fun t => (t.1, t.2.1))).card = s.acc.card :=
    Finset.card_image_of_injOn hinj
  exact ⟨s', hstar, hreach', by rw [hpaid, hswept_eq, hcard]⟩

end Zkpc.Core
