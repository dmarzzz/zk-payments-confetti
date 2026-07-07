import Zkpc.Core.T1

/-!
# T2 — Payee balance security (task D3; Spec.md rev-7 §7 T2, statement A, N = 1)

Two halves, per Spec.md T2-A:

* **Upper bound (unconditional):** the ledger's `nf`-dedup and per-ticket
  price cap the gateway's settled total — `paidGw = C · |swept|`, every
  swept nullifier traces to an accepted ticket, so
  `paidGw ≤ C · #(distinct accepted nullifiers)`. No payer behavior can
  overpay the payee, and no accepted ticket is ever paid twice.
* **Collectability (the "exactly" direction):** from any reachable state,
  every accepted-but-unswept ticket whose sweep window is open and which
  is not sweep-barred (MC20) is sweepable *now* (`sweepOne_enabled`), and
  a finite sequence of sweeps — no time passing, no payer cooperation —
  settles all of them (`T2_collectable`). When neither restriction binds,
  the result is settlement of exactly `C · |T|` (`T2_settles_exactly`).

The MC20 layer (rev-7): a settled close bars its claimed-unused
nullifiers from sweeps. For honest payers' tickets the bar **never
binds** (`honest_payer_tickets_never_barred`: an honest close claims only
indices it never used, so no accepted ticket of an honest payer is ever
barred). A ticket of a *dishonest* payer can be barred — exactly when the
payer's false unused-claim went undisputed and settled — and is then
uncollectable **by design**: Spec.md rev-6's loss-bearer decision places
that loss on the gateway whose checkpoint was stale, not on the pool.
The payee's corresponding duty is `false_claim_disputable`: whenever a
false claim exists against its accepted set, the `closeDispute` step is
enabled throughout the close window, and taking it voids the close (so
the bar never forms).

GATE-NOTE (deltas between Spec.md T2-A and these statements):
1. *Deadlines.* Spec.md states a deadline `t_done ≥ last sweep + Δ` (+ the
   dispute-window close where a slash intervened). The machine folds the
   ledger's `Δ`-inclusion to instantaneous inclusion at the action's clock
   (State.lean header), so the deadline clause becomes: sweeps are *enabled
   now* and settle *at the action*, with no ticks needed
   (`SweepStar` contains no `tick`). The `Δ` re-enters as prose when
   interpreting machine time, exactly as for T5.
2. *Monitoring duty (MC16) and checkpoint currency (rev-6).* "Follows the
   sweep protocol" is formalized as two side conditions: `sweepOpen` (the
   post-slash priority window has not expired — sweep within it) and
   `¬ sweepBarred` (no settled false claim covers the nullifier — dispute
   false claims within the close window, via `false_claim_disputable`,
   and the bar never forms). Tickets the payee let either window lapse on
   are *not* covered — that is the content of the duties, not a
   weakening. Spec.md's "given the payee's checkpoints are current"
   proviso is automatic here: `acc` *is* the pre-close checkpoint at
   `N = 1` (State.lean checkpoint note), so checkpoint *staleness* — and
   with it the in-flight/tardy-gateway loss facet — has no content in
   this machine and returns with the fleet model (G1).
3. *Aggregation.* `paidGw` is the gateway's cumulative revenue and `s.acc`
   is its whole accepted set; at `N = 1` the set `T` of Spec.md is `s.acc`,
   so "exactly `C · |T|`" is stated against `s.acc.card`. No per-payer
   split is needed (and pre-slash, none is possible — nullifiers are
   unattributable by design, Spec.md MC16).
-/

namespace Zkpc.Core

open Finset

variable {K M : Type} [DecidableEq K] [DecidableEq M]
variable {C D τ : ℕ} {honest : K → Prop}

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
theorem sweep_inv {s : St K M} (h : Reach C D τ honest s) :
    SweepInv C s := by
  induction h with
  | init => exact ⟨by simp [Zkpc.Core.init], by simp [Zkpc.Core.init]⟩
  | step hprev hstep ih =>
    obtain ⟨hpaid, hsub⟩ := ih
    cases hstep with
    | tick => exact ⟨hpaid, hsub⟩
    | openCh k hnew => exact ⟨hpaid, hsub⟩
    | emitHonest k m hh hlive hsolv => exact ⟨hpaid, hsub⟩
    | emitAdv k i m hadv => exact ⟨hpaid, hsub⟩
    | accept k i m hsig hlive hsolv hfresh =>
      refine ⟨hpaid, fun p hp => ?_⟩
      obtain ⟨m', hm'⟩ := hsub p hp
      exact ⟨m', Finset.mem_insert_of_mem hm'⟩
    | slash k i m m' h1 h2 hne hopen hns => exact ⟨hpaid, hsub⟩
    | payerClose k U hlive hUlt hUeq => exact ⟨hpaid, hsub⟩
    | closeDispute k i m U t hc hiU hacc hwin hnotYet => exact ⟨hpaid, hsub⟩
    | settleClose k U t hc hexp hns hswbar hnotYet => exact ⟨hpaid, hsub⟩
    | settleVoid k U t hc hexp hns hnotYet hover => exact ⟨hpaid, hsub⟩
    | sweepOne k i m hacc hdedup hwin hbar =>
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
theorem T2_paid_exact {s : St K M} (h : Reach C D τ honest s) :
    s.paidGw = C * s.swept.card :=
  (sweep_inv h).1

/-- **T2, attribution half.** Every swept nullifier `(k, i)` is the
nullifier of some ticket the honest payee actually accepted: sweeps only
ever pay for redeemed tuples (Spec.md §2 Close, MC16 — the sweep verifier
checks the tuple against `R_spend`). -/
theorem T2_swept_accepted {s : St K M} (h : Reach C D τ honest s) :
    ∀ p ∈ s.swept, ∃ m : M, (p.1, p.2, m) ∈ s.acc :=
  (sweep_inv h).2

/-- **T2 upper bound (Spec.md §7 T2-A).** The payee's settled total never
exceeds `C` times the number of *distinct accepted nullifiers*: the payee
is never overpaid, regardless of payer or scheduler behavior. -/
theorem T2_upper {s : St K M} (h : Reach C D τ honest s) :
    s.paidGw ≤ C * (s.acc.image (fun t => (t.1, t.2.1))).card := by
  obtain ⟨hpaid, hsub⟩ := sweep_inv h
  have hss : s.swept ⊆ s.acc.image (fun t => (t.1, t.2.1)) := by
    intro p hp
    obtain ⟨m, hm⟩ := hsub p hp
    exact Finset.mem_image.mpr ⟨(p.1, p.2, m), hm, rfl⟩
  rw [hpaid]
  exact Nat.mul_le_mul (Nat.le_refl C) (Finset.card_le_card hss)

/-- Weaker corollary of `T2_upper`: settled total at most `C · |acc|`. -/
theorem T2_upper' {s : St K M} (h : Reach C D τ honest s) :
    s.paidGw ≤ C * s.acc.card :=
  le_trans (T2_upper h)
    (Nat.mul_le_mul (Nat.le_refl C) Finset.card_image_le)

/-- **T2 enabledness (Spec.md §7 T2-A collectability; MC16 monitoring
duty + MC20 sweep bar).** Any accepted, not-yet-swept ticket whose sweep
window is still open and whose nullifier is not barred by a settled close
is sweepable *right now*, unilaterally, with no payer cooperation: the
`sweepOne` step is enabled. The honest sweep protocol's duties (Spec.md
MC16, rev-6) are precisely "invoke this while `sweepOpen` still holds"
and "keep the bar from forming via `false_claim_disputable`"; the machine
guarantees the sweep is available while both hold and pays `C`. -/
theorem sweepOne_enabled (s : St K M) (k : K) (i : ℕ) (m : M)
    (hacc : (k, i, m) ∈ s.acc) (hdedup : (k, i) ∉ s.swept)
    (hwin : sweepOpen τ s k) (hbar : ¬ s.sweepBarred k i) :
    Step C D τ honest s (.sweepOne k i m)
      { s with swept := insert (k, i) s.swept, paidGw := s.paidGw + C } :=
  Step.sweepOne s k i m hacc hdedup hwin hbar

/-- **T2 payee duty at a payer close (Spec.md §2 Close A, window branch
(a); MC20).** Whenever a close's claimed-unused set contains an index the
gateway actually accepted — a false unused-claim — the `closeDispute`
step is enabled throughout the close window: the gateway can always void
the false close (slashing the claimant) before it settles, so the sweep
bar never forms over its accepted tickets. At `N = 1`, `acc` is the
pre-close checkpoint (State.lean checkpoint note), so no currency proviso
is needed. -/
theorem false_claim_disputable (s : St K M) (k : K) {U : Finset ℕ}
    {t i : ℕ} (m : M)
    (hc : s.closedAt k = some (U, t)) (hiU : i ∈ U)
    (hacc : (k, i, m) ∈ s.acc) (hwin : s.clock ≤ t + τ)
    (hnotYet : s.closeSettled k = false) :
    Step C D τ honest s (.closeDispute k i m)
      { s with slashedAt := Function.update s.slashedAt k (some s.clock) } :=
  Step.closeDispute s k i m U t hc hiU hacc hwin hnotYet

/-- **The MC20 bar never binds against honest payers (Spec.md §2 Close A:
sweeps of tickets accepted before a payer-close remain payable after
it).** An accepted ticket of an *honest* payer is never sweep-barred: an
honest close claims only indices it never used
(`honest_close_claims_unused`), and every accepted index was used. Barred
tickets exist only for dishonest payers whose false claims settled
undisputed — the rev-6 loss-bearer decision (see the file header). -/
theorem honest_payer_tickets_never_barred {s : St K M}
    (h : Reach C D τ honest s) (k : K) (hk : honest k)
    {i : ℕ} {m : M} (hacc : (k, i, m) ∈ s.acc) :
    ¬ s.sweepBarred k i := by
  rintro ⟨U, t, hc, -, hiU⟩
  exact honest_close_undisputable h k hk hc hiU hacc

/-- A finite sequence of `sweepOne` steps and nothing else — the honest
payee's unilateral sweep strategy. No `tick` occurs, so the entire
settlement happens at one machine time (Spec.md T5 payee half: sweeps have
no window). -/
inductive SweepStar (C D τ : ℕ) (honest : K → Prop) :
    St K M → St K M → Prop
  | refl (s : St K M) : SweepStar C D τ honest s s
  | step {s s₁ s₂ : St K M} {k : K} {i : ℕ} {m : M} :
      Step C D τ honest s (.sweepOne k i m) s₁ →
      SweepStar C D τ honest s₁ s₂ →
      SweepStar C D τ honest s s₂

/-- A sweep sequence starting from a reachable state ends in a reachable
state. -/
theorem SweepStar.reach {s s' : St K M} :
    SweepStar C D τ honest s s' →
    Reach C D τ honest s → Reach C D τ honest s' := by
  intro hs
  induction hs with
  | refl => exact id
  | step hstep _ ih => exact fun h => ih (Reach.step h hstep)

/-- Sweep sequences compose. -/
theorem SweepStar.trans {s₁ s₂ s₃ : St K M} :
    SweepStar C D τ honest s₁ s₂ →
    SweepStar C D τ honest s₂ s₃ →
    SweepStar C D τ honest s₁ s₃ := by
  intro h₁
  induction h₁ with
  | refl => exact id
  | step hstep _ ih => exact fun h₂ => .step hstep (ih h₂)

/-- Frame conditions of a pure sweep sequence: the clock, the accepted
set, the slash record, the close records and the settlement flags are
untouched (sweeping is ledger bookkeeping only), and the swept set only
grows. -/
theorem SweepStar.frame {s s' : St K M}
    (hs : SweepStar C D τ honest s s') :
    s'.clock = s.clock ∧ s'.acc = s.acc ∧ s'.slashedAt = s.slashedAt ∧
      s'.closedAt = s.closedAt ∧ s'.closeSettled = s.closeSettled ∧
      s.swept ⊆ s'.swept := by
  induction hs with
  | refl => exact ⟨rfl, rfl, rfl, rfl, rfl, Finset.Subset.refl _⟩
  | step hstep _ ih =>
    cases hstep with
    | sweepOne k i m hacc hdedup hwin hbar =>
      obtain ⟨hc, ha, hsl, hcl, hcs, hw⟩ := ih
      exact ⟨hc, ha, hsl, hcl, hcs, (Finset.subset_insert _ _).trans hw⟩

/-- Sweep strategy over an explicit finite target set: every targeted
accepted ticket with an open window and no bar gets swept by some
pure-sweep sequence. Auxiliary to `T2_collectable`. -/
theorem sweep_targets {s : St K M} (T : Finset (K × ℕ × M))
    (hT : ∀ t ∈ T, t ∈ s.acc ∧ sweepOpen τ s t.1 ∧ ¬ s.sweepBarred t.1 t.2.1) :
    ∃ s', SweepStar C D τ honest s s' ∧
      ∀ t ∈ T, (t.1, t.2.1) ∈ s'.swept := by
  induction T using Finset.induction_on with
  | empty => exact ⟨s, .refl s, by simp⟩
  | @insert t T' htn ih =>
    obtain ⟨s₁, hstar₁, hcov₁⟩ := ih (fun u hu => hT u (Finset.mem_insert_of_mem hu))
    obtain ⟨ht_acc, ht_open, ht_bar⟩ := hT t (Finset.mem_insert_self _ _)
    obtain ⟨hclock, hacc, hslash, hclosed, hsettled, hswept⟩ :=
      SweepStar.frame hstar₁
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
      have hbar₁ : ¬ s₁.sweepBarred k i := by
        rintro ⟨U, t', hcU, hset, hiU⟩
        rw [hclosed] at hcU
        rw [hsettled] at hset
        exact ht_bar ⟨U, t', hcU, hset, hiU⟩
      have hstep := Step.sweepOne (C := C) (D := D) (τ := τ) (honest := honest)
        s₁ k i m ht_acc₁ hsw hopen₁ hbar₁
      refine ⟨_, hstar₁.trans (.step hstep (.refl _)), fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hcov₁ u hu')

/-- **T2 collectability (Spec.md §7 T2-A, the "exactly" direction as a
strategy theorem).** From any reachable state the honest payee can, by a
finite sequence of unilateral `sweepOne` steps — no ticks, no payer
cooperation, no counterparty transactions — reach a state in which every
currently-sweepable accepted ticket (unswept, window open per `sweepOpen`,
not sweep-barred per MC20) is swept, and its settled revenue is exactly
`C` per swept nullifier. This formalizes "an honest payee that follows
the sweep protocol — MC16 monitoring, rev-6 close-window disputing —
settles what it is owed": the duties are to sweep before windows close
and to dispute false claims before they settle
(`false_claim_disputable`), and the machine guarantees the sweeps stay
enabled while the duties are met, each paying `C`. For honest payers'
tickets the bar condition is vacuous (`honest_payer_tickets_never_barred`);
barred tickets of dishonest payers are uncollectable by design (the
loss-bearer decision — file header). See GATE-NOTE 1–2 for the
`Δ`-deadline and checkpoint deltas. -/
theorem T2_collectable {s : St K M} (h : Reach C D τ honest s) :
    ∃ s', SweepStar C D τ honest s s' ∧
      Reach C D τ honest s' ∧
      s'.clock = s.clock ∧
      (∀ k i m, (k, i, m) ∈ s.acc → sweepOpen τ s k → ¬ s.sweepBarred k i →
        (k, i) ∈ s'.swept) ∧
      s'.paidGw = C * s'.swept.card := by
  obtain ⟨s', hstar, hcov⟩ := sweep_targets (s := s)
    (T := s.acc.filter (fun t => sweepOpen τ s t.1 ∧ ¬ s.sweepBarred t.1 t.2.1))
    (fun t ht => by
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp ht
      exact ⟨h1, h2, h3⟩)
  have hreach' : Reach C D τ honest s' := hstar.reach h
  refine ⟨s', hstar, hreach', (SweepStar.frame hstar).1, ?_, (sweep_inv hreach').1⟩
  intro k i m hm hopen hbar
  exact hcov (k, i, m) (Finset.mem_filter.mpr ⟨hm, hopen, hbar⟩)

/-- **T2 exact settlement (Spec.md §7 T2-A, "settled from the ledger
exactly `C · |T|`").** If neither restriction binds on any accepted
ticket — every member is unslashed or inside its dispute window, and no
settled false claim covers an accepted nullifier (both automatic when the
payee performed its MC16/rev-6 duties in time, and the bar side automatic
outright for honest payers) — then the sweep strategy of `T2_collectable`
settles exactly `C · |acc|`: one price per accepted ticket, none missed,
none double-paid, regardless of payer behavior. -/
theorem T2_settles_exactly {s : St K M} (h : Reach C D τ honest s)
    (hall : ∀ k i m, (k, i, m) ∈ s.acc →
      sweepOpen τ s k ∧ ¬ s.sweepBarred k i) :
    ∃ s', SweepStar C D τ honest s s' ∧
      Reach C D τ honest s' ∧
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
      exact hcov k i m htmem (hall k i m htmem).1 (hall k i m htmem).2
  obtain ⟨⟨hFresh, -, -⟩, -⟩ := reach_inv h
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
