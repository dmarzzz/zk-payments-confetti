import Zkpc.Chain.V2.Close

/-!
# Spec-v2 settlement machine: explicit clock, explicit challenge window

The Spec-v2 successor of `Zkpc/Chain/State.lean`, discharging that module's
three disclosed fiats:

1. **The honest-recipient `settleSplit` guard is gone.** Settlement is
   enabled by *window expiry alone*; nothing checks the close was honest.
   Bob's protection is the theorem `challenge_enabled_iff_unsafe`: whenever
   an unsafe close is pending, a challenge transition exists at every instant
   of the window. A Bob who sleeps through his window settles an unsafe
   close — now an explicit reachable outcome, out of scope by vigilance, not
   by fiat.
2. **The challenge guard is evidence-based**, not the index rule `i < len`:
   the `challenge` transition carries an actual held-message witness against
   the close's exhibit set (Spec-v2 §5, via `Zkpc/Chain/V2/Close.lean`),
   including the same-state exception and the unsigned modes of A2.
3. **Timing is explicit.** A clock `now`, the close timestamp, Bob's
   close-request timestamp, and the three Spec-v2 constants (`Tabs` = 90 d,
   `Treq` = 7 d, `tau` = 7 d) appear as machine data; window and deadline
   comparisons are guards, not abstractions.

New relative to the seed machine, per A2: the one-deep unsigned frontier
(`ghostSend`/`signGhost`), closes on unsigned states (`CloseObj`), and the
forfeit-all challenge with its window.

## Modeling conventions (carried from the seed, unchanged where not listed)

Idealized ledger; signatures and knowledge soundness as transition guards
(an accepted payment IS its witness; residual crypto lives outside this
symbolic layer); balances as plain data (hiding is the anonymity layer's
business); nullifiers as an injective chain `nul : ℕ → N` (collision-freedom
hypothesis, `Zkpc/Chain/V2/Close.lean`). GATE-NOTE: single channel; `δ : ℕ`
(A2.ii by type); Bob's `requestClose` is modeled once (re-requests change
nothing); `tick` is enabled while the channel is live, so deadlines are
reachable but not forced — *guaranteed*-liveness under fairness is ROADMAP
obligation 5, not this module. **Frontier injectivity** (Spec-v2 §3
normative rule, gate finding F-R1-1) is structural here: `ghostSend`
requires a clean frontier, so the machine cannot emit two sibling
commitments for one parent — the machine models a rule-abiding Alice, and
the liveness theorems below are conditioned on that rule exactly as
Spec-v2 §7 states. The self-wedge reachable by a rule-breaking Alice is
outside this state space by construction (disclosed, not hidden: it is the
point of the rule).
-/

namespace Zkpc.Chain.V2

/-- Spec-v2 §1 time constants and the deposit: `Tabs` (absolute close
deadline, 90 days), `Treq` (close-on-request deadline, 7 days), `tau`
(challenge window, A3, 7 days). Kept abstract; instantiation is free. -/
structure Params where
  D : ℕ
  Tabs : ℕ
  Treq : ℕ
  tau : ℕ

/-- Machine state. `now` is the clock; `len`, `msgs`, `balOf`, `ghostδ` are
the channel context (`Ctx`); `closeReqAt` records Bob's close request;
`closing = some (x, t0)` means close object `x` was opened on-chain at time
`t0` and its challenge window runs until `t0 + tau`; the settlement
bookkeeping is as in the seed machine. -/
structure St where
  now : ℕ
  len : ℕ
  msgs : ℕ
  balOf : ℕ → ℕ
  ghostδ : ℕ
  closeReqAt : Option ℕ
  closing : Option (CloseObj × ℕ)
  settled : Bool
  forfeited : Bool
  alicePay : ℕ
  bobPay : ℕ

/-- The channel context of a machine state (the close-time view that
`Zkpc/Chain/V2/Close.lean` reasons about). -/
def St.ctx (s : St) : Ctx := ⟨s.len, s.msgs, s.balOf, s.ghostδ⟩

/-- Genesis: clock zero, nothing signed, nothing sent, channel live. -/
def St.init : St :=
  ⟨0, 0, 0, fun _ => 0, 0, none, none, false, false, 0, 0⟩

/-- Bob's earned balance: the latest countersigned state's balance. -/
def St.earned (s : St) : ℕ := s.balOf s.len

/-- Transition labels (Spec-v2 §§2–6). -/
inductive Act
  /-- time passes -/
  | tick (dt : ℕ)
  /-- Alice sends a payment message; Bob countersigns it -/
  | pay (δ : ℕ)
  /-- Alice sends a payment message; Bob withholds the countersignature
  (the G2 wedge lever) -/
  | ghostSend (δ : ℕ)
  /-- Bob countersigns the outstanding ghosted message after all -/
  | signGhost
  /-- Bob requests close, starting the `Treq` timer -/
  | requestClose
  /-- Alice opens the on-chain close of object `x` -/
  | closeOn (x : CloseObj)
  /-- Bob challenges the pending close with held message `j` -/
  | challenge (j : ℕ)
  /-- the challenge window expires; the claimed split settles -/
  | settle
  /-- a missed deadline; Bob takes the whole deposit -/
  | timeoutForfeit

variable {N : Type}

/-- The step relation, parameterized by the deposit/timers `P` and the
nullifier chain `nul`. Guards transcribe Spec-v2: the payment relation's
value clauses (§3) guard `pay`/`ghostSend`; close legality (§4) is
`Valid`; challenge validity (§5) is a real evidence witness inside the
window; settlement (§4/§6) is window expiry. -/
inductive Step (P : Params) (nul : ℕ → N) : St → Act → St → Prop
  /-- Time passes freely while the channel is unsettled. -/
  | tick (s : St) (dt : ℕ) (hlive : s.settled = false) :
      Step P nul s (.tick dt) { s with now := s.now + dt }
  /-- **Countersigned payment** (Spec-v2 §3): needs a clean frontier
  (`msgs = len`, no ghost outstanding), a live un-closing channel, and the
  in-circuit cap `earned + δ ≤ D`. -/
  | pay (s : St) (δ : ℕ) (hlive : s.settled = false)
      (hopen : s.closing = none) (hfront : s.msgs = s.len)
      (hcap : s.earned + δ ≤ P.D) :
      Step P nul s (.pay δ)
        { s with len := s.len + 1, msgs := s.msgs + 1,
                 balOf := Function.update s.balOf (s.len + 1)
                   (s.earned + δ) }
  /-- **Ghosted payment** (A2/G2): same message, no countersignature. The
  frontier is now one deep; no further payment can extend it (Spec-v2 §3). -/
  | ghostSend (s : St) (δ : ℕ) (hlive : s.settled = false)
      (hopen : s.closing = none) (hfront : s.msgs = s.len)
      (hcap : s.earned + δ ≤ P.D) :
      Step P nul s (.ghostSend δ)
        { s with msgs := s.msgs + 1, ghostδ := δ }
  /-- Bob countersigns the ghost late; the frontier is clean again. -/
  | signGhost (s : St) (hlive : s.settled = false)
      (hopen : s.closing = none) (hghost : s.msgs = s.len + 1) :
      Step P nul s .signGhost
        { s with len := s.len + 1,
                 balOf := Function.update s.balOf (s.len + 1)
                   (s.earned + s.ghostδ) }
  /-- Bob requests close (Spec-v2 §4 timers), once. -/
  | requestClose (s : St) (hlive : s.settled = false)
      (hopen : s.closing = none) (hnone : s.closeReqAt = none) :
      Step P nul s .requestClose { s with closeReqAt := some s.now }
  /-- **Close** (Spec-v2 §4): any proof-valid object; starts the window. -/
  | closeOn (s : St) (x : CloseObj) (hlive : s.settled = false)
      (hopen : s.closing = none) (hv : Valid P.D s.ctx x) :
      Step P nul s (.closeOn x) { s with closing := some (x, s.now) }
  /-- **Challenge** (Spec-v2 §5): inside the window, a held message `j`
  that is not the closed state and whose revealed nullifier `nul j` equals
  an exhibited nullifier `nul k` of the close. Forfeit-all (A2/G5). -/
  | challenge (s : St) (x : CloseObj) (t0 j k : ℕ)
      (hlive : s.settled = false) (hcl : s.closing = some (x, t0))
      (hwin : s.now < t0 + P.tau) (hj1 : 1 ≤ j) (hj2 : j ≤ s.msgs)
      (hns : ¬ SameState s.ctx j x) (hex : ExhibitIdx s.ctx x k)
      (hcol : nul j = nul k) :
      Step P nul s (.challenge j)
        { s with settled := true, forfeited := true,
                 alicePay := 0, bobPay := P.D }
  /-- **Settlement** (Spec-v2 §4/§6): the window elapsed; the claimed
  balance is paid. No honesty guard — that is the discharged fiat. -/
  | settle (s : St) (x : CloseObj) (t0 : ℕ) (hlive : s.settled = false)
      (hcl : s.closing = some (x, t0)) (hwin : t0 + P.tau ≤ s.now) :
      Step P nul s .settle
        { s with settled := true,
                 alicePay := P.D - balV s.ctx x,
                 bobPay := balV s.ctx x }
  /-- **Timeout** (Spec-v2 §4 timers): no close pending and a deadline
  passed — the absolute `Tabs`, or `Treq` after Bob's request. -/
  | timeoutForfeit (s : St) (hlive : s.settled = false)
      (hopen : s.closing = none)
      (hlate : P.Tabs ≤ s.now ∨
        ∃ t, s.closeReqAt = some t ∧ t + P.Treq ≤ s.now) :
      Step P nul s .timeoutForfeit
        { s with settled := true, forfeited := true,
                 alicePay := 0, bobPay := P.D }

/-- Reachability from the genesis. -/
inductive Reach (P : Params) (nul : ℕ → N) : St → Prop
  | init : Reach P nul St.init
  | step {s s' : St} {a : Act} :
      Reach P nul s → Step P nul s a s' → Reach P nul s'

/-- The conjunctive safety invariant: a well-formed context (genesis zero,
caps, monotone chain, one-deep frontier, ghost cap); every pending close is
proof-valid; live channels are unforfeited with no payouts; settlements
conserve `D`, and cooperative ones pay the closed object's claimed balance. -/
def Inv (P : Params) (s : St) : Prop :=
  s.ctx.WF P.D ∧
  (∀ x t0, s.closing = some (x, t0) → Valid P.D s.ctx x) ∧
  (s.settled = false → s.forfeited = false) ∧
  (s.settled = false → s.alicePay = 0 ∧ s.bobPay = 0) ∧
  (s.settled = true → s.alicePay + s.bobPay = P.D) ∧
  (s.settled = true → s.forfeited = false →
    ∃ x t0, s.closing = some (x, t0) ∧ s.bobPay = balV s.ctx x)

/-- `Inv` holds at every reachable state (the Class A induction). -/
theorem reach_inv {P : Params} {nul : ℕ → N} {s : St}
    (h : Reach P nul s) : Inv P s := by
  induction h with
  | init =>
    refine ⟨⟨rfl, fun i => Nat.zero_le _, ?_, le_refl _, ?_, ?_⟩,
      ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [St.init, St.ctx]
  | @step s s' a _ hstep ih =>
    obtain ⟨hwf, hclv, hunf, hpre, hcons, hcoop⟩ := ih
    obtain ⟨hz, hcap, hmono, hlb, hub, hgc⟩ := hwf
    cases hstep with
    | tick dt hlive =>
      exact ⟨⟨hz, hcap, hmono, hlb, hub, hgc⟩, hclv, hunf, hpre, hcons,
        hcoop⟩
    | pay δ hlive hopen hfront hcap' =>
      have hearned : s.earned = s.balOf s.len := rfl
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · show Function.update s.balOf (s.len + 1) (s.earned + δ) 0 = 0
        rw [Function.update_apply, if_neg (by omega)]
        exact hz
      · intro i
        show Function.update s.balOf (s.len + 1) (s.earned + δ) i ≤ P.D
        rw [Function.update_apply]
        split
        · exact hcap'
        · exact hcap i
      · intro i j hij hj
        show Function.update s.balOf (s.len + 1) (s.earned + δ) i ≤
          Function.update s.balOf (s.len + 1) (s.earned + δ) j
        rw [Function.update_apply, Function.update_apply]
        rcases eq_or_ne j (s.len + 1) with rfl | hjne
        · rw [if_pos rfl]
          split
          · exact le_refl _
          · have : s.balOf i ≤ s.balOf s.len :=
              hmono i s.len (by omega) (le_refl _)
            omega
        · have hjlen : j ≤ s.len := by
            simp only [St.ctx] at hj
            omega
          rw [if_neg hjne, if_neg (by omega)]
          exact hmono i j hij hjlen
      · show s.len + 1 ≤ s.msgs + 1
        omega
      · show s.msgs + 1 ≤ s.len + 1 + 1
        omega
      · intro hg
        simp only [St.ctx] at hg
        omega
      · intro x t0 hx
        rw [hopen] at hx
        exact absurd hx (by simp)
      · exact hunf
      · exact hpre
      · intro hset
        exact absurd (hlive.symm.trans hset) (by simp)
      · intro hset
        exact absurd (hlive.symm.trans hset) (by simp)
    | ghostSend δ hlive hopen hfront hcap' =>
      refine ⟨⟨hz, hcap, hmono, ?_, ?_, ?_⟩, ?_, hunf, hpre, ?_, ?_⟩
      · show s.len ≤ s.msgs + 1
        omega
      · show s.msgs + 1 ≤ s.len + 1
        omega
      · intro _
        show s.balOf s.len + δ ≤ P.D
        exact hcap'
      · intro x t0 hx
        rw [hopen] at hx
        exact absurd hx (by simp)
      · intro hset
        exact absurd (hlive.symm.trans hset) (by simp)
      · intro hset
        exact absurd (hlive.symm.trans hset) (by simp)
    | signGhost hlive hopen hghost =>
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hunf, hpre, ?_, ?_⟩
      · show Function.update s.balOf (s.len + 1) (s.earned + s.ghostδ) 0 = 0
        rw [Function.update_apply, if_neg (by omega)]
        exact hz
      · intro i
        show Function.update s.balOf (s.len + 1) (s.earned + s.ghostδ) i ≤
          P.D
        rw [Function.update_apply]
        split
        · exact hgc hghost
        · exact hcap i
      · intro i j hij hj
        show Function.update s.balOf (s.len + 1) (s.earned + s.ghostδ) i ≤
          Function.update s.balOf (s.len + 1) (s.earned + s.ghostδ) j
        rw [Function.update_apply, Function.update_apply]
        rcases eq_or_ne j (s.len + 1) with rfl | hjne
        · rw [if_pos rfl]
          split
          · exact le_refl _
          · have h1 : s.balOf i ≤ s.balOf s.len :=
              hmono i s.len (by omega) (le_refl _)
            have hearned : s.earned = s.balOf s.len := rfl
            omega
        · have hjlen : j ≤ s.len := by
            simp only [St.ctx] at hj
            omega
          rw [if_neg hjne, if_neg (by omega)]
          exact hmono i j hij hjlen
      · show s.len + 1 ≤ s.msgs
        omega
      · show s.msgs ≤ s.len + 1 + 1
        omega
      · intro hg
        simp only [St.ctx] at hg
        omega
      · intro x t0 hx
        rw [hopen] at hx
        exact absurd hx (by simp)
      · intro hset
        exact absurd (hlive.symm.trans hset) (by simp)
      · intro hset
        exact absurd (hlive.symm.trans hset) (by simp)
    | requestClose hlive hopen hnone =>
      exact ⟨⟨hz, hcap, hmono, hlb, hub, hgc⟩, hclv, hunf, hpre, hcons,
        hcoop⟩
    | closeOn x hlive hopen hv =>
      refine ⟨⟨hz, hcap, hmono, hlb, hub, hgc⟩, ?_, hunf, hpre, hcons,
        ?_⟩
      · intro y t0 hy
        simp only [Option.some.injEq, Prod.mk.injEq] at hy
        rw [← hy.1]
        exact hv
      · intro hset
        exact absurd (hlive.symm.trans hset) (by simp)
    | challenge x t0 j k hlive hcl hwin hj1 hj2 hns hex hcol =>
      refine ⟨⟨hz, hcap, hmono, hlb, hub, hgc⟩, hclv, ?_, ?_, ?_, ?_⟩
      · intro hf
        exact absurd hf (by simp)
      · intro hf
        exact absurd hf (by simp)
      · intro _
        show (0 : ℕ) + P.D = P.D
        omega
      · intro _ hf
        exact absurd hf (by simp)
    | settle x t0 hlive hcl hwin =>
      have hv := hclv x t0 hcl
      have hble : balV s.ctx x ≤ P.D :=
        balV_le P.D s.ctx ⟨hz, hcap, hmono, hlb, hub, hgc⟩ x hv
      refine ⟨⟨hz, hcap, hmono, hlb, hub, hgc⟩, hclv, ?_, ?_, ?_, ?_⟩
      · intro hf
        exact absurd hf (by simp)
      · intro hf
        exact absurd hf (by simp)
      · intro _
        show (P.D - balV s.ctx x) + balV s.ctx x = P.D
        omega
      · intro _ _
        exact ⟨x, t0, hcl, rfl⟩
    | timeoutForfeit hlive hopen hlate =>
      refine ⟨⟨hz, hcap, hmono, hlb, hub, hgc⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro x t0 hx
        rw [hopen] at hx
        exact absurd hx (by simp)
      · intro hf
        exact absurd hf (by simp)
      · intro hf
        exact absurd hf (by simp)
      · intro _
        show (0 : ℕ) + P.D = P.D
        omega
      · intro _ hf
        exact absurd hf (by simp)

/-! ## Safety theorems -/

/-- **Conservation** (Spec-v2 §6): every settlement splits exactly `D`. -/
theorem conservation {P : Params} {nul : ℕ → N} {s : St}
    (h : Reach P nul s) (hset : s.settled = true) :
    s.alicePay + s.bobPay = P.D :=
  (reach_inv h).2.2.2.2.1 hset

/-- **No overspend** (Spec-v2 §7): every committed balance and Bob's
settlement payout are at most the deposit. -/
theorem no_overspend {P : Params} {nul : ℕ → N} {s : St}
    (h : Reach P nul s) : s.bobPay ≤ P.D ∧ ∀ i, s.balOf i ≤ P.D := by
  obtain ⟨hwf, -, -, hpre, hcons, -⟩ := reach_inv h
  refine ⟨?_, hwf.cap⟩
  rcases hb : s.settled with _ | _
  · exact (hpre hb).2 ▸ Nat.zero_le P.D
  · have := hcons hb
    omega

/-- **Cooperative settlements pay the claimed balance exactly**
(Spec-v2 §6), and in particular a cooperative settlement of a *safe* close
pays Bob at least his earned balance — the cooperative half of "Bob never
loses" (§7). The unsafe-close settlement is reachable only past an expired
window in which `challenge_enabled_iff_unsafe` held throughout. -/
theorem cooperative_exact {P : Params} {nul : ℕ → N} {s : St}
    (h : Reach P nul s) (hset : s.settled = true)
    (hf : s.forfeited = false) :
    ∃ x t0, s.closing = some (x, t0) ∧ s.bobPay = balV s.ctx x ∧
      s.alicePay = P.D - balV s.ctx x := by
  obtain ⟨-, -, -, -, hcons, hcoop⟩ := reach_inv h
  obtain ⟨x, t0, hcl, hbob⟩ := hcoop hset hf
  refine ⟨x, t0, hcl, hbob, ?_⟩
  have := hcons hset
  have hble : balV s.ctx x ≤ P.D := by
    have hv := (reach_inv h).2.1 x t0 hcl
    exact balV_le P.D s.ctx (reach_inv h).1 x hv
  omega

/-- The cooperative floor: settling a safe close pays Bob at least
`earned`. -/
theorem cooperative_safe_floor {P : Params} {nul : ℕ → N}
    (hinj : Function.Injective nul) {s : St} (h : Reach P nul s)
    (hset : s.settled = true) (hf : s.forfeited = false)
    {x : CloseObj} {t0 : ℕ} (hcl : s.closing = some (x, t0))
    (hsafe : Safe nul P.D s.ctx x) : s.earned ≤ s.bobPay := by
  obtain ⟨y, t1, hcl', hbob, -⟩ := cooperative_exact h hset hf
  rw [hcl] at hcl'
  simp only [Option.some.injEq, Prod.mk.injEq] at hcl'
  rw [hbob, ← hcl'.1]
  exact safe_payout_ge_earned nul hinj P.D s.ctx (reach_inv h).1 x hsafe

/-- **The challenge guard is exactly challenge evidence** (fiat 2
discharged): with a close pending inside its window, a challenge transition
exists iff evidence against the close exists. -/
theorem challenge_enabled_iff_evidence {P : Params} {nul : ℕ → N} {s : St}
    (hlive : s.settled = false) {x : CloseObj} {t0 : ℕ}
    (hcl : s.closing = some (x, t0)) (hwin : s.now < t0 + P.tau) :
    (∃ j s', Step P nul s (.challenge j) s') ↔ Evidence nul s.ctx x := by
  constructor
  · rintro ⟨j, s', hstep⟩
    cases hstep with
    | challenge y t1 _j k' hlive' hcl' hwin' hj1' hj2' hns' hex' hcol' =>
      rw [hcl] at hcl'
      simp only [Option.some.injEq, Prod.mk.injEq] at hcl'
      exact ⟨j, k', hj1', hj2', hcl'.1 ▸ hns', hcl'.1 ▸ hex', hcol'⟩
  · rintro ⟨j, k, hj1, hj2, hns, hex, hcol⟩
    exact ⟨j, _, Step.challenge s x t0 j k hlive hcl hwin hj1 hj2 hns hex
      hcol⟩

/-- **Vigilant Bob wins** (the honest-recipient environment, now a theorem
instead of a guard): while an *unsafe* close is pending inside its window,
a challenge transition exists — awarding Bob the whole deposit. Combined
with `cooperative_safe_floor`, this is "Bob never loses" for any Bob who
acts within `tau`. -/
theorem challenge_enabled_iff_unsafe {P : Params} {nul : ℕ → N}
    {s : St} (h : Reach P nul s)
    (hlive : s.settled = false) {x : CloseObj} {t0 : ℕ}
    (hcl : s.closing = some (x, t0)) (hwin : s.now < t0 + P.tau) :
    (∃ j s', Step P nul s (.challenge j) s') ↔
      ¬ Safe nul P.D s.ctx x := by
  have hv := (reach_inv h).2.1 x t0 hcl
  rw [challenge_enabled_iff_evidence hlive hcl hwin]
  unfold Safe
  constructor
  · rintro he ⟨-, hne⟩
    exact hne he
  · intro hns
    by_contra hne
    exact hns ⟨hv, hne⟩

/-- A safe pending close admits no challenge at any instant — the honest
closer (including the wedged closer on the ghost) is never slashed. -/
theorem safe_close_unchallengeable {P : Params} {nul : ℕ → N} {s : St}
    {x : CloseObj} {t0 : ℕ} (hcl : s.closing = some (x, t0))
    (hsafe : Safe nul P.D s.ctx x) :
    ¬ ∃ j s', Step P nul s (.challenge j) s' := by
  rintro ⟨j, s', hstep⟩
  cases hstep with
  | challenge y t1 _j k' hlive' hcl' hwin' hj1' hj2' hns' hex' hcol' =>
    rw [hcl] at hcl'
    simp only [Option.some.injEq, Prod.mk.injEq] at hcl'
    exact hsafe.2 ⟨j, k', hj1', hj2', hcl'.1 ▸ hns', hcl'.1 ▸ hex', hcol'⟩

/-- No settlement before the window elapses (Spec-v2 §4, A3: payout is
deferred). -/
theorem settle_waits {P : Params} {nul : ℕ → N} {s s' : St}
    (hstep : Step P nul s .settle s') :
    ∃ x t0, s.closing = some (x, t0) ∧ t0 + P.tau ≤ s.now := by
  cases hstep with
  | settle x t0 hlive hcl hwin => exact ⟨x, t0, hcl, hwin⟩

/-- **Liveness for Alice, wedge included** (Spec-v2 §7, the G2 repair):
from every reachable live state with no close pending, Alice and the clock
alone drive the channel to a cooperative settlement paying her
`D - owed` — where `owed` exceeds her countersigned debt by at most the one
ghosted δ (`Ctx.owed_le_earned_add_ghost`) — and the close she uses (the
canonical one) admits no challenge at any point along the way
(`safe_close_unchallengeable` applies at every intermediate state, whose
context is unchanged). Bob's cooperation is never needed: `closeOn`,
`tick`, and `settle` are Alice- and clock-moves. -/
theorem alice_liveness {P : Params} {nul : ℕ → N}
    (hinj : Function.Injective nul) {s : St} (h : Reach P nul s)
    (hlive : s.settled = false) (hopen : s.closing = none) :
    ∃ s', Reach P nul s' ∧ s'.settled = true ∧ s'.forfeited = false ∧
      s'.bobPay = s.ctx.owed ∧ s'.alicePay = P.D - s.ctx.owed ∧
      Safe nul P.D s.ctx (canonical s.ctx) := by
  have hwf := (reach_inv h).1
  have hv := canonical_valid P.D s.ctx hwf
  -- close on the canonical object at time `now`
  have step1 : Step P nul s (.closeOn (canonical s.ctx))
      { s with closing := some (canonical s.ctx, s.now) } :=
    Step.closeOn s (canonical s.ctx) hlive hopen hv
  set s1 : St := { s with closing := some (canonical s.ctx, s.now) }
  -- let the window pass
  have step2 : Step P nul s1 (.tick P.tau)
      { s1 with now := s1.now + P.tau } :=
    Step.tick s1 P.tau hlive
  set s2 : St := { s1 with now := s1.now + P.tau }
  -- settle
  have hctx2 : s2.ctx = s.ctx := rfl
  have step3 : Step P nul s2 .settle
      { s2 with settled := true,
                alicePay := P.D - balV s2.ctx (canonical s.ctx),
                bobPay := balV s2.ctx (canonical s.ctx) } :=
    Step.settle s2 (canonical s.ctx) s.now hlive rfl (by
      show s.now + P.tau ≤ s.now + P.tau
      exact le_refl _)
  refine ⟨_, Reach.step (Reach.step (Reach.step h step1) step2) step3,
    rfl, ?_, ?_, ?_, canonical_safe nul hinj P.D s.ctx hwf⟩
  · show s.forfeited = false
    exact (reach_inv h).2.2.1 hlive
  · show balV s2.ctx (canonical s.ctx) = s.ctx.owed
    rw [hctx2]
    exact canonical_balV P.D s.ctx hwf
  · show P.D - balV s2.ctx (canonical s.ctx) = P.D - s.ctx.owed
    rw [hctx2, canonical_balV P.D s.ctx hwf]

/-- **The wedge price** (Spec-v2 §7): the settlement `alice_liveness`
reaches refunds Alice at least `D - earned - ghostδ`; relative to a fully
countersigned exit (`D - earned`) the withheld countersignature costs her
at most the one ghosted δ. -/
theorem wedge_price {P : Params} {nul : ℕ → N}
    (hinj : Function.Injective nul) {s : St} (h : Reach P nul s)
    (hlive : s.settled = false) (hopen : s.closing = none) :
    ∃ s', Reach P nul s' ∧ s'.settled = true ∧ s'.forfeited = false ∧
      P.D - s.earned - s.ghostδ ≤ s'.alicePay := by
  obtain ⟨s', hr, hset, hf, -, hap, -⟩ := alice_liveness hinj h hlive hopen
  refine ⟨s', hr, hset, hf, ?_⟩
  rw [hap]
  have h1 : s.ctx.owed ≤ s.ctx.earned + s.ctx.ghostδ :=
    s.ctx.owed_le_earned_add_ghost
  have h2 : s.ctx.earned = s.earned := rfl
  have h3 : s.ctx.ghostδ = s.ghostδ := rfl
  omega

end Zkpc.Chain.V2

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.V2.reach_inv
#print axioms Zkpc.Chain.V2.conservation
#print axioms Zkpc.Chain.V2.no_overspend
#print axioms Zkpc.Chain.V2.cooperative_exact
#print axioms Zkpc.Chain.V2.cooperative_safe_floor
#print axioms Zkpc.Chain.V2.challenge_enabled_iff_evidence
#print axioms Zkpc.Chain.V2.challenge_enabled_iff_unsafe
#print axioms Zkpc.Chain.V2.safe_close_unchallengeable
#print axioms Zkpc.Chain.V2.settle_waits
#print axioms Zkpc.Chain.V2.alice_liveness
#print axioms Zkpc.Chain.V2.wedge_price
