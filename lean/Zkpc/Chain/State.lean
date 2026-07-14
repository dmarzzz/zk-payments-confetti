import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic

/-!
# Nullifier-chain channel: settlement state machine and safety (Class A)

Formalizes the core of the unidirectional zk payment channel of
`PROTOCOL.md` (the
nullifier-chain design): Alice deposits `D` naming Bob; each off-chain
payment produces a successor state whose balance grows by a public `δ` under
the guard `new_balance ≤ D`; Bob countersigns every state he accepts; Alice
closes on some state she holds; a stale close is challengeable by nullifier
collision and forfeits the whole deposit to Bob; an abandoned channel times
out in Bob's favor.

This is an **additional instantiation** alongside `Zkpc/Core` and
`Zkpc/Refund`; it does not touch the frozen `Spec.md` definitions. It follows
the Class A template of `Zkpc/Core/T1.lean` (conjunctive invariant + induction
on reachability).

## Modeling conventions (recorded per the repo's conventions)

* **Idealized ledger.** The contract is the transition system itself; on-chain
  time (the 90-day / 7-day windows) is abstracted into the enabledness of the
  `timeoutForfeit` and `settleSplit` actions.
* **Signatures as transition guards (knowledge soundness as transition
  guards).** Bob's countersignature is not a cryptographic object here: a
  state exists in the machine (index `i ≤ len`) *iff* Bob countersigned it (or
  it is the genesis). The design doc's "extends the genesis or a Bob-signed
  state, verified inside the STARK" is therefore the `pay` transition itself:
  an accepted payment IS its witness. The residual cryptographic content
  (forging a countersignature, breaking the STARK's knowledge soundness) is
  outside this symbolic layer, exactly as in `Zkpc/Core` (see its `accept`
  guard `acc ⊆ sigs`).
* **Balances.** `balOf i` is the (Bob-side) balance committed in state `i`;
  it is hidden from Bob in the real protocol but is plain data in the safety
  machine, since safety is about amounts, not views. Hiding is the business of
  `Zkpc/Chain/Anonymity.lean`.
* **Honest-recipient environment.** `settleSplit` carries the guard
  `i = len` ("the close survived the challenge window unchallenged"). The
  contract cannot check this directly; it is the *behavioral consequence* of
  an honest Bob who challenges every stale close. That Bob always **can**
  challenge a stale close (he holds the colliding message) and never has a
  valid challenge against an honest close is proved in
  `Zkpc/Chain/Collision.lean` (`stale_close_detectable`,
  `honest_close_unchallengeable`), which is exactly what justifies this
  guard. A Bob who sleeps through his own challenge window is out of scope,
  as in every channel construction.
* **GATE-NOTE (single channel, non-negative δ).** One channel, one deposit;
  `δ : ℕ` so payments are non-negative by type (the design is unidirectional).
  Fleet composition is out of scope for this module family.
-/

namespace Zkpc.Chain

/-- Channel state. `len` is the index of the latest countersigned state
(0 = genesis, which needs no signature); `balOf i` is the balance committed in
state `i`; `closing = some i` means Alice has opened the on-chain close of
state `i` and the challenge window is running; the settlement bookkeeping
(`settled`, `forfeited`, `alicePay`, `bobPay`) records the terminal outcome.
`forfeited` marks the two whole-deposit-to-Bob paths (challenged stale close,
timeout), as opposed to the cooperative split. -/
structure St where
  /-- index of the latest countersigned state (genesis = 0) -/
  len : ℕ
  /-- committed balance of each state index -/
  balOf : ℕ → ℕ
  /-- index of the state being closed on, while the challenge window runs -/
  closing : Option ℕ
  /-- channel has settled (terminal) -/
  settled : Bool
  /-- settlement was by forfeit (challenge or timeout), not cooperative -/
  forfeited : Bool
  /-- Alice's settlement payout -/
  alicePay : ℕ
  /-- Bob's settlement payout -/
  bobPay : ℕ

/-- Genesis: no countersigned state, zero balances, channel live
(design doc "Open": the deposit `D` is escrowed, the genesis has balance 0). -/
def St.init : St := ⟨0, fun _ => 0, none, false, false, 0, 0⟩

/-- Bob's earned balance: the balance of the latest countersigned state. -/
def St.earned (s : St) : ℕ := s.balOf s.len

/-- Transition labels (design doc "Payment" / "Close"). -/
inductive Act
  /-- Alice pays `δ`; Bob countersigns the successor state -/
  | pay (δ : ℕ)
  /-- Alice opens the on-chain close of state `i` (a payment state, or the
  genesis `i = 0` for a full refund) -/
  | closeOn (i : ℕ)
  /-- the challenge window expires unchallenged; the split stands -/
  | settleSplit
  /-- Bob challenges a stale close by exhibiting the colliding message -/
  | challenge
  /-- Alice never withdrew within the deadline; Bob takes everything -/
  | timeoutForfeit

/-- The step relation, parameterized by the deposit `D`. Guards transcribe the
design doc: the payment proof's `parent_balance + δ = new_balance ≤ D` is the
`pay` guard; only held states (`i ≤ len`) can be closed on; the challenge
fires exactly against a non-final state (`i < len`, justified by the
collision mechanism in `Zkpc/Chain/Collision.lean`). -/
inductive Step (D : ℕ) : St → Act → St → Prop
  /-- **Payment** (design doc "Payment"). Requires a live, un-closing channel;
  the new balance `earned + δ` respects the deposit cap `≤ D` (the guard the
  ZK proof enforces, which prevents Alice paying Bob past the deposit and
  recovering the excess). Bob's countersignature is the transition itself. -/
  | pay (s : St) (δ : ℕ)
      (hlive : s.settled = false) (hopen : s.closing = none)
      (hcap : s.earned + δ ≤ D) :
      Step D s (.pay δ)
        { s with len := s.len + 1,
                 balOf := Function.update s.balOf (s.len + 1) (s.earned + δ) }
  /-- **Close** (design doc "Close"). Alice opens the committed-next-nullifier
  of a state she holds: any countersigned state or the genesis, `i ≤ len`.
  Starts the challenge window. -/
  | closeOn (s : St) (i : ℕ)
      (hlive : s.settled = false) (hopen : s.closing = none)
      (hi : i ≤ s.len) :
      Step D s (.closeOn i) { s with closing := some i }
  /-- **Unchallenged settlement.** The window expires with no challenge; the
  split of the closed state stands: Bob gets its balance, Alice the rest. The
  guard `i = len` is the honest-recipient environment: by
  `Zkpc.Chain.stale_close_detectable` an honest Bob challenges every `i < len`
  close within the window, so only the latest state settles this way. -/
  | settleSplit (s : St) (i : ℕ)
      (hlive : s.settled = false) (hcl : s.closing = some i)
      (hlatest : i = s.len) :
      Step D s .settleSplit
        { s with settled := true,
                 alicePay := D - s.balOf i, bobPay := s.balOf i }
  /-- **Challenge** (design doc "Bob challenges if he holds a message that
  revealed `N`"). Enabled exactly when the closed state is stale (`i < len`):
  the successor message revealed the very nullifier the close opened
  (`Zkpc.Chain.stale_close_detectable`), and only then
  (`Zkpc.Chain.honest_close_unchallengeable`). Alice forfeits everything. -/
  | challenge (s : St) (i : ℕ)
      (hlive : s.settled = false) (hcl : s.closing = some i)
      (hstale : i < s.len) :
      Step D s .challenge
        { s with settled := true, forfeited := true,
                 alicePay := 0, bobPay := D }
  /-- **Timeout** (design doc: Alice must withdraw within 90 days, or within
  7 days of Bob requesting close; otherwise Bob takes the whole deposit). -/
  | timeoutForfeit (s : St)
      (hlive : s.settled = false) (hopen : s.closing = none) :
      Step D s .timeoutForfeit
        { s with settled := true, forfeited := true,
                 alicePay := 0, bobPay := D }

/-- Reachability from the genesis under deposit `D`. -/
inductive Reach (D : ℕ) : St → Prop
  | init : Reach D St.init
  | step {s s' : St} {a : Act} : Reach D s → Step D s a s' → Reach D s'

/-- The conjunctive safety invariant (Class A template, `Zkpc/Core/T1.lean`):
genesis balance zero; every committed balance capped by the deposit; balances
monotone along the countersigned chain; a closing index is a held state; no
payout before settlement; settlement conserves exactly `D`; Bob's settlement
payout is bracketed `earned ≤ bobPay ≤ D`; a cooperative (unforfeited)
settlement pays the closed latest state's balance exactly. -/
def Inv (D : ℕ) (s : St) : Prop :=
  s.balOf 0 = 0 ∧
  (∀ i, s.balOf i ≤ D) ∧
  (∀ i j, i ≤ j → j ≤ s.len → s.balOf i ≤ s.balOf j) ∧
  (∀ i, s.closing = some i → i ≤ s.len) ∧
  (s.settled = false → s.alicePay = 0 ∧ s.bobPay = 0) ∧
  (s.settled = true → s.alicePay + s.bobPay = D) ∧
  (s.settled = true → s.earned ≤ s.bobPay ∧ s.bobPay ≤ D) ∧
  (s.settled = true → s.forfeited = false →
    s.bobPay = s.earned ∧ s.alicePay = D - s.earned)

/-- `Inv` holds at every reachable state (the Class A induction). -/
theorem reach_inv {D : ℕ} {s : St} (h : Reach D s) : Inv D s := by
  induction h with
  | init =>
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [St.init]
  | @step s s' a _ hstep ih =>
    obtain ⟨hz, hcap, hmono, hcl, hpre, hcons, hbr, hcoop⟩ := ih
    cases hstep with
    | pay δ hlive hopen hδ =>
      have hearned : s.earned = s.balOf s.len := rfl
      refine ⟨?_, ?_, ?_, ?_, hpre, ?_, ?_, ?_⟩
      · show Function.update s.balOf (s.len + 1) (s.earned + δ) 0 = 0
        rw [Function.update_apply, if_neg (by omega)]
        exact hz
      · intro i
        show Function.update s.balOf (s.len + 1) (s.earned + δ) i ≤ D
        rw [Function.update_apply]
        split
        · exact hδ
        · exact hcap i
      · intro i j hij hj
        show Function.update s.balOf (s.len + 1) (s.earned + δ) i ≤
          Function.update s.balOf (s.len + 1) (s.earned + δ) j
        rw [Function.update_apply, Function.update_apply]
        rcases eq_or_ne j (s.len + 1) with rfl | hjne
        · rw [if_pos rfl]
          split
          · exact le_refl _
          · have : s.balOf i ≤ s.balOf s.len := hmono i s.len (by omega) (le_refl _)
            omega
        · have hj' : j ≤ s.len + 1 := hj
          have hjlen : j ≤ s.len := by omega
          rw [if_neg hjne, if_neg (by omega)]
          exact hmono i j hij hjlen
      · intro i hi
        rw [hopen] at hi
        exact absurd hi (by simp)
      · intro hset
        exact hcons hset
      · intro hset
        exact absurd (hlive.symm.trans hset) (by simp)
      · intro hset
        exact absurd (hlive.symm.trans hset) (by simp)
    | closeOn i hlive hopen hi =>
      refine ⟨hz, hcap, hmono, ?_, hpre, hcons, hbr, hcoop⟩
      intro j hj
      simp only [Option.some.injEq] at hj
      subst hj
      exact hi
    | settleSplit i hlive hclosing hlatest =>
      have hbi : s.balOf i ≤ D := hcap i
      refine ⟨hz, hcap, hmono, hcl, ?_, ?_, ?_, ?_⟩
      · intro hf
        exact absurd hf (by simp)
      · intro _
        show (D - s.balOf i) + s.balOf i = D
        omega
      · intro _
        subst hlatest
        exact ⟨le_refl _, hbi⟩
      · intro _ _
        subst hlatest
        exact ⟨rfl, rfl⟩
    | challenge i hlive hclosing hstale =>
      refine ⟨hz, hcap, hmono, hcl, ?_, ?_, ?_, ?_⟩
      · intro hf
        exact absurd hf (by simp)
      · intro _
        show (0 : ℕ) + D = D
        omega
      · intro _
        exact ⟨hcap s.len, le_refl D⟩
      · intro _ hf
        exact absurd hf (by simp)
    | timeoutForfeit hlive hopen =>
      refine ⟨hz, hcap, hmono, hcl, ?_, ?_, ?_, ?_⟩
      · intro hf
        exact absurd hf (by simp)
      · intro _
        show (0 : ℕ) + D = D
        omega
      · intro _
        exact ⟨hcap s.len, le_refl D⟩
      · intro _ hf
        exact absurd hf (by simp)

/-- **No overspend** (design doc "Safety": `new_balance ≤ D` in each payment
proof "prevents Alice from paying Bob past the deposit and then recovering
it"). On every reachable state, every committed balance and Bob's actual
settlement payout are at most the deposit `D`. -/
theorem chain_no_overspend {D : ℕ} {s : St} (h : Reach D s) :
    s.bobPay ≤ D ∧ ∀ i, s.balOf i ≤ D := by
  obtain ⟨-, hcap, -, -, hpre, -, hbr, -⟩ := reach_inv h
  refine ⟨?_, hcap⟩
  rcases hb : s.settled with _ | _
  · exact (hpre hb).2 ▸ Nat.zero_le D
  · exact (hbr hb).2

/-- **Bob never loses** (design doc "Payment-channel safety": "Bob never
loses money he has earned. His worst case is receiving the entire deposit
(≥ what he's owed)"). On every settled terminal state, Bob's payout is at
least the balance of the latest state he countersigned: the honest close pays
it exactly, a challenged stale close and the timeout path pay the whole
deposit `D ≥ earned`. -/
theorem bob_never_loses {D : ℕ} {s : St} (h : Reach D s)
    (hset : s.settled = true) : s.earned ≤ s.bobPay :=
  ((reach_inv h).2.2.2.2.2.2.1 hset).1

/-- **Cooperative settlement is exact** (design doc "Safety": "honest close →
his exact balance"). An unforfeited settlement pays Bob exactly the latest
countersigned balance and refunds Alice exactly the remainder. -/
theorem honest_close_exact {D : ℕ} {s : St} (h : Reach D s)
    (hset : s.settled = true) (hf : s.forfeited = false) :
    s.bobPay = s.earned ∧ s.alicePay = D - s.earned :=
  (reach_inv h).2.2.2.2.2.2.2 hset hf

/-- **Conservation** (idealized-ledger accounting). Every settled channel
splits exactly the deposit `D` between Alice and Bob — cooperative split,
challenged forfeit, and timeout alike. -/
theorem conservation {D : ℕ} {s : St} (h : Reach D s)
    (hset : s.settled = true) : s.alicePay + s.bobPay = D :=
  (reach_inv h).2.2.2.2.2.1 hset

/-- **Alice refund liveness** (design doc "Liveness for Alice": "If Bob never
signed anything, Alice can unilaterally recover her full deposit"). From any
reachable live state in which Bob countersigned nothing (`len = 0`), Alice
can drive the channel — close on the genesis, let the window expire — to a
settled state paying her exactly `D` and Bob `0`. Nothing here needs Bob's
cooperation: `closeOn` and `settleSplit` are Alice- and clock-moves. -/
theorem alice_refund_liveness {D : ℕ} {s : St} (h : Reach D s)
    (hlen : s.len = 0) (hlive : s.settled = false)
    (hopen : s.closing = none) :
    ∃ s', Reach D s' ∧ s'.settled = true ∧
      s'.alicePay = D ∧ s'.bobPay = 0 := by
  obtain ⟨hz, -, -, -, -, -, -, -⟩ := reach_inv h
  refine ⟨_, Reach.step (Reach.step h
    (Step.closeOn s 0 hlive hopen (by omega)))
    (Step.settleSplit _ 0 hlive rfl (by simpa using hlen.symm)), rfl, ?_, ?_⟩
  · show D - s.balOf 0 = D
    rw [hz]
    omega
  · show s.balOf 0 = 0
    exact hz

/-- **No overpay recovery** (optional corollary of the cap invariant): the
`new_balance ≤ D` guard means no state Alice can create — hence no honest
close — pays Bob more than `D`. Falls out of `chain_no_overspend`. -/
theorem no_overpay_recovery {D : ℕ} {s : St} (h : Reach D s) (i : ℕ) :
    s.balOf i ≤ D :=
  (chain_no_overspend h).2 i

end Zkpc.Chain

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.chain_no_overspend
#print axioms Zkpc.Chain.bob_never_loses
#print axioms Zkpc.Chain.honest_close_exact
#print axioms Zkpc.Chain.conservation
#print axioms Zkpc.Chain.alice_refund_liveness
#print axioms Zkpc.Chain.no_overpay_recovery
