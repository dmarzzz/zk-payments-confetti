import VCVio
import Zkpc.Games.Framework

/-!
# Nullifier-chain channel: per-request anonymity (Class B)

The design doc (`research_knowledge/vitalik-nullifier-chain-channel.md`,
"Goals" / "Privacy properties") asks for **per-request anonymity**: Bob must
not learn that two payments came from the same Alice, nor that they belong to
the same channel — he learns only "someone paid me δ". This module states and
proves that property for the ideal-model wire view of two payments, in the
Class B style of `Zkpc/Games/Coupling.lean` / `Zkpc/Games/T4.lean`: a
two-world hidden-bit game whose advantage is exactly `0`.

## The ideal model (recorded per the repo's conventions)

A payment message (design doc "Payment") carries: the **revealed nullifier**
(the value `N_{i+1}` the parent state committed to), a **hiding commitment to
the new balance**, a **hiding commitment to the fresh next nullifier**
`N_{i+2}`, and the **public δ**. The idealizations:

* **Hashes as a lazily-sampled random oracle.** Every chain value
  `N_{j+1} = H(N_j, c)` lives at a slot keyed by the payer's secret `c`,
  which Bob never queries (he does not know `c`); a lazily-sampled RO answers
  each such fresh slot with a fresh uniform field element. So the honest
  generator `payStep` samples the next nullifier as `$ᵗ F`. This is the same
  fresh-slot idealization the `flatInstance` of
  `Zkpc/Games/FlatInstance.lean` records (its `prfRomIdealization` ledger
  entry in `Zkpc/Games/T4.lean`).
* **Hiding commitments as one-time additive masks.** `Com(v; r) = r + v`
  with fresh uniform `r`, the perfectly-hiding reference commitment of
  `Zkpc/Crypto/MaskedEncryption.lean` (translation invariance of the uniform
  distribution is the hiding property). A deployed RO-based commitment pays
  its own binding/hiding bound in place of this exact identity.
* **The ZK proof is not part of the view.** As in `flatInstance`, the π-free
  view is the simulation; `Zkpc/Games/FullTicketInstance.lean` shows how a
  proof-bearing view bridges back at zero loss for an ideal proof encoding.

## What the theorem does and does not cover

`chain_two_payment_anonymity` says: Bob's view of two payment messages is
**identically distributed** whether they are consecutive payments on one
chain (so the second message reveals exactly the nullifier the first message
committed to) or single payments on two independently opened channels — for
*every* adversary, advantage exactly `0`. Together with the "same-sender
across two channels" reading (the `b = false` world is literally two separate
channels), this is the design doc's "Bob cannot link two payments to the same
sender or channel".

Deliberately **not** covered (the design doc's own stated leaks/boundaries):
the δ values are public by design and are equal across the two worlds here —
correlating *distinct* payments by their δ values or by timing/network
metadata is out of scope; deposit-amount (`D`), close-amount, and open/close
footprint privacy are leaked at the channel boundary in the base protocol
(see the doc's "Does not have" list and its shielded-pool extension);
recipient anonymity is explicitly out of scope (Bob is named on chain).
-/

open OracleSpec OracleComp

namespace Zkpc.Chain

variable {F : Type} [AddGroup F] [SampleableType F]

/-- The adversary-visible payment message (design doc "Payment"): revealed
parent-committed nullifier, hiding commitment to the new balance, hiding
commitment to the fresh next nullifier, public δ. -/
structure PayMsg (F : Type) where
  /-- the nullifier `N_{i+1}` the parent state committed to, now revealed -/
  reveal : F
  /-- hiding commitment to the new balance -/
  balCom : F
  /-- hiding commitment to the fresh next nullifier `N_{i+2}` -/
  nulCom : F
  /-- the public per-request price -/
  delta : F

/-- Alice's private per-chain state: the next nullifier the current state
committed to (hidden from Bob inside a commitment) and the current balance. -/
structure ChainSt (F : Type) where
  /-- committed next nullifier of the current state -/
  next : F
  /-- current balance -/
  bal : F

/-- **Open** (design doc): the genesis commits (hiding) to `N₁` at balance
`0`. In the lazy-RO model the fresh chain slot `N₁` is a fresh uniform
sample. -/
def openChain : ProbComp (ChainSt F) := do
  let n ← ($ᵗ F)
  pure ⟨n, 0⟩

/-- **One honest payment** (design doc "Payment"): reveal the parent's
committed nullifier `st.next`; commit (mask `rBal`) to the new balance
`st.bal + δ`; sample the fresh next chain nullifier (lazy RO) and commit to
it (mask `rNul`); δ is public. Returns the message and the successor chain
state. -/
def payStep (st : ChainSt F) (δ : F) : ProbComp (PayMsg F × ChainSt F) := do
  let nNext ← ($ᵗ F)
  let rBal ← ($ᵗ F)
  let rNul ← ($ᵗ F)
  pure (⟨st.next, rBal + (st.bal + δ), rNul + nNext, δ⟩, ⟨nNext, st.bal + δ⟩)

/-- **World `true`**: two consecutive payments on one chain — the second
message reveals exactly the nullifier the first message committed to, and the
balance accumulates. Written flat; `sameChain_eq_comp` checks it is the
composition of `openChain` and two `payStep`s. -/
def sameChain (δ₁ δ₂ : F) : ProbComp (PayMsg F × PayMsg F) := do
  let n₀ ← ($ᵗ F)
  let n₁ ← ($ᵗ F)
  let rB ← ($ᵗ F)
  let rN ← ($ᵗ F)
  let n₂ ← ($ᵗ F)
  let sB ← ($ᵗ F)
  let sN ← ($ᵗ F)
  pure ((⟨n₀, rB + (0 + δ₁), rN + n₁, δ₁⟩ : PayMsg F),
        (⟨n₁, sB + (0 + δ₁ + δ₂), sN + n₂, δ₂⟩ : PayMsg F))

/-- **World `false`**: one payment on each of two independently opened
chains (equivalently: two different senders). Written flat;
`crossChain_eq_comp` checks it is the composition of two `openChain`s and
one `payStep` each. -/
def crossChain (δ₁ δ₂ : F) : ProbComp (PayMsg F × PayMsg F) := do
  let n₀ ← ($ᵗ F)
  let n₀' ← ($ᵗ F)
  let n₁ ← ($ᵗ F)
  let rB ← ($ᵗ F)
  let rN ← ($ᵗ F)
  let n₂ ← ($ᵗ F)
  let sB ← ($ᵗ F)
  let sN ← ($ᵗ F)
  pure ((⟨n₀, rB + (0 + δ₁), rN + n₁, δ₁⟩ : PayMsg F),
        (⟨n₀', sB + (0 + δ₂), sN + n₂, δ₂⟩ : PayMsg F))

/-- `sameChain` is the honest protocol composition: open one channel, make
two consecutive payments, hand Bob the two messages. -/
lemma sameChain_eq_comp (δ₁ δ₂ : F) :
    sameChain δ₁ δ₂ = (do
      let ch₀ ← openChain
      let (m₁, st₁) ← payStep ch₀ δ₁
      let (m₂, _) ← payStep st₁ δ₂
      pure (m₁, m₂)) := by
  simp only [sameChain, openChain, payStep, bind_assoc, pure_bind]

/-- `crossChain` is the honest protocol composition: open two independent
channels, make one payment on each, hand Bob the two messages. -/
lemma crossChain_eq_comp (δ₁ δ₂ : F) :
    crossChain δ₁ δ₂ = (do
      let ch₀ ← openChain
      let ch₁ ← openChain
      let (m₁, _) ← payStep ch₀ δ₁
      let (m₂, _) ← payStep ch₁ δ₂
      pure (m₁, m₂)) := by
  simp only [crossChain, openChain, payStep, bind_assoc, pure_bind]

/-- The canonical fresh view: every non-δ component an independent uniform
sample. Binder order matches the coupling proofs below. -/
def freshPair (δ₁ δ₂ : F) : ProbComp (PayMsg F × PayMsg F) := do
  let a ← ($ᵗ F)
  let d ← ($ᵗ F)
  let b ← ($ᵗ F)
  let c ← ($ᵗ F)
  let e ← ($ᵗ F)
  let f ← ($ᵗ F)
  pure ((⟨a, b, c, δ₁⟩ : PayMsg F), (⟨d, e, f, δ₂⟩ : PayMsg F))

/-- The tail coupling shared by both worlds: for any fixed message-1 fields
and any fixed leftover chain value `n₂`, the second message's two committed
components are fresh-uniform (mask translations), after which `n₂` is unused
and integrates out. -/
private lemma evalDist_tail (m₁ : PayMsg F) (v r₂ δ₂ : F) :
    𝒟[(do
      let n₂ ← ($ᵗ F)
      let sB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure (m₁, (⟨r₂, sB + v, sN + n₂, δ₂⟩ : PayMsg F)) :
        ProbComp (PayMsg F × PayMsg F))] =
    𝒟[(do
      let e ← ($ᵗ F)
      let f ← ($ᵗ F)
      pure (m₁, (⟨r₂, e, f, δ₂⟩ : PayMsg F)) :
        ProbComp (PayMsg F × PayMsg F))] := by
  refine Eq.trans (evalDist_bind_congr' ($ᵗ F) fun n₂ => ?_)
    (OracleComp.DeferredSampling.evalDist_bind_const_neverFails ($ᵗ F) (probFailure_uniformSample F) _)
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id v (fun e => do
      let sN ← ($ᵗ F)
      pure (m₁, (⟨r₂, e, sN + n₂, δ₂⟩ : PayMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun e => ?_
  exact evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id n₂
    (fun f => pure (m₁, (⟨r₂, e, f, δ₂⟩ : PayMsg F)))

/-- **Same-chain coupling**: the two-consecutive-payments view is exactly the
canonical fresh view. Every component Bob sees is either a fresh unqueried
random-oracle output (the revealed nullifiers) or a one-time-masked
commitment, so the chain linkage (message 2 reveals what message 1 committed)
leaves no distributional trace. -/
lemma evalDist_sameChain (δ₁ δ₂ : F) :
    𝒟[sameChain δ₁ δ₂] = 𝒟[freshPair δ₁ δ₂] := by
  unfold sameChain freshPair
  refine evalDist_bind_congr' ($ᵗ F) fun n₀ => ?_
  refine evalDist_bind_congr' ($ᵗ F) fun n₁ => ?_
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id (0 + δ₁) (fun b => do
      let rN ← ($ᵗ F)
      let n₂ ← ($ᵗ F)
      let sB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure ((⟨n₀, b, rN + n₁, δ₁⟩ : PayMsg F),
            (⟨n₁, sB + (0 + δ₁ + δ₂), sN + n₂, δ₂⟩ : PayMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun b => ?_
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id n₁ (fun c => do
      let n₂ ← ($ᵗ F)
      let sB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure ((⟨n₀, b, c, δ₁⟩ : PayMsg F),
            (⟨n₁, sB + (0 + δ₁ + δ₂), sN + n₂, δ₂⟩ : PayMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun c => ?_
  exact evalDist_tail (⟨n₀, b, c, δ₁⟩ : PayMsg F) (0 + δ₁ + δ₂) n₁ δ₂

/-- **Cross-chain coupling**: the two-independent-channels view is exactly
the same canonical fresh view. -/
lemma evalDist_crossChain (δ₁ δ₂ : F) :
    𝒟[crossChain δ₁ δ₂] = 𝒟[freshPair δ₁ δ₂] := by
  unfold crossChain freshPair
  refine evalDist_bind_congr' ($ᵗ F) fun n₀ => ?_
  refine evalDist_bind_congr' ($ᵗ F) fun n₀' => ?_
  refine Eq.trans (evalDist_bind_congr' ($ᵗ F) fun n₁ => ?_)
    (OracleComp.DeferredSampling.evalDist_bind_const_neverFails ($ᵗ F) (probFailure_uniformSample F) _)
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id (0 + δ₁) (fun b => do
      let rN ← ($ᵗ F)
      let n₂ ← ($ᵗ F)
      let sB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure ((⟨n₀, b, rN + n₁, δ₁⟩ : PayMsg F),
            (⟨n₀', sB + (0 + δ₂), sN + n₂, δ₂⟩ : PayMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun b => ?_
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id n₁ (fun c => do
      let n₂ ← ($ᵗ F)
      let sB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure ((⟨n₀, b, c, δ₁⟩ : PayMsg F),
            (⟨n₀', sB + (0 + δ₂), sN + n₂, δ₂⟩ : PayMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun c => ?_
  exact evalDist_tail (⟨n₀, b, c, δ₁⟩ : PayMsg F) (0 + δ₂) n₀' δ₂

/-- The two worlds the hidden bit selects between. -/
def pairView (b : Bool) (δ₁ δ₂ : F) : ProbComp (PayMsg F × PayMsg F) :=
  if b then sameChain δ₁ δ₂ else crossChain δ₁ δ₂

/-- The two-payment linkage game (design doc "Per-request anonymity"): a
hidden bit selects same-chain (consecutive payments, `b = true`) or
different-chains (`b = false`); the adversary — Bob, who sees exactly the
two payment messages with their public δs — outputs a probabilistic guess.
`b`-first sampling as in `Zkpc.Games.unlinkGame`. -/
def anonGame (A : PayMsg F × PayMsg F → ProbComp Bool) (δ₁ δ₂ : F) :
    ProbComp Bool := do
  let b ← ($ᵗ Bool)
  let b' ← (do
    let v ← pairView b δ₁ δ₂
    A v)
  pure (decide (b = b'))

/-- Advantage in Spec.md's `|Pr[b' = b] − 1/2|` form (`Zkpc.Games.guessGap`). -/
noncomputable def anonAdvantage (A : PayMsg F × PayMsg F → ProbComp Bool)
    (δ₁ δ₂ : F) : ℝ :=
  Zkpc.Games.guessGap (anonGame A δ₁ δ₂)

/-- **Per-request anonymity (advantage exactly 0).** For every adversary and
every pair of public prices, the two-payment linkage game is a coin toss:
both worlds' views equal the canonical fresh view (`evalDist_sameChain`,
`evalDist_crossChain`), because unqueried `H(N_i, c)` random-oracle slots are
fresh-uniform and the balance/next-nullifier commitments are perfectly
hiding. This is the design doc's per-request anonymity ("Bob cannot link two
payments to the same sender or channel") for the two-message wire view; see
the module docstring for what is deliberately not covered (public δ
correlation across distinct prices, timing, channel-boundary leaks). -/
theorem chain_two_payment_anonymity (A : PayMsg F × PayMsg F → ProbComp Bool)
    (δ₁ δ₂ : F) : anonAdvantage A δ₁ δ₂ = 0 := by
  have hview : 𝒟[(do let v ← pairView true δ₁ δ₂; A v : ProbComp Bool)] =
      𝒟[(do let v ← pairView false δ₁ δ₂; A v : ProbComp Bool)] := by
    simp only [pairView, if_true, Bool.false_eq_true, if_false]
    rw [evalDist_bind, evalDist_bind, evalDist_sameChain, evalDist_crossChain]
  have hhalf : Pr[= true | anonGame A δ₁ δ₂] = 1 / 2 := by
    unfold anonGame
    exact probOutput_decide_eq_uniformBool_half
      (fun b => do let v ← pairView b δ₁ δ₂; A v) hview
  unfold anonAdvantage Zkpc.Games.guessGap
  rw [hhalf]
  norm_num

end Zkpc.Chain

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.evalDist_sameChain
#print axioms Zkpc.Chain.evalDist_crossChain
#print axioms Zkpc.Chain.chain_two_payment_anonymity
