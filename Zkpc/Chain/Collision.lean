import Zkpc.Chain.State

/-!
# Nullifier-chain channel: the stale-close collision mechanism

The algebra behind the challenge rule of
`PROTOCOL.md` ("How it works" /
"Stale-close detection"): each state `i` commits (hiding) to the next
nullifier `N_{i+1}`; message `j ≥ 1` (the payment creating state `j`)
*reveals* `N_j`, the nullifier its parent committed to; closing state `i`
opens `N_{i+1}` on chain. Stale-close detection is **by collision, not by
Bob finding the latest state** (which anonymity prevents): if Alice closes a
non-final state, the successor message already revealed the very nullifier
the close opens, so an honest Bob — who keeps every message he countersigned —
holds the colliding evidence and challenges. The genesis is just a state that
commits to `N₁`, so a refund-close after a payment collides with message 1:
"Uniform rule, no special case."

## Modeling conventions

* **Hashes as a lazily-sampled random oracle.** The chain
  `N_{j+1} = H(N_j, c)` is abstracted to a sequence `nul : ℕ → N` of
  nullifier values (`nul j` is the design doc's `N_j`). The single property
  the mechanism needs from the random oracle is **collision-freedom along the
  chain**, carried here as the explicit hypothesis
  `Function.Injective nul`. In the lazy-RO model each fresh slot
  `H(N_j, c)` is a fresh uniform sample, so a collision among the first `n`
  chain links occurs with probability at most `n²/|N|`; the theorems below
  take the collision-free event as a hypothesis rather than folding a
  negligible term into every statement (the same idealization the
  `Zkpc/Games` layer makes explicit per instance).
* The state-machine bridge theorems work over `Zkpc.Chain.St` from
  `Zkpc/Chain/State.lean` and justify its `settleSplit`/`challenge` guards.
-/

namespace Zkpc.Chain

variable {N : Type}

/-- The nullifier opened on chain by closing state `i`: the committed
next-nullifier `N_{i+1}` (design doc "Close": "She withdraws by opening the
committed-next-nullifier of the state she closes on"). For `i = 0` this is
the genesis refund opening `N₁`. -/
def opensAtClose (nul : ℕ → N) (i : ℕ) : N := nul (i + 1)

/-- The nullifiers an honest Bob has seen revealed after countersigning
`len` payments: message `j` (creating state `j`, `1 ≤ j ≤ len`) revealed
`N_j` (design doc "Payment": "a message revealing `N_{i+1}`, the nullifier
the prior state committed to"). -/
def Revealed (nul : ℕ → N) (len : ℕ) (x : N) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ len ∧ nul j = x

/-- **Stale-close detectability (completeness of the challenge).** If Alice
closes state `i` while Bob countersigned `len > i` states, the nullifier her
close opens — `N_{i+1}` — is exactly the one message `i+1` revealed, so
honest Bob holds a colliding message and the design doc's challenge predicate
("Bob challenges if he holds a message that revealed `N`") fires. The
genesis-refund-after-payment case is the instance `i = 0`: closing the
genesis opens `N₁`, which message 1 revealed — the uniform rule, no special
case. No random-oracle property is needed for this direction: the collision
is an equality of chain positions. -/
theorem stale_close_detectable (nul : ℕ → N) {i len : ℕ} (h : i < len) :
    Revealed nul len (opensAtClose nul i) :=
  ⟨i + 1, by omega, by omega, rfl⟩

/-- **Honest-close exculpability (soundness of the challenge).** Closing the
latest countersigned state `len` opens `N_{len+1}`, a nullifier no message
ever revealed (messages revealed only `N₁ … N_len`), so no valid challenge
exists and an honest Alice is never slashed. This is the direction that
consumes the random-oracle idealization: chain collision-freedom
(`Function.Injective nul`) guarantees `N_{len+1}` differs from every earlier
chain value. -/
theorem honest_close_unchallengeable (nul : ℕ → N)
    (hinj : Function.Injective nul) (len : ℕ) :
    ¬ Revealed nul len (opensAtClose nul len) := by
  rintro ⟨j, h1, h2, hj⟩
  have := hinj hj
  omega

/-- **The challenge predicate is exact.** For any held state `i ≤ len`, the
nullifier opened by closing `i` collides with a revealed nullifier **iff**
the close is stale (`i < len`). Packages the two directions above; this
equivalence is what justifies transcribing the design doc's evidence-based
challenge rule as the index guard `i < len` in `Zkpc.Chain.Step`. -/
theorem collision_iff_stale (nul : ℕ → N) (hinj : Function.Injective nul)
    {i len : ℕ} (_hi : i ≤ len) :
    Revealed nul len (opensAtClose nul i) ↔ i < len := by
  constructor
  · rintro ⟨j, h1, h2, hj⟩
    have := hinj hj
    omega
  · exact stale_close_detectable nul

/-! ## Bridge to the settlement state machine

The two theorems below connect the collision algebra to the enabledness of
the `challenge` action in `Zkpc.Chain.Step`, discharging the guard
justification promised in `Zkpc/Chain/State.lean`. -/

/-- **Machine bridge, stale side.** In any reachable live state whose
challenge window is running on a stale index (`closing = some i`, `i < len`),
honest Bob's collision evidence exists (`stale_close_detectable`) and the
`challenge` transition is enabled: the whole deposit is awardable to Bob. -/
theorem challenge_enabled_of_stale {D : ℕ} {s : St} (nul : ℕ → N)
    (_hreach : Reach D s) (hlive : s.settled = false) {i : ℕ}
    (hcl : s.closing = some i) (hstale : i < s.len) :
    Revealed nul s.len (opensAtClose nul i) ∧
      ∃ s', Step D s .challenge s' :=
  ⟨stale_close_detectable nul hstale,
    ⟨_, Step.challenge s i hlive hcl hstale⟩⟩

/-- **Machine bridge, honest side.** In any reachable state closing on the
*latest* countersigned state, no revealed nullifier collides with the opened
one (under chain collision-freedom), so no challenge evidence exists — and
correspondingly no `challenge` transition is enabled: an honest closer is
never slashed, and only the cooperative `settleSplit` can settle her close. -/
theorem honest_close_never_slashed {D : ℕ} {s : St} (nul : ℕ → N)
    (hinj : Function.Injective nul) (_hreach : Reach D s) {i : ℕ}
    (hcl : s.closing = some i) (hlatest : i = s.len) :
    ¬ Revealed nul s.len (opensAtClose nul i) ∧
      ¬ ∃ s', Step D s .challenge s' := by
  subst hlatest
  refine ⟨honest_close_unchallengeable nul hinj s.len, ?_⟩
  rintro ⟨s', hstep⟩
  cases hstep with
  | challenge j hlive hcl' hstale =>
    rw [hcl] at hcl'
    simp only [Option.some.injEq] at hcl'
    omega

end Zkpc.Chain

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.stale_close_detectable
#print axioms Zkpc.Chain.honest_close_unchallengeable
#print axioms Zkpc.Chain.collision_iff_stale
#print axioms Zkpc.Chain.challenge_enabled_of_stale
#print axioms Zkpc.Chain.honest_close_never_slashed
