import Zkpc.Chain.Anonymity

/-!
# Anonymity calibration battery for the chain view (obligation 4, anti-vacuity)

The anti-vacuity discipline of `Zkpc/Games/Calibration.lean`, ported to the
two-payment chain anonymity game of `Zkpc/Chain/Anonymity.lean`: the game
must *catch* a scheme that leaks linkage, or the advantage-0 theorem
`chain_two_payment_anonymity` would be vacuous. A calibration is a broken
scheme together with a witness that its two worlds are distinguishable —
here, distributional separation (`𝒟[same] ≠ 𝒟[cross]`), the exact negation
of the real scheme's coupling `evalDist_sameChain = evalDist_crossChain`.

**The must-catch leak: linkable nullifiers.** The real `payStep`
(`Zkpc/Chain/Anonymity.lean`) commits to the fresh next-nullifier under a
one-time mask (`nulCom = rNul + nNext`), which is what hides the chain
link. The broken variant drops the mask (`nulCom = nNext`, the raw value).
Then in the same-chain world message 2's revealed nullifier equals message
1's `nulCom` *deterministically* (both are the shared chain value), while in
the cross-chain world they are independent. The distinguishing event
`m₁.nulCom = m₂.reveal` therefore holds with certainty in one world and not
the other, so the two world-distributions differ: the game catches the leak.

`linkable_leak_detected`: `𝒟[linkableSame] ≠ 𝒟[linkableCross]`, needing only
`Nontrivial F` (two distinct nullifier values, so "cross is not always on
the diagonal" bites). The must-pass counterpart is the existing
`chain_two_payment_anonymity` (advantage 0 for the masked scheme). Together
they are the calibration: the game passes the hiding scheme and separates
the leaking one.
-/

open OracleSpec OracleComp

namespace Zkpc.Chain.V2

open Zkpc.Chain (PayMsg)

variable {F : Type} [AddGroup F] [SampleableType F] [DecidableEq F]

/-- Broken same-chain world: two consecutive payments with **linkable**
nullifiers — the fresh next-nullifier is committed with the identity mask
(`nulCom = n₁`, raw), so message 2's reveal `n₁` equals message 1's
`nulCom`. Otherwise identical to `Zkpc.Chain.sameChain`. -/
def linkableSame (δ₁ δ₂ : F) : ProbComp (PayMsg F × PayMsg F) := do
  let n₀ ← ($ᵗ F)
  let n₁ ← ($ᵗ F)
  let rB ← ($ᵗ F)
  let n₂ ← ($ᵗ F)
  let sB ← ($ᵗ F)
  pure ((⟨n₀, rB + (0 + δ₁), n₁, δ₁⟩ : PayMsg F),
        (⟨n₁, sB + (0 + δ₁ + δ₂), n₂, δ₂⟩ : PayMsg F))

/-- Broken cross-chain world: one payment on each of two independent
channels, same linkable (unmasked) next-nullifier. Message 1's `nulCom` is
`n₁`, message 2's reveal is the *other* channel's genesis `n₀'` —
independent. -/
def linkableCross (δ₁ δ₂ : F) : ProbComp (PayMsg F × PayMsg F) := do
  let n₀ ← ($ᵗ F)
  let n₀' ← ($ᵗ F)
  let n₁ ← ($ᵗ F)
  let rB ← ($ᵗ F)
  let n₂ ← ($ᵗ F)
  let sB ← ($ᵗ F)
  pure ((⟨n₀, rB + (0 + δ₁), n₁, δ₁⟩ : PayMsg F),
        (⟨n₀', sB + (0 + δ₂), n₂, δ₂⟩ : PayMsg F))

/-- The distinguishing event: message 1's next-nullifier commitment equals
message 2's revealed nullifier. In the masked (real) scheme a coincidence;
with linkable nullifiers it is the chain link, exposed. -/
def linkEvent (p : PayMsg F × PayMsg F) : Prop := p.1.nulCom = p.2.reveal

instance : DecidablePred (linkEvent (F := F)) :=
  fun p => decEq p.1.nulCom p.2.reveal

/-- In the broken same-chain world the link event is **certain**: message 2
reveals exactly what message 1 committed (both are `n₁`). -/
theorem probEvent_linkableSame (δ₁ δ₂ : F) :
    Pr[linkEvent | linkableSame δ₁ δ₂] = 1 := by
  rw [probEvent_eq_one_iff]
  refine ⟨by simp [linkableSame], ?_⟩
  intro x hx
  simp only [linkableSame, mem_support_bind_iff, mem_support_uniformSample,
    support_pure, Set.mem_singleton_iff, true_and, exists_const] at hx
  obtain ⟨n₀, n₁, rB, n₂, sB, rfl⟩ := hx
  rfl

/-- In the broken cross-chain world the link event is **not** certain: the
two nullifiers are independent uniforms, and (given at least two field
elements) there is a support run on which they differ. -/
theorem probEvent_linkableCross_ne_one [Nontrivial F] (δ₁ δ₂ : F) :
    Pr[linkEvent | linkableCross δ₁ δ₂] ≠ 1 := by
  intro hcontra
  rw [probEvent_eq_one_iff] at hcontra
  obtain ⟨-, hall⟩ := hcontra
  obtain ⟨u, v, huv⟩ := exists_pair_ne F
  have hmem : ((⟨0, (0 : F) + (0 + δ₁), v, δ₁⟩ : PayMsg F),
      (⟨u, (0 : F) + (0 + δ₂), 0, δ₂⟩ : PayMsg F))
      ∈ support (linkableCross δ₁ δ₂) := by
    simp only [linkableCross, mem_support_bind_iff, mem_support_uniformSample,
      support_pure, Set.mem_singleton_iff, true_and]
    exact ⟨0, u, v, 0, 0, 0, rfl⟩
  -- linkEvent on this run is `v = u`, contradicting `u ≠ v`
  exact huv (hall _ hmem).symm

/-- **The game catches the linkable-nullifier leak** (obligation 4
anti-vacuity): the broken scheme's two worlds are distributionally distinct,
so *some* adversary distinguishes them — the exact negation of the real
scheme's coupling `Zkpc.Chain.evalDist_sameChain =
Zkpc.Chain.evalDist_crossChain`. The must-pass counterpart (advantage 0 for
the masked scheme) is `Zkpc.Chain.chain_two_payment_anonymity`. -/
theorem linkable_leak_detected [Nontrivial F] (δ₁ δ₂ : F) :
    𝒟[linkableSame δ₁ δ₂] ≠ 𝒟[linkableCross δ₁ δ₂] := by
  intro h
  have hcontra : Pr[linkEvent | linkableSame δ₁ δ₂]
      = Pr[linkEvent | linkableCross δ₁ δ₂] := by
    simp only [probEvent, h]
  rw [probEvent_linkableSame] at hcontra
  exact probEvent_linkableCross_ne_one δ₁ δ₂ hcontra.symm

end Zkpc.Chain.V2

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.V2.probEvent_linkableSame
#print axioms Zkpc.Chain.V2.probEvent_linkableCross_ne_one
#print axioms Zkpc.Chain.V2.linkable_leak_detected
