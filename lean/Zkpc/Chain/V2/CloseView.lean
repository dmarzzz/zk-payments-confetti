import Zkpc.Chain.Anonymity

/-!
# Signed-close view unlinkability (ROADMAP obligation 4, stage 1)

Spec-v2 §4 [R1] claims a fully countersigned honest close is
**attribution-free**: nothing it publishes lets Bob link the close to any
payment message he holds. This module proves that claim for the two-channel
session view, in the exact ideal model and Class B style of
`Zkpc/Chain/Anonymity.lean` (lazy-RO fresh-uniform chain slots, perfectly
hiding one-time-mask commitments, proof objects outside the view) — and it
*found a definitional bug on the way*: the round-1 draft published the
closed commitment `C_x`, which Bob (its countersigner) can match against
his store, attributing the tip message. The theorem below is provable only
for the repaired close (Spec-v2 §4 [R2, F-R2-1]): a signed close publishes
`(bal, N_{x+1})` and proves knowledge of a signed opening, keeping the
commitment a private witness.

## The game

Two channels, one countersigned payment each, equal public price `δ` and
equal split (equal-δ session form: unequal splits are the conceded
close-split disclosure, Spec-v2 §8 leak 3 — the theorem isolates the
*linkage* content beyond that concession). A hidden bit selects which
channel then closes on its signed tip; the close view is the public split
together with the opened next-nullifier. Bob sees both payment messages
and the close view.

`signed_close_anonymity`: advantage exactly `0`. The opened next-nullifier
is a fresh chain slot no message revealed, and the closing state's
commitment stays hidden behind its one-time mask, so the close view is
distributionally independent of which channel it settles — the [R1]
mode-dependent exhibit-set design (signed closes exhibit no parent-reveal)
stated as a theorem.

Not covered here (later stages of obligation 4): adaptive adversaries with
oracle access, session vectors `q > 2`, countersignature-withholding as a
charged abort lever, the ghost-close view (which *is* attributed, by
design — Spec-v2 §8 leak 1), and the full calibration battery.
-/

open OracleSpec OracleComp

namespace Zkpc.Chain.V2

open Zkpc.Chain (PayMsg)

variable {F : Type} [AddGroup F] [SampleableType F]

/-- The public view of a signed tip close after the F-R2-1 repair: the
split in the clear and the opened committed next-nullifier. The commitment
and countersignature are proof witnesses, not view components. -/
structure CloseMsg (F : Type) where
  /-- the closed state's balance, published at settlement (base protocol) -/
  split : F
  /-- the opened committed next-nullifier `N_{x+1}` -/
  opened : F

/-- World `true`: channels A and B each make one countersigned payment of
public price `δ`; channel A closes on its signed tip. Flat program; binder
order chosen for the coupling proof. -/
def closeViewA (δ : F) : ProbComp (PayMsg F × PayMsg F × CloseMsg F) := do
  let n₀ ← ($ᵗ F)
  let m₀ ← ($ᵗ F)
  let nA ← ($ᵗ F)
  let rB ← ($ᵗ F)
  let rN ← ($ᵗ F)
  let sB ← ($ᵗ F)
  let nB ← ($ᵗ F)
  let sN ← ($ᵗ F)
  pure (⟨n₀, rB + (0 + δ), rN + nA, δ⟩, ⟨m₀, sB + (0 + δ), sN + nB, δ⟩,
    ⟨0 + δ, nA⟩)

/-- World `false`: the same two channels; channel B closes instead. -/
def closeViewB (δ : F) : ProbComp (PayMsg F × PayMsg F × CloseMsg F) := do
  let n₀ ← ($ᵗ F)
  let m₀ ← ($ᵗ F)
  let nB ← ($ᵗ F)
  let rB ← ($ᵗ F)
  let nA ← ($ᵗ F)
  let rN ← ($ᵗ F)
  let sB ← ($ᵗ F)
  let sN ← ($ᵗ F)
  pure (⟨n₀, rB + (0 + δ), rN + nA, δ⟩, ⟨m₀, sB + (0 + δ), sN + nB, δ⟩,
    ⟨0 + δ, nB⟩)

/-- The canonical fresh view: revealed nullifiers, masked commitment slots,
and the opened close nullifier are all independent uniforms; only the
public `δ`-derived values carry structure. -/
def closeFresh (δ : F) : ProbComp (PayMsg F × PayMsg F × CloseMsg F) := do
  let n₀ ← ($ᵗ F)
  let m₀ ← ($ᵗ F)
  let y ← ($ᵗ F)
  let x₁ ← ($ᵗ F)
  let x₂ ← ($ᵗ F)
  let x₃ ← ($ᵗ F)
  let x₄ ← ($ᵗ F)
  pure (⟨n₀, x₁, x₂, δ⟩, ⟨m₀, x₃, x₄, δ⟩, ⟨0 + δ, y⟩)

/-- Shared tail: with everything else fixed, the never-revealed committed
next-nullifier of the *unclosed* channel is masked once and integrates
out. -/
private lemma evalDist_closeTail (m₁ : PayMsg F) (r₂ x₃ δ y : F) :
    𝒟[(do
      let nB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure (m₁, (⟨r₂, x₃, sN + nB, δ⟩ : PayMsg F), (⟨0 + δ, y⟩ : CloseMsg F)) :
        ProbComp (PayMsg F × PayMsg F × CloseMsg F))] =
    𝒟[(do
      let x₄ ← ($ᵗ F)
      pure (m₁, (⟨r₂, x₃, x₄, δ⟩ : PayMsg F), (⟨0 + δ, y⟩ : CloseMsg F)) :
        ProbComp (PayMsg F × PayMsg F × CloseMsg F))] := by
  refine Eq.trans (evalDist_bind_congr' ($ᵗ F) fun nB => ?_)
    (OracleComp.DeferredSampling.evalDist_bind_const_neverFails ($ᵗ F)
      (probFailure_uniformSample F) _)
  exact evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id nB
    (fun x₄ => pure (m₁, (⟨r₂, x₃, x₄, δ⟩ : PayMsg F),
      (⟨0 + δ, y⟩ : CloseMsg F)))

/-- **World A coupling**: the close-A view is the canonical fresh view. -/
lemma evalDist_closeViewA (δ : F) :
    𝒟[closeViewA δ] = 𝒟[closeFresh δ] := by
  unfold closeViewA closeFresh
  refine evalDist_bind_congr' ($ᵗ F) fun n₀ => ?_
  refine evalDist_bind_congr' ($ᵗ F) fun m₀ => ?_
  refine evalDist_bind_congr' ($ᵗ F) fun nA => ?_
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id (0 + δ) (fun x₁ => do
      let rN ← ($ᵗ F)
      let sB ← ($ᵗ F)
      let nB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure ((⟨n₀, x₁, rN + nA, δ⟩ : PayMsg F),
            (⟨m₀, sB + (0 + δ), sN + nB, δ⟩ : PayMsg F),
            (⟨0 + δ, nA⟩ : CloseMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun x₁ => ?_
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id nA (fun x₂ => do
      let sB ← ($ᵗ F)
      let nB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure ((⟨n₀, x₁, x₂, δ⟩ : PayMsg F),
            (⟨m₀, sB + (0 + δ), sN + nB, δ⟩ : PayMsg F),
            (⟨0 + δ, nA⟩ : CloseMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun x₂ => ?_
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id (0 + δ) (fun x₃ => do
      let nB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure ((⟨n₀, x₁, x₂, δ⟩ : PayMsg F),
            (⟨m₀, x₃, sN + nB, δ⟩ : PayMsg F),
            (⟨0 + δ, nA⟩ : CloseMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun x₃ => ?_
  exact evalDist_closeTail (⟨n₀, x₁, x₂, δ⟩ : PayMsg F) m₀ x₃ δ nA

/-- **World B coupling**: the close-B view is the same canonical fresh
view. -/
lemma evalDist_closeViewB (δ : F) :
    𝒟[closeViewB δ] = 𝒟[closeFresh δ] := by
  unfold closeViewB closeFresh
  refine evalDist_bind_congr' ($ᵗ F) fun n₀ => ?_
  refine evalDist_bind_congr' ($ᵗ F) fun m₀ => ?_
  refine evalDist_bind_congr' ($ᵗ F) fun nB => ?_
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id (0 + δ) (fun x₁ => do
      let nA ← ($ᵗ F)
      let rN ← ($ᵗ F)
      let sB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure ((⟨n₀, x₁, rN + nA, δ⟩ : PayMsg F),
            (⟨m₀, sB + (0 + δ), sN + nB, δ⟩ : PayMsg F),
            (⟨0 + δ, nB⟩ : CloseMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun x₁ => ?_
  refine Eq.trans (evalDist_bind_congr' ($ᵗ F) fun nA => ?_)
    (OracleComp.DeferredSampling.evalDist_bind_const_neverFails ($ᵗ F)
      (probFailure_uniformSample F) _)
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id nA (fun x₂ => do
      let sB ← ($ᵗ F)
      let sN ← ($ᵗ F)
      pure ((⟨n₀, x₁, x₂, δ⟩ : PayMsg F),
            (⟨m₀, sB + (0 + δ), sN + nB, δ⟩ : PayMsg F),
            (⟨0 + δ, nB⟩ : CloseMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun x₂ => ?_
  refine Eq.trans (evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id (0 + δ) (fun x₃ => do
      let sN ← ($ᵗ F)
      pure ((⟨n₀, x₁, x₂, δ⟩ : PayMsg F),
            (⟨m₀, x₃, sN + nB, δ⟩ : PayMsg F),
            (⟨0 + δ, nB⟩ : CloseMsg F)))) ?_
  refine evalDist_bind_congr' ($ᵗ F) fun x₃ => ?_
  exact evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id nB
    (fun x₄ => pure ((⟨n₀, x₁, x₂, δ⟩ : PayMsg F),
      (⟨m₀, x₃, x₄, δ⟩ : PayMsg F), (⟨0 + δ, nB⟩ : CloseMsg F)))

/-- The two worlds the hidden bit selects between. -/
def closePairView (b : Bool) (δ : F) :
    ProbComp (PayMsg F × PayMsg F × CloseMsg F) :=
  if b then closeViewA δ else closeViewB δ

/-- The close-attribution game: Bob sees both payment messages and the
signed-tip close view of one of the two channels; he guesses which. -/
def closeAnonGame
    (A : PayMsg F × PayMsg F × CloseMsg F → ProbComp Bool) (δ : F) :
    ProbComp Bool := do
  let b ← ($ᵗ Bool)
  let b' ← (do
    let v ← closePairView b δ
    A v)
  pure (decide (b = b'))

/-- Advantage in the `|Pr[b' = b] − 1/2|` form. -/
noncomputable def closeAnonAdvantage
    (A : PayMsg F × PayMsg F × CloseMsg F → ProbComp Bool) (δ : F) : ℝ :=
  Zkpc.Games.guessGap (closeAnonGame A δ)

/-- **Signed-close unlinkability (advantage exactly 0)** — Spec-v2 §4's
attribution-freeness [R1] as a theorem, provable because of the F-R2-1
repair: for every adversary, the equal-split close-attribution game is a
coin toss. -/
theorem signed_close_anonymity
    (A : PayMsg F × PayMsg F × CloseMsg F → ProbComp Bool) (δ : F) :
    closeAnonAdvantage A δ = 0 := by
  have hview : 𝒟[(do let v ← closePairView true δ; A v : ProbComp Bool)] =
      𝒟[(do let v ← closePairView false δ; A v : ProbComp Bool)] := by
    simp only [closePairView, if_true, Bool.false_eq_true, if_false]
    rw [evalDist_bind, evalDist_bind, evalDist_closeViewA,
      evalDist_closeViewB]
  have hhalf : Pr[= true | closeAnonGame A δ] = 1 / 2 := by
    unfold closeAnonGame
    exact probOutput_decide_eq_uniformBool_half
      (fun b => do let v ← closePairView b δ; A v) hview
  unfold closeAnonAdvantage Zkpc.Games.guessGap
  rw [hhalf]
  norm_num

end Zkpc.Chain.V2

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.V2.evalDist_closeViewA
#print axioms Zkpc.Chain.V2.evalDist_closeViewB
#print axioms Zkpc.Chain.V2.signed_close_anonymity
