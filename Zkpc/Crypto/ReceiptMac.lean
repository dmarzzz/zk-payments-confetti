import VCVio
import Mathlib.Algebra.Field.Basic

/-!
# Receipt authentication: pairwise-independent one-time MAC

Issue #5 asks for receipt-signature instantiation and chain authenticity
proved as a reduction rather than absorbed into transition guards. In this
repository's information-theoretic reference style (see
`Zkpc/Crypto/MaskedEncryption.lean`), the receipt authenticator is the
pairwise-independent one-time MAC `tag(m) = a·m + b` under payer-issuer key
`(a, b)`:

* `verify_tag` — correctness.
* `evalDist_keyTag_eq` — the **transcript reparametrization**: a uniform key
  observed through one tag is distributionally `(a, t)` with `t` fresh-uniform
  and `b = t − a·m` hidden; this is the coupling that makes the forgery bound
  a single-point guess.
* `mac_forgery_bound` — **fixed-pair forgery bound**: for every observed tag
  `t` on `m` and every fixed forgery pair `(m', t')` with `m' ≠ m`,
  verification succeeds with probability at most `1/|F|` over the hidden
  slope in the reparametrized view. The forgery pair is a parameter of the
  statement, not adversary output.

* `adaptiveForgeryGame` / `adaptive_mac_forgery_bound` — the actual adaptive
  one-query EUF game: after seeing the authentic tag, the adversary chooses
  its fresh-message forgery, and the proof conditions on the observed tag.

* `runForgeryChain_bound` / `adaptive_mac_chain_bound` — composition of
  independently keyed receipt links, with total failure at most `n/|F|`.
-/

open OracleSpec OracleComp

namespace Zkpc.Crypto.ReceiptMac

variable {F : Type} [Field F] [DecidableEq F]

/-- One-time MAC tag under key `(a, b)`. -/
def tag (a b m : F) : F := a * m + b

/-- Tag verification. -/
def verify (a b m t : F) : Prop := tag a b m = t

/-- Correctness. -/
theorem verify_tag (a b m : F) : verify a b m (tag a b m) := rfl

instance (a b m t : F) : Decidable (verify a b m t) :=
  decidable_of_iff (tag a b m = t) Iff.rfl

section Privacy

variable [Fintype F] [SampleableType F]

/-- **Transcript reparametrization**: a uniform key `(a, b)` observed through
the single tag `t = a·m + b` is distributed exactly as an independent uniform
pair `(a, t)`; the second key coordinate is recoverable as `b = t − a·m` but
carries no further information. -/
theorem evalDist_keyTag_eq (m : F) :
    𝒟[do let a ← ($ᵗ F); let b ← ($ᵗ F); pure (a, tag a b m)] =
      𝒟[do let a ← ($ᵗ F); let t ← ($ᵗ F); pure (a, t)] := by
  refine evalDist_bind_congr' ($ᵗ F) fun a => ?_
  unfold tag
  rw [show (do let b ← ($ᵗ F); pure (a, a * m + b) : ProbComp (F × F))
      = (do let b ← ($ᵗ F); pure (a, (fun x : F => x) b + a * m)) from by
        simp only [add_comm (a * m)]
      ]
  exact evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id (a * m) (fun t => pure (a, t))

/-- The unique slope consistent with an observed tag and a forged tag. -/
def forgedSlope (m t m' t' : F) : F := (t' - t) / (m' - m)

/-- **One-time unforgeability / per-link chain authenticity.** In the
reparametrized view (tag `t` on `m` observed, slope `a` hidden uniform,
`b = t − a·m`), a forgery `(m', t')` at a fresh message `m' ≠ m` verifies only
at the single slope `forgedSlope m t m' t'`, so it succeeds with probability
at most `1/|F|`. -/
theorem mac_forgery_bound (m t m' t' : F) (hne : m' ≠ m) :
    Pr[= true | (do
        let a ← ($ᵗ F)
        pure (decide (verify a (t - a * m) m' t')))]
      ≤ (Fintype.card F : ENNReal)⁻¹ := by
  rw [probOutput_bind_eq_tsum]
  have hkey : ∀ a : F, verify a (t - a * m) m' t' ↔ a = forgedSlope m t m' t' := by
    intro a
    unfold verify tag forgedSlope
    have hdiff : m' - m ≠ 0 := sub_ne_zero.mpr hne
    constructor
    · intro h
      have : a * (m' - m) = t' - t := by
        calc a * (m' - m) = a * m' + (t - a * m) - t := by ring
          _ = t' - t := by rw [h]
      field_simp
      calc a * (m' - m) = t' - t := this
        _ = t' - t := rfl
    · intro h
      subst h
      field_simp
      ring
  calc ∑' a : F, Pr[= a | ($ᵗ F)] *
          Pr[= true | (pure (decide (verify a (t - a * m) m' t')) : ProbComp Bool)]
      ≤ ∑' a : F, Pr[= a | ($ᵗ F)] *
          (if a = forgedSlope m t m' t' then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun a => mul_le_mul_left' ?_ _
        by_cases hs : verify a (t - a * m) m' t'
        · have h1 : Pr[= true |
              (pure (decide (verify a (t - a * m) m' t')) : ProbComp Bool)] = 1 := by
            simp [hs]
          rw [h1, if_pos ((hkey a).mp hs)]
        · have h0 : Pr[= true |
              (pure (decide (verify a (t - a * m) m' t')) : ProbComp Bool)] = 0 := by
            simp [hs]
          rw [h0]; exact zero_le'
    _ = ∑' a : F, (if a = forgedSlope m t m' t' then Pr[= a | ($ᵗ F)] else 0) := by
        refine tsum_congr fun a => ?_
        split <;> simp
    _ = Pr[= forgedSlope m t m' t' | ($ᵗ F)] := by
        rw [tsum_eq_single (forgedSlope m t m' t') fun a ha => if_neg ha]
        simp
    _ = (Fintype.card F : ENNReal)⁻¹ := by rw [probOutput_uniformSample]

/-- Adaptive one-query EUF game in the reparametrized transcript view.
The adversary observes the authentic tag `t`, then chooses both the forged
message and tag.  The hidden slope is sampled only after that choice has been
fixed; this is distributionally equivalent to sampling the original uniform
key before revealing its tag by `evalDist_keyTag_eq`. -/
def adaptiveForgeryGame (m : F) (forge : F → F × F) : ProbComp Bool := do
  let t ← ($ᵗ F)
  let a ← ($ᵗ F)
  let out := forge t
  pure (decide (verify a (t - a * m) out.1 out.2))

/-- **Adaptive one-query unforgeability.** Even when the forgery is an
arbitrary function of the observed authentic tag, every fresh-message
forgery succeeds with probability at most `1/|F|`. -/
theorem adaptive_mac_forgery_bound (m : F) (forge : F → F × F)
    (fresh : ∀ t, (forge t).1 ≠ m) :
    Pr[= true | adaptiveForgeryGame m forge]
      ≤ (Fintype.card F : ENNReal)⁻¹ := by
  unfold adaptiveForgeryGame
  rw [← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le (m := ProbComp)
    (q := fun b : Bool => b = true) ?_
  intro t _
  rw [probEvent_eq_eq_probOutput]
  exact mac_forgery_bound m t (forge t).1 (forge t).2 (fresh t)

/-- Sequentially execute independently keyed per-link forgery experiments and
report whether any receipt link was forged.  Short-circuiting is operationally
useful and does not weaken the union-bound proof. -/
def runForgeryChain : List (ProbComp Bool) → ProbComp Bool
  | [] => pure false
  | game :: games => do
      let forged ← game
      if forged then pure true else runForgeryChain games

/-- Generic finite-chain union bound.  It applies to adaptive per-link games:
each `game` may already include an arbitrary attacker strategy conditioned on
that link's authentic transcript. -/
theorem runForgeryChain_bound (games : List (ProbComp Bool)) (ε : ENNReal)
    (bounded : ∀ game ∈ games, Pr[= true | game] ≤ ε) :
    Pr[= true | runForgeryChain games] ≤ (games.length : ENNReal) * ε := by
  induction games with
  | nil => simp [runForgeryChain]
  | cons game games ih =>
      rw [← probEvent_eq_eq_probOutput]
      unfold runForgeryChain
      have hub :
          Pr[fun forged : Bool => ¬ forged = false |
            game >>= fun forged =>
              if forged then pure true else runForgeryChain games]
            ≤ ε + (games.length : ENNReal) * ε := by
        refine probEvent_bind_le_add (m := ProbComp)
          (mx := game)
          (my := fun forged =>
            if forged then pure true else runForgeryChain games)
          (p := fun forged : Bool => forged = false)
          (q := fun forged : Bool => forged = false)
          (ε₁ := ε) (ε₂ := (games.length : ENNReal) * ε) ?_ ?_
        · simpa only [Bool.not_eq_false, probEvent_eq_eq_probOutput] using
            bounded game (by simp)
        · intro forged _ hfalse
          subst forged
          simp only [Bool.false_eq_true, ↓reduceIte]
          simpa only [Bool.not_eq_false, probEvent_eq_eq_probOutput] using
            ih (fun g hg => bounded g (by simp [hg]))
      have hub' :
          Pr[fun forged : Bool => forged = true |
            (do
              let forged ← game
              if forged then pure true else runForgeryChain games)]
            ≤ ε + (games.length : ENNReal) * ε := by
        simpa only [Bool.not_eq_false] using hub
      refine hub'.trans ?_
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring_nf
      exact le_rfl

/-- A chain of adaptive one-query receipt forgeries has total failure
probability at most `n/|F|`. -/
theorem adaptive_mac_chain_bound (m : F) (forges : List (F → F × F))
    (fresh : ∀ forge ∈ forges, ∀ t, (forge t).1 ≠ m) :
    Pr[= true |
        runForgeryChain (forges.map (adaptiveForgeryGame m))]
      ≤ (forges.length : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  have h := runForgeryChain_bound
    (forges.map (adaptiveForgeryGame m))
    (Fintype.card F : ENNReal)⁻¹ (by
      intro game hgame
      simp only [List.mem_map] at hgame
      obtain ⟨forge, hforge, rfl⟩ := hgame
      exact adaptive_mac_forgery_bound m forge (fresh forge hforge))
  simpa only [List.length_map] using h

end Privacy

end Zkpc.Crypto.ReceiptMac

#print axioms Zkpc.Crypto.ReceiptMac.verify_tag
#print axioms Zkpc.Crypto.ReceiptMac.evalDist_keyTag_eq
#print axioms Zkpc.Crypto.ReceiptMac.mac_forgery_bound
#print axioms Zkpc.Crypto.ReceiptMac.adaptive_mac_forgery_bound
#print axioms Zkpc.Crypto.ReceiptMac.runForgeryChain_bound
#print axioms Zkpc.Crypto.ReceiptMac.adaptive_mac_chain_bound
