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

What is *not* formalized here, and is the intended unformalized reading
toward the issue-#5 reduction: the adaptive forgery game in which the
adversary chooses `(m', t')` as a function of the observed tag (the standard
argument conditions on `t` via `evalDist_keyTag_eq` and applies the
fixed-pair bound per branch), and the `n`-link chain claim that a receipt
chain of `n` adversarial links is broken with probability at most `n/|F|` by
a union bound over links. Both are prose motivation until stated as games in
this file.
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

end Privacy

end Zkpc.Crypto.ReceiptMac

#print axioms Zkpc.Crypto.ReceiptMac.verify_tag
#print axioms Zkpc.Crypto.ReceiptMac.evalDist_keyTag_eq
#print axioms Zkpc.Crypto.ReceiptMac.mac_forgery_bound
