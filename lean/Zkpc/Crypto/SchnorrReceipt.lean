import VCVio

/-!
# Schnorr authentication for refund receipts

The information-theoretic `ReceiptMac` is useful for exact finite bounds but
uses an independent key per link.  This module supplies a reusable public-key
authenticator suitable for an arbitrary receipt chain.  It defines standard
additive Schnorr signatures over a scalar field/module group, proves signing
correctness, and proves the deterministic fork-extraction core of the
multi-query EUF-CMA reduction.

The challenge oracle must hash the public key, commitment, and complete
serialized receipt message.  A full ROM forking lemma must additionally turn
a successful adaptive forger into the two accepting executions required by
`fork_extracts`; the extractor itself and all algebraic obligations are proved
here without assumptions.
-/

namespace Zkpc.Crypto.SchnorrReceipt

variable {F G Message : Type}
variable [Field F] [AddCommGroup G] [Module F G]

/-- Fiat--Shamir challenge oracle binding key, commitment, and receipt. -/
abbrev ChallengeOracle := G → G → Message → F

/-- Schnorr receipt signature. -/
structure Signature (F G : Type) where
  commitment : G
  response : F
  deriving DecidableEq

/-- Public verification equation `zG = R + cX`. -/
def Verify (H : ChallengeOracle (F := F) (G := G) (Message := Message))
    (base publicKey : G) (message : Message) (sig : Signature F G) : Prop :=
  sig.response • base =
    sig.commitment + H publicKey sig.commitment message • publicKey

/-- Verification is decidable whenever group equality is. -/
instance [DecidableEq G]
    (H : ChallengeOracle (F := F) (G := G) (Message := Message))
    (base publicKey : G) (message : Message) (sig : Signature F G) :
    Decidable (Verify H base publicKey message sig) := by
  unfold Verify
  infer_instance

/-- Sign a receipt with explicit nonce. -/
def sign (H : ChallengeOracle (F := F) (G := G) (Message := Message))
    (base : G) (secret nonce : F) (message : Message) : Signature F G :=
  let publicKey := secret • base
  let commitment := nonce • base
  let challenge := H publicKey commitment message
  ⟨commitment, nonce + challenge * secret⟩

/-- Honest signatures verify. -/
theorem sign_verifies
    (H : ChallengeOracle (F := F) (G := G) (Message := Message))
    (base : G) (secret nonce : F) (message : Message) :
    Verify H base (secret • base) message
      (sign H base secret nonce message) := by
  unfold Verify sign
  simp only [add_smul, mul_smul]

/-- Extract the secret scalar from two response/challenge pairs. -/
def extract (c₁ c₂ z₁ z₂ : F) : F := (z₁ - z₂) / (c₁ - c₂)

/-- **Schnorr fork extraction.** Two accepting signatures for the same public
key, message, and commitment, under distinct programmed challenges, recover a
scalar whose public key is exactly the signed public key. -/
theorem fork_extracts
    (H₁ H₂ : ChallengeOracle (F := F) (G := G) (Message := Message))
    (base publicKey : G) (message : Message) (sig₁ sig₂ : Signature F G)
    (hcommit : sig₁.commitment = sig₂.commitment)
    (hv₁ : Verify H₁ base publicKey message sig₁)
    (hv₂ : Verify H₂ base publicKey message sig₂)
    (hchallenge : H₁ publicKey sig₁.commitment message ≠
      H₂ publicKey sig₂.commitment message) :
    extract (H₁ publicKey sig₁.commitment message)
        (H₂ publicKey sig₂.commitment message)
        sig₁.response sig₂.response • base = publicKey := by
  unfold Verify at hv₁ hv₂
  rw [← hcommit] at hv₂ hchallenge ⊢
  let c₁ := H₁ publicKey sig₁.commitment message
  let c₂ := H₂ publicKey sig₁.commitment message
  have hc : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hchallenge
  have hdiff : (sig₁.response - sig₂.response) • base =
      (c₁ - c₂) • publicKey := by
    rw [sub_smul]
    change sig₁.response • base - sig₂.response • base = _
    rw [hv₁, hv₂]
    simp only [sub_smul]
    dsimp only [c₁, c₂]
    abel
  unfold extract
  rw [div_eq_mul_inv, mul_comm, mul_smul, hdiff, ← mul_smul]
  dsimp only [c₁, c₂] at hc ⊢
  field_simp
  simp

/-- The receipt message can be signed repeatedly under one public key; nonce
freshness is the only per-signature state required by the algorithm. -/
def signMany
    (H : ChallengeOracle (F := F) (G := G) (Message := Message))
    (base : G) (secret : F) : List (F × Message) → List (Signature F G) :=
  List.map fun pair => sign H base secret pair.1 pair.2

/-- Every signature emitted by `signMany` verifies under the shared public
key. -/
theorem signMany_verifies
    (H : ChallengeOracle (F := F) (G := G) (Message := Message))
    (base : G) (secret : F) (pairs : List (F × Message)) :
    ∀ sig ∈ signMany H base secret pairs,
      ∃ nonce message, (nonce, message) ∈ pairs ∧
        sig = sign H base secret nonce message ∧
        Verify H base (secret • base) message sig := by
  intro sig hsig
  simp only [signMany, List.mem_map] at hsig
  obtain ⟨pair, hpair, rfl⟩ := hsig
  exact ⟨pair.1, pair.2, hpair, rfl,
    sign_verifies H base secret pair.1 pair.2⟩

end Zkpc.Crypto.SchnorrReceipt

#print axioms Zkpc.Crypto.SchnorrReceipt.sign_verifies
#print axioms Zkpc.Crypto.SchnorrReceipt.fork_extracts
#print axioms Zkpc.Crypto.SchnorrReceipt.signMany_verifies
