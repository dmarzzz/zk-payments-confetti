import VCVio

/-!
# Rerandomizable additive ElGamal

This is the concrete public-key encryption algebra needed by refund receipts.
Messages live in an additive group `G`; scalars live in a field `F`; and a
public key is the group point `sk • base`.  Encryption and rerandomization are
the standard additive ElGamal formulas:

* `Enc(pk, m; r) = (r • base, m + r • pk)`;
* `Dec(sk, (c₁,c₂)) = c₂ - sk • c₁`;
* `Rerand(pk, ct; ρ) = ct + (ρ • base, ρ • pk)`.

The file proves correctness, homomorphic addition, rerandomization
correctness, and the exact composition law saying rerandomizing randomness
`r` by `ρ` yields encryption randomness `r + ρ`.  Computational ciphertext
privacy is intentionally not asserted from algebra alone: connecting this
construction to IND-CPA requires the usual DDH assumption for the selected
prime-order group and a representation/serialization refinement.
-/

namespace Zkpc.Crypto.ElGamal

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- Secret scalar. -/
abbrev SecretKey (F : Type) := F

/-- Public group point. -/
abbrev PublicKey (G : Type) := G

/-- Additive ElGamal ciphertext. -/
structure Cipher (G : Type) where
  c1 : G
  c2 : G
  deriving DecidableEq

omit [Field F] [AddCommGroup G] [Module F G] in
/-- Ciphertexts are equal when both group components are equal. -/
@[ext] theorem Cipher.ext {x y : Cipher G}
    (hc1 : x.c1 = y.c1) (hc2 : x.c2 = y.c2) : x = y := by
  cases x
  cases y
  simp_all

/-- Derive a public key from a secret scalar and fixed base point. -/
def derivePublic (base : G) (sk : SecretKey F) : PublicKey G := sk • base

/-- Encrypt a group message with explicit randomness. -/
def encrypt (base : G) (pk : PublicKey G) (m : G) (r : F) : Cipher G :=
  ⟨r • base, m + r • pk⟩

/-- Decrypt with the secret scalar. -/
def decrypt (sk : SecretKey F) (ct : Cipher G) : G := ct.c2 - sk • ct.c1

/-- Componentwise ciphertext addition. -/
def add (ct₁ ct₂ : Cipher G) : Cipher G :=
  ⟨ct₁.c1 + ct₂.c1, ct₁.c2 + ct₂.c2⟩

/-- Public rerandomization by adding an encryption of zero. -/
def rerandomize (base : G) (pk : PublicKey G) (ct : Cipher G) (ρ : F) : Cipher G :=
  ⟨ct.c1 + ρ • base, ct.c2 + ρ • pk⟩

/-- Public-key encryption correctness. -/
theorem decrypt_encrypt (base : G) (sk : F) (m : G) (r : F) :
    decrypt sk (encrypt base (derivePublic base sk) m r) = m := by
  simp only [decrypt, encrypt, derivePublic]
  rw [smul_smul, smul_smul, mul_comm r sk]
  exact add_sub_cancel_right m ((sk * r) • base)

/-- Ciphertext addition encrypts the sum under summed randomness. -/
theorem add_encrypt (base pk m₁ m₂ : G) (r₁ r₂ : F) :
    add (encrypt base pk m₁ r₁) (encrypt base pk m₂ r₂) =
      encrypt base pk (m₁ + m₂) (r₁ + r₂) := by
  apply Cipher.ext
  · simp only [add, encrypt, add_smul]
  · simp only [add, encrypt, add_smul]
    abel

/-- Rerandomization is exactly addition of encryption randomness. -/
theorem rerandomize_encrypt (base pk m : G) (r ρ : F) :
    rerandomize base pk (encrypt base pk m r) ρ =
      encrypt base pk m (r + ρ) := by
  apply Cipher.ext
  · simp only [rerandomize, encrypt, add_smul]
  · simp only [rerandomize, encrypt, add_smul]
    abel

/-- Public rerandomization preserves the decrypted plaintext. -/
theorem decrypt_rerandomize (base : G) (sk : F) (ct : Cipher G) (ρ : F) :
    decrypt sk (rerandomize base (derivePublic base sk) ct ρ) = decrypt sk ct := by
  simp only [decrypt, rerandomize, derivePublic]
  rw [smul_add, smul_smul, smul_smul, mul_comm ρ sk]
  abel

/-- Homomorphically add a refund amount (encoded as a group point) and
rerandomize the resulting receipt ciphertext. -/
def refundUpdate (base : G) (pk : PublicKey G) (ct : Cipher G)
    (refund : G) (ρ : F) : Cipher G :=
  rerandomize base pk (add ct (encrypt base pk refund (0 : F))) ρ

/-- Refund-update correctness under the corresponding secret key. -/
theorem decrypt_refundUpdate (base : G) (sk : F) (ct : Cipher G)
    (refund : G) (ρ : F) :
    decrypt sk (refundUpdate base (derivePublic base sk) ct refund ρ) =
      decrypt sk ct + refund := by
  rw [refundUpdate, decrypt_rerandomize]
  simp only [decrypt, add, encrypt, zero_smul, add_zero]
  abel

end Zkpc.Crypto.ElGamal

#print axioms Zkpc.Crypto.ElGamal.decrypt_encrypt
#print axioms Zkpc.Crypto.ElGamal.add_encrypt
#print axioms Zkpc.Crypto.ElGamal.rerandomize_encrypt
#print axioms Zkpc.Crypto.ElGamal.decrypt_rerandomize
#print axioms Zkpc.Crypto.ElGamal.decrypt_refundUpdate
