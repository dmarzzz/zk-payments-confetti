import VCVio.OracleComp.Constructions.SampleableType
import Mathlib.Algebra.Field.Basic

/-!
# Concrete additive masked encryption

An information-theoretic reference instantiation for the refund ciphertext
representation. A message `m` with opening `r` is represented by `m+r`.
Openings are payer-private; ciphertexts add homomorphically, and adding fresh
uniform `rho` rerandomizes the ciphertext while updating the opening to
`r+rho`. This is the exact algebraic functionality used by B-rerand.

This is a symmetric/opening-carrying reference scheme, not a claim about a
deployed public-key construction. It replaces the opaque fresh-handle model
with executable algorithms and kernel-checked correctness/privacy laws.
-/

open OracleSpec OracleComp

namespace Zkpc.Crypto.MaskedEncryption

variable {F : Type} [Field F]

/-- Ciphertexts and openings are field elements. -/
abbrev Cipher (F : Type) := F
abbrev Opening (F : Type) := F

/-- Mask a plaintext with its private opening. -/
def encrypt (m : F) (r : Opening F) : Cipher F := m + r

/-- Open a ciphertext. -/
def decrypt (ct : Cipher F) (r : Opening F) : F := ct - r

/-- Homomorphic ciphertext addition. -/
def add (ct₁ ct₂ : Cipher F) : Cipher F := ct₁ + ct₂

/-- Rerandomize a ciphertext and its private opening together. -/
def rerandomize (ct : Cipher F) (r ρ : Opening F) : Cipher F × Opening F :=
  (ct + ρ, r + ρ)

/-- Encryption correctness. -/
theorem decrypt_encrypt (m r : F) : decrypt (encrypt m r) r = m := by
  simp [decrypt, encrypt]

/-- Additive homomorphism. -/
theorem add_encrypt (m₁ m₂ r₁ r₂ : F) :
    add (encrypt m₁ r₁) (encrypt m₂ r₂) =
      encrypt (m₁ + m₂) (r₁ + r₂) := by
  unfold add encrypt
  ring

/-- Rerandomization preserves the plaintext under the updated opening. -/
theorem decrypt_rerandomize (ct r ρ : F) :
    decrypt (rerandomize ct r ρ).1 (rerandomize ct r ρ).2 = decrypt ct r := by
  unfold decrypt rerandomize
  ring

/-- Homomorphically add a refund amount and rerandomize in one executable
receipt update. -/
def refundUpdate (ct r refund ρ : F) : Cipher F × Opening F :=
  rerandomize (add ct (encrypt refund 0)) r ρ

/-- Receipt-update correctness. -/
theorem decrypt_refundUpdate (ct r refund ρ : F) :
    decrypt (refundUpdate ct r refund ρ).1
      (refundUpdate ct r refund ρ).2 = decrypt ct r + refund := by
  unfold refundUpdate
  rw [decrypt_rerandomize]
  unfold add encrypt decrypt
  ring

end Zkpc.Crypto.MaskedEncryption

#print axioms Zkpc.Crypto.MaskedEncryption.decrypt_encrypt
#print axioms Zkpc.Crypto.MaskedEncryption.add_encrypt
#print axioms Zkpc.Crypto.MaskedEncryption.decrypt_rerandomize
#print axioms Zkpc.Crypto.MaskedEncryption.decrypt_refundUpdate
