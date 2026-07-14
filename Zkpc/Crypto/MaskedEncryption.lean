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

/-! ## Distributional privacy laws

The adversary view of a refund receipt is the ciphertext alone (openings are
payer-private). The three theorems below are the distributional
rerandomization-privacy layer: fresh-opening encryption is perfectly secret,
a rerandomized ciphertext is fresh-uniform regardless of its predecessor, and
consequently receipt updates are unlinkable across any two histories. -/

section Privacy

variable [Fintype F] [SampleableType F]

/-- **Perfect secrecy of fresh-opening encryption**: the ciphertext of any
plaintext under a uniform opening is exactly uniform, so the ciphertext
distribution is independent of the plaintext. -/
theorem evalDist_encrypt_uniform (m : F) :
    𝒟[do let r ← ($ᵗ F); pure (encrypt m r)] = 𝒟[($ᵗ F)] := by
  unfold encrypt
  simp only [add_comm m]
  rw [show (do let r ← ($ᵗ F); pure (r + m) : ProbComp F)
      = (do let r ← ($ᵗ F); pure ((fun x : F => x) r + m)) from rfl]
  rw [evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id m pure]
  rw [bind_pure]

/-- **Rerandomization privacy**: with a fresh uniform mask the rerandomized
ciphertext is exactly uniform, independent of the input ciphertext. -/
theorem evalDist_rerandomize_cipher_uniform (ct r : F) :
    𝒟[do let ρ ← ($ᵗ F); pure (rerandomize ct r ρ).1] = 𝒟[($ᵗ F)] := by
  unfold rerandomize
  simp only [add_comm ct]
  rw [show (do let ρ ← ($ᵗ F); pure (ρ + ct) : ProbComp F)
      = (do let ρ ← ($ᵗ F); pure ((fun x : F => x) ρ + ct)) from rfl]
  rw [evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id ct pure]
  rw [bind_pure]

/-- **Receipt unlinkability**: rerandomized ciphertexts from any two receipt
histories are identically distributed. -/
theorem evalDist_rerandomize_cipher_eq (ct₁ r₁ ct₂ r₂ : F) :
    𝒟[do let ρ ← ($ᵗ F); pure (rerandomize ct₁ r₁ ρ).1] =
      𝒟[do let ρ ← ($ᵗ F); pure (rerandomize ct₂ r₂ ρ).1] := by
  rw [evalDist_rerandomize_cipher_uniform, evalDist_rerandomize_cipher_uniform]

/-- **Refund-update privacy**: the updated receipt ciphertext is exactly
uniform, revealing nothing about the prior balance or the refund amount. -/
theorem evalDist_refundUpdate_cipher_uniform (ct r refund : F) :
    𝒟[do let ρ ← ($ᵗ F); pure (refundUpdate ct r refund ρ).1] = 𝒟[($ᵗ F)] := by
  unfold refundUpdate rerandomize add encrypt
  simp only [add_comm]
  rw [show (do let ρ ← ($ᵗ F); pure (ρ + (ct + (refund + 0))) : ProbComp F)
      = (do let ρ ← ($ᵗ F); pure ((fun x : F => x) ρ + (ct + (refund + 0))))
      from rfl]
  rw [evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id (ct + (refund + 0)) pure]
  rw [bind_pure]

/-- **Refund-update unlinkability**: updated receipt ciphertexts from any two
balance/refund histories are identically distributed. -/
theorem evalDist_refundUpdate_cipher_eq (ct₁ r₁ v₁ ct₂ r₂ v₂ : F) :
    𝒟[do let ρ ← ($ᵗ F); pure (refundUpdate ct₁ r₁ v₁ ρ).1] =
      𝒟[do let ρ ← ($ᵗ F); pure (refundUpdate ct₂ r₂ v₂ ρ).1] := by
  rw [evalDist_refundUpdate_cipher_uniform, evalDist_refundUpdate_cipher_uniform]

end Privacy

end Zkpc.Crypto.MaskedEncryption

#print axioms Zkpc.Crypto.MaskedEncryption.evalDist_encrypt_uniform
#print axioms Zkpc.Crypto.MaskedEncryption.evalDist_rerandomize_cipher_uniform
#print axioms Zkpc.Crypto.MaskedEncryption.evalDist_rerandomize_cipher_eq
#print axioms Zkpc.Crypto.MaskedEncryption.evalDist_refundUpdate_cipher_uniform
#print axioms Zkpc.Crypto.MaskedEncryption.evalDist_refundUpdate_cipher_eq
#print axioms Zkpc.Crypto.MaskedEncryption.decrypt_encrypt
#print axioms Zkpc.Crypto.MaskedEncryption.add_encrypt
#print axioms Zkpc.Crypto.MaskedEncryption.decrypt_rerandomize
#print axioms Zkpc.Crypto.MaskedEncryption.decrypt_refundUpdate
