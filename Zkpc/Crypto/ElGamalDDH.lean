import Zkpc.Crypto.ElGamal

/-!
# ElGamal privacy as a DDH reduction

This module exposes the exact computational assumption behind the concrete
refund encryption.  It defines real and random Diffie--Hellman tuple games,
the corresponding real-encryption and random-pad hybrids, and proves:

* real encryption is exactly a projection of a real DDH tuple;
* the encryption hybrid is exactly the same projection of a random tuple;
* random-pad hybrids are message independent; and
* two-message ElGamal distinguishing advantage is at most the sum of two DDH
  distinguishing advantages for explicit reductions.

Thus privacy is no longer hidden inside a transition guard.  A deployed group
instantiation must supply a bound for `ddhAdvantage`; serialization and PPT
cost preservation remain separate refinement obligations.
-/

open OracleSpec OracleComp

namespace Zkpc.Crypto.ElGamal

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
variable [Fintype F] [SampleableType F] [Fintype G] [SampleableType G]

/-- The three adversary-visible points of a DDH challenge relative to a fixed
base: public key, ephemeral point, and candidate shared secret. -/
structure DDHTuple (G : Type) where
  publicKey : G
  ephemeral : G
  shared : G

/-- Real Diffie--Hellman tuples. -/
def ddhReal (base : G) : ProbComp (DDHTuple G) := do
  let sk ← ($ᵗ F)
  let r ← ($ᵗ F)
  pure ⟨sk • base, r • base, r • (sk • base)⟩

/-- Random Diffie--Hellman tuples with an independent uniform group point. -/
def ddhRandom (base : G) : ProbComp (DDHTuple G) := do
  let sk ← ($ᵗ F)
  let r ← ($ᵗ F)
  let z ← ($ᵗ G)
  pure ⟨sk • base, r • base, z⟩

/-- Convert a DDH tuple into the public-key/ciphertext view for message `m`. -/
def tupleView (m : G) (t : DDHTuple G) : PublicKey G × Cipher G :=
  (t.publicKey, ⟨t.ephemeral, m + t.shared⟩)

/-- Honest one-challenge ElGamal view. -/
def encryptionReal (base m : G) : ProbComp (PublicKey G × Cipher G) := do
  let sk ← ($ᵗ F)
  let r ← ($ᵗ F)
  pure (derivePublic base sk, encrypt base (derivePublic base sk) m r)

/-- Random-pad encryption hybrid. -/
def encryptionHybrid (base m : G) : ProbComp (PublicKey G × Cipher G) :=
  tupleView m <$> ddhRandom (F := F) base

/-- Real encryption is definitionally the real-DDH projection. -/
theorem evalDist_encryptionReal_eq_ddh (base m : G) :
    𝒟[encryptionReal (F := F) base m] =
      𝒟[tupleView m <$> ddhReal (F := F) base] := by
  unfold encryptionReal ddhReal tupleView derivePublic encrypt
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine evalDist_bind_congr' ($ᵗ F) fun sk => ?_
  refine evalDist_bind_congr' ($ᵗ F) fun r => ?_
  rfl

/-- Random-pad hybrids reveal no message information. -/
theorem evalDist_encryptionHybrid_message_independent (base m₀ m₁ : G) :
    𝒟[encryptionHybrid (F := F) base m₀] =
      𝒟[encryptionHybrid (F := F) base m₁] := by
  unfold encryptionHybrid ddhRandom tupleView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine evalDist_bind_congr' ($ᵗ F) fun sk => ?_
  refine evalDist_bind_congr' ($ᵗ F) fun r => ?_
  let cont : G → ProbComp (PublicKey G × Cipher G) := fun padded =>
    pure (sk • base, ⟨r • base, padded⟩)
  calc
    𝒟[do let z ← ($ᵗ G); pure (sk • base,
        ({ c1 := r • base, c2 := m₀ + z } : Cipher G))] =
        𝒟[do let z ← ($ᵗ G); cont (z + m₀)] := by
          apply evalDist_bind_congr' ($ᵗ G)
          intro z
          simp only [cont, add_comm]
    _ = 𝒟[do let z ← ($ᵗ G); cont (z + m₁)] :=
      evalDist_bind_bijective_add_right_eq (α := G) (β := G)
        (fun z : G => z) Function.bijective_id m₀ m₁ cont
    _ = 𝒟[do let z ← ($ᵗ G); pure (sk • base,
        ({ c1 := r • base, c2 := m₁ + z } : Cipher G))] := by
          apply evalDist_bind_congr' ($ᵗ G)
          intro z
          simp only [cont, add_comm]

/-- Boolean-output statistical gap used for both DDH and encryption games. -/
noncomputable def outputGap (game₀ game₁ : ProbComp Bool) : ℝ :=
  |Pr[= true | game₀].toReal - Pr[= true | game₁].toReal|

/-- DDH distinguishing advantage of an explicit tuple distinguisher. -/
noncomputable def ddhAdvantage (F : Type) [Field F] [Module F G]
    [Fintype F] [SampleableType F]
    (base : G) (D : DDHTuple G → Bool) : ℝ :=
  outputGap (D <$> ddhReal (F := F) base) (D <$> ddhRandom (F := F) base)

/-- Two-message encryption distinguishing advantage. -/
noncomputable def encryptionAdvantage (F : Type) [Field F] [Module F G]
    [Fintype F] [SampleableType F] (base m₀ m₁ : G)
    (D : PublicKey G × Cipher G → Bool) : ℝ :=
  outputGap (D <$> encryptionReal (F := F) base m₀)
    (D <$> encryptionReal (F := F) base m₁)

/-- DDH reduction obtained by interpreting a tuple as an encryption of `m`. -/
def ddhReduction (m : G) (D : PublicKey G × Cipher G → Bool) :
    DDHTuple G → Bool := fun tuple => D (tupleView m tuple)

/-- Mapping a real DDH tuple through the reduction gives the real encryption
distinguisher experiment. -/
theorem evalDist_ddhReduction_real (base m : G)
    (D : PublicKey G × Cipher G → Bool) :
    𝒟[ddhReduction m D <$> ddhReal (F := F) base] =
      𝒟[D <$> encryptionReal (F := F) base m] := by
  unfold ddhReduction ddhReal encryptionReal tupleView derivePublic encrypt
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]

/-- Mapping a random DDH tuple through the reduction gives the random-pad
hybrid distinguisher experiment. -/
theorem evalDist_ddhReduction_random (base m : G)
    (D : PublicKey G × Cipher G → Bool) :
    𝒟[ddhReduction m D <$> ddhRandom (F := F) base] =
      𝒟[D <$> encryptionHybrid (F := F) base m] := by
  unfold ddhReduction encryptionHybrid ddhRandom tupleView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]

/-- **ElGamal IND reduction.** Any two-message encryption distinguisher gives
two explicit DDH distinguishers; its advantage is bounded by the sum of their
DDH advantages. -/
theorem encryptionAdvantage_le_ddh (base m₀ m₁ : G)
    (D : PublicKey G × Cipher G → Bool) :
    encryptionAdvantage F base m₀ m₁ D ≤
      ddhAdvantage F base (ddhReduction m₀ D) +
      ddhAdvantage F base (ddhReduction m₁ D) := by
  have hr (m : G) :
      Pr[= true | ddhReduction m D <$> ddhReal (F := F) base] =
        Pr[= true | D <$> encryptionReal (F := F) base m] := by
    rw [probOutput_def, probOutput_def, evalDist_ddhReduction_real]
  have hh (m : G) :
      Pr[= true | ddhReduction m D <$> ddhRandom (F := F) base] =
        Pr[= true | D <$> encryptionHybrid (F := F) base m] := by
    rw [probOutput_def, probOutput_def, evalDist_ddhReduction_random]
  have hhybrid :
      Pr[= true | D <$> encryptionHybrid (F := F) base m₀] =
        Pr[= true | D <$> encryptionHybrid (F := F) base m₁] := by
    rw [probOutput_def, probOutput_def]
    exact congrArg (fun d => d true)
      (evalDist_map_eq_of_evalDist_eq
        (evalDist_encryptionHybrid_message_independent (F := F) base m₀ m₁) D)
  unfold encryptionAdvantage ddhAdvantage outputGap
  rw [hr m₀, hh m₀, hr m₁, hh m₁]
  let r₀ := Pr[= true | D <$> encryptionReal (F := F) base m₀].toReal
  let r₁ := Pr[= true | D <$> encryptionReal (F := F) base m₁].toReal
  let h₀ := Pr[= true | D <$> encryptionHybrid (F := F) base m₀].toReal
  let h₁ := Pr[= true | D <$> encryptionHybrid (F := F) base m₁].toReal
  have hhybrid' : h₀ = h₁ := congrArg ENNReal.toReal hhybrid
  change |r₀ - r₁| ≤ |r₀ - h₀| + |r₁ - h₁|
  rw [hhybrid']
  calc
    |r₀ - r₁| = |(r₀ - h₁) + (h₁ - r₁)| := by ring
    _ ≤ |r₀ - h₁| + |h₁ - r₁| := by
      simpa [Real.norm_eq_abs] using norm_add_le (r₀ - h₁) (h₁ - r₁)
    _ = |r₀ - h₁| + |r₁ - h₁| := by rw [abs_sub_comm h₁ r₁]

end Zkpc.Crypto.ElGamal

#print axioms Zkpc.Crypto.ElGamal.evalDist_encryptionHybrid_message_independent
#print axioms Zkpc.Crypto.ElGamal.encryptionAdvantage_le_ddh
