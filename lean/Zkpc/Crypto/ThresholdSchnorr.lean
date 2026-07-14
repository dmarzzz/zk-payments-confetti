import Zkpc.Crypto.SchnorrReceipt

/-!
# Lagrange-weighted threshold Schnorr

Authorized signer subsets reconstruct a Schnorr signature using the same
public Lagrange coefficients used for threshold key reconstruction.  This
module gives executable combination functions and proves the combined
signature verifies.  It is the concrete threshold-signature correctness layer
for portable issuance and receipt authorization; adaptive-corruption
unforgeability remains a game reduction built over this construction.
-/

namespace Zkpc.Crypto.ThresholdSchnorr

open SchnorrReceipt

variable {F G Message : Type}
variable [Field F] [AddCommGroup G] [Module F G]

/-- Weighted scalar sum, truncating exactly as `List.zipWith` does. -/
def weightedScalar : List F → List F → F
  | c :: cs, x :: xs => c * x + weightedScalar cs xs
  | _, _ => 0

/-- Weighted group-point sum. -/
def weightedPoint : List F → List G → G
  | c :: cs, x :: xs => c • x + weightedPoint cs xs
  | _, _ => 0

/-- One signer's response share for common challenge `challenge`. -/
def partialResponse (challenge secret nonce : F) : F :=
  nonce + challenge * secret

/-- Combined secret scalar of an authorized subset. -/
def combinedSecret (coeffs secrets : List F) : F :=
  weightedScalar coeffs secrets

/-- Combined public key. -/
def combinedPublic (base : G) (coeffs secrets : List F) : G :=
  combinedSecret coeffs secrets • base

/-- Combined signature from the subset's secret and nonce shares. -/
def combineSignature (base : G) (coeffs secrets nonces : List F)
    (challenge : F) : Signature F G :=
  ⟨weightedPoint coeffs (nonces.map (· • base)),
    weightedScalar coeffs
      (List.zipWith (partialResponse challenge) secrets nonces)⟩

/-- Weighted public-key reconstruction commutes with scalar multiplication. -/
theorem weightedPoint_smul (base : G) :
    ∀ (coeffs scalars : List F), coeffs.length = scalars.length →
      weightedPoint coeffs (scalars.map (· • base)) =
        weightedScalar coeffs scalars • base := by
  intro coeffs
  induction coeffs with
  | nil => intro scalars h; cases scalars <;> simp [weightedPoint, weightedScalar]
  | cons c coeffs ih =>
      intro scalars hlen
      cases scalars with
      | nil => simp at hlen
      | cons x xs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.map_cons, weightedPoint, weightedScalar, add_smul,
            mul_smul]
          rw [ih xs hlen]

/-- Algebraic core: combining response shares equals one response formed from
the reconstructed nonce and secret. -/
theorem weightedResponse_eq (challenge : F) :
    ∀ (coeffs secrets nonces : List F),
      coeffs.length = secrets.length → secrets.length = nonces.length →
      weightedScalar coeffs
          (List.zipWith (partialResponse challenge) secrets nonces) =
        weightedScalar coeffs nonces +
          challenge * weightedScalar coeffs secrets := by
  intro coeffs
  induction coeffs with
  | nil =>
      intro secrets nonces hc hs
      cases secrets <;> cases nonces <;>
        simp_all [weightedScalar]
  | cons c coeffs ih =>
      intro secrets nonces hc hs
      cases secrets with
      | nil => simp at hc
      | cons secret secrets =>
          cases nonces with
          | nil => simp at hs
          | cons nonce nonces =>
              have hc' : coeffs.length = secrets.length := by simpa using hc
              have hs' : secrets.length = nonces.length := by simpa using hs
              simp only [List.zipWith_cons_cons, weightedScalar, partialResponse]
              rw [ih secrets nonces hc' hs']
              ring

/-- **Threshold Schnorr correctness.** If the Fiat--Shamir oracle returns the
challenge used by the selected signers, their Lagrange-weighted aggregate
signature verifies under the Lagrange-weighted public key. -/
theorem combineSignature_verifies
    (H : ChallengeOracle (F := F) (G := G) (Message := Message))
    (base : G) (coeffs secrets nonces : List F) (message : Message)
    (hcs : coeffs.length = secrets.length)
    (hsn : secrets.length = nonces.length) :
    Verify H base (combinedPublic base coeffs secrets) message
      (combineSignature base coeffs secrets nonces
        (H (combinedPublic base coeffs secrets)
          (weightedPoint coeffs (nonces.map (· • base))) message)) := by
  let challenge := H (combinedPublic base coeffs secrets)
    (weightedPoint coeffs (nonces.map (· • base))) message
  unfold Verify combineSignature combinedPublic combinedSecret
  change weightedScalar coeffs
      (List.zipWith (partialResponse challenge) secrets nonces) • base =
    weightedPoint coeffs (nonces.map (· • base)) +
      challenge • (weightedScalar coeffs secrets • base)
  rw [weightedResponse_eq challenge coeffs secrets nonces hcs hsn,
    add_smul, mul_smul, weightedPoint_smul base coeffs nonces
      (hcs.trans hsn)]

end Zkpc.Crypto.ThresholdSchnorr

#print axioms Zkpc.Crypto.ThresholdSchnorr.weightedPoint_smul
#print axioms Zkpc.Crypto.ThresholdSchnorr.weightedResponse_eq
#print axioms Zkpc.Crypto.ThresholdSchnorr.combineSignature_verifies
