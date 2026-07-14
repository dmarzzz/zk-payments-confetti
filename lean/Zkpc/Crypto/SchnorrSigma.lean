import Zkpc.Crypto.SchnorrReceipt
import VCVio.CryptoFoundations.FiatShamir.Sigma.Security

/-!
# Schnorr as VCVio's generic Sigma protocol

This instantiation connects the concrete receipt authenticator to VCVio's
source-valid Pointcheval--Stern replay-forking and EUF-CMA framework.  It
supplies the protocol algorithms, the discrete-log relation, special
soundness, and a non-failing extractor.  The remaining inputs to
`FiatShamir.euf_cma_bound` are the standard Schnorr HVZK/predictability proofs
and the concrete adversary query certificate.
-/

open OracleSpec OracleComp

namespace Zkpc.Crypto.SchnorrSigma

variable {F G : Type}
variable [Field F] [AddCommGroup G] [Module F G]
variable [DecidableEq G] [SampleableType F]

/-- Discrete-log relation at fixed base. -/
def relation (base : G) (publicKey : G) (secret : F) : Bool :=
  decide (publicKey = secret • base)

/-- Standard Schnorr identification protocol. -/
def protocol (base : G) : SigmaProtocol G F G F F F (relation base) where
  commit _ _ := do
    let nonce ← ($ᵗ F)
    pure (nonce • base, nonce)
  respond _ secret nonce challenge :=
    pure (nonce + challenge * secret)
  verify publicKey commitment challenge response :=
    decide (response • base = commitment + challenge • publicKey)
  sim _ := do
    let nonce ← ($ᵗ F)
    pure (nonce • base)
  extract challenge₁ response₁ challenge₂ response₂ :=
    pure (SchnorrReceipt.extract challenge₁ challenge₂ response₁ response₂)

/-- The generic verifier is exactly the concrete Schnorr equation. -/
theorem protocol_verify_eq (base publicKey commitment : G)
    (challenge response : F) :
    (protocol (F := F) base).verify publicKey commitment challenge response = true ↔
      response • base = commitment + challenge • publicKey := by
  simp [protocol]

/-- **Special soundness** for the generic Schnorr protocol. -/
theorem speciallySound (base : G) : (protocol (F := F) base).SpeciallySound := by
  intro publicKey commitment challenge₁ challenge₂ response₁ response₂
    hchallenge hv₁ hv₂ witness hwitness
  simp only [protocol, support_pure, Set.mem_singleton_iff] at hwitness
  subst witness
  have hv₁' : response₁ • base = commitment + challenge₁ • publicKey :=
    (protocol_verify_eq (F := F) base publicKey commitment challenge₁ response₁).mp hv₁
  have hv₂' : response₂ • base = commitment + challenge₂ • publicKey :=
    (protocol_verify_eq (F := F) base publicKey commitment challenge₂ response₂).mp hv₂
  have hdiff : (response₁ - response₂) • base =
      (challenge₁ - challenge₂) • publicKey := by
    rw [sub_smul, hv₁', hv₂', sub_smul]
    abel
  have hc : challenge₁ - challenge₂ ≠ 0 := sub_ne_zero.mpr hchallenge
  apply decide_eq_true
  unfold SchnorrReceipt.extract
  symm
  rw [div_eq_mul_inv, mul_comm, mul_smul, hdiff, ← mul_smul]
  field_simp
  simp

/-- The extractor is a pure computation and never fails, satisfying the
non-failure premise of `FiatShamir.euf_nma_bound`/`euf_cma_bound`. -/
theorem extract_never_fails (base : G) :
    ∀ challenge₁ response₁ challenge₂ response₂,
      Pr[⊥ | (protocol (F := F) base).extract challenge₁ response₁ challenge₂ response₂] = 0 := by
  intro challenge₁ response₁ challenge₂ response₂
  simp [protocol]

section HVZK

variable [Fintype F]

/-- Standard witness-free Schnorr transcript simulator: choose challenge and
response, then solve the verification equation for the commitment. -/
def simulatedTranscript (base publicKey : G) : ProbComp (G × F × F) := do
  let challenge ← ($ᵗ F)
  let response ← ($ᵗ F)
  pure (response • base - challenge • publicKey, challenge, response)

/-- **Perfect Schnorr HVZK.** For every valid discrete-log pair, the honest
transcript distribution equals the witness-free simulator exactly. -/
theorem perfectHVZK (base : G) :
    (protocol (F := F) base).PerfectHVZK (simulatedTranscript (F := F) base) := by
  intro publicKey secret hrel
  have hpk : publicKey = secret • base := by
    simp only [relation, decide_eq_true_eq] at hrel
    exact hrel
  simp only [SigmaProtocol.realTranscript, protocol, simulatedTranscript,
    bind_assoc, pure_bind]
  change 𝒟[do
      let nonce ← ($ᵗ F)
      let challenge ← ($ᵗ F)
      pure (nonce • base, challenge, nonce + challenge * secret)] =
    𝒟[do
      let challenge ← ($ᵗ F)
      let response ← ($ᵗ F)
      pure (response • base - challenge • publicKey, challenge, response)]
  calc
    𝒟[do
        let nonce ← ($ᵗ F)
        let challenge ← ($ᵗ F)
        pure (nonce • base, challenge, nonce + challenge * secret)] =
      𝒟[do
        let challenge ← ($ᵗ F)
        let nonce ← ($ᵗ F)
        pure (nonce • base, challenge, nonce + challenge * secret)] :=
      evalDist_bind_bind_swap ($ᵗ F) ($ᵗ F)
        (fun nonce challenge =>
          pure (nonce • base, challenge, nonce + challenge * secret))
    _ = 𝒟[do
        let challenge ← ($ᵗ F)
        let response ← ($ᵗ F)
        pure (response • base - challenge • publicKey, challenge, response)] := by
      refine evalDist_bind_congr' ($ᵗ F) fun challenge => ?_
      let cont : F → ProbComp (G × F × F) := fun response =>
        pure ((response - challenge * secret) • base, challenge, response)
      calc
        𝒟[do
            let nonce ← ($ᵗ F)
            pure (nonce • base, challenge, nonce + challenge * secret)] =
          𝒟[do
            let nonce ← ($ᵗ F)
            cont (nonce + challenge * secret)] := by
              refine evalDist_bind_congr' ($ᵗ F) fun nonce => ?_
              simp only [cont]
              congr 3
              · rw [add_sub_cancel_right]
        _ = 𝒟[do let response ← ($ᵗ F); cont response] :=
          evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
            Function.bijective_id (challenge * secret) cont
        _ = 𝒟[do
            let response ← ($ᵗ F)
            pure (response • base - challenge • publicKey,
              challenge, response)] := by
              refine evalDist_bind_congr' ($ᵗ F) fun response => ?_
              simp only [cont, hpk, sub_smul, mul_smul]

/-- Exact HVZK implies the zero-loss premise used by the generic EUF-CMA
reduction. -/
theorem hvzk_zero (base : G) :
    (protocol (F := F) base).HVZK (simulatedTranscript (F := F) base) 0 :=
  ((SigmaProtocol.perfectHVZK_iff_hvzk_zero
    (protocol (F := F) base) (simulatedTranscript (F := F) base)).mp
      (perfectHVZK (F := F) base))

end HVZK

end Zkpc.Crypto.SchnorrSigma

#print axioms Zkpc.Crypto.SchnorrSigma.speciallySound
#print axioms Zkpc.Crypto.SchnorrSigma.extract_never_fails
#print axioms Zkpc.Crypto.SchnorrSigma.perfectHVZK
#print axioms Zkpc.Crypto.SchnorrSigma.hvzk_zero
