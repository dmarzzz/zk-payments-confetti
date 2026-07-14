import Zkpc.Refund.ElGamalRefinement
import Zkpc.Crypto.SchnorrReceipt

/-!
# Authenticated encrypted refund execution

This module joins the two concrete refund primitives at the executable ledger
boundary.  A payee signs the complete receipt message with reusable Schnorr;
the payer/ledger verifies that signature before applying the homomorphic,
rerandomized ElGamal refund update.  The main theorem transports a successful
authenticated call into `Refund.Step.accept` and preserves the ciphertext
representation invariant.
-/

namespace Zkpc.Refund

variable {F G ChannelTag : Type}
variable [Field F] [AddCommGroup G] [Module F G]
variable [DecidableEq G]

/-- All fields that receipt authentication must bind.  `priorCipher` prevents
splicing a valid update onto another channel history; `channel` prevents
cross-channel reuse; index and cost bind the symbolic transition. -/
structure CryptoReceiptMessage (G ChannelTag : Type) where
  channel : ChannelTag
  index : ℕ
  cost : ℕ
  priorCipher : Crypto.ElGamal.Cipher G
  refundPoint : G
  rerandomizerCommitment : G
  deriving DecidableEq

/-- Proof-bearing authenticated refund request. -/
structure CryptoReceipt (F G ChannelTag : Type) where
  message : CryptoReceiptMessage G ChannelTag
  signature : Crypto.SchnorrReceipt.Signature F G

/-- Verify a receipt and, only on success, execute the concrete encrypted
refund transition. -/
def execAuthenticatedElGamalAccept
    (H : Crypto.SchnorrReceipt.ChallengeOracle
      (F := F) (G := G) (Message := CryptoReceiptMessage G ChannelTag))
    (Cmax D : ℕ) (base signerKey encryptionKey : G)
    (encode : ℕ → G) (s : St (Crypto.ElGamal.Cipher G))
    (receipt : CryptoReceipt F G ChannelTag) (ρ : F) :
    Option (St (Crypto.ElGamal.Cipher G)) :=
  if Crypto.SchnorrReceipt.Verify H base signerKey
      receipt.message receipt.signature ∧
      receipt.message.index = s.idx ∧
      receipt.message.priorCipher = s.rep ∧
      receipt.message.refundPoint = encode (Cmax - receipt.message.cost) ∧
      receipt.message.rerandomizerCommitment = ρ • base then
    execElGamalAccept Cmax D base encryptionKey encode s
      receipt.message.cost ρ
  else none

/-- **Concrete authenticated-refund refinement.** A valid channel-bound,
history-bound Schnorr receipt gates the ElGamal state update; successful
execution is a symbolic acceptance and retains the encrypted accumulated
refund invariant. -/
theorem execAuthenticatedElGamalAccept_refines
    (H : Crypto.SchnorrReceipt.ChallengeOracle
      (F := F) (G := G) (Message := CryptoReceiptMessage G ChannelTag))
    (Cmax D : ℕ) (base signerKey : G) (encryptionSecret : F)
    (encode : ℕ → G)
    (encode_add : ∀ x y, encode (x + y) = encode x + encode y)
    (s : St (Crypto.ElGamal.Cipher G))
    (receipt : CryptoReceipt F G ChannelTag) (ρ : F)
    (hsig : Crypto.SchnorrReceipt.Verify H base signerKey
      receipt.message receipt.signature)
    (hindex : receipt.message.index = s.idx)
    (hprior : receipt.message.priorCipher = s.rep)
    (hrefund : receipt.message.refundPoint =
      encode (Cmax - receipt.message.cost))
    (hrand : receipt.message.rerandomizerCommitment = ρ • base)
    (hlive : s.closed = false)
    (hcost : receipt.message.cost ≤ Cmax)
    (hsolvent : (s.idx + 1) * Cmax ≤ D + s.R)
    (hrep : Crypto.ElGamal.decrypt encryptionSecret s.rep = encode s.R) :
    ∃ s',
      execAuthenticatedElGamalAccept H Cmax D base signerKey
          (Crypto.ElGamal.derivePublic base encryptionSecret) encode s receipt ρ =
        some s' ∧
      Step Cmax D s (.accept receipt.message.cost s'.rep) s' ∧
      Crypto.ElGamal.decrypt encryptionSecret s'.rep = encode s'.R := by
  have hguard :
      Crypto.SchnorrReceipt.Verify H base signerKey
          receipt.message receipt.signature ∧
        receipt.message.index = s.idx ∧
        receipt.message.priorCipher = s.rep ∧
        receipt.message.refundPoint = encode (Cmax - receipt.message.cost) ∧
        receipt.message.rerandomizerCommitment = ρ • base :=
    ⟨hsig, hindex, hprior, hrefund, hrand⟩
  obtain ⟨s', hexec, hstep, hinv⟩ :=
    execElGamalAccept_refines Cmax D base encryptionSecret encode encode_add
      s receipt.message.cost ρ hlive hcost hsolvent hrep
  refine ⟨s', ?_, hstep, hinv⟩
  unfold execAuthenticatedElGamalAccept
  rw [if_pos hguard]
  exact hexec

end Zkpc.Refund

#print axioms Zkpc.Refund.execAuthenticatedElGamalAccept_refines
