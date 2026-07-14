import Zkpc.Refund.CryptoRefinement
import Zkpc.Crypto.Serialization

/-!
# Byte-level refund-call refinement

This module transports the authenticated encrypted refund executor across a
canonical deployment codec.  Malformed bytes reject; bytes produced by the
canonical encoder decode and execute exactly the typed operation.  Contract
ABI/RLP/SSZ implementations instantiate `Codec` and then only need to prove
their concrete round-trip law.
-/

namespace Zkpc.Refund

variable {F G ChannelTag Bytes : Type}
variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Decode a serialized receipt and run the typed authenticated executor. -/
def execSerializedAuthenticatedAccept
    (codec : Crypto.Serialization.Codec Bytes (CryptoReceipt F G ChannelTag))
    (H : Crypto.SchnorrReceipt.ChallengeOracle
      (F := F) (G := G) (Message := CryptoReceiptMessage G ChannelTag))
    (Cmax D : ℕ) (base signerKey encryptionKey : G)
    (encodeRefund : ℕ → G) (s : St (Crypto.ElGamal.Cipher G))
    (bytes : Bytes) (ρ : F) : Option (St (Crypto.ElGamal.Cipher G)) :=
  match codec.decode bytes with
  | none => none
  | some receipt =>
      execAuthenticatedElGamalAccept H Cmax D base signerKey encryptionKey
        encodeRefund s receipt ρ

/-- Canonically serialized calls execute exactly their typed counterpart. -/
theorem execSerialized_encode
    (codec : Crypto.Serialization.Codec Bytes (CryptoReceipt F G ChannelTag))
    (H : Crypto.SchnorrReceipt.ChallengeOracle
      (F := F) (G := G) (Message := CryptoReceiptMessage G ChannelTag))
    (Cmax D : ℕ) (base signerKey encryptionKey : G)
    (encodeRefund : ℕ → G) (s : St (Crypto.ElGamal.Cipher G))
    (receipt : CryptoReceipt F G ChannelTag) (ρ : F) :
    execSerializedAuthenticatedAccept codec H Cmax D base signerKey encryptionKey
        encodeRefund s (codec.encode receipt) ρ =
      execAuthenticatedElGamalAccept H Cmax D base signerKey encryptionKey
        encodeRefund s receipt ρ := by
  unfold execSerializedAuthenticatedAccept
  rw [codec.decode_encode]

/-- Byte-level successful calls inherit the complete typed refinement theorem. -/
theorem execSerializedAuthenticatedAccept_refines
    (codec : Crypto.Serialization.Codec Bytes (CryptoReceipt F G ChannelTag))
    (H : Crypto.SchnorrReceipt.ChallengeOracle
      (F := F) (G := G) (Message := CryptoReceiptMessage G ChannelTag))
    (Cmax D : ℕ) (base signerKey : G) (encryptionSecret : F)
    (encodeRefund : ℕ → G)
    (encode_add : ∀ x y, encodeRefund (x + y) = encodeRefund x + encodeRefund y)
    (s : St (Crypto.ElGamal.Cipher G))
    (receipt : CryptoReceipt F G ChannelTag) (ρ : F)
    (hsig : Crypto.SchnorrReceipt.Verify H base signerKey
      receipt.message receipt.signature)
    (hindex : receipt.message.index = s.idx)
    (hprior : receipt.message.priorCipher = s.rep)
    (hrefund : receipt.message.refundPoint =
      encodeRefund (Cmax - receipt.message.cost))
    (hrand : receipt.message.rerandomizerCommitment = ρ • base)
    (hlive : s.closed = false)
    (hcost : receipt.message.cost ≤ Cmax)
    (hsolvent : (s.idx + 1) * Cmax ≤ D + s.R)
    (hrep : Crypto.ElGamal.decrypt encryptionSecret s.rep = encodeRefund s.R) :
    ∃ s',
      execSerializedAuthenticatedAccept codec H Cmax D base signerKey
          (Crypto.ElGamal.derivePublic base encryptionSecret) encodeRefund s
          (codec.encode receipt) ρ = some s' ∧
      Step Cmax D s (.accept receipt.message.cost s'.rep) s' ∧
      Crypto.ElGamal.decrypt encryptionSecret s'.rep = encodeRefund s'.R := by
  rw [execSerialized_encode]
  exact execAuthenticatedElGamalAccept_refines H Cmax D base signerKey
    encryptionSecret encodeRefund encode_add s receipt ρ hsig hindex hprior
    hrefund hrand hlive hcost hsolvent hrep

end Zkpc.Refund

#print axioms Zkpc.Refund.execSerializedAuthenticatedAccept_refines
