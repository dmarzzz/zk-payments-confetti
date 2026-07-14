import Zkpc.Refund.Refinement
import Zkpc.Crypto.ElGamal

/-!
# ElGamal-encrypted refund-state refinement

This module connects the concrete rerandomizable public-key construction to
the executable refund transition.  A symbolic representation is now an
actual ElGamal ciphertext of the accumulated refund total.  On acceptance,
the executable transition homomorphically adds `encode (Cmax - cost)`,
rerandomizes, and updates the symbolic counter in the same step.
-/

namespace Zkpc.Refund

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- Execute an authenticated refund acceptance whose new representation is a
publicly rerandomized ElGamal encryption of the updated refund total. -/
def execElGamalAccept (Cmax D : ℕ) (base : G)
    (pk : Crypto.ElGamal.PublicKey G) (encode : ℕ → G)
    (s : St (Crypto.ElGamal.Cipher G)) (cost : ℕ) (ρ : F) :
    Option (St (Crypto.ElGamal.Cipher G)) :=
  let ct' := Crypto.ElGamal.refundUpdate base pk s.rep (encode (Cmax - cost)) ρ
  execAccept Cmax D s cost ct'

/-- One successful concrete encrypted acceptance simultaneously refines the
symbolic refund step and preserves the ciphertext/plaintext representation
invariant. -/
theorem execElGamalAccept_refines
    (Cmax D : ℕ) (base : G) (sk : F) (encode : ℕ → G)
    (encode_add : ∀ x y, encode (x + y) = encode x + encode y)
    (s : St (Crypto.ElGamal.Cipher G)) (cost : ℕ) (ρ : F)
    (hlive : s.closed = false) (hcost : cost ≤ Cmax)
    (hsolvent : (s.idx + 1) * Cmax ≤ D + s.R)
    (hrep : Crypto.ElGamal.decrypt sk s.rep = encode s.R) :
    ∃ s',
      execElGamalAccept Cmax D base
          (Crypto.ElGamal.derivePublic base sk) encode s cost ρ = some s' ∧
      Step Cmax D s (.accept cost s'.rep) s' ∧
      Crypto.ElGamal.decrypt sk s'.rep = encode s'.R := by
  let ct' := Crypto.ElGamal.refundUpdate base
    (Crypto.ElGamal.derivePublic base sk) s.rep (encode (Cmax - cost)) ρ
  let s' : St (Crypto.ElGamal.Cipher G) :=
    { s with idx := s.idx + 1
             R := s.R + (Cmax - cost)
             sumc := s.sumc + cost
             rep := ct' }
  refine ⟨s', ?_, ?_, ?_⟩
  · simp [execElGamalAccept, execAccept, hlive, hcost, hsolvent, ct', s']
  · exact Step.accept s cost ct' hlive hcost hsolvent
  · change Crypto.ElGamal.decrypt sk ct' = encode (s.R + (Cmax - cost))
    dsimp only [ct']
    rw [Crypto.ElGamal.decrypt_refundUpdate, hrep, encode_add]

end Zkpc.Refund

#print axioms Zkpc.Refund.execElGamalAccept_refines
