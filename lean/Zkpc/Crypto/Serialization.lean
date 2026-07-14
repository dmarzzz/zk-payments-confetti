/-!
# Canonical cryptographic serialization

Deployed hashes and contracts consume bytes, while the proof development uses
typed messages.  `Codec` is the refinement boundary: decoding an encoding is
the original value.  This law immediately gives canonical-encoding
injectivity, which is the property needed to transport typed binding claims
to byte-oriented challenge oracles and contract inputs.
-/

namespace Zkpc.Crypto.Serialization

/-- A canonical, round-tripping encoding into a deployment byte type. -/
structure Codec (Bytes Value : Type) where
  encode : Value → Bytes
  decode : Bytes → Option Value
  decode_encode : ∀ value, decode (encode value) = some value

/-- Canonical encodings are injective. -/
theorem Codec.encode_injective {Bytes Value : Type} (codec : Codec Bytes Value) :
    Function.Injective codec.encode := by
  intro x y h
  have hx := codec.decode_encode x
  have hy := codec.decode_encode y
  rw [h, hy] at hx
  exact Option.some.inj hx.symm

/-- Equality of serialized cryptographic messages implies equality of every
typed field contained in them. -/
theorem Codec.binding {Bytes Value : Type} (codec : Codec Bytes Value)
    {x y : Value} (h : codec.encode x = codec.encode y) : x = y :=
  codec.encode_injective h

end Zkpc.Crypto.Serialization

#print axioms Zkpc.Crypto.Serialization.Codec.encode_injective
#print axioms Zkpc.Crypto.Serialization.Codec.binding
