import Zkpc.Network.Scheduler
import Zkpc.Crypto.Serialization

/-!
# Serialized adversarial network scheduler

This is the byte-oriented contract entrypoint for the portable network.  Each
submitted blob is decoded independently: malformed blobs reject and later
transactions continue; decoded actions use the total adversarial scheduler.
The resulting state remains symbolically reachable for every byte sequence.
-/

namespace Zkpc.Network

variable {Recipient Nf Payload Bytes : Type}
variable [DecidableEq Recipient] [DecidableEq Nf] [DecidableEq Payload]

/-- Decode and execute one submitted transaction blob. -/
def execSerializedTransaction
    (codec : Crypto.Serialization.Codec Bytes (Act Recipient Nf Payload))
    (s : St Recipient Nf Payload) (bytes : Bytes) :
    TxOutcome × St Recipient Nf Payload :=
  match codec.decode bytes with
  | none => (.rejected, s)
  | some action => execTransaction s action

/-- Execute an arbitrary serialized mempool ordering. -/
def execSerializedSchedule
    (codec : Crypto.Serialization.Codec Bytes (Act Recipient Nf Payload)) :
    St Recipient Nf Payload → List Bytes →
      List TxOutcome × St Recipient Nf Payload
  | s, [] => ([], s)
  | s, bytes :: rest =>
      let (outcome, s') := execSerializedTransaction codec s bytes
      let (outcomes, t) := execSerializedSchedule codec s' rest
      (outcome :: outcomes, t)

/-- Canonically encoded actions execute exactly the typed transaction. -/
theorem execSerializedTransaction_encode
    (codec : Crypto.Serialization.Codec Bytes (Act Recipient Nf Payload))
    (s : St Recipient Nf Payload) (action : Act Recipient Nf Payload) :
    execSerializedTransaction codec s (codec.encode action) =
      execTransaction s action := by
  unfold execSerializedTransaction
  rw [codec.decode_encode]

/-- Every serialized transaction, including malformed input, preserves
reachability. -/
theorem execSerializedTransaction_reachable
    (codec : Crypto.Serialization.Codec Bytes (Act Recipient Nf Payload))
    {D : ℕ} {s : St Recipient Nf Payload} (hreach : Reach D s)
    (bytes : Bytes) : Reach D (execSerializedTransaction codec s bytes).2 := by
  unfold execSerializedTransaction
  cases hdecode : codec.decode bytes with
  | none => exact hreach
  | some action => exact execTransaction_reachable hreach action

/-- Every adversarial byte schedule preserves symbolic reachability. -/
theorem execSerializedSchedule_reachable
    (codec : Crypto.Serialization.Codec Bytes (Act Recipient Nf Payload))
    {D : ℕ} {s : St Recipient Nf Payload} (hreach : Reach D s) :
    ∀ blobs, Reach D (execSerializedSchedule codec s blobs).2 := by
  intro blobs
  induction blobs generalizing s with
  | nil => exact hreach
  | cons bytes blobs ih =>
      simp only [execSerializedSchedule]
      cases htx : execSerializedTransaction codec s bytes with
      | mk outcome s' =>
          simp only
          apply ih
          have hs' := execSerializedTransaction_reachable codec hreach bytes
          simpa [htx] using hs'

/-- **Serialized scheduler safety.** No byte sequence can cause global replay
or spend beyond the portable deposit. -/
theorem execSerializedSchedule_safety
    (codec : Crypto.Serialization.Codec Bytes (Act Recipient Nf Payload))
    (D : ℕ) (blobs : List Bytes) :
    let terminal := (execSerializedSchedule codec (init D) blobs).2
    terminal.totalPaid ≤ D ∧ NfUnique terminal.accepted := by
  intro terminal
  have hreach : Reach D terminal :=
    execSerializedSchedule_reachable codec Reach.init blobs
  exact ⟨no_overspend hreach, global_dedup hreach⟩

end Zkpc.Network

#print axioms Zkpc.Network.execSerializedTransaction_encode
#print axioms Zkpc.Network.execSerializedSchedule_reachable
#print axioms Zkpc.Network.execSerializedSchedule_safety
