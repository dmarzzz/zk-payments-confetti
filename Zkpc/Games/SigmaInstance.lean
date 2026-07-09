import Zkpc.Crypto.LinearSigma
import Zkpc.Games.FullTicketInstance

/-!
# Verified Sigma-proof T4 instance

This instance replaces the opaque proof field of the ideal full-ticket game
with a concrete accepting transcript for knowledge of the RLN line witness.
The prover carries member secret `k`; each spend samples a fresh slope and
emits the resulting point plus its proof. `LinearSigma` proves that the whole
point/proof pair is exactly simulatable, which lifts here to arbitrary solvent
challenge batches and zero UNLINK advantage.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

open Zkpc.Crypto.LinearSigma

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]

/-- Complete verified wire view. -/
structure SigmaFlatView (F : Type) where
  root : F
  epoch : ℕ
  nfe : F
  message : F
  nf : F
  statement : Statement F
  proof : Transcript F

/-- Payer state retaining the proof witness and retry ticket. -/
structure SigmaFlatPSt (F : Type) where
  key : F
  idx : ℕ
  last : Option (SigmaFlatView F)

end Zkpc.Games
