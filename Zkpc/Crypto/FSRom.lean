import Zkpc.Crypto.LinearSigma
import VCVio

/-!
# Lazy-ROM Fiat--Shamir: distributional simulation and the programming loss

`LinearSigma` gives the Fiat--Shamir proof object its deterministic verifier,
completeness, pointwise programmed-oracle simulator, and algebraic fork
extractor. This module supplies the *probabilistic* random-oracle layer
(Spec.md assumption 2, issue #4):

* `fsProveLazy` / `fsSimulateLazy` — the honest FS prover and the witness-free
  simulator under **lazy random-oracle evaluation**: the challenge at the fresh
  `(statement, commitment)` slot is a uniform sample. Lazy sampling is the
  standard ROM semantics; the slot is fresh for the honest prover because the
  commitment carries fresh first-message randomness.
* `evalDist_fsProveLazy_eq_simulated` — **distributional zero-knowledge for
  the lazily evaluated FS proof**: the real proof object and the simulated one
  are equal as distributions (not merely pointwise related). This is the
  non-interactive counterpart of `evalDist_real_eq_simulated`.
* `evalDist_fsRealSignalProofLazy_eq_simulated` — the same equality for a
  complete RLN signal (statement plus FS proof), the FS counterpart of
  `evalDist_realSignalProof_eq_simulated`.
* `fsProgramCollisionBound` — the **concrete query-dependent programming
  loss**: an adversary making `q` adaptive oracle probes hits the hidden
  fresh-uniform programmed slot with probability at most `q/|F|`. Outside that
  event the simulator's programmed answer is consistent with lazy evaluation,
  so the ROM reduction loses exactly this term.
* `fsForkChallengeCollisionBound` — the forking-side loss: a rerun's
  independent uniform challenge collides with the first run's challenge with
  probability exactly `1/|F|`; outside that event `fs_fork_extracts` extracts
  the witness unconditionally.

Scope note: this lazy-ROM model has no shared oracle channel between the
prover/simulator and an adversary — each lemma samples its own fresh slots.
Accordingly `fsProgramCollisionBound` and `fsForkChallengeCollisionBound` are
standalone hidden-target kernels; composing them with the FS oracle semantics
(a common programmable oracle queried by an adaptive adversary, and the final
query-dependent knowledge-soundness loss) is the open reduction tracked as
`ROADMAP-STATUS.md` remaining item 2.
-/

open OracleSpec OracleComp

namespace Zkpc.Crypto.LinearSigma

variable {F : Type} [Field F] [DecidableEq F]

section LazyROM

variable [SampleableType F]

/-- Honest FS prover under lazy ROM evaluation: the challenge at the fresh
`(statement, commitment)` slot is sampled uniformly, then the prover responds
exactly as `fsProve` with an oracle programmed to that sample. -/
def fsProveLazy (st : Statement F) (w : Witness F) : ProbComp (FSProof F) := do
  let c ← ($ᵗ F)
  let tK ← ($ᵗ F)
  let tA ← ($ᵗ F)
  pure (fsProve (fun _ _ => c) st w ⟨tK, tA⟩)

/-- Witness-free FS simulator under lazy ROM programming: fresh uniform
challenge and responses, commitment solved by `fsSimulate`. -/
def fsSimulateLazy (st : Statement F) : ProbComp (FSProof F) := do
  let c ← ($ᵗ F)
  let zK ← ($ᵗ F)
  let zA ← ($ᵗ F)
  pure (fsSimulate st c zK zA)

/-- Pointwise transport: the honest lazy FS proof at randomness `(tK, tA)`
IS the simulated proof at the transported responses. -/
theorem fsProve_const_eq_fsSimulate (st : Statement F) (w : Witness F)
    (hw : Holds st w) (c tK tA : F) :
    fsProve (fun _ _ => c) st w ⟨tK, tA⟩
      = fsSimulate st c (tK + c * w.k) (tA + c * w.a) := by
  unfold fsProve fsSimulate commit
  simp only [FSProof.mk.injEq, and_true, true_and, and_self]
  rw [hw]
  ring

/-- **Distributional ZK for the lazily evaluated FS proof**: real and
simulated FS proof objects have identical distributions. -/
theorem evalDist_fsProveLazy_eq_simulated [Fintype F] (st : Statement F)
    (w : Witness F) (hw : Holds st w) :
    𝒟[fsProveLazy st w] = 𝒟[fsSimulateLazy st] := by
  unfold fsProveLazy fsSimulateLazy
  refine evalDist_bind_congr' ($ᵗ F) fun c => ?_
  calc
    𝒟[do
        let tK ← ($ᵗ F)
        let tA ← ($ᵗ F)
        pure (fsProve (fun _ _ => c) st w ⟨tK, tA⟩)] =
      𝒟[do
        let tK ← ($ᵗ F)
        let tA ← ($ᵗ F)
        pure (fsSimulate st c (tK + c * w.k) (tA + c * w.a))] := by
          refine evalDist_bind_congr' ($ᵗ F) fun tK => ?_
          refine evalDist_bind_congr' ($ᵗ F) fun tA => ?_
          rw [fsProve_const_eq_fsSimulate st w hw]
    _ = 𝒟[do
        let zK ← ($ᵗ F)
        let tA ← ($ᵗ F)
        pure (fsSimulate st c zK (tA + c * w.a))] := by
          exact evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
            Function.bijective_id (c * w.k) (fun zK => do
              let tA ← ($ᵗ F)
              pure (fsSimulate st c zK (tA + c * w.a)))
    _ = 𝒟[do
        let zK ← ($ᵗ F)
        let zA ← ($ᵗ F)
        pure (fsSimulate st c zK zA)] := by
          refine evalDist_bind_congr' ($ᵗ F) fun zK => ?_
          exact evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
            Function.bijective_id (c * w.a)
            (fun zA => pure (fsSimulate st c zK zA))

/-- A real RLN point paired with a lazily evaluated FS proof. -/
def fsRealSignalProofLazy (k m : F) :
    ProbComp (Statement F × FSProof F) := do
  let a ← ($ᵗ F)
  let st : Statement F := ⟨nonzeroX m, a * nonzeroX m + k⟩
  let pi ← fsProveLazy st ⟨k, a⟩
  pure (st, pi)

/-- Witness-free simulator for a complete RLN point and FS proof. -/
def fsSimulatedSignalProofLazy (m : F) :
    ProbComp (Statement F × FSProof F) := do
  let y ← ($ᵗ F)
  let st : Statement F := ⟨nonzeroX m, y⟩
  let pi ← fsSimulateLazy st
  pure (st, pi)

/-- A fresh slope hides the RLN intercept even when the complete
non-interactive FS proof is included: the FS counterpart of
`evalDist_realSignalProof_eq_simulated`. -/
theorem evalDist_fsRealSignalProofLazy_eq_simulated [Fintype F] (k m : F) :
    𝒟[fsRealSignalProofLazy k m] = 𝒟[fsSimulatedSignalProofLazy m] := by
  let x := nonzeroX m
  have hx : x ≠ 0 := nonzeroX_ne_zero m
  let f : F → F := fun a => a * x
  have hf : Function.Bijective f := mulRight_bijective₀ x hx
  unfold fsRealSignalProofLazy fsSimulatedSignalProofLazy
  calc
    𝒟[do
        let a ← ($ᵗ F)
        let st : Statement F := ⟨nonzeroX m, a * nonzeroX m + k⟩
        let pi ← fsProveLazy st ⟨k, a⟩
        pure (st, pi)] =
      𝒟[do
        let a ← ($ᵗ F)
        let st : Statement F := ⟨nonzeroX m, a * nonzeroX m + k⟩
        let pi ← fsSimulateLazy st
        pure (st, pi)] := by
          refine evalDist_bind_congr' ($ᵗ F) fun a => ?_
          apply evalDist_map_eq_of_evalDist_eq
          apply evalDist_fsProveLazy_eq_simulated
          unfold Holds
          ring
    _ = 𝒟[do
        let y ← ($ᵗ F)
        let st : Statement F := ⟨nonzeroX m, y⟩
        let pi ← fsSimulateLazy st
        pure (st, pi)] := by
          exact evalDist_bind_bijective_add_right_uniform (α := F) (β := F) f hf k
            (fun y => do
              let st : Statement F := ⟨nonzeroX m, y⟩
              let pi ← fsSimulateLazy st
              pure (st, pi))

end LazyROM

section Loss

variable [SampleableType F] [Fintype F]

/-- **The FS programming loss is `q/|F|`.** The simulator programs the
challenge oracle at a hidden fresh-uniform commitment slot; an adversary
making `q` adaptive probes (each probe a candidate slot, adaptivity modeled
by the strategy `σ` over the probe history) fires on the programmed slot
with probability at most `q/|F|`. Outside this event the programmed oracle
is indistinguishable from lazy evaluation, so `q/|F|` is the concrete
query-dependent ROM loss of `evalDist_fsProveLazy_eq_simulated`. -/
theorem fsProgramCollisionBound (q : ℕ) (σ : List Bool → F) :
    Pr[(fun b : Bool => b = true) |
        OracleComp.hiddenReadMany ($ᵗ F) q σ]
      ≤ (q : ENNReal) * (Fintype.card F : ENNReal)⁻¹ :=
  OracleComp.probEvent_hiddenReadMany_le
    (fun r : F => (probOutput_uniformSample F r).le) q σ

/-- **The forking loss is `1/|F|`.** A rerun's independent uniform challenge
collides with the first run's challenge with probability at most `1/|F|`;
outside this event two accepting forked executions satisfy the distinctness
hypothesis of `fs_fork_extracts` and the witness is extracted
unconditionally. -/
theorem fsForkChallengeCollisionBound (c₁ : F) :
    Pr[(fun c : F => c = c₁) | ($ᵗ F)]
      ≤ (Fintype.card F : ENNReal)⁻¹ := by
  rw [probEvent_eq_eq_probOutput]
  exact (probOutput_uniformSample F c₁).le

end Loss

end Zkpc.Crypto.LinearSigma

#print axioms Zkpc.Crypto.LinearSigma.fsProve_const_eq_fsSimulate
#print axioms Zkpc.Crypto.LinearSigma.evalDist_fsProveLazy_eq_simulated
#print axioms Zkpc.Crypto.LinearSigma.evalDist_fsRealSignalProofLazy_eq_simulated
#print axioms Zkpc.Crypto.LinearSigma.fsProgramCollisionBound
#print axioms Zkpc.Crypto.LinearSigma.fsForkChallengeCollisionBound
