import Mathlib.Algebra.Field.Basic
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Concrete finite-field Sigma protocol for RLN line knowledge

For public `(x,y)`, the witness `(k,a)` satisfies `y = k + a*x`.  The
protocol commits with fresh `(tK,tA)`, receives challenge `c`, and responds
`(tK+c*k, tA+c*a)`.  Verification is the corresponding linear equation.

The module proves the three algebraic properties needed by a Fiat--Shamir or
interactive instantiation: completeness, perfect honest-verifier simulation
(via an explicit bijection between prover randomness and simulated
responses), and special soundness by extraction from two accepting
transcripts with the same commitment and distinct challenges.
-/

namespace Zkpc.Crypto.LinearSigma

variable {F : Type} [Field F]

open OracleSpec OracleComp

/-- Public RLN line point. -/
structure Statement (F : Type) where
  x : F
  y : F

/-- Secret line intercept and slope. -/
structure Witness (F : Type) where
  k : F
  a : F

/-- The NP relation proved by the protocol. -/
def Holds (st : Statement F) (w : Witness F) : Prop :=
  st.y = w.k + w.a * st.x

/-- First-message randomness. -/
structure Randomness (F : Type) where
  tK : F
  tA : F

/-- Complete public Sigma transcript. -/
structure Transcript (F : Type) where
  commitment : F
  challenge : F
  zK : F
  zA : F

/-- Linear first message. -/
def commit (st : Statement F) (r : Randomness F) : F :=
  r.tK + r.tA * st.x

/-- Honest prover transcript for a fixed verifier challenge. -/
def prove (st : Statement F) (w : Witness F) (r : Randomness F) (c : F) :
    Transcript F :=
  ⟨commit st r, c, r.tK + c * w.k, r.tA + c * w.a⟩

/-- Concrete transcript verifier. -/
def Verify (st : Statement F) (tr : Transcript F) : Prop :=
  tr.zK + tr.zA * st.x = tr.commitment + tr.challenge * st.y

/-- Honest proofs of true statements verify. -/
theorem completeness (st : Statement F) (w : Witness F) (r : Randomness F)
    (c : F) (hw : Holds st w) : Verify st (prove st w r c) := by
  unfold Verify prove commit Holds at *
  rw [hw]
  ring

/-- Honest-verifier simulator: sample responses and solve for the unique
commitment that makes the transcript accept. -/
def simulate (st : Statement F) (c zK zA : F) : Transcript F :=
  ⟨zK + zA * st.x - c * st.y, c, zK, zA⟩

/-- Every simulated transcript accepts, without a witness. -/
theorem simulate_verifies (st : Statement F) (c zK zA : F) :
    Verify st (simulate st c zK zA) := by
  unfold Verify simulate
  ring

/-- The honest transcript is definitionally the simulator applied to its
responses. This is the pointwise perfect-HVZK coupling. -/
theorem prove_eq_simulate (st : Statement F) (w : Witness F)
    (r : Randomness F) (c : F) (hw : Holds st w) :
    prove st w r c =
      simulate st c (r.tK + c * w.k) (r.tA + c * w.a) := by
  apply Transcript.ext <;> simp [prove, simulate, commit]
  unfold Holds at hw
  rw [hw]
  ring

/-- Translate prover randomness into response randomness. -/
def responses (w : Witness F) (c : F) (r : Randomness F) : Randomness F :=
  ⟨r.tK + c * w.k, r.tA + c * w.a⟩

/-- Recover prover randomness from simulated responses. -/
def unresponses (w : Witness F) (c : F) (z : Randomness F) : Randomness F :=
  ⟨z.tK - c * w.k, z.tA - c * w.a⟩

/-- Response translation is a bijection. Consequently uniform prover
randomness and uniform simulator responses have identical distributions. -/
def responseEquiv (w : Witness F) (c : F) : Randomness F ≃ Randomness F where
  toFun := responses w c
  invFun := unresponses w c
  left_inv := by
    intro r
    apply Randomness.ext <;> simp [responses, unresponses]
  right_inv := by
    intro z
    apply Randomness.ext <;> simp [responses, unresponses]

/-- Honest proof generation with a uniform verifier challenge and uniform
first-message randomness. -/
def realTranscript [SampleableType F] (st : Statement F) (w : Witness F) :
    ProbComp (Transcript F) := do
  let c ← ($ᵗ F)
  let tK ← ($ᵗ F)
  let tA ← ($ᵗ F)
  pure (prove st w ⟨tK, tA⟩ c)

/-- Honest-verifier simulator distribution. -/
def simulatedTranscript [SampleableType F] (st : Statement F) :
    ProbComp (Transcript F) := do
  let c ← ($ᵗ F)
  let zK ← ($ᵗ F)
  let zA ← ($ᵗ F)
  pure (simulate st c zK zA)

/-- Perfect honest-verifier zero knowledge as an equality of complete
transcript distributions, not merely a pointwise simulator equation. -/
theorem evalDist_real_eq_simulated [SampleableType F]
    (st : Statement F) (w : Witness F) (hw : Holds st w) :
    𝒹[realTranscript st w] = 𝒹[simulatedTranscript st] := by
  unfold realTranscript simulatedTranscript
  refine evalDist_bind_congr' ($ᵗ F) fun c => ?_
  calc
    𝒹[do
        let tK ← ($ᵗ F)
        let tA ← ($ᵗ F)
        pure (prove st w ⟨tK, tA⟩ c)] =
      𝒹[do
        let tK ← ($ᵗ F)
        let tA ← ($ᵗ F)
        pure (simulate st c (tK + c * w.k) (tA + c * w.a))] := by
          refine evalDist_bind_congr' ($ᵗ F) fun tK => ?_
          refine evalDist_bind_congr' ($ᵗ F) fun tA => ?_
          rw [prove_eq_simulate st w ⟨tK, tA⟩ c hw]
    _ = 𝒹[do
        let tK ← ($ᵗ F)
        let zA ← ($ᵗ F)
        pure (simulate st c (tK + c * w.k) zA)] := by
          refine evalDist_bind_congr' ($ᵗ F) fun tK => ?_
          exact evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
            Function.bijective_id (c * w.a)
            (fun zA => pure (simulate st c (tK + c * w.k) zA))
    _ = 𝒹[do
        let zK ← ($ᵗ F)
        let zA ← ($ᵗ F)
        pure (simulate st c zK zA)] :=
          evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
            Function.bijective_id (c * w.k)
            (fun zK => do
              let zA ← ($ᵗ F)
              pure (simulate st c zK zA))

/-- Normalize a public message digest into the nonzero line-coordinate
domain required for single-point hiding. -/
def nonzeroX (x : F) : F := if x = 0 then 1 else x

theorem nonzeroX_ne_zero (x : F) : nonzeroX x ≠ 0 := by
  unfold nonzeroX
  split
  · exact one_ne_zero
  · assumption

/-- Real RLN signal point together with its concrete proof transcript. -/
def realSignalProof [SampleableType F] (k m : F) :
    ProbComp (Statement F × Transcript F) := do
  let a ← ($ᵗ F)
  let st : Statement F := ⟨nonzeroX m, a * nonzeroX m + k⟩
  let tr ← realTranscript st ⟨k, a⟩
  pure (st, tr)

/-- Witness-free simulator for a complete signal/proof pair. -/
def simulatedSignalProof [SampleableType F] (m : F) :
    ProbComp (Statement F × Transcript F) := do
  let y ← ($ᵗ F)
  let st : Statement F := ⟨nonzeroX m, y⟩
  let tr ← simulatedTranscript st
  pure (st, tr)

/-- The complete verified RLN point and proof transcript is perfectly
simulatable without the member secret. This composes single-point hiding
with the Sigma transcript simulator and is the concrete T4 bridge kernel. -/
theorem evalDist_realSignalProof_eq_simulated [SampleableType F] (k m : F) :
    𝒹[realSignalProof k m] = 𝒹[simulatedSignalProof m] := by
  let x := nonzeroX m
  have hx : x ≠ 0 := nonzeroX_ne_zero m
  let f : F → F := fun a => a * x
  have hf : Function.Bijective f := mulRight_bijective₀ x hx
  unfold realSignalProof simulatedSignalProof
  calc
    𝒹[do
        let a ← ($ᵗ F)
        let st : Statement F := ⟨nonzeroX m, a * nonzeroX m + k⟩
        let tr ← realTranscript st ⟨k, a⟩
        pure (st, tr)] =
      𝒹[do
        let a ← ($ᵗ F)
        let st : Statement F := ⟨nonzeroX m, a * nonzeroX m + k⟩
        let tr ← simulatedTranscript st
        pure (st, tr)] := by
          refine evalDist_bind_congr' ($ᵗ F) fun a => ?_
          apply evalDist_map_eq_of_evalDist_eq
          apply evalDist_real_eq_simulated
          unfold Holds
          ring
    _ = 𝒹[do
        let y ← ($ᵗ F)
        let st : Statement F := ⟨nonzeroX m, y⟩
        let tr ← simulatedTranscript st
        pure (st, tr)] := by
          exact evalDist_bind_bijective_add_right_uniform f hf k
            (fun y => do
              let st : Statement F := ⟨nonzeroX m, y⟩
              let tr ← simulatedTranscript st
              pure (st, tr))

/-- Extract the unique witness from two response pairs at distinct
challenges. -/
def extract (tr₁ tr₂ : Transcript F) : Witness F :=
  ⟨(tr₁.zK - tr₂.zK) / (tr₁.challenge - tr₂.challenge),
   (tr₁.zA - tr₂.zA) / (tr₁.challenge - tr₂.challenge)⟩

/-- Special soundness: two accepting transcripts sharing a commitment but
using distinct challenges extract a valid RLN line witness. -/
theorem special_soundness (st : Statement F) (tr₁ tr₂ : Transcript F)
    (hv₁ : Verify st tr₁) (hv₂ : Verify st tr₂)
    (hcommit : tr₁.commitment = tr₂.commitment)
    (hchallenge : tr₁.challenge ≠ tr₂.challenge) :
    Holds st (extract tr₁ tr₂) := by
  unfold Verify at hv₁ hv₂
  unfold Holds extract
  have hden : tr₁.challenge - tr₂.challenge ≠ 0 := sub_ne_zero.mpr hchallenge
  field_simp
  rw [mul_sub]
  calc
    st.y * tr₁.challenge - st.y * tr₂.challenge =
        (tr₁.zK + tr₁.zA * st.x - tr₁.commitment) -
        (tr₂.zK + tr₂.zA * st.x - tr₂.commitment) := by
          rw [mul_comm st.y tr₁.challenge, mul_comm st.y tr₂.challenge]
          rw [← hv₁, ← hv₂]
          ring
    _ = (tr₁.zK - tr₂.zK) +
        (tr₁.zA - tr₂.zA) * st.x := by rw [hcommit]; ring

/-! ## Fiat--Shamir-shaped non-interactive proof -/

/-- A challenge oracle hashes the statement and first message. Keeping it as
an explicit function makes ROM programming and forking hypotheses visible. -/
abbrev ChallengeOracle (F : Type) := Statement F → F → F

/-- Non-interactive proof: the challenge is recomputed by the verifier. -/
structure FSProof (F : Type) where
  commitment : F
  zK : F
  zA : F

/-- Interpret an FS proof as its underlying Sigma transcript. -/
def fsTranscript (H : ChallengeOracle F) (st : Statement F) (pi : FSProof F) :
    Transcript F :=
  ⟨pi.commitment, H st pi.commitment, pi.zK, pi.zA⟩

/-- Fiat--Shamir prover for a deterministic challenge oracle. -/
def fsProve (H : ChallengeOracle F) (st : Statement F) (w : Witness F)
    (r : Randomness F) : FSProof F :=
  let T := commit st r
  let c := H st T
  ⟨T, r.tK + c * w.k, r.tA + c * w.a⟩

/-- Fiat--Shamir verifier. -/
def FSVerify (H : ChallengeOracle F) (st : Statement F) (pi : FSProof F) : Prop :=
  Verify st (fsTranscript H st pi)

/-- Fiat--Shamir completeness follows from Sigma completeness. -/
theorem fs_completeness (H : ChallengeOracle F) (st : Statement F)
    (w : Witness F) (r : Randomness F) (hw : Holds st w) :
    FSVerify H st (fsProve H st w r) := by
  exact completeness st w r (H st (commit st r)) hw

/-- Simulator proof obtained by solving for the first message at a chosen
challenge. It verifies whenever the programmable oracle returns that
challenge at the simulated query. -/
def fsSimulate (st : Statement F) (c zK zA : F) : FSProof F :=
  ⟨zK + zA * st.x - c * st.y, zK, zA⟩

/-- Programmed-ROM simulation correctness. -/
theorem fsSimulate_verifies (H : ChallengeOracle F) (st : Statement F)
    (c zK zA : F)
    (hprogram : H st (zK + zA * st.x - c * st.y) = c) :
    FSVerify H st (fsSimulate st c zK zA) := by
  unfold FSVerify fsTranscript fsSimulate
  rw [hprogram]
  exact simulate_verifies st c zK zA

/-- Extract from two accepting forked executions. The oracle answers differ
at the shared `(statement, commitment)` query, exactly the conclusion supplied
by a forking lemma; the algebraic extractor itself is unconditional. -/
theorem fs_fork_extracts (H₁ H₂ : ChallengeOracle F) (st : Statement F)
    (pi₁ pi₂ : FSProof F)
    (hcommit : pi₁.commitment = pi₂.commitment)
    (hv₁ : FSVerify H₁ st pi₁) (hv₂ : FSVerify H₂ st pi₂)
    (hchallenge : H₁ st pi₁.commitment ≠ H₂ st pi₂.commitment) :
    Holds st (extract (fsTranscript H₁ st pi₁) (fsTranscript H₂ st pi₂)) := by
  apply special_soundness st (fsTranscript H₁ st pi₁)
    (fsTranscript H₂ st pi₂) hv₁ hv₂
  · exact hcommit
  · exact hchallenge

end Zkpc.Crypto.LinearSigma

#print axioms Zkpc.Crypto.LinearSigma.completeness
#print axioms Zkpc.Crypto.LinearSigma.simulate_verifies
#print axioms Zkpc.Crypto.LinearSigma.prove_eq_simulate
#print axioms Zkpc.Crypto.LinearSigma.responseEquiv
#print axioms Zkpc.Crypto.LinearSigma.evalDist_real_eq_simulated
#print axioms Zkpc.Crypto.LinearSigma.evalDist_realSignalProof_eq_simulated
#print axioms Zkpc.Crypto.LinearSigma.special_soundness
#print axioms Zkpc.Crypto.LinearSigma.fs_completeness
#print axioms Zkpc.Crypto.LinearSigma.fsSimulate_verifies
#print axioms Zkpc.Crypto.LinearSigma.fs_fork_extracts
