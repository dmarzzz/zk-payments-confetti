import Mathlib.Algebra.Field.Basic

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

end Zkpc.Crypto.LinearSigma

#print axioms Zkpc.Crypto.LinearSigma.completeness
#print axioms Zkpc.Crypto.LinearSigma.simulate_verifies
#print axioms Zkpc.Crypto.LinearSigma.prove_eq_simulate
#print axioms Zkpc.Crypto.LinearSigma.responseEquiv
#print axioms Zkpc.Crypto.LinearSigma.special_soundness
