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

/-- One real verified-proof spend. -/
def sigmaFlatSpend (budget e : ℕ) (st : SigmaFlatPSt F) (m : F) :
    ProbComp (Option (SigmaFlatView F × SigmaFlatPSt F)) :=
  if st.idx < budget then do
    let nfe ← ($ᵗ F)
    let nf ← ($ᵗ F)
    let (statement, proof) ← realSignalProof st.key m
    let v : SigmaFlatView F :=
      ⟨0, e, nfe, m, nf, statement, proof⟩
    pure (some (v, ⟨st.key, st.idx + 1, some v⟩))
  else pure none

/-- Concrete proof-bearing UNLINK instance. -/
def sigmaFlatInstance (budget : ℕ) : UnlinkScheme where
  M := F
  View := SigmaFlatView F
  CloseView := List F
  OpenView := PUnit
  GenesisInput := PUnit
  Receipt := PUnit
  PSt := SigmaFlatPSt F
  openCh _ := do
    let key ← ($ᵗ F)
    pure (⟨key, 0, none⟩, PUnit.unit)
  spend e st m := sigmaFlatSpend budget e st m
  lastTicket st := st.last
  serve st _ := st
  close _ st := do
    let U ← freshFList (budget - st.idx)
    pure (U, st)
  capableFor q st := decide (st.idx + q ≤ budget)

/-- Witness-free simulator distribution for a solvent session. -/
def sigmaFreshBatch (e : ℕ) : List F → ProbComp (Option (List (SigmaFlatView F)))
  | [] => pure (some [])
  | m :: ms => do
      let nfe ← ($ᵗ F)
      let nf ← ($ᵗ F)
      let (statement, proof) ← simulatedSignalProof m
      let v : SigmaFlatView F := ⟨0, e, nfe, m, nf, statement, proof⟩
      Option.map (v :: ·) <$> sigmaFreshBatch e ms

/-- Every solvent real-prover batch equals the witness-free simulator batch. -/
lemma evalDist_spendBatch_sigmaFlat (budget e : ℕ) :
    ∀ (ms : List F) (st : SigmaFlatPSt F), st.idx + ms.length ≤ budget →
      𝒹[spendBatch (sigmaFlatInstance (F := F) budget) e st ms] =
        𝒹[sigmaFreshBatch e ms] := by
  intro ms
  induction ms with
  | nil => intro st _; rfl
  | cons m ms ih =>
      intro st hst
      have hsolv : st.idx < budget := by
        have : st.idx + (ms.length + 1) ≤ budget := by simpa using hst
        omega
      simp only [spendBatch, sigmaFlatInstance, sigmaFlatSpend, sigmaFreshBatch,
        if_pos hsolv, bind_assoc, pure_bind]
      refine evalDist_bind_congr' ($ᵗ F) fun nfe => ?_
      refine evalDist_bind_congr' ($ᵗ F) fun nf => ?_
      rw [evalDist_bind, evalDist_realSignalProof_eq_simulated st.key m, ← evalDist_bind]
      refine evalDist_bind_congr' (simulatedSignalProof m) fun p => ?_
      rcases p with ⟨statement, proof⟩
      apply evalDist_map_eq_of_evalDist_eq
      apply ih
      show st.idx + 1 + ms.length ≤ budget
      omega

private lemma sigma_capable_of_challengeCapable (budget : ℕ)
    (g : GSt (sigmaFlatInstance (F := F) budget)) (q : ℕ)
    (h : challengeCapable (sigmaFlatInstance (F := F) budget) g q = true) :
    (g.cand false).idx + q ≤ budget ∧ (g.cand true).idx + q ≤ budget := by
  simp only [challengeCapable, sigmaFlatInstance, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2.2⟩

/-- The complete verified-proof challenge distribution is hidden-bit free. -/
theorem challengeResp_sigmaFlat_bitfree (budget : ℕ)
    (g : GSt (sigmaFlatInstance (F := F) budget)) (ms : List F) (b b' : Bool) :
    𝒹[challengeResp (sigmaFlatInstance (F := F) budget) g b ms] =
      𝒹[challengeResp (sigmaFlatInstance (F := F) budget) g b' ms] := by
  unfold challengeResp
  split_ifs with hcond
  · have hcap : challengeCapable (sigmaFlatInstance (F := F) budget)
        g ms.length = true := by
      simp only [Bool.and_eq_true] at hcond
      exact hcond.2
    obtain ⟨hf, ht⟩ := sigma_capable_of_challengeCapable budget g ms.length hcap
    rw [evalDist_spendBatch_sigmaFlat budget g.epoch ms (g.cand b)
        (by cases b <;> assumption),
      evalDist_spendBatch_sigmaFlat budget g.epoch ms (g.cand b')
        (by cases b' <;> assumption)]
  · rfl

/-- T4 for the concrete verified Sigma-proof wire protocol. -/
theorem T4_sigmaFlat_unlinkability (budget : ℕ)
    (A : UnlinkAdversary (sigmaFlatInstance (F := F) budget)) :
    unlinkAdvantage (sigmaFlatInstance (F := F) budget) A = 0 :=
  unlinkAdvantage_eq_zero_of_challenge_bitfree _ A
    (challengeResp_sigmaFlat_bitfree budget)

/-- Concrete zero-loss bridge from verified Sigma transcripts to the
proof-free flat-ticket result. -/
theorem sigmaFlat_zkBridge (budget : ℕ) :
    zkBridgeObligation (sigmaFlatInstance (F := F) budget)
      (flatInstance (F := F) budget) 0 := by
  intro A
  refine ⟨flatDummyAdversary budget, ?_⟩
  rw [T4_sigmaFlat_unlinkability budget A]
  exact add_nonneg (abs_nonneg _) (le_refl 0)

end Zkpc.Games

#print axioms Zkpc.Games.evalDist_spendBatch_sigmaFlat
#print axioms Zkpc.Games.challengeResp_sigmaFlat_bitfree
#print axioms Zkpc.Games.T4_sigmaFlat_unlinkability
#print axioms Zkpc.Games.sigmaFlat_zkBridge
