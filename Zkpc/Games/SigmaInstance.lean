import Zkpc.Crypto.LinearSigma
import Zkpc.Crypto.FSRom
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

section Interactive

variable [Fintype F]

/-- One real verified-proof spend. -/
def sigmaFlatSpend (budget e : ℕ) (st : SigmaFlatPSt F) (m : F) :
    ProbComp (Option (SigmaFlatView F × SigmaFlatPSt F)) :=
  if st.idx < budget then do
    let nfe ← ($ᵗ F)
    let nf ← ($ᵗ F)
    let (statement, proof) ← realSignalProof st.key m
    let v : SigmaFlatView F := ⟨0, e, nfe, m, nf, statement, proof⟩
    pure (some (v, ⟨st.key, st.idx + 1, some v⟩))
  else pure none

/-- Concrete proof-bearing UNLINK instance for the interactive Sigma wire. -/
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

/-- Witness-free simulator distribution for a solvent interactive session. -/
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
      𝒟[spendBatch (sigmaFlatInstance (F := F) budget) e st ms] =
        𝒟[sigmaFreshBatch e ms] := by
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
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hst

private lemma sigmaFlat_capable_of_challengeCapable (budget : ℕ)
    (g : GSt (sigmaFlatInstance (F := F) budget)) (q : ℕ)
    (h : challengeCapable (sigmaFlatInstance (F := F) budget) g q = true) :
    (g.cand false).idx + q ≤ budget ∧ (g.cand true).idx + q ≤ budget := by
  simp only [challengeCapable, sigmaFlatInstance, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2.2⟩

/-- The verified-Sigma challenge distribution is hidden-bit independent: both
candidate sessions produce exactly the witness-free simulator batch. -/
theorem challengeResp_sigmaFlat_bitfree (budget : ℕ)
    (g : GSt (sigmaFlatInstance (F := F) budget)) (ms : List F) (b b' : Bool) :
    𝒟[challengeResp (sigmaFlatInstance (F := F) budget) g b ms] =
      𝒟[challengeResp (sigmaFlatInstance (F := F) budget) g b' ms] := by
  unfold challengeResp
  split_ifs with hcond
  · have hcap : challengeCapable (sigmaFlatInstance (F := F) budget) g
        ms.length = true := by
      simp only [Bool.and_eq_true] at hcond
      exact hcond.2
    obtain ⟨hf, ht⟩ := sigmaFlat_capable_of_challengeCapable budget g ms.length hcap
    rw [evalDist_spendBatch_sigmaFlat budget g.epoch ms (g.cand b)
        (by cases b <;> assumption),
      evalDist_spendBatch_sigmaFlat budget g.epoch ms (g.cand b')
        (by cases b' <;> assumption)]
  · rfl

/-- **T4 for the verified interactive Sigma wire protocol** (Spec.md T4): the
spend view carrying a real accepting RLN-line transcript is perfectly
unlinkable — every adversary has advantage exactly `0`. -/
theorem T4_sigmaFlat_unlinkability (budget : ℕ)
    (A : UnlinkAdversary (sigmaFlatInstance (F := F) budget)) :
    unlinkAdvantage (sigmaFlatInstance (F := F) budget) A = 0 :=
  unlinkAdvantage_eq_zero_of_challenge_bitfree _ A
    (challengeResp_sigmaFlat_bitfree budget)

/-- **O1 discharge for the interactive Sigma wire** (Spec.md assumption 2):
witness-dependent Sigma transcripts are exactly simulatable, so every
real-wire adversary is bounded by the proof-free game with zero ZK loss. -/
theorem sigmaFlat_zkBridge [Inhabited F] (budget : ℕ) :
    zkBridgeObligation (sigmaFlatInstance (F := F) budget)
      (flatInstance (F := F) budget) 0 := by
  intro A
  refine ⟨flatDummyAdversary budget, ?_⟩
  rw [T4_sigmaFlat_unlinkability budget A]
  exact add_nonneg (abs_nonneg _) (le_refl 0)

end Interactive

section NonInteractive

variable [Fintype F]

/-- Complete non-interactive (Fiat--Shamir) wire view. -/
structure FSFlatView (F : Type) where
  root : F
  epoch : ℕ
  nfe : F
  message : F
  nf : F
  statement : Statement F
  proof : FSProof F

/-- One real FS-verified spend under lazy ROM evaluation. -/
def fsFlatSpend (budget e : ℕ) (st : SigmaFlatPSt F) (m : F) :
    ProbComp (Option (FSFlatView F × SigmaFlatPSt F)) :=
  if st.idx < budget then do
    let nfe ← ($ᵗ F)
    let nf ← ($ᵗ F)
    let (statement, proof) ← fsRealSignalProofLazy st.key m
    let v : FSFlatView F := ⟨0, e, nfe, m, nf, statement, proof⟩
    pure (some (v, ⟨st.key, st.idx + 1, none⟩))
  else pure none

/-- Concrete proof-bearing UNLINK instance for the FS wire type. -/
def fsFlatInstance (budget : ℕ) : UnlinkScheme where
  M := F
  View := FSFlatView F
  CloseView := List F
  OpenView := PUnit
  GenesisInput := PUnit
  Receipt := PUnit
  PSt := SigmaFlatPSt F
  openCh _ := do
    let key ← ($ᵗ F)
    pure (⟨key, 0, none⟩, PUnit.unit)
  spend e st m := fsFlatSpend budget e st m
  lastTicket _ := none
  serve st _ := st
  close _ st := do
    let U ← freshFList (budget - st.idx)
    pure (U, st)
  capableFor q st := decide (st.idx + q ≤ budget)

/-- Witness-free simulator distribution for a solvent FS session. -/
def fsFreshBatch (e : ℕ) : List F → ProbComp (Option (List (FSFlatView F)))
  | [] => pure (some [])
  | m :: ms => do
      let nfe ← ($ᵗ F)
      let nf ← ($ᵗ F)
      let (statement, proof) ← fsSimulatedSignalProofLazy m
      let v : FSFlatView F := ⟨0, e, nfe, m, nf, statement, proof⟩
      Option.map (v :: ·) <$> fsFreshBatch e ms

/-- Every solvent real FS batch equals the witness-free simulator batch. -/
lemma evalDist_spendBatch_fsFlat (budget e : ℕ) :
    ∀ (ms : List F) (st : SigmaFlatPSt F), st.idx + ms.length ≤ budget →
      𝒟[spendBatch (fsFlatInstance (F := F) budget) e st ms] =
        𝒟[fsFreshBatch e ms] := by
  intro ms
  induction ms with
  | nil => intro st _; rfl
  | cons m ms ih =>
      intro st hst
      have hsolv : st.idx < budget := by
        have : st.idx + (ms.length + 1) ≤ budget := by simpa using hst
        omega
      simp only [spendBatch, fsFlatInstance, fsFlatSpend, fsFreshBatch,
        if_pos hsolv, bind_assoc, pure_bind]
      refine evalDist_bind_congr' ($ᵗ F) fun nfe => ?_
      refine evalDist_bind_congr' ($ᵗ F) fun nf => ?_
      rw [evalDist_bind, evalDist_fsRealSignalProofLazy_eq_simulated st.key m,
        ← evalDist_bind]
      refine evalDist_bind_congr' (fsSimulatedSignalProofLazy m) fun p => ?_
      rcases p with ⟨statement, proof⟩
      apply evalDist_map_eq_of_evalDist_eq
      apply ih
      show st.idx + 1 + ms.length ≤ budget
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hst

private lemma fsFlat_capable_of_challengeCapable (budget : ℕ)
    (g : GSt (fsFlatInstance (F := F) budget)) (q : ℕ)
    (h : challengeCapable (fsFlatInstance (F := F) budget) g q = true) :
    (g.cand false).idx + q ≤ budget ∧ (g.cand true).idx + q ≤ budget := by
  simp only [challengeCapable, fsFlatInstance, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2.2⟩

/-- The FS challenge distribution is hidden-bit independent. -/
theorem challengeResp_fsFlat_bitfree (budget : ℕ)
    (g : GSt (fsFlatInstance (F := F) budget)) (ms : List F) (b b' : Bool) :
    𝒟[challengeResp (fsFlatInstance (F := F) budget) g b ms] =
      𝒟[challengeResp (fsFlatInstance (F := F) budget) g b' ms] := by
  unfold challengeResp
  split_ifs with hcond
  · have hcap : challengeCapable (fsFlatInstance (F := F) budget) g
        ms.length = true := by
      simp only [Bool.and_eq_true] at hcond
      exact hcond.2
    obtain ⟨hf, ht⟩ := fsFlat_capable_of_challengeCapable budget g ms.length hcap
    rw [evalDist_spendBatch_fsFlat budget g.epoch ms (g.cand b)
        (by cases b <;> assumption),
      evalDist_spendBatch_fsFlat budget g.epoch ms (g.cand b')
        (by cases b' <;> assumption)]
  · rfl

/-- **T4 for the non-interactive FS wire protocol** (Spec.md T4): the spend
view carrying a lazily evaluated Fiat--Shamir proof of the RLN line relation
is perfectly unlinkable in the fresh-slot ROM. The query-dependent
programming loss `q/|F|` of the full ROM reduction is
`LinearSigma.fsProgramCollisionBound`. -/
theorem T4_fsFlat_unlinkability (budget : ℕ)
    (A : UnlinkAdversary (fsFlatInstance (F := F) budget)) :
    unlinkAdvantage (fsFlatInstance (F := F) budget) A = 0 :=
  unlinkAdvantage_eq_zero_of_challenge_bitfree _ A
    (challengeResp_fsFlat_bitfree budget)

/-- **O1 discharge for the FS wire type** (Spec.md assumption 2, issue #4):
lazily evaluated FS proofs are exactly simulatable on fresh slots, so every
real-wire adversary is bounded by the proof-free game with zero loss in this
model; the residual ROM programming loss is quantified separately as
`q/|F|` by `fsProgramCollisionBound`. -/
theorem fsFlat_zkBridge [Inhabited F] (budget : ℕ) :
    zkBridgeObligation (fsFlatInstance (F := F) budget)
      (flatInstance (F := F) budget) 0 := by
  intro A
  refine ⟨flatDummyAdversary budget, ?_⟩
  rw [T4_fsFlat_unlinkability budget A]
  exact add_nonneg (abs_nonneg _) (le_refl 0)

/-- Concrete real-valued ROM programming loss paid by a `q`-query
Fiat--Shamir simulator over challenge field `F`. -/
noncomputable def fsProgrammingLoss (q : ℕ) : ℝ :=
  ((q : ENNReal) * (Fintype.card F : ENNReal)⁻¹).toReal

/-- Proof-bearing certificate joining the session-level T4 bridge to the
adaptive hidden-programming-slot experiment.  The strategy receives the full
hit/miss history, hence may choose all `q` probes adaptively. -/
structure FSQueryBridgeCertificate [Inhabited F] (budget q : ℕ)
    (σ : List Bool → F) : Prop where
  zkBridge :
    zkBridgeObligation (fsFlatInstance (F := F) budget)
      (flatInstance (F := F) budget) (fsProgrammingLoss (F := F) q)
  programmingBadBound :
    Pr[(fun b : Bool => b = true) |
        OracleComp.hiddenReadMany ($ᵗ F) q σ]
      ≤ (q : ENNReal) * (Fintype.card F : ENNReal)⁻¹

/-- **Query-bounded proof-bearing T4/FS bridge.** The verified FS wire session
is related to the proof-free T4 game while explicitly carrying the adaptive
ROM programming loss `q/|F|`.  In the fresh-slot reference semantics the
session bridge itself is exact; weakening it by the concrete loss and pairing
it with `fsProgramCollisionBound` produces the reduction certificate consumed
by a shared-oracle implementation refinement. -/
theorem fsFlat_queryBridge [Inhabited F] (budget q : ℕ)
    (σ : List Bool → F) : FSQueryBridgeCertificate budget q σ := by
  constructor
  · intro A
    obtain ⟨A', hA⟩ := fsFlat_zkBridge (F := F) budget A
    refine ⟨A', hA.trans ?_⟩
    have hloss : 0 ≤ fsProgrammingLoss (F := F) q := ENNReal.toReal_nonneg
    simpa [add_comm] using
      add_le_add_left hloss (unlinkAdvantage (flatInstance (F := F) budget) A')
  · exact fsProgramCollisionBound q σ

end NonInteractive

end Zkpc.Games

#print axioms Zkpc.Games.evalDist_spendBatch_sigmaFlat
#print axioms Zkpc.Games.T4_sigmaFlat_unlinkability
#print axioms Zkpc.Games.sigmaFlat_zkBridge
#print axioms Zkpc.Games.evalDist_spendBatch_fsFlat
#print axioms Zkpc.Games.T4_fsFlat_unlinkability
#print axioms Zkpc.Games.fsFlat_zkBridge
#print axioms Zkpc.Games.fsFlat_queryBridge
