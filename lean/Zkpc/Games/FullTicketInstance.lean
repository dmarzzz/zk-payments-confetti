import Zkpc.Games.FlatInstance
import Zkpc.Games.Coupling

/-!
# Proof-bearing flat-ticket reference instance

This module closes M1/O1 for an explicit ideal proof system.  Unlike
`flatInstance`, its wire view retains the common membership root, public epoch,
and a simulated proof value.  The proof is sampled independently of the hidden
candidate, which is the ideal functionality supplied by NIZK zero knowledge.

This is deliberately the *ideal proof-bearing hop*, not a computational NIZK
claim.  A concrete NIZK instantiation must subsequently prove that its real
proof distribution is indistinguishable from this reference instance and pay
that scheme's `εZK` in `zkBridgeObligation`.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [SampleableType F] [Inhabited F]

/-- Complete adversary-visible flat ticket: common root, public epoch, the
proof-free ticket payload, and the simulated NIZK proof. -/
structure FullFlatView (F : Type) where
  root : F
  epoch : ℕ
  ticket : FlatView F
  proof : F

/-- Payer state for the proof-bearing reference instance. -/
structure FullFlatPSt (F : Type) where
  idx : ℕ
  last : Option (FullFlatView F)

/-- One proof-bearing spend.  `root` is the common public root `0`; the epoch
is supplied by the game; payload and simulated proof are fresh ideal values. -/
def fullFlatSpend (budget e : ℕ) (st : FullFlatPSt F) (m : F) :
    ProbComp (Option (FullFlatView F × FullFlatPSt F)) :=
  if st.idx < budget then do
    let nfe ← ($ᵗ F)
    let y ← ($ᵗ F)
    let nf ← ($ᵗ F)
    let π ← ($ᵗ F)
    let v : FullFlatView F := ⟨default, e, ⟨nfe, m, y, nf⟩, π⟩
    pure (some (v, ⟨st.idx + 1, some v⟩))
  else
    pure none

/-- Ideal proof-bearing flat-ticket scheme. -/
def fullFlatInstance (budget : ℕ) : UnlinkScheme where
  M := F
  View := FullFlatView F
  CloseView := List F
  OpenView := PUnit
  GenesisInput := PUnit
  Receipt := PUnit
  PSt := FullFlatPSt F
  openCh _ := pure (⟨0, none⟩, PUnit.unit)
  spend e st m := fullFlatSpend budget e st m
  lastTicket st := st.last
  serve st _ := st
  close _ st := do
    let U ← freshFList (budget - st.idx)
    pure (U, st)
  capableFor q st := decide (st.idx + q ≤ budget)

/-- State-independent distribution of a proof-bearing session. -/
def fullFlatFreshBatch (e : ℕ) : List F → ProbComp (Option (List (FullFlatView F)))
  | [] => pure (some [])
  | m :: ms => do
      let nfe ← ($ᵗ F)
      let y ← ($ᵗ F)
      let nf ← ($ᵗ F)
      let π ← ($ᵗ F)
      Option.map (⟨default, e, ⟨nfe, m, y, nf⟩, π⟩ :: ·) <$> fullFlatFreshBatch e ms

/-- A solvent proof-bearing session has the state-independent reference
distribution. -/
lemma evalDist_spendBatch_fullFlat (budget e : ℕ) :
    ∀ (ms : List F) (st : FullFlatPSt F), st.idx + ms.length ≤ budget →
      𝒟[spendBatch (fullFlatInstance (F := F) budget) e st ms] =
        𝒟[fullFlatFreshBatch e ms] := by
  intro ms
  induction ms with
  | nil => intro st _; rfl
  | cons m ms ih =>
    intro st hst
    have hlen : st.idx + (ms.length + 1) ≤ budget := by simpa using hst
    have hsolv : st.idx < budget := by omega
    simp only [spendBatch, fullFlatInstance, fullFlatSpend, fullFlatFreshBatch,
      if_pos hsolv, bind_assoc, pure_bind, evalDist_bind]
    refine bind_congr fun nfe => bind_congr fun y => bind_congr fun nf =>
      bind_congr fun π => ?_
    exact evalDist_map_eq_of_evalDist_eq
      (ih ⟨st.idx + 1, some ⟨default, e, ⟨nfe, m, y, nf⟩, π⟩⟩
        (by show st.idx + 1 + ms.length ≤ budget; omega)) _

private lemma fullFlat_capable_of_challengeCapable (budget : ℕ)
    (g : GSt (fullFlatInstance (F := F) budget)) (q : ℕ)
    (h : challengeCapable (fullFlatInstance (F := F) budget) g q = true) :
    (g.cand false).idx + q ≤ budget ∧ (g.cand true).idx + q ≤ budget := by
  simp only [challengeCapable, fullFlatInstance, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2.2⟩

/-- The full wire-ticket challenge distribution is hidden-bit independent. -/
theorem challengeResp_fullFlat_bitfree (budget : ℕ)
    (g : GSt (fullFlatInstance (F := F) budget)) (ms : List F) (b b' : Bool) :
    𝒟[challengeResp (fullFlatInstance (F := F) budget) g b ms] =
      𝒟[challengeResp (fullFlatInstance (F := F) budget) g b' ms] := by
  unfold challengeResp
  split_ifs with hcond
  · have hcap : challengeCapable (fullFlatInstance (F := F) budget) g ms.length = true := by
      simp only [Bool.and_eq_true] at hcond
      exact hcond.2
    obtain ⟨hf, ht⟩ := fullFlat_capable_of_challengeCapable budget g ms.length hcap
    rw [evalDist_spendBatch_fullFlat budget g.epoch ms (g.cand b)
        (by cases b <;> assumption),
      evalDist_spendBatch_fullFlat budget g.epoch ms (g.cand b')
        (by cases b' <;> assumption)]
  · rfl

/-- T4 for the complete ideal proof-bearing wire view. -/
theorem T4_fullFlat_unlinkability (budget : ℕ)
    (A : UnlinkAdversary (fullFlatInstance (F := F) budget)) :
    unlinkAdvantage (fullFlatInstance (F := F) budget) A = 0 :=
  unlinkAdvantage_eq_zero_of_challenge_bitfree _ A
    (challengeResp_fullFlat_bitfree budget)

/-- A fixed proof-free adversary used as the existential witness for the
zero-loss ideal bridge. -/
def flatDummyAdversary (budget : ℕ) :
    UnlinkAdversary (flatInstance (F := F) budget) where
  Aux0 := PUnit
  phase0 := pure ((PUnit.unit, PUnit.unit), PUnit.unit)
  main := {
    Aux := PUnit
    phase1 := fun _ => pure ([(default : F)], PUnit.unit)
    guess := fun _ _ => false
  }

/-- **O1/M1 discharge for the ideal proof system.** Every adversary against
the proof-bearing reference instance has zero advantage, hence is bounded by
the proof-free game with zero ZK loss. -/
theorem fullFlat_zkBridge (budget : ℕ) :
    zkBridgeObligation (fullFlatInstance (F := F) budget)
      (flatInstance (F := F) budget) 0 := by
  intro A
  refine ⟨flatDummyAdversary budget, ?_⟩
  rw [T4_fullFlat_unlinkability budget A]
  exact add_nonneg (abs_nonneg _) (le_refl 0)

/-! ## A concrete perfectly zero-knowledge proof encoding

The following instance separates the honest prover from its simulator.  The
prover retains a witness `key` and publishes `key + mask`; the mask is sampled
uniformly for every proof.  The simulator samples the proof value directly.
Translation invariance of the uniform distribution is the concrete
zero-knowledge argument.  Although intentionally minimal, this is a genuine
proof-bearing real/ideal hop: the real transcript depends syntactically on a
private witness, while the simulated transcript does not.
-/

/-- Payer state for the real masked-proof instance. -/
structure MaskedProofPSt (F : Type) where
  key : F
  idx : ℕ
  last : Option (FullFlatView F)

/-- A real prover step.  Its proof is the witness hidden by fresh additive
randomness. -/
def maskedProofSpend [Add F] (budget e : ℕ) (st : MaskedProofPSt F) (m : F) :
    ProbComp (Option (FullFlatView F × MaskedProofPSt F)) :=
  if st.idx < budget then do
    let nfe ← ($ᵗ F)
    let y ← ($ᵗ F)
    let nf ← ($ᵗ F)
    let mask ← ($ᵗ F)
    let v : FullFlatView F := ⟨default, e, ⟨nfe, m, y, nf⟩, mask + st.key⟩
    pure (some (v, ⟨st.key, st.idx + 1, some v⟩))
  else
    pure none

/-- Concrete full-ticket instance using the masked proof encoding. -/
def maskedProofInstance [Add F] (budget : ℕ) : UnlinkScheme where
  M := F
  View := FullFlatView F
  CloseView := List F
  OpenView := PUnit
  GenesisInput := PUnit
  Receipt := PUnit
  PSt := MaskedProofPSt F
  openCh _ := do
    let key ← ($ᵗ F)
    pure (⟨key, 0, none⟩, PUnit.unit)
  spend e st m := maskedProofSpend budget e st m
  lastTicket st := st.last
  serve st _ := st
  close _ st := do
    let U ← freshFList (budget - st.idx)
    pure (U, st)
  capableFor q st := decide (st.idx + q ≤ budget)

/-- Every solvent real-prover batch has exactly the simulator's distribution.
This is the session-level NIZK zero-knowledge theorem. -/
lemma evalDist_spendBatch_maskedProof [AddGroup F] (budget e : ℕ) :
    ∀ (ms : List F) (st : MaskedProofPSt F), st.idx + ms.length ≤ budget →
      𝒟[spendBatch (maskedProofInstance (F := F) budget) e st ms] =
        𝒟[fullFlatFreshBatch e ms] := by
  intro ms
  induction ms with
  | nil => intro st _; rfl
  | cons m ms ih =>
    intro st hst
    have hlen : st.idx + (ms.length + 1) ≤ budget := by simpa using hst
    have hsolv : st.idx < budget := by
      omega
    simp only [spendBatch, maskedProofInstance, maskedProofSpend, fullFlatFreshBatch,
      if_pos hsolv, bind_assoc, pure_bind]
    refine evalDist_bind_congr' ($ᵗ F) fun nfe => ?_
    refine evalDist_bind_congr' ($ᵗ F) fun y => ?_
    refine evalDist_bind_congr' ($ᵗ F) fun nf => ?_
    let realCont : F → ProbComp (Option (List (FullFlatView F))) := fun π =>
      Option.map (⟨default, e, ⟨nfe, m, y, nf⟩, π⟩ :: ·) <$>
        spendBatch (maskedProofInstance (F := F) budget) e
          ⟨st.key, st.idx + 1, some ⟨default, e, ⟨nfe, m, y, nf⟩, π⟩⟩ ms
    calc
      𝒟[do let mask ← ($ᵗ F); realCont (mask + st.key)] =
          𝒟[do let π ← ($ᵗ F); realCont π] :=
        evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
          Function.bijective_id st.key realCont
      _ = 𝒟[do
          let π ← ($ᵗ F)
          let v : FullFlatView F := ⟨default, e, ⟨nfe, m, y, nf⟩, π⟩
          Option.map (v :: ·) <$>
            fullFlatFreshBatch e ms] := by
        refine evalDist_bind_congr' ($ᵗ F) fun π => ?_
        exact evalDist_map_eq_of_evalDist_eq
          (ih ⟨st.key, st.idx + 1, some ⟨default, e, ⟨nfe, m, y, nf⟩, π⟩⟩
            (by show st.idx + 1 + ms.length ≤ budget; omega)) _

private lemma maskedProof_capable_of_challengeCapable [AddGroup F] (budget : ℕ)
    (g : GSt (maskedProofInstance (F := F) budget)) (q : ℕ)
    (h : challengeCapable (maskedProofInstance (F := F) budget) g q = true) :
    (g.cand false).idx + q ≤ budget ∧ (g.cand true).idx + q ≤ budget := by
  simp only [challengeCapable, maskedProofInstance, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2.2⟩

/-- The concrete real-proof challenge distribution is hidden-bit independent. -/
theorem challengeResp_maskedProof_bitfree [AddGroup F] (budget : ℕ)
    (g : GSt (maskedProofInstance (F := F) budget)) (ms : List F) (b b' : Bool) :
    𝒟[challengeResp (maskedProofInstance (F := F) budget) g b ms] =
      𝒟[challengeResp (maskedProofInstance (F := F) budget) g b' ms] := by
  unfold challengeResp
  split_ifs with hcond
  · have hcap : challengeCapable (maskedProofInstance (F := F) budget) g ms.length = true := by
      simp only [Bool.and_eq_true] at hcond
      exact hcond.2
    obtain ⟨hf, ht⟩ := maskedProof_capable_of_challengeCapable budget g ms.length hcap
    rw [evalDist_spendBatch_maskedProof budget g.epoch ms (g.cand b)
        (by cases b <;> assumption),
      evalDist_spendBatch_maskedProof budget g.epoch ms (g.cand b')
        (by cases b' <;> assumption)]
  · rfl

/-- T4 for the concrete witness-dependent masked-proof wire protocol. -/
theorem T4_maskedProof_unlinkability [AddGroup F] (budget : ℕ)
    (A : UnlinkAdversary (maskedProofInstance (F := F) budget)) :
    unlinkAdvantage (maskedProofInstance (F := F) budget) A = 0 :=
  unlinkAdvantage_eq_zero_of_challenge_bitfree _ A
    (challengeResp_maskedProof_bitfree budget)

/-- Concrete O1 discharge: witness-dependent real proofs are simulated with
zero loss, so every real-wire adversary is bounded by the proof-free game. -/
theorem maskedProof_zkBridge [AddGroup F] (budget : ℕ) :
    zkBridgeObligation (maskedProofInstance (F := F) budget)
      (flatInstance (F := F) budget) 0 := by
  intro A
  refine ⟨flatDummyAdversary budget, ?_⟩
  rw [T4_maskedProof_unlinkability budget A]
  exact add_nonneg (abs_nonneg _) (le_refl 0)

end Zkpc.Games

#print axioms Zkpc.Games.T4_fullFlat_unlinkability
#print axioms Zkpc.Games.fullFlat_zkBridge
#print axioms Zkpc.Games.evalDist_spendBatch_maskedProof
#print axioms Zkpc.Games.T4_maskedProof_unlinkability
#print axioms Zkpc.Games.maskedProof_zkBridge
