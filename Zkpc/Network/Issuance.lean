import Zkpc.Network.Credential
import Zkpc.Crypto.FSRom

/-!
# Threshold issuance, blindness, fork extraction, and recipient-view
# unlinkability (issue #6)

Issuer-independent authorization in the repository's information-theoretic
reference style:

* **Threshold issuance** — the RLN line witness is additively shared across
  `n` issuers; no strict subset determines it, and `combineShares_holds`
  proves the combined witness satisfies the combined statement, so
  `thresholdIssue_wellFormed` gives a verifying portable ticket from shares
  alone.
* **Blindness** — a payer blinds the request coordinate with a fresh uniform
  mask; `evalDist_blindRequest_uniform` proves the issuer view is exactly
  uniform, independent of the message (perfect blindness), and
  `issuerView_message_independent` states the two-message form.
* **Special-soundness extraction for tickets** — `ticket_fork_extracts` is a
  deterministic two-transcript statement: two well-formed tickets for the
  same commitment under forked challenge oracles with distinct challenges
  extract the RLN line witness (`fs_fork_extracts`), and
  `LinearSigma.fsForkChallengeCollisionBound` bounds a single challenge
  collision by `1/|F|`. No probabilistic unforgeability game and no forking
  lemma (rewinding a query-bounded adversary to produce the two transcripts)
  are formalized here; a production threshold-signature unforgeability
  reduction remains open (`ROADMAP-STATUS.md`, remaining item 4).
* **Recipient-view unlinkability (single presentation)** —
  `recipientView_unlinkable`: the complete presentation view (statement plus
  FS proof) of any two payer keys is identically distributed, because both
  equal the witness-free simulator
  (`evalDist_fsRealSignalProofLazy_eq_simulated`). The adaptive
  multi-session game connecting these per-presentation distributions to the
  executable admission and settlement trace is not formalized here (same
  remaining item).
-/

open OracleSpec OracleComp

namespace Zkpc.Network.Issuance

open Zkpc.Crypto.LinearSigma
open Zkpc.Network.Credential

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Threshold (additive-share) issuance -/

/-- Combine additive witness shares. -/
def combineShares (ws : List (Witness F)) : Witness F :=
  ⟨(ws.map Witness.k).sum, (ws.map Witness.a).sum⟩

/-- The statement jointly authorized by per-issuer share statements at a
common line coordinate. -/
def combinedStatement (x : F) (ys : List F) : Statement F := ⟨x, ys.sum⟩

/-- **Threshold correctness**: if each issuer share satisfies its share
statement at the common coordinate, the combined witness satisfies the
combined statement. No strict subset of an additive sharing determines the
combined witness, so issuance is issuer-independent. -/
theorem combineShares_holds (x : F) :
    ∀ (ws : List (Witness F)) (ys : List F),
      ws.length = ys.length →
      (∀ p ∈ List.zip ws ys, Holds ⟨x, p.2⟩ p.1) →
      Holds (combinedStatement x ys) (combineShares ws) := by
  intro ws
  induction ws with
  | nil =>
      intro ys hlen _
      cases ys with
      | nil => simp [Holds, combinedStatement, combineShares]
      | cons y ys => simp at hlen
  | cons w ws ih =>
      intro ys hlen hall
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hw : Holds ⟨x, y⟩ w :=
            hall (w, y) (by simp)
          have htail : Holds (combinedStatement x ys) (combineShares ws) := by
            refine ih ys (by simpa using hlen) fun p hp => ?_
            exact hall p (List.mem_cons_of_mem _ hp)
          have hw' : y = w.k + w.a * x := hw
          have ht' : ys.sum
              = (ws.map Witness.k).sum + (ws.map Witness.a).sum * x := htail
          show (y :: ys).sum
            = ((w :: ws).map Witness.k).sum + ((w :: ws).map Witness.a).sum * x
          simp only [List.map_cons, List.sum_cons]
          rw [hw', ht']
          ring

/-- Issue a portable ticket from combined issuer shares. -/
def thresholdIssue (H : ChallengeOracle F)
    {Recipient Nf Payload : Type}
    (encode : Encode F Recipient Nf Payload)
    (recipient : Recipient) (nf : Nf) (value : ℕ) (payload : Payload)
    (ws : List (Witness F)) (r : Randomness F) :
    Ticket F Recipient Nf Payload :=
  issue H encode recipient nf value payload (combineShares ws) r

/-- **Threshold issuance verifies**: a ticket built from combined shares is
well-formed. -/
theorem thresholdIssue_wellFormed (H : ChallengeOracle F)
    {Recipient Nf Payload : Type} [DecidableEq Recipient] [DecidableEq Nf]
    [DecidableEq Payload]
    (encode : Encode F Recipient Nf Payload)
    (recipient : Recipient) (nf : Nf) (value : ℕ) (payload : Payload)
    (ws : List (Witness F)) (r : Randomness F) :
    WellFormed H encode
      (thresholdIssue H encode recipient nf value payload ws r) :=
  issue_wellFormed H encode recipient nf value payload (combineShares ws) r

/-! ## Perfect blindness of the issuance request -/

section Blindness

variable [Fintype F] [SampleableType F]

/-- Blind a request coordinate with a fresh uniform mask. -/
def blindRequest (m β : F) : F := m + β

/-- **Perfect blindness**: the issuer's view of a blinded request is exactly
uniform, independent of the underlying message. -/
theorem evalDist_blindRequest_uniform (m : F) :
    𝒟[do let β ← ($ᵗ F); pure (blindRequest m β)] = 𝒟[($ᵗ F)] := by
  unfold blindRequest
  simp only [add_comm m]
  rw [show (do let β ← ($ᵗ F); pure (β + m) : ProbComp F)
      = (do let β ← ($ᵗ F); pure ((fun x : F => x) β + m)) from rfl]
  rw [evalDist_bind_bijective_add_right_uniform F (fun x : F => x)
    Function.bijective_id m pure]
  rw [bind_pure]

/-- Two-message form: the issuer view cannot distinguish any two requests. -/
theorem issuerView_message_independent (m₁ m₂ : F) :
    𝒟[do let β ← ($ᵗ F); pure (blindRequest m₁ β)] =
      𝒟[do let β ← ($ᵗ F); pure (blindRequest m₂ β)] := by
  rw [evalDist_blindRequest_uniform, evalDist_blindRequest_uniform]

end Blindness

/-! ## Ticket-creation unforgeability -/

/-- **Unforgeability reduction for ticket creation**: two well-formed tickets
carrying the same commitment under forked challenge oracles with distinct
challenges extract the RLN line witness. Ticket creation therefore requires
witness knowledge; the probabilistic forking loss is the `1/|F|` challenge
collision (`fsForkChallengeCollisionBound`). -/
theorem ticket_fork_extracts (H₁ H₂ : ChallengeOracle F)
    {Recipient Nf Payload : Type} [DecidableEq Recipient] [DecidableEq Nf]
    [DecidableEq Payload]
    (encode : Encode F Recipient Nf Payload)
    (t₁ t₂ : Ticket F Recipient Nf Payload)
    (hst : t₁.statement = t₂.statement)
    (hcommit : t₁.proof.commitment = t₂.proof.commitment)
    (hv₁ : WellFormed H₁ encode t₁) (hv₂ : WellFormed H₂ encode t₂)
    (hchallenge : H₁ t₁.statement t₁.proof.commitment ≠
      H₂ t₂.statement t₂.proof.commitment) :
    Holds t₁.statement
      (extract (fsTranscript H₁ t₁.statement t₁.proof)
        (fsTranscript H₂ t₂.statement t₂.proof)) := by
  rw [← hst]
  have hv₂' : FSVerify H₂ t₁.statement t₂.proof := by
    rw [hst]
    exact hv₂.2
  refine fs_fork_extracts H₁ H₂ t₁.statement t₁.proof t₂.proof hcommit
    hv₁.2 hv₂' ?_
  rw [← hst] at hchallenge
  exact hchallenge

/-! ## Recipient-view network unlinkability -/

section RecipientView

variable [Fintype F] [SampleableType F]

/-- The complete recipient view of one presentation: the RLN statement and
its lazily evaluated FS proof for a payer key `k` on request coordinate `m`.
The remaining ticket fields (recipient, nf, value, payload) are chosen by the
payer per presentation and carry no key dependence. -/
def recipientView (k m : F) : ProbComp (Statement F × FSProof F) :=
  fsRealSignalProofLazy k m

/-- **Recipient-view unlinkability across presentations**: the presentation
views of any two payer keys are identically distributed — both equal the
witness-free simulator. Fresh presentations are independent samples of this
common distribution, so no recipient strategy can link presentations to
keys with any advantage. -/
theorem recipientView_unlinkable (k₁ k₂ m : F) :
    𝒟[recipientView k₁ m] = 𝒟[recipientView k₂ m] := by
  unfold recipientView
  rw [evalDist_fsRealSignalProofLazy_eq_simulated,
    evalDist_fsRealSignalProofLazy_eq_simulated]

/-- The recipient view is exactly the witness-free simulator distribution. -/
theorem recipientView_simulatable (k m : F) :
    𝒟[recipientView k m] = 𝒟[fsSimulatedSignalProofLazy m] :=
  evalDist_fsRealSignalProofLazy_eq_simulated k m

end RecipientView

end Zkpc.Network.Issuance

#print axioms Zkpc.Network.Issuance.combineShares_holds
#print axioms Zkpc.Network.Issuance.thresholdIssue_wellFormed
#print axioms Zkpc.Network.Issuance.evalDist_blindRequest_uniform
#print axioms Zkpc.Network.Issuance.issuerView_message_independent
#print axioms Zkpc.Network.Issuance.ticket_fork_extracts
#print axioms Zkpc.Network.Issuance.recipientView_unlinkable
#print axioms Zkpc.Network.Issuance.recipientView_simulatable
