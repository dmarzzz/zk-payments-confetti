/-!
# Assumptions (task A4; Spec.md §5)

The executor contract requires every cryptographic assumption to live in
this file, named for the standard property it encodes, with CI forbidding
`axiom` anywhere else. This development goes one step further than the
contract: **it contains no `axiom` declarations at all.** The formalization
works in an idealized model in which each assumption below is discharged
*by construction*. When the tree builds, Lean checks the proofs against that
model; final-candidate evidence is recorded separately. The modeling trust
surface is the definitions (reviewed by the B1/B3/K1 agent simulations,
with independent-human acceptance still pending) plus this registry. The K2
axiom audit checks this file against actual usage: captured `#print axioms`
output for an audited theorem must list nothing beyond Lean's own
`propext`/`Quot.sound`/`Classical.choice`; final-candidate outputs are recorded
only after the release audit runs.

How each named assumption of Spec.md §5 enters the model instead:

| # | Assumption | Where it lives in the model |
|---|---|---|
| 1 | NIZK knowledge soundness | Transition guards: the symbolic layer's `Redeem` accepts a ticket iff its *semantic witness* satisfies `R_spend` (Spec.md §3/§4). An accepted ticket "is" its extracted witness; forged proofs do not exist in that model. `Crypto.LinearSigma` also proves its algebraic extractor and `Crypto.FSRom` proves standalone forking/programming-loss kernels, but a composed adaptive Fiat--Shamir knowledge-soundness reduction for a deployed proof system is not claimed. |
| 2 | NIZK zero-knowledge | `Games.FullTicketInstance` proves a masked witness-dependent proof transcript equal in distribution to a witness-free one. `Crypto.LinearSigma` proves the interactive Sigma simulation, `Crypto.FSRom` proves the ideal lazy-ROM Fiat--Shamir simulation, and `Games.SigmaInstance` lifts both reference layers to the session T4 instances. The proof-free instance is the final ideal reduction target; no concrete production-NIZK reduction is claimed. |
| 3 | PRF/ROM idealization + domain separation (MC9) | The FRAME game exposes domain-separated lazy random-oracle interfaces for `H_a`, `H_x`, `H_nf`, `H_e`, and `H_id`; `H_x` is mapped away from zero by the reference handler and `H_id` is the public identity-commitment interface. The symbolic refund layer carries the separate `H_tag` binding, and symbolic nullifiers retain their preimage structure. These are ideal-model choices, not a deployed-hash reduction. |
| 3′ | `single_signal_hiding` | Stated and *proved* in the ROM game layer (`Zkpc.Games`): one point `(x, k + a·x)` with fresh-uniform `a` leaves `k` uniform. Named separately because standard PRF security does not imply it (the key is used additively — KDM-flavored; rev-1 gate finding). |
| 4 | EUF-CMA signatures (B) | Symbolic layer: the refund-receipt chain admits only payee-issued links; forged receipts do not exist in the model. Used by T1-B, T2-B, and T3-B: forged receipts could break conservation, inflate the payee settlement, or reduce the payer remainder. The chain-binding tag (MC7) excludes *honestly issued but spliced* receipts; that is a channel-binding theorem obligation rather than EUF-CMA itself. |
| 5 | Re-randomizable AH encryption (B) | `Crypto.MaskedEncryption` gives an executable additive opening-carrying reference scheme. `add_encrypt` proves opening-homomorphism (summand openings add to an opening of the ciphertext sum), while the file also proves correctness, rerandomization correctness, and exact rerandomization/refund-update privacy (`evalDist_rerandomize_cipher_uniform`/`_eq`, `evalDist_refundUpdate_cipher_uniform`/`_eq`). Used by B-rerand T4 and by honest completeness of B spends/closes, including the T3-B/T5-B upgrade path. What remains outside the layer is a reduction from a deployed public-key AH scheme to this reference model. |
| 6 | Blind-signature unforgeability + blindness | **Declared and unused** (Spec.md §5.6): exercised by no instantiation in scope. Present in the registry so its non-use is auditable rather than silent. |

If a future proof genuinely needs a Lean `axiom`, it goes here, documented,
and the K2 audit re-runs. Definition drift in the *model* (weakening a guard
to make a theorem pass) is the failure mode CI cannot catch — that is what
gates B3 and K1/K3 review.
-/

namespace Zkpc.Assumptions

/-- The registry of named cryptographic assumptions (Spec.md §5). Each
constructor is one assumption; `dischargedBy` records how the idealized
model absorbs it. This is data for the K2 audit, not logic. -/
inductive Named
  /-- From any accepted proof an extractor obtains a witness in `R_spend`.
  Used by: T1, T2, T3, T6, T7. -/
  | nizkKnowledgeSoundness
  /-- Proofs are simulatable without the witness in the masked, interactive
  Sigma, and ideal lazy-ROM Fiat--Shamir reference layers. Used by: T4. -/
  | nizkZeroKnowledge
  /-- Domain-separated PRF/ROM idealization of `H_a`, nonzero `H_x`, `H_nf`,
  `H_e`, and `H_id` (plus symbolic `H_tag` binding); collision resistance and
  `H_id` hiding/binding. Used by: T4, T7, index-injectivity in T1. -/
  | prfRomIdealization
  /-- One signal `(x, k + H_a(k,i)·x)` per index reveals nothing about `k`.
  Consequence of 3 stated separately (KDM-flavored key use; rev-1 finding).
  Used by: T4, T7. -/
  | singleSignalHiding
  /-- Unforgeability of the payee's refund-receipt signatures (B only).
  Used by: T1-B, T2-B, T3-B. -/
  | eufCmaSignatures
  /-- IND-CPA + opening-homomorphic addition + re-randomization independence
  (B only). Used by: T4 on B-rerand and honest completeness of B spends/closes,
  including the T3-B/T5-B upgrade path; its absence of use breaks B-static. -/
  | rerandomizableEncryption
  /-- Blind-signature unforgeability and blindness. Declared per the
  executor contract; used by NO instantiation in scope (Spec.md §5.6). -/
  | blindSignatureUnforgeabilityBlindness
  deriving DecidableEq, Repr

/-- How an assumption is absorbed by the idealized model. -/
inductive Discharge
  /-- embodied as a guard/shape of the symbolic transition system -/
  | modelGuard
  /-- embodied as random-oracle / ideal-functionality sampling in the game layer -/
  | romConstruction
  /-- stated and proved as a lemma of the game layer -/
  | provedLemma
  /-- declared for auditability; exercised by no in-scope instantiation -/
  | declaredUnused
  deriving DecidableEq, Repr

open Named Discharge in
/-- The audit table (K2 reads this): where each named assumption lives. -/
def dischargedBy : Named → Discharge
  | nizkKnowledgeSoundness => modelGuard
  | nizkZeroKnowledge => provedLemma
  | prfRomIdealization => romConstruction
  | singleSignalHiding => provedLemma
  | eufCmaSignatures => modelGuard
  | rerandomizableEncryption => romConstruction
  | blindSignatureUnforgeabilityBlindness => declaredUnused

end Zkpc.Assumptions
