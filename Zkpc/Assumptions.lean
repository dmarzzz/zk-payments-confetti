/-!
# Assumptions (task A4; Spec.md §5)

The executor contract requires every cryptographic assumption to live in
this file, named for the standard property it encodes, with CI forbidding
`axiom` anywhere else. This development goes one step further than the
contract: **it contains no `axiom` declarations at all.** The formalization
works in an idealized model in which each assumption below is discharged
*by construction*, so the kernel checks everything and the trust surface is
exactly the model definitions (reviewed at gates B1/B3/K1) plus this
registry. The K2 axiom audit checks this file against actual usage: the
`#print axioms` output of every theorem must list nothing beyond Lean's
own `propext`/`Quot.sound`/`Classical.choice`.

How each named assumption of Spec.md §5 enters the model instead:

| # | Assumption | Where it lives in the model |
|---|---|---|
| 1 | NIZK knowledge soundness | Transition guards: the symbolic layer's `Redeem` accepts a ticket iff its *semantic witness* satisfies `R_spend` (Spec.md §3/§4). An accepted ticket "is" its extracted witness; forged proofs do not exist in the model. |
| 2 | NIZK zero-knowledge | `Games.FullTicketInstance` includes a real witness-dependent proof `key + mask` and proves its complete session transcript equal in distribution to a witness-free simulated proof. The proof-free instance is the final reduction target. |
| 3 | PRF/ROM idealization + domain separation (MC9) | The game layer samples `H_a(k,·)`, `H_e(k,·)`, `H_nf` as random oracles (VCVio `randomOracle`); the symbolic layer identifies nullifiers with their preimage pairs (collision-freeness by construction). |
| 3′ | `single_signal_hiding` | Stated and *proved* in the ROM game layer (`Zkpc.Games`): one point `(x, k + a·x)` with fresh-uniform `a` leaves `k` uniform. Named separately because standard PRF security does not imply it (the key is used additively — KDM-flavored; rev-1 gate finding). |
| 4 | EUF-CMA signatures (B) | Symbolic layer: the refund-receipt chain admits only payee-issued links; forged receipts do not exist in the model. The chain-binding tag (MC7) is what excludes *honestly issued but spliced* receipts — that one is a theorem obligation (T1-B), not an assumption. |
| 5 | Re-randomizable AH encryption (B) | `Crypto.MaskedEncryption` gives an executable additive opening-carrying reference scheme with correctness and rerandomization operations, and *proves* exact rerandomization and refund-update privacy (`evalDist_rerandomize_cipher_uniform`/`_eq`, `evalDist_refundUpdate_cipher_uniform`/`_eq` in `Zkpc/Crypto/MaskedEncryption.lean`). What remains outside the layer is a reduction from a deployed public-key AH scheme to this reference model. |
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
  /-- Proofs are simulatable without the witness. Used by: T4. -/
  | nizkZeroKnowledge
  /-- Domain-separated PRF/ROM idealization of the hash family; collision
  resistance; `H_id` hiding/binding. Used by: T4, T7, index-injectivity in T1. -/
  | prfRomIdealization
  /-- One signal `(x, k + H_a(k,i)·x)` per index reveals nothing about `k`.
  Consequence of 3 stated separately (KDM-flavored key use; rev-1 finding).
  Used by: T4, T7. -/
  | singleSignalHiding
  /-- Unforgeability of the payee's refund-receipt signatures (B only).
  Used by: T1-B, T3-B. -/
  | eufCmaSignatures
  /-- IND-CPA + correct homomorphic addition + re-randomization independence
  (B only). Used by: T4 on B-rerand; its absence of use breaks B-static. -/
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
  | nizkZeroKnowledge => romConstruction
  | prfRomIdealization => romConstruction
  | singleSignalHiding => provedLemma
  | eufCmaSignatures => modelGuard
  | rerandomizableEncryption => romConstruction
  | blindSignatureUnforgeabilityBlindness => declaredUnused

end Zkpc.Assumptions
