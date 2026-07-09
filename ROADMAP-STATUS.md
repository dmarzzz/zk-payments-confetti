# End-to-end formalization status

Checkpoint for the implementation PR based on upstream commit `0d13b42`.

## Implemented in this branch

- Query-bounded T7 infrastructure: separate direct-secret, `H_nf`, and
  honest-signal structural budgets; the adaptive uniform-secret first-hit
  lemma; quantitative real-to-ideal composition; and the corrected
  `(q_A + q_E + q_Id + q_Nf*q_sig + q_sig^2 + 1) / |F|` endpoint from a deferred-sampling
  certificate.
- A proof-bearing T4 reference instance and a witness-dependent masked-proof
  instance, including session-level simulator equality, perfect unlinkability,
  and a zero-loss bridge to the proof-free game.
- B-instance obligations for genesis receipts, receipt updates, capability
  monotonicity, close-view simulation, and the rerandomized challenge path.
- Refund cascade and finite-fleet safety: exact upgrade count, terminal
  settlement, payout conservation, aggregate no-overspend, payer floor, and
  identity/fund-slash recovery rules.
- Executable-ledger refinement for the flat object, arbitrary sweep lists,
  refund accept/close/force-close, and fleet tick/admission/slash.
- Executable MC20 contract drivers for close disputes, successful settlement,
  settlement-time voiding, and receipt-cascade upgrade/settle progress, each
  refined to its relational transition.
- A portable multi-recipient accounting machine with one shared deposit,
  global nullifier deduplication, recipient-directed settlement, exact payout
  partitioning, recipient-view isolation, and executable refinement.
- A concrete portable credential adapter (`Network.Credential`): recipient,
  global nullifier, value, and payload are bound into a Fiat--Shamir statement;
  honest issuance verifies; verified fresh redemption refines to network
  admission; and cross-recipient replay of an admitted nullifier is rejected.
  Its end-to-end theorem composes verification, executable redemption,
  executable settlement, reachability, and shared-deposit no-overspend.
- A concrete finite-field Sigma protocol for knowledge of an RLN line:
  verifier completeness, perfect honest-verifier simulation via an explicit
  randomness/response equivalence, and two-transcript special-soundness
  extraction.
- A verified-proof T4 instance (`Games.SigmaInstance`) whose real payer emits
  an RLN point and accepting Sigma transcript. The complete signal/proof pair
  and arbitrary solvent batches are exactly simulator-distributed, yielding
  perfect T4 and a zero-loss proof-free bridge. The Sigma core also includes a
  Fiat--Shamir proof object, programmed-oracle simulation, and fork extractor.

## Remaining before the complete roadmap is proved

1. **Unconditional T7 handler coupling.** Construct
   `FrameDeferredSampling` from the actual stateful `frameImpl`. The proof must
   relate the real shared caches to a secret-independent ideal handler up to
   the first direct-secret hit, slope-preimage hit, or honest-slope collision.
   It must account for public `cm`, honest `spend`, legacy
   `close`, `nfAt`, direct `roX`/`roNf`, cache hits, and adaptive continuations.
   The formal slope-reveal calibration proves why `q_Nf*q_sig` is required;
   the collision term covers repeated honest slopes. The existing composition
   theorem then supplies the corrected bound.

2. **Production Fiat--Shamir reduction.** The linear Sigma protocol now has a
   Fiat--Shamir proof object, deterministic verifier, completeness,
   programmed-oracle simulator, and algebraic fork extractor; the interactive
   verified transcript is also connected to the full T4 game. What remains is
   the probabilistic ROM programming/forking lemma for the non-interactive
   instance, including its concrete query-dependent loss, followed by a
   `zkBridgeObligation` instantiation for that FS wire type. The masked-proof
   and interactive-Sigma bridges are exact reference endpoints.

3. **Concrete refund cryptography.** Replace the ideal fresh-handle model with
   an explicit rerandomizable additively homomorphic encryption interface and
   reduction; instantiate receipt signatures and prove EUF-CMA chain
   authenticity rather than absorbing it into transition guards.

4. **Threshold issuance and network unlinkability.** The accounting machine is
   now connected to a concrete proof-bearing portable ticket, and verification
   refines to admission with cross-recipient replay rejection. What remains is
   threshold/blind issuance (or another issuer-independent authorization
   mechanism), an unforgeability reduction for ticket creation, and a
   recipient-view network unlinkability game/reduction across presentations.

5. **Full channel/fleet composition theorem.** The portable credential path now
   has an end-to-end verification→redemption→settlement→no-overspend theorem.
   What remains is the larger channel theorem connecting proof verification,
   flat/refund admission, reconciliation/slashing, close settlement, and all
   T1--T7 guarantees over one complete trace.

6. **Final validation and documentation.** After the items above, run a cold
   dependency fetch and clean full build, the forbidden-placeholder audit,
   `git diff --check`, all `#print axioms` checks, and reconcile `Spec.md`, the
   paper theorem table, assumption registry, and `OPEN-PROOFS.md` with the
   final implementation. Existing validation covers the current branch, not
   these remaining deliverables.

The roadmap is not complete until every item above is implemented and the
final composition and clean-build audit pass.
