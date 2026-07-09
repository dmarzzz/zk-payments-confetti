# End-to-end formalization status

Checkpoint for the implementation PR based on upstream commit `0d13b42`.

## Implemented in this branch

- Query-bounded T7 infrastructure: separate `H_a`, `H_e`, and `H_id`
  structural budgets; the adaptive uniform-secret first-hit lemma; quantitative
  real-to-ideal composition; and the final exact
  `(q_A + q_E + q_Id + 1) / |F|` endpoint from a deferred-sampling
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
- A portable multi-recipient accounting machine with one shared deposit,
  global nullifier deduplication, recipient-directed settlement, exact payout
  partitioning, recipient-view isolation, and executable refinement.
- A concrete finite-field Sigma protocol for knowledge of an RLN line:
  verifier completeness, perfect honest-verifier simulation via an explicit
  randomness/response equivalence, and two-transcript special-soundness
  extraction.

## Remaining before the complete roadmap is proved

1. **Unconditional T7 handler coupling.** Construct
   `FrameDeferredSampling` from the actual stateful `frameImpl`. The proof must
   relate the real shared caches to a secret-independent ideal handler up to
   the first direct `roA`, `roE`, or `roId` query whose candidate equals the
   hidden secret. It must account for public `cm`, honest `spend`, legacy
   `close`, `nfAt`, direct `roX`/`roNf`, cache hits, and adaptive continuations.
   The existing composition theorem then supplies the advertised bound.

2. **Non-interactive production proof bridge.** The linear Sigma protocol is
   an algebraic proof-of-knowledge core, not yet a Fiat--Shamir NIZK. Add the
   random-oracle challenge transform, prove completeness and an appropriate
   forking/special-soundness reduction, prove zero knowledge against the full
   ticket game, and instantiate `zkBridgeObligation` with its concrete loss.
   The current masked-proof bridge remains an ideal/perfect reference.

3. **Concrete refund cryptography.** Replace the ideal fresh-handle model with
   an explicit rerandomizable additively homomorphic encryption interface and
   reduction; instantiate receipt signatures and prove EUF-CMA chain
   authenticity rather than absorbing it into transition guards.

4. **Portable network credential.** Connect the multi-recipient accounting
   machine to a concrete portable credential or threshold-issued ticketbook.
   Prove that credential verification implies an admissible network event,
   globally unique nullifiers survive cross-recipient presentation, and each
   recipient's cryptographic view satisfies the network unlinkability game.

5. **Internal scheduler execution.** Add executable drivers and refinement for
   close-window dispute/settle/void transitions and the receipt-upgrade
   cascade. The relational safety/liveness results exist, but these automatic
   contract paths are not all exposed through deterministic drivers.

6. **End-to-end composition theorem.** State and prove one theorem connecting
   concrete proof verification, executable admission, reconciliation/slashing,
   close/settlement, and the T1--T7 guarantees for a complete trace. Current
   theorems cover the layers separately.

7. **Final validation and documentation.** After the items above, run a cold
   dependency fetch and clean full build, the forbidden-placeholder audit,
   `git diff --check`, all `#print axioms` checks, and reconcile `Spec.md`, the
   paper theorem table, assumption registry, and `OPEN-PROOFS.md` with the
   final implementation. Existing validation covers the current branch, not
   these remaining deliverables.

The roadmap is not complete until every item above is implemented and the
final composition and clean-build audit pass.
