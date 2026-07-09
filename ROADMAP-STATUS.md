# End-to-end formalization status

Checkpoint for the implementation PR based on upstream commit `0d13b42`.

## Implemented in this branch

- Query-bounded T7 infrastructure: separate direct-secret, `H_nf`, and
  honest-signal structural budgets; the adaptive uniform-secret first-hit
  lemma; quantitative real-to-ideal composition; and the corrected
  `(q_A + q_E + q_Id + q_Nf*q_sig + q_sig^2 + 1) / |F|` endpoint from a deferred-sampling
  certificate.
- Corrected T7 quantitative kernels: an adaptive multi-target slope-preimage
  bound `q_Nf*q_sig/|F|` and a logged-oracle honest-slope birthday bound.
  `Games.FrameAudit` decorates the actual handler with secret probes, slope
  probes, and slope exposures, proves bad-event monotonicity and per-step
  resource growth, and erases exactly to `frameImpl` for every adaptive run.
  `Games.FrameIdeal` supplies the secret-independent handler, canonical
  secret-erasing state map, and programmed initial-state relation. Exact
  public-oracle step coupling was attempted at this checkpoint but is not yet
  retained as a proved API; the failed obligations are listed below.
- A proof-free T4 reference instance and a witness-dependent masked-proof
  instance, including session-level simulator equality, perfect unlinkability,
  and a zero-loss bridge to the proof-free game. The separate proof-bearing
  Sigma/T4 construction remains an open bridge obligation.
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
- A concrete finite-field Sigma algebraic core for knowledge of an RLN line:
  verifier completeness, a simulator construction, response equivalence, and
  two-transcript special-soundness extraction. Distributional
  honest-verifier-ZK and the proof-bearing T4 instance are deliberately not
  claimed until their sampling argument is formalized.
- A Fiat--Shamir-shaped proof object, deterministic verifier, programmed
  simulator interface, and algebraic fork extractor. Its probabilistic ROM
  programming/forking reduction and T4 wire-level bridge remain open.
- A concrete additive masked refund ciphertext with executable encryption,
  opening, homomorphic addition, rerandomization, receipt updates, and
  correctness. Its distributional rerandomization-privacy argument remains a
  named reduction obligation.

## Remaining before the complete roadmap is proved

### Checkpoint validation status

This PR is an **in-progress research checkpoint**, not a completed
formalization. The focused `FrameAudit`, `FrameIdeal`, and `T7` targets
source-build without `sorryAx`; experimental logged-slope and exact
public-oracle coupling claims that did not source-build were removed. The
unconditional T7 theorem remains open.

1. **Unconditional T7 handler coupling.** Construct
   `FrameDeferredSampling` from the actual stateful `frameImpl`. The proof must
   relate the real shared caches to a secret-independent ideal handler up to
   the first direct-secret hit, slope-preimage hit, or honest-slope collision.
   It must account for public `cm`, honest `spend`, legacy
   `close`, `nfAt`, direct `roX`/`roNf`, cache hits, and adaptive continuations.
   The formal slope-reveal calibration proves why `q_Nf*q_sig` is required;
   the collision term covers repeated honest slopes. The existing composition
   theorem then supplies the corrected bound. The exact real-handler audit,
   monotonic bad event, projection theorem, the multi-target slope kernel, and a
   secret-independent ideal handler with canonical cache erasure are now
   present. Programmed initialization and every good public-oracle step
   (`roX`, `roA`, `roE`, `roId`, and `roNf`) now commute exactly with
   canonical idealization. The nullifier case is supported by a proved
   audit-completeness invariant and cache-disjointness lemmas, so the hidden
   composed cache is preserved rather than assumed. The atomic
   fresh-slope and collision bounds still need
   source-valid proofs. The remaining semantic step is the
   `spend`/`close`/`nfAt` bad-or-good relation and final VCV-io quantitative
   simulation application. In particular, `nfAt` can sample a slope before a
   later adaptive message choice, so this needs continuation-level deferred
   sampling rather than only a pointwise state relation.

2. **Production Fiat--Shamir reduction.** The linear Sigma protocol has a
   Fiat--Shamir proof object, deterministic verifier, completeness,
   programmed-oracle simulator interface, and algebraic fork extractor. What
   remains is the distributional honest-verifier-ZK argument, the
   probabilistic ROM programming/forking lemma for the non-interactive
   instance (including its concrete query-dependent loss), and a
   `zkBridgeObligation` instantiation for that FS wire type. The masked-proof
   bridge is an exact reference endpoint; the interactive-Sigma bridge is not
   yet connected to T4.

3. **Production refund cryptography.** The opaque fresh handle has an
   executable information-theoretic additive masked-cipher reference
   instantiation with receipt-update correctness. What remains is its
   distributional rerandomization-privacy proof, a deployed public-key AH
   scheme reduction, receipt-signature instantiation, and EUF-CMA chain
   authenticity rather than absorption into transition guards.

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
   final implementation.

The roadmap is not complete until every item above is implemented and the
final composition and clean-build audit pass.
