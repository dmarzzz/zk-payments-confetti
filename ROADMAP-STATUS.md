# End-to-end formalization status

Checkpoint for the implementation PR based on upstream commit `0d13b42`.

## Implemented in this branch

- Query-bounded T7 infrastructure: separate direct-secret, `H_nf`, and
  honest-signal structural budgets; the adaptive uniform-secret first-hit
  lemma; quantitative real-to-ideal composition; and the corrected
  `(q_A + q_E + q_Id + q_Nf*q_sig + q_sig^2 + 1) / |F|` endpoint from a deferred-sampling
  certificate.
- Corrected T7 quantitative kernels: the adaptive multi-target slope-preimage
  bound `uniformSlopeProbeBound` (`q_Nf*q_sig/|F|`) alongside the per-channel
  `uniformSecretProbeBound`. An earlier logged-oracle honest-slope birthday
  draft did not source-build and was removed; that collision term is part of
  the open handler argument, not a proved kernel.
  `Games.FrameAudit` decorates the actual handler with secret probes, slope
  probes, and slope exposures, proves bad-event monotonicity and per-step
  resource growth, and erases exactly to `frameImpl` for every adaptive run.
  `Games.FrameIdeal` supplies the secret-independent handler, canonical
  secret-erasing state map, and programmed initial-state relation, and proves
  the exact public-oracle step coupling: every good
  `roX`/`roA`/`roE`/`roId`/`roNf` step commutes with canonical idealization
  (`idealize_roX_step` through `idealize_roNf_step`).
- T7 composition-socket correction (`Games.FrameDeferred`, commit `3df0169`):
  a kernel-checked refutation (`frameDeferredSampling_refuted`) shows the
  pointwise-in-`k` `FrameDeferredSampling` certificate is unsatisfiable over
  any field with more than five elements, and the corrected secret-averaged
  socket `FrameDeferredSamplingAvg` with `T7_frame_query_bound_avg` recovers
  the same `(qb.total + 1)/|F|` endpoint
  (`research_knowledge/gates.md`, Round 4 of 2026-07-09).
- Proof-free, masked-proof, interactive-Sigma, and Fiat--Shamir T4 instances.
  The Sigma and lazy-ROM FS wires have session-level simulator equalities,
  perfect unlinkability, and zero-loss bridges to the proof-free game; the FS
  layer also proves explicit programming- and fork-collision bounds.
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
  verifier completeness, a simulator construction, response equivalence,
  two-transcript special-soundness extraction, and distributional
  honest-verifier ZK for both the transcript and the complete signal/proof
  pair (`evalDist_real_eq_simulated`,
  `evalDist_realSignalProof_eq_simulated` in `Crypto.LinearSigma`).
  `Games.SigmaInstance` lands the proof-bearing T4 instances and their
  zero-loss ZK bridges for both the interactive and FS wires.
- A Fiat--Shamir-shaped proof object, deterministic verifier, programmed
  simulator interface, and algebraic fork extractor, with lazy-ROM
  distributional simulation and explicit programming/fork collision bounds
  (`Crypto.FSRom`) and the T4 wire-level bridge (`Games.SigmaInstance`).
  What remains open is the reduction from a deployed hash implementation and
  adversarial oracle-query semantics to this ideal lazy-ROM model
  (remaining item 2 below).
- A concrete additive masked refund ciphertext with executable encryption,
  opening, homomorphic addition, rerandomization, receipt updates, and
  correctness, together with exact distributional rerandomization privacy.
  A one-time algebraic receipt MAC has correctness and a `1/|F|` fresh-message
  forgery bound.
- A finite threshold issuance reference construction with share aggregation,
  correctness, perfectly hiding blind requests, fork extraction, and exact
  recipient-view simulation/unlinkability.
- One-trace channel and wire composition endpoints bundling settlement,
  payer floor, no-overspend, exact payee settlement, exculpability, FS-wire
  unlinkability, and its proof-free ZK bridge.
- A nullifier-chain channel instantiation with deposit-capped monotone
  balances, stale-close collision detection, honest-close exculpability,
  conservation/refund liveness, a two-payment anonymity game, and a guarded
  executable ledger proved sound and complete for the relational machine.

## Remaining before the complete roadmap is proved

**Release audit (current branch):** the Fiat--Shamir wire bridge, refund
rerandomization/MAC reduction, threshold issuance and recipient unlinkability,
and channel/wire composition are implemented. A clean full build and source
placeholder audit pass. The sole remaining formal obligation is the
unconditional T7 handler coupling below; the remaining release task is to keep
the detailed historical checkpoint notes reconciled with these landed results.

### Checkpoint validation status

This PR is an **in-progress research checkpoint**, not a completed
formalization. The focused `FrameAudit`, `FrameIdeal`, and `T7` targets
source-build without `sorryAx`; an experimental logged-slope draft that did
not source-build was removed, while the exact public-oracle step coupling was
subsequently reproved and retained in `Games.FrameIdeal`. The root module
`Zkpc.lean` now imports the previously orphaned `Core.Composition`,
`Crypto.ReceiptMac`, and `Network.Issuance` modules, so the default build
kernel-checks them (commit `3e0e18c`). The unconditional T7 theorem remains
open.

1. **Unconditional T7 handler coupling.** Construct
   `FrameDeferredSamplingAvg` — the secret-averaged socket; the pointwise
   `FrameDeferredSampling` is refuted by `frameDeferredSampling_refuted` —
   from the actual stateful `frameImpl`. The proof must
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
   composed cache is preserved rather than assumed. `nfAt` and the shared
   `spend`/`close` emission kernel preserve audit completeness on every
   supported outcome. The cache-free real and ideal fresh-signal observables
   are now proved exactly equal in distribution by the nonzero-digest slope
   bijection. The first complete real `spend` transition from empty caches,
   after secret erasure, is also proved exactly equal to the ideal response
   and full successor-state distribution (message cache, index, and indexed
   nullifier included). The general stateful atomic
   fresh-slope and collision bounds still need
   source-valid proofs. The remaining semantic step is the
   `spend`/`close`/`nfAt` bad-or-good relation and final VCV-io quantitative
   simulation application. In particular, `nfAt` can sample a slope before a
   later adaptive message choice, so this needs continuation-level deferred
   sampling rather than only a pointwise state relation. `Games.FrameGhost`
   now provides a secret-independent ghost handler, exact erasure to the ideal
   handler, transcript monotonicity/completeness, and support-wise structural
   query bounds. `Games.FrameGhostBounds` proves the deferred-uniform
   direct-secret contribution `(qA+qE+qId)/|F|` and assembles the full
   `qb.total/|F|` leakage bound from the precise remaining
   `GhostSlopeBadBounds` interface. Thus only the adaptive slope-hit and
   honest-slope collision fields, followed by real/ghost off-bad coupling,
   remain in this lane. `Games.FrameGhostCoupling` now supplies the missing
   run invariant: programmed initialization, canonical real/ideal state
   relation, hidden-slope/cache alignment, exact real/ghost bad-event
   equivalence, and transfer of ghost slope completeness to the audited real
   state. The next coupling step can therefore reuse the arbitrary-state
   public and materialized-`nfAt` lemmas without paying a second bad-event
   loss. The reuse is now explicit: `realGhost_public_step_erase_evalDist_eq`
   covers every good `roX`/`roA`/`roE`/`roId`/`roNf` operation, and
   `realGhost_nfAt_materialized_erase_evalDist_eq` covers both cached and
   fresh-nullifier branches whenever the hidden slope is already
   materialized. Only operations that create a fresh hidden slope remain in
   the probabilistic step relation. `Games.FrameGhostCoverage` additionally
   proves, per step and for full adaptive runs, that every populated public
   ghost `roNf` entry came from a recorded adversarial slope probe; the
   coupling transfers this to the real `RoNfCovered` invariant. Consequently
   a fresh honest slope cannot collide with a pre-existing public nullifier
   entry without raising the charged slope-hit event.
   `Games.FrameFactor` now also performs the run-level algebra: exact audit
   erasure, rewriting the real slash game as one audited joint experiment,
   the generic good/bad probability split, and the master
   `frame_real_le_ghost_plus_bad` inequality. Its only hypotheses are the
   explicitly named `FrameGoodSliceTransfer` and `FrameBadMassTransfer`, so
   completing the fresh-slope induction plugs directly into the averaged T7
   endpoint without further game rearrangement. The run induction now also
   has its two threadable real-side invariants: every supported step and full
   adaptive run preserves `FrameLeakBad ∨ FrameAuditComplete`, and every
   populated `roX` cache entry remains nonzero. The former handles a
   direct-secret query that becomes bad while materializing an otherwise
   unaudited slope; the latter justifies the line-value bijection on cache
   hits as well as fresh digests.

2. **Production Fiat--Shamir reduction.** The finite-field Sigma and lazy-ROM
   Fiat--Shamir reference models now have exact simulator distributions,
   proof-bearing T4 instances, zero-loss `zkBridgeObligation` endpoints, and
   explicit programming/fork collision bounds. What remains for a deployed
   claim is a reduction from a concrete hash implementation and adversary
   oracle-query semantics to this ideal lazy-ROM model (including the final
   query-dependent knowledge-soundness/forking loss).

3. **Production refund cryptography.** The information-theoretic additive
   masked-cipher reference now proves exact rerandomization and refund-update
   privacy, and the algebraic one-time receipt MAC proves a fresh-message
   forgery bound. What remains is a deployed public-key AH scheme reduction
   and a multi-query EUF-CMA signature/MAC chain-authenticity reduction rather
   than absorption into transition guards.

4. **Threshold issuance and network unlinkability.** A finite threshold
   issuance reference construction now proves aggregation correctness, blind
   request message-independence, fork extraction, and exact recipient-view
   unlinkability/simulation. What remains is an adaptive multi-session network
   game connecting these local distributions to the executable admission and
   settlement trace, plus a production threshold-signature unforgeability
   reduction for ticket creation.

5. **Full channel/fleet composition theorem.** One-trace channel and FS-wire
   bundles now compose close liveness, payer floor, T1/T2 accounting,
   exculpability, unlinkability, and the ZK bridge. What remains is a single
   theorem quantifying over the executable flat/refund/fleet/network trace and
   incorporating reconciliation/slashing, issuance, and the unconditional T7
   endpoint rather than presenting those checked components as separate
   conjunctive interfaces.

6. **Final validation and documentation.** After the items above, run a cold
   dependency fetch and clean full build, the forbidden-placeholder audit,
   `git diff --check`, all `#print axioms` checks, and reconcile `Spec.md`, the
   paper theorem table, assumption registry, and `OPEN-PROOFS.md` with the
   final implementation.

The roadmap is not complete until every item above is implemented and the
final composition and clean-build audit pass.
