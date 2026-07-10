# Open proofs

This is the worklist for anyone (human or agent swarm) picking up the Lean
verification. It lists what is already proved, the general classes the
proofs fall into with a worked template for each class, and the specific
open obligations ranked by value. Everything here builds on frozen
definitions: `Spec.md` is the trust surface and was signed off after
eleven rounds of adversarial review, and the security games under
`Zkpc/Games/` are signed off too, so a contribution proves theorems
*against* those definitions rather than changing them. If a proof cannot
go through as stated, that is a finding about the definition, and it goes
to the gate record (`research_knowledge/gates.md`), not into a weakened
statement.

## Ground rules for a contribution

- Toolchain is pinned: `leanprover/lean4:v4.30.0`, mathlib v4.30.0, VCV-io
  at `8f5dc4f`. `lake exe cache get` then `lake build`. This repo's Lake is
  5.0.0 and has no `-j` flag; cap parallelism with `LEAN_NUM_THREADS=N`.
- Zero `sorry`, zero `admit`, zero `native_decide`, and no `axiom` outside
  `Zkpc/Assumptions.lean` (which itself declares none: the crypto
  assumptions are discharged by the shape of the idealized model). CI greps
  for all four on every push, including inside comments, so do not write
  the bare token words in docstrings.
- Every theorem carries an English docstring restating it and citing its
  `Spec.md` clause. The statement is the contract; make it a faithful
  transcription.
- Verify with `#print axioms <thm>`: a finished proof depends on only
  `propext`, `Classical.choice`, `Quot.sound`.

## What is already proved

All kernel-checked, axiom-clean (`research_knowledge/k2-axiom-audit.md`).

| Theorem | Lean name | File |
|---|---|---|
| T1 no-overspend | `Core.T1_no_overspend` | `Zkpc/Core/T1.lean` |
| Exculpability (honest never slashed / disputed) | `Core.honest_never_slashed`, `honest_close_undisputable`, `honest_settleVoid_never` | `Zkpc/Core/T1.lean` |
| T2 payee balance (exact settlement + collectability) | `Core.T2_paid_exact`, `T2_collectable`, `T2_settles_exactly` | `Zkpc/Core/T2.lean` |
| T3 payer balance (floor + never slashed) | `Core.T3_payer_balance_security` | `Zkpc/Core/T3.lean` |
| T5 closure liveness | `Core.T5_payer_close_liveness` | `Zkpc/Core/T5.lean` |
| T6 priced divergence (both clauses) | `Fleet.T6_priced_divergence`, `T6_slash_within_L`, `epochs_in_window` | `Zkpc/Fleet/{T6,Basic}.lean` |
| T4 spend unlinkability (advantage = 0, session form) | `Games.T4_flat_unlinkability` | `Zkpc/Games/T4.lean` |
| T7 exculpability bound (conditional base plus averaged endpoint; final coupling open) | `Games.T7_frame_bound`, `T7_frame_query_bound_avg` | `Zkpc/Games/{T7,FrameDeferred,FrameAssembly,FrameTransfer}.lean` |
| Calibration pair (B-static loses 1/2, B-rerand passes 0) | `Games.unlinkAdvantage_staticDistinguisher_eq_half`, `unlinkAdvantage_bRerand_eq_zero` | `Zkpc/Games/Calibration.lean` |
| Battery + FRAME must-win breaks | `Games.unlinkAdvantage_{aIndexLeak,nfeReuse,multTagDistinguisher_eq_half}`, `frameWinProb_{YK,aReuse}_eq_one` | `Zkpc/Games/{Calibration,T7}.lean` |
| RLN algebra | `Games.rln_recover_k`, `rln_single_point_hiding`, `rln_evidence_sound` | `Zkpc/Games/RLN.lean` |
| Refund safety (T1-B, T3-B, conservation) | `Refund.T1_B_no_overspend`, `T3_B_floor`, `conservation`, `self_slash_race_closed` | `Zkpc/Refund/Safety.lean` |
| T4 non-vacuity (challenge fires) | `Games.challengeResp_flat_fires` | `Zkpc/Games/T4Fires.lean` |
| Sigma-protocol core (perfect HVZK, special soundness, FS fork extraction) | `Crypto.LinearSigma.evalDist_real_eq_simulated`, `special_soundness`, `fs_fork_extracts` | `Zkpc/Crypto/LinearSigma.lean` |
| Lazy-ROM FS simulation + programming/fork collision bounds | `Crypto.LinearSigma.evalDist_fsProveLazy_eq_simulated`, `fsProgramCollisionBound`, `fsForkChallengeCollisionBound` | `Zkpc/Crypto/FSRom.lean` |
| Masked-encryption privacy (uniform ciphertexts; rerandomized and refund-updated ciphertexts exactly indistinguishable) | `Crypto.MaskedEncryption.evalDist_encrypt_uniform`, `evalDist_rerandomize_cipher_eq`, `evalDist_refundUpdate_cipher_eq` | `Zkpc/Crypto/MaskedEncryption.lean` |
| One-time receipt MAC (forgery probability `1/\|F\|`, tag hides key) | `Crypto.ReceiptMac.mac_forgery_bound`, `evalDist_keyTag_eq` | `Zkpc/Crypto/ReceiptMac.lean` |
| Sigma / FS wire instances of T4 + their zero-loss ZK bridges | `Games.T4_sigmaFlat_unlinkability`, `sigmaFlat_zkBridge`, `fsFlat_zkBridge` | `Zkpc/Games/SigmaInstance.lean` |
| Full-ticket instance (O1 discharged with zero loss for the masked-proof encoding) | `Games.T4_maskedProof_unlinkability`, `maskedProof_zkBridge`, `fullFlat_zkBridge` | `Zkpc/Games/FullTicketInstance.lean` |
| One-trace end-to-end composition (channel-level and wire-level endpoints) | `Core.channel_endToEnd_composition`, `Games.wire_endToEnd_composition` | `Zkpc/Core/Composition.lean` |
| Executable core-ledger refinement (each executable step and list sweep returns a `Step` trace) | `Core.Flat.refined_steps_reachable`, `sweep_refines_trace` | `Zkpc/Core/Refinement.lean` |
| Executable refund / fleet operations refine their machines | `Refund.exec_step_reachable`, `Fleet.exec_step_reachable` | `Zkpc/{Refund,Fleet}/Refinement.lean` |
| Finite-fleet refund safety (aggregated no-overspend, conservation, payer floor) | `Refund.fleet_no_overspend`, `fleet_conservation`, `fleet_payer_floor` | `Zkpc/Refund/Fleet.lean` |
| Receipt-upgrade cascade (claims never overshoot, terminal cascades settle, exact final payouts) | `Refund.cascade_upgrades_le_understatement`, `cascade_terminal_settled`, `cascade_final_payouts` | `Zkpc/Refund/Cascade.lean` |
| Fleet-side T2 aggregate recovery (seniority, caps, conservation, fund-slash forfeit path) | `Fleet.identityRecovery_conservation`, `identityRecovery_all_full`, `fundSlashRecovery_full` | `Zkpc/Fleet/Recovery.lean` |
| Portable-deposit network accounting (global dedup, no-overspend, view isolation, executable refinement) | `Network.no_overspend`, `Network.global_dedup`, `Network.execSettle_refines` | `Zkpc/Network/State.lean` |
| Credential adapter (honest issuance verifies, fresh redemption refines admission, global replay rejected) | `Network.Credential.redeem_refines`, `redeem_rejects_global_replay`, `credential_payment_end_to_end` | `Zkpc/Network/Credential.lean` |
| Threshold issuance reference suite (share aggregation, blind-request hiding, fork extraction, recipient unlinkability) | `Network.Issuance.thresholdIssue_wellFormed`, `ticket_fork_extracts`, `recipientView_unlinkable` | `Zkpc/Network/Issuance.lean` |
| FRAME audit/ideal substrate (exact ghost ornament of the real handler; secret-independent handler with per-operation commutation steps) | `Games.auditedFrameImpl_run_project`, `frameCoupled_initial`, `idealize_roNf_step` | `Zkpc/Games/{FrameAudit,FrameIdeal}.lean` |
| Pointwise deferred-sampling certificate refuted; k-averaged socket derives `(qb.total+1)/\|F\|` from any `FrameDeferredSamplingAvg` instance | `Games.frameDeferredSampling_refuted`, `T7_frame_query_bound_avg` | `Zkpc/Games/FrameDeferred.lean` |
| Ghost model (exact secret erasure of the ghost run, structural budget bounds) | `Games.ghostFrameRun_erase`, `ghostFrameRun_audit_bounds` | `Zkpc/Games/FrameGhost.lean` |
| Ghost bad mass closed unconditionally (`qb.total/\|F\|`) | `Games.ghostSlopeBadBounds_holds`, `ghostFrameRun_leakBad_prob_le` | `Zkpc/Games/FrameBadMass.lean` |
| Master factorization real ≤ ghost-win + ghost-bad, from the two named transfers; deferred-secret atomic couplings incl. the nfAt-then-spend crux | `Games.frame_real_le_ghost_plus_bad`, `initial_nfAt_spend_deferredSecret_ghost_eq` | `Zkpc/Games/FrameFactor.lean` |
| T7 assembly routes A and B: the `(qb.total+1)/\|F\|` endpoint from `FrameGoodSliceTransfer` plus either `FrameBadMassTransfer` (route A; ghost slope socket already unconditional) or `FrameRealBadMassLe` (route B) | `Games.T7_frame_query_bound_of_realGhostTransfers`, `T7_frame_query_bound_of_goodSlice_and_realBad`, `ghostFrameRun_win_eq_certificate_form` | `Zkpc/Games/{FrameAssembly,FrameTransfer}.lean` |
| Chain instantiation C: settlement safety + collision algebra (no-overspend, Bob's floor, refund liveness; stale-close detection exact, honest close never slashed) | `Chain.chain_no_overspend`, `bob_never_loses`, `collision_iff_stale` | `Zkpc/Chain/{State,Collision}.lean` |
| Chain instantiation C: two-payment anonymity (advantage exactly 0) + executable refinement both ways | `Chain.chain_two_payment_anonymity`, `execStep_sound`, `execStep_complete` | `Zkpc/Chain/{Anonymity,Refinement}.lean` |

## The five proof classes (with a template each)

Every open obligation below is one of these shapes. If you have written
proofs of one shape before, the template is the file to read first.

**Class A: safety invariant over a labelled transition system.** Define a
conjunctive invariant, prove it holds at `init`, prove each transition
preserves it, then read the target off it. Induction is on the reachability
predicate (`Reach` / `FReach`). Template: `Zkpc/Core/T1.lean` (`reach_inv`
then `T1_no_overspend`). This class covers all of T1, T2, T3, T5, the T6
counting bound, and the refund safety layer.

**Class B: game-based perfect indistinguishability by RO coupling.** Reduce
"advantage against every adversary" to a single per-challenge
distributional-equality obligation, then discharge it by observing the view
components are fresh-uniform random-oracle samples on slots unqueried in
both worlds (so swapping the two candidates is a measure-preserving
bijection on the cache). Template: `Zkpc/Games/Coupling.lean`
(`unlinkAdvantage_eq_zero_of_challenge_bitfree`) plus
`Zkpc/Games/FlatInstance.lean` (`challengeResp_flat_bitfree`) and
`Zkpc/Games/T4.lean`. This is how the headline and B-rerand were proved.

**Class C: constructive distinguisher / must-win adversary.** Build one
explicit adversary and compute its advantage exactly. The trick is reducing
the concrete run to a closed form: in this codebase `pure_bind`/`map_pure`
do not fire on raw `OracleComp` terms, so run reductions use
`rw [<def>, <spend_eq>]; rfl` and defeq `show`, not `simp`. Template:
`Zkpc/Games/Calibration.lean` (`staticDistinguisher` and
`unlinkAdvantage_staticDistinguisher_eq_half`) and `Zkpc/Games/T7.lean`
(`frameWinProb_YK_eq_one`). This is how the calibration battery and the
FRAME breaks were built.

**Class D: reduction / union-bound / identical-until-bad (game hopping).**
Bound advantage by a chain of hops whose only gap is a named bad event,
then bound the bad event. This is the hardest class and where the biggest
open work sits. Partial template: `Zkpc/Games/T7.lean` (`frame_blind_bound`
gives the `1/|F|` term). VCV-io's `IdenticalUntilBad.lean` and the SecExp
hybrid lemmas are the machinery.

**Class E: field / algebra lemma.** Direct field computation, usually
`field_simp; ring` or a `Finset` support argument. Template:
`Zkpc/Games/RLN.lean`.

## Open obligations, ranked

### 1. T7 unconditional bound (Class D, highest value, hardest)

`Zkpc/Games/T7.lean` proves the FRAME slash probability `≤ 1/|F|` **only
under the hypothesis `hobliv`** (the adversary's evidence distribution is
independent of the secret, i.e. no random-oracle query hit `k`). `Spec.md`
T7 asks for the unconditional `negl(λ)` bound. The obligation: discharge
`hobliv` by a lazy-RO identical-until-bad argument over an unbounded
interactive adversary. The original three-channel numerator is insufficient:
`H_nf` preimage probes recover exposed slopes, and multiple signals introduce
slope-collision targets. The corrected conservative target is
`(q_A + q_Id + q_E + q_Nf*q_sig + q_sig^2 + 1) / |F|`. This is the
single most valuable open proof, the "hard 20%" the VCV-io survey
(`research_knowledge/vcvio-gap.md`) flagged. Start from `frame_blind_bound`
and VCV-io `IdenticalUntilBad`.

**Infrastructure landed:** `FrameQueryBounds` now records separate structural
`IsQueryBoundP` certificates for direct secret probes, nullifier probes, and
honest signal exposures, and
`uniformSecretProbeBound` kernel-checks the adaptive `q/|F|` first-fire term.
`T7_frame_bound_of_pointwise` assembles a pointwise real/ideal loss `ε` with
the blind term to obtain `1/|F| + ε`. The remaining proof is therefore the
handler-level deferred-sampling/identical-until-bad factorization that supplies
the corrected direct-probe, slope-preimage, and collision loss.

**Composition endpoint landed:** `FrameDeferredSampling` now states that
handler factorization as a typed certificate tied to the actual
`FrameQueryBounds`; `frameQueryCharge_eq` combines all leakage terms; and
`T7_frame_query_bound` derives `(qb.total + 1)/|F|`, where `qb.total` includes
`q_Nf*q_sig + q_sig^2`. Thus the structural budgets are no longer
disconnected metadata.

**Pointwise certificate REFUTED; averaged socket landed (2026-07-09,
`Zkpc/Games/FrameDeferred.lean`):** the pointwise-in-`k` `close` field of
`FrameDeferredSampling` is *unsatisfiable*: `frameDeferredSampling_refuted`
is a kernel-checked proof that the two-probe adversary (`roId` at two
constants, `qId = 2`, `total = 2`) admits no certificate over any field with
more than five elements — its real win probabilities at the two probed
secrets are `1` and `≥ 1 − 1/|F|`, while the two slash slices are disjoint,
so no single generator can dominate both pointwise. The finding is recorded
in `research_knowledge/gates.md` (Round 4). The corrected socket is
`FrameDeferredSamplingAvg` (the same comparison averaged over the uniform
secret — exactly the quantity the FRAME experiment produces), with
`T7_frame_query_bound_avg` deriving the identical final bound
`(qb.total + 1)/|F|` and `FrameDeferredSampling.toAvg` showing the averaged
form is weaker. The residual open obligation is therefore constructing
`FrameDeferredSamplingAvg` from `frameImpl` by the stateful transcript
coupling; on the real side, VCV-io's
`probOutput_simulateQ_run'_le_add_bad_add_slack` (heterogeneous bad + slack)
matches the needed per-`k` shape with `bad := FrameLeakBad k` and `ε := 0`,
leaving the `k`-averaged bad-mass bound
`E_k[Pr[FrameLeakBad k]] ≤ qb.total/|F|` as the quantitative kernel (note it
is genuinely *only* true on average: the refuting adversary forces
`Pr[FrameLeakBad c₁] = 1` pointwise).

**Corrected coupling substrate landed:** `uniformSlopeProbeBound` proves the
adaptive multi-target `q_Nf*q_sig/|F|` term. The honest-slope birthday term
remains part of the required final handler argument; an earlier logged-oracle
draft was removed because it did not source-build.
`Zkpc/Games/FrameAudit.lean` is an exact ghost ornament of `frameImpl`: it
records all three leakage classes, proves monotonicity and one-step resource
growth, and projects arbitrary adaptive runs exactly to the original handler.
`Zkpc/Games/FrameIdeal.lean` now supplies the secret-independent handler,
canonical cache-erasing projection, and initial-state relation. The remaining
coupling work includes source-valid public-oracle function-update relations,
the signal/`nfAt` bad-or-good relation, and application of VCV-io's
heterogeneous bad-plus-slack simulation theorem.

**General-state coupling bricks landed (2026-07-09,
`Zkpc/Games/FrameCoupling.lean`):** the per-operation real/ideal
commutation is now discharged at *arbitrary* audit-complete states for
every FRAME operation except fresh-slope signal emission. New invariants:
`HiddenSlopeInj` (distinct honest indices never share a materialized
slope; automatic on the good event) and `RoNfCovered` (every `H_nf` cache
key is a recorded probe or a recorded honest slope, making honest-slope
collisions with the public nullifier cache *detected* bad events). New
theorems: `idealize_nfAt_step_cached` / `idealize_nfAt_step_freshNf` (the
MC20 reveal at a materialized slope commutes exactly with `idealizeFrame`,
using injectivity to confine the ideal per-index image change), and
good-outcome preservation of `HiddenSlopeInj` across all eight operations
(`hiddenSlopeInj_{roA_step,public_step,nfAt_step,emitSignal}` — the
duplication branches are absorbed into `FrameLeakBad`).

**The two remaining per-step obligations, precisely:**

1. *Fresh-slope emission collision carve-out* (`spend`/`close`/`nfAt` at an
   unmaterialized index, general state): the freshly sampled slope can hit
   an existing public `H_nf` entry, so the step is not an exact
   commutation but an identical-until-bad step whose mismatch mass is
   contained in `FrameLeakBad` via `RoNfCovered` (adversary-probe hits are
   the `slopeProbes` branch, honest repeats the duplication branch). This
   needs the inequality-shaped `hstep` of VCV-io's
   `probOutput_simulateQ_run'_le_add_bad_add_slack` rather than a
   distributional equality; it is mechanical but voluminous.
2. *The eager-read obstruction* (`spend` at an index whose slope was
   pre-materialized by an earlier `nfAt` at or beyond the counter): from a
   *fixed* real state the emitted `y = k + a·x` is deterministic (both `k`
   and the cached `a` are fixed) while the ideal `y` is fresh-uniform, so
   the per-state step TV distance is ≈ 1 and no pointwise state coupling
   can close it — even though the *run-level* distributions agree (the
   slope was sampled inside the run). This is exactly the eager-commit
   read-back failure mode described in VCV-io's averaged-state-measure
   section (`avgBadM`, `ProgramLogic/Relational/SimulateQ.lean`): the
   resolution is either (i) instantiating that state-*law* scaffold for
   the FRAME handler, or (ii) first proving `frameImpl` distributionally
   equivalent to a deferred-sampling variant whose `nfAt` draws the
   nullifier directly and defers the slope to first spend — itself an
   identical-until-bad handler equivalence. Either route is the genuinely
   hard residual core; everything else in the per-`k` half is now reduced
   to bookkeeping over the landed bricks. The averaged bad-mass kernel
   `E_k[Pr[FrameLeakBad k]] ≤ qb.total/|F|` (route (c)) in turn consumes
   the same coupling to transport the transcript law to the secret-free
   world before applying the hidden-target bounds
   (`uniformSecretProbeBound` / `uniformSlopeProbeBound`).

**Endpoint assembly landed (2026-07-10,
`Zkpc/Games/FrameAssembly.lean`):** the three lanes are now stitched to the
composition endpoint. `ghostFrameRun_win_eq_certificate_form` transports the
deferred-secret ghost win mass into the certificate shape (ghost erasure +
secret commutation); `frameDeferredSamplingAvg_of_transfers` constructs
`FrameDeferredSamplingAvg` for every query-bounded adversary from exactly
three named residuals; and `T7_frame_query_bound_of_transfers` derives the
complete corrected FRAME bound `(qb.total + 1)/|F|` from them. The whole
remaining unconditional T7 obligation is therefore precisely:
`FrameGoodSliceTransfer` and `FrameBadMassTransfer` (the run-level off-bad
real/ghost coupling induction of `Zkpc/Games/FrameFactor.lean`) plus
`GhostSlopeBadBounds` (the ghost slope-tape masses, whose closing induction
is in progress in `Zkpc/Games/FrameBadMass.lean`; its direct-secret summand
and the `qNf*qSig`/`qSig^2` kernels are already proved). No other
probability algebra or game rearrangement remains between those three Props
and the unconditional Spec.md S7 T7 endpoint.

**Route-B assembly + `FrameBadMassTransfer` warning (2026-07-10,
`Zkpc/Games/FrameTransfer.lean`):** `FrameBadMassTransfer` (real-bad <=
ghost-bad, k-averaged) is *not per-transcript dominated*: conditioned on a
generic two-signal transcript with one `H_nf` probe, the real leakage mass
is exactly `3/|F|` (three deterministic k-roots) while the ghost mass is
`3/|F| - 2/|F|^2` (independent ghost slopes, inclusion-exclusion), so any
proof of that transfer must carry exact second-order cancellation — no
per-step or per-transcript coupling can close it, and it may fail. The
safer, first-order target is the *direct* real-side bound
`FrameRealBadMassLe` (`Pr[FrameLeakBad] <= qb.total/|F|` over the audited
joint experiment): under the answer-transcript re-parameterization every
leakage branch pins the deferred secret or one fresh slope to a single
root per budget pair, so plain union bounds suffice.
`frameDeferredSamplingAvg_of_goodSlice_and_realBad` and
`T7_frame_query_bound_of_goodSlice_and_realBad` land the corresponding
assembly: the unconditional endpoint now follows from
`FrameGoodSliceTransfer` plus *either* route A
(`FrameBadMassTransfer` + `GhostSlopeBadBounds`) *or* route B
(`FrameRealBadMassLe`). Recommended: discharge route B.

**Lane claim (2026-07-10):** `FrameRealBadMassLe` — in progress (route-B
real-side induction), claimed by the assembly/route-B agent. Working
architecture (shared substrate also usable for `FrameGoodSliceTransfer`):
stage 1, an identical-until-bad handler equivalence between the audited
real handler and a *deferred-slope* real handler whose `nfAt` draws the
indexed nullifier directly and whose `spend` draws the hidden slope at
consumption time (their divergence events are contained in `FrameLeakBad`
via `RoNfCovered`); stage 2, an exact per-`k` pointwise-state step
coupling between the deferred-slope handler and the ghost handler (the
consumption-time slope makes `y = k + a·x` fresh-uniform by the
`mulRight` bijection, eliminating the eager-read obstruction), after
which both the good-slice and the real-bad-mass claims transport to the
landed ghost-side theorems.
Refined plan after design validation (2026-07-10, second pass): the
deferred-slope handler is precisely *the ghost handler with the honest
line value computed as `y = k + a·x` from a consumption-time slope draw*
(everything else, including `roId`/`roA`/`roE` handling, copies the ghost
handler; divergences from the real handler occur only on `roNf` probes at
a deferred slope and on consumption-time slope collisions, both contained
in `FrameLeakBad`). Never-spent `nfAt` slopes are drawn as a post-run
tape, exactly as in `FrameBadMass`'s `materializeSlopeTape`. Stage 2 for
`FrameRealBadMassLe` is then a per-transcript union bound mirroring the
landed tape kernels plus one new k-root family: for consumed indices the
slope is the deterministic root `(y_i − k)/x_i`, so each `H_nf` probe and
each index pair pins the deferred uniform `k` to one point — giving
`(qA+qE+qId) + qNf·qSig + qSig²` total roots, i.e. `qb.total/|F|`,
first-order. Stage 1 (real ≡ deferred up to `FrameLeakBad`, exact on the
good slice) is the remaining custom induction; its divergence events are
enumerated above and each is chargeable. The same stage 1 + the
`mulRight` bijection give `FrameGoodSliceTransfer`, so the two open Props
share all substrate except the final counting step.

**Fixed-transcript root kernel landed (2026-07-10,
`Zkpc/Games/FrameTransfer.lean`):** `DeferredLine`,
`frameRealRootCandidates`, and
`probEvent_uniform_mem_frameRealRootCandidates_le` now machine-check the
stage-2 arithmetic: the direct candidates, one root for every
slope-probe/line pair, and padded ordered collision roots have length at
most `qA + qE + qId + qNf*qSig + qSig²`; a deferred uniform secret hits
that list with at most the corresponding `1/|F|` mass. The two singleton
root equivalences are also proved. What remains is only transporting the
actual adaptive handler into this fixed transcript form.

**Lane claim (2026-07-10, orchestrator):** `FrameGoodSliceTransfer` —
the good-slice consumption of the shared substrate, in
`Zkpc/Games/FrameGoodSlice.lean`: the `mulRight`-bijection win-functional
transport through the stage-1 deferred-slope equivalence and the stage-2
ghost coupling as they land (consumed by their committed names, never
redefined), the good-slice mass-drop bookkeeping at bad-firing steps, and
the final instantiation into `T7_frame_query_bound_of_goodSlice_and_realBad`.
Stage 1 itself belongs to the route-B lane above; if its shape shifts,
only the transport re-targets.

### 2. The ZK bridge, O1 (Class D, high value)

`Zkpc.Games.zkBridgeObligation` is stated but not discharged for a concrete
instance. Prove, for a full-ticket instance `Sfull` carrying the NIZK proof
`π`, that advantage against its game is at most advantage against the
proof-free `flatInstance` plus the scheme's zero-knowledge distinguishing
advantage (Spec.md assumption 2). This is what lets the perfect
`T4_flat_unlinkability` (proved on the π-free view) speak about the real
wire protocol. See the disposition in `Zkpc/Games/FlatInstance.lean` and
`Zkpc/Games/T4.lean`.

**Concrete ideal-cryptography bridge landed:**
`Zkpc/Games/FullTicketInstance.lean` defines both a simulator-side full wire
view and `maskedProofInstance`, whose honest prover retains a private witness
and emits the witness plus a fresh additive one-time mask.  The session-level
theorem `evalDist_spendBatch_maskedProof` proves that the witness-dependent
real transcript is exactly the simulator distribution; consequently
`T4_maskedProof_unlinkability` and `maskedProof_zkBridge` discharge O1 with
zero loss for this concrete perfectly-ZK proof encoding.  A production NIZK
(for example a Fiat--Shamir proof under a computational assumption) remains
an optional refinement and would replace exact equality by its scheme-specific
`εZK` reduction.

**Sigma and lazy-ROM FS bridges landed:** `Zkpc/Crypto/LinearSigma.lean` gives
the finite-field proof-of-knowledge core and `Zkpc/Crypto/FSRom.lean` proves
the lazy-ROM simulator distributions plus explicit programming/fork collision
bounds. `Zkpc/Games/SigmaInstance.lean` connects both proof-bearing wire types
to T4 and discharges their zero-loss ZK bridges. A deployed hash-function
reduction and final adversarial-query knowledge-soundness bound remain outside
this ideal lazy-ROM reference layer.

### 3. B-instance obligations O2 / O3 / O4 (discharged)

For the refund instantiation, `bRerand_spendBatch_none_zero` discharges O2,
`bIdeal_openCh_adversary_genesis`, `bIdeal_serve_issuer_receipt`, and
`bIdeal_serve_capable_mono` discharge the adversary-issued-genesis/receipt
semantics (M2/O3) — noting that O3's discharge rests on the rev-9 model
redefinition, under which the issuer abstraction leaves no malformed-handle
case to rule out (`Zkpc/Games/README-games.md`, rev-9 obligation register) —
and `bIdeal_closeViewSimulatable` discharges O4 for both B-static and
B-rerand.

### 4. T4 challenge-fires lemma (discharged)

K3's non-vacuity recommendation is now kernel-checked by
`challengeResp_flat_fires` in `Zkpc/Games/T4Fires.lean`: for every positive
budget, the opened flat challenge produces a concrete nonempty ticket batch.
The lemma is included in the proved-theorems table above.

### 5. Refund cascade and fleet-side settlement (Class A, medium)

`Zkpc/Refund/` models one close-dispute round at `N = 1`. Extend it to the
full upgrade sub-window cascade (`Spec.md` §2, the receipt-withholding
repair) and to the multi-gateway fleet. Separately, the fleet-side T2
recovery clauses (identity- vs fund-slash window claims, `Spec.md` MC19)
exist as prose and an `N = 1` core; lift them to the fleet transition
system (the `Zkpc/Fleet/` machine is the place).

**Finite-fleet safety and cascade landed:** `Zkpc/Refund/Fleet.lean` defines
interleaved multi-channel reachability, proves each component is reachable in
the single-channel machine, and aggregates no-overspend, settlement
conservation, and the cooperative payer floor across any finite fleet.
`Zkpc/Refund/Cascade.lean` models successive withheld-receipt upgrades, proves
claims never overshoot the certified count, proves terminal cascades settle,
and establishes the exact `n-j` upgrade count plus final payout conservation.
`Zkpc/Fleet/Recovery.lean` now formalizes the fleet-side T2 aggregate recovery
rule: pre-slash checkpoint eligibility, sweep-before-conflict seniority,
remainder-capped payouts, exact conservation, full recovery when eligible
demand fits, and the distinct fund-slash forfeit path. Connecting individual
checkpoint membership witnesses and deadlines to the executable ledger trace
remains part of the ledger-refinement task.

**Executable ledger bridges landed:** `Zkpc/Core/Refinement.lean` proves
that successful `Open`, honest `Spend`, fresh `Redeem`, payer close, identity
dispute, and arbitrary list sweeps return traces of their corresponding `Step`
constructors; the sweep trace accounts explicitly for skipped ineligible
entries. `Zkpc/Refund/Refinement.lean` supplies guarded executable accept,
cooperative-close, and force-close operations for B, while
`Zkpc/Fleet/Refinement.lean` supplies executable tick, gateway admission, and
reconciliation slash. Consequently generated states inherit T1--T6 and the
refund/fleet invariants. Remaining execution work is the contract-internal
close-window scheduler and the receipt-upgrade cascade driver.

### 6. Multi-recipient generalisation (accounting layer landed)

`Zkpc/Network/State.lean` defines a portable-deposit network in which one
deposit funds arbitrarily many recipients, admissions share a global
nullifier set, and settlements are recipient-directed. It proves global
deduplication, exact payout accounting, network-wide no-overspend, payout
partitioning across a finite recipient set, unrelated-recipient view
isolation, and executable-operation refinement. This closes the definition
and accounting portion of the named open problem.

`Zkpc/Network/Credential.lean` now supplies the first concrete credential
adapter: every application field is bound into a Fiat--Shamir statement,
honest issuance verifies, valid fresh redemption refines to the network
admission transition, and a nullifier replay is rejected even when redirected
to another recipient. `Zkpc/Network/Issuance.lean` adds finite threshold share
aggregation, perfectly hiding blind requests, fork extraction, and exact
recipient-view simulation/unlinkability. An adaptive multi-session game
connecting those local results to executable network traces, and a production
threshold-signature unforgeability reduction, remain open.

## Where the definitions and their rationale live

- `Spec.md`: the object, the games, the seven theorems, and the modeling
  choices (MC1..MC20), each tied to a counterexample that forced it.
- `research_knowledge/gates.md`: the eleven-round review record, so you can
  see why every clause is the way it is before you try to prove around it.
- `Zkpc/Games/README-games.md`: the obligation register (O1..O4) and
  prover guidance specific to the game layer.
- `paper/`: the systematization and the theorem-to-file map at paper
  altitude.

## The nullifier-chain channel instantiation (`Zkpc/Chain/`, landed)

A separate, much simpler unidirectional-channel design
(`research_knowledge/vitalik-nullifier-chain-channel.md`: Alice keeps a
nullifier chain `N_{i+1} = H(N_i, c)`; each payment reveals the parent's
committed next-nullifier, proves `parent_balance + δ = new_balance ≤ D` in
zero knowledge, and commits to a fresh next nullifier; Bob countersigns and
refuses duplicates; a stale close is challengeable by nullifier collision).
Formalized as an **additional instantiation** alongside `Zkpc/Refund/`; it
does not touch the frozen `Spec.md` definitions. All theorems kernel-checked,
depending only on `propext`/`Classical.choice`/`Quot.sound`.

**Class A — settlement state machine** (`Zkpc/Chain/State.lean`, template
`Zkpc/Core/T1.lean`): `chain_no_overspend` (Bob's payout and every committed
balance `≤ D` on every reachable trace), `bob_never_loses` (every terminal
state pays Bob at least his latest countersigned balance: honest close pays
it exactly per `honest_close_exact`; challenged stale close and Alice-AWOL
timeout pay the whole deposit), `conservation` (every settled channel splits
exactly `D`), `alice_refund_liveness` (if Bob never countersigned, Alice can
unilaterally drive the channel to a settlement paying her exactly `D`), and
`no_overpay_recovery` (the `new_balance ≤ D` guard caps every closable
state). Bob's countersignature is idealized as the transition guard itself
(an accepted countersigned state IS its witness), matching the repo's
knowledge-soundness-as-transition-guard convention.

**Collision mechanism** (`Zkpc/Chain/Collision.lean`): the algebra behind
the challenge rule. `stale_close_detectable` (completeness: closing any
non-final state — including the genesis-refund-after-payment case, uniformly
— opens exactly the nullifier the successor message revealed, so an honest
Bob holds the colliding evidence), `honest_close_unchallengeable`
(soundness/exculpability: closing the latest state opens a nullifier no
message ever revealed, so an honest Alice is never slashed),
`collision_iff_stale` (the challenge predicate is exact — the fact that
justifies transcribing the evidence rule as the machine's `i < len` guard),
plus the machine bridges `challenge_enabled_of_stale` /
`honest_close_never_slashed`. Chain collision-freedom (`Injective nul`) is
the explicit lazy-RO hypothesis. `Zkpc/Chain/Refinement.lean` adds the
deterministic guarded executor with both refinement directions, so
executable traces inherit the safety layer.

**Class B — per-request anonymity** (`Zkpc/Chain/Anonymity.lean`, templates
`Zkpc/Games/Coupling.lean` + `T4.lean`): `chain_two_payment_anonymity` —
the two-payment linkage game (hidden bit selects same-chain-consecutive vs
two-independent-channels; Bob sees the two messages: revealed nullifier,
hiding commitments to new balance and next nullifier, public δ) has
advantage exactly `0` for every adversary. Both worlds' views equal one
canonical fresh view (`evalDist_sameChain` / `evalDist_crossChain`):
unqueried `H(N_i, c)` slots are fresh-uniform in the lazy ROM and the
commitments are one-time additive masks (the perfectly hiding reference
scheme of `Zkpc/Crypto/MaskedEncryption.lean`).

**Deliberately not claimed** (the design doc's own stated boundaries and
extensions): deposit-amount (`D`) and close-amount privacy, open/close
footprint hiding, recipient anonymity (Bob is named on chain),
shielded-pool integration, δ-correlation and timing across payments with
*distinct* public prices, and real signature/STARK reductions (a deployed
scheme replaces the ideal guards/commitments and pays its own
unforgeability/knowledge-soundness/hiding bounds).

**Lane re-claim (2026-07-10, continuation):** `FrameRealBadComponents` — in
progress, continuation of the e17023c/0ac9005 architecture (stage 1: real ≡
deferred-slope handler up to `FrameLeakBad`; stage 2: per-transcript k-root
union bound mirroring the landed tape kernels). New work goes in
`Zkpc/Games/FrameRealBad.lean`; `FrameTransfer.lean` is not edited by this
lane.

**Route-B stage 1 DISCHARGED (2026-07-10, continuation session):**
`RealDSStepCoupling` is now a kernel-checked theorem
(`realDSStepCoupling_holds`, `Zkpc/Games/FrameRealBadStep.lean`): all eight
FRAME operations satisfy the real/deferred-slope identical-until-bad step
coupling over `RealDSGood` (canonical secret-erasure + hidden-slope
retention + literal audit equality + `DSSlopesCovered`/`RoNfCovered`/
`HiddenSlopeInj` + goodness). The deferred-slope handler `dsFrameImpl`
(`FrameRealBad.lean`) pins each hidden slope at first honest touch — the
same instant the real audit records it — which eliminates the eager-read
obstruction from this lane entirely: every divergence (secret probes,
`H_nf` probes at recorded slopes, fresh-slope collisions, `H_id(k)` reads)
raises `FrameLeakBad` on both sides in the same step. The generic coupling
rule is `relTriple_simulateQ_run_untilAbsorbing` (reusable; built on
VCV-io's relational `simulateQ` layer). Consequences
(`FrameRealBadTransfer.lean`, `FrameRealBadStep.lean`, all axiom-clean):
`auditedFrameJoint_bad_le_dsFrameJoint` (k-averaged real bad mass ≤
deferred bad mass, unconditional) and `frameRealBadMassLe_of_dsCount`:
`FrameRealBadMassLe` — hence the complete corrected T7 via
`T7_frame_query_bound_of_goodSlice_and_dsCount` — is now reduced to
exactly two named residuals:

1. `DSBadMassLe` (`FrameRealBadTransfer.lean`, stage 2): the k-averaged
   leakage mass of the k-root-clean deferred run `dsFrameJoint` is at most
   `qb.total/|F|`. Proof plan: per-emission pad bijection `a ↦ k + a·x`
   (fresh consumption) plus tape-deferral of pinned-but-unconsumed
   `nfAt` slopes (mirror `FrameBadMass.materializeSlopeTape` /
   `skelFrameImpl_*_prob_le`), then the landed root kernels
   (`frameRealRootCandidates`, `probEvent_uniform_mem_list_le`).
2. `FramePointwiseGoodSlice` (`FrameGoodSlice.lean`, orchestrator lane).
   Note: the ds coupling gives an alternative consumption path — the
   until-absorbing coupling already yields, pointwise in `k`,
   `Pr[Slashes ∧ ¬bad | real] ≤ Pr[Slashes | dsFrameRun k]` (bad branch
   refutes the left event), so the good-slice lane can equivalently close
   by comparing the deferred-run win mass to the ghost win mass with the
   same pad/tape machinery as `DSBadMassLe`.
