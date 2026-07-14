# Roadmap — the v2 worklist (nullifier-chain protocol)

This is the worklist for anyone (human or agent swarm) picking up the
verification of the new design of record, `PROTOCOL.md`. It replaces the
rev-11 worklist wholesale: the old object's open items were either
discharged by the PR #2 campaign (the T7 finite-query bound, ideal-model
ZK bridges, refund fleet/cascade, end-to-end compositions — all closed as
historical results about the rev-11 object; inventory preserved at
`research/raw/proof-inventory-rev11.md`) or are moot under the
redesign (the B-instance obligations and the encrypted-refund layer, whose
primitive the new protocol removes).

**Ground rule carried over unchanged:** definitions are the risk surface.
Nothing below gets proved against a moving target. Phase 0 freezes a
Spec-v2 through adversarial gate rounds first; if a proof cannot go
through as stated, that is a finding about the definition and goes to
`research/raw/gates.md`, not into a weakened statement.

## Phase 0 — definitional prerequisites (blocks everything)

`PROTOCOL.md` is a design note, not yet a frozen spec. Five open
definitional issues, recorded as round-0 findings of the v2 gate series in
`research/raw/gates.md`:

- **G1 ([#10](https://github.com/dmarzzz/zk-payments-confetti/issues/10)) — signature channel-binding.** What exactly Bob signs must bind the
  channel id and recipient, or cross-channel signature splicing rebuilds
  the rev-1 attack against the no-overspend analogue.
- **G2 ([#11](https://github.com/dmarzzz/zk-payments-confetti/issues/11)) — the withheld-countersignature wedge (critical path).** Alice
  reveals `N_{i+1}`; Bob refuses to countersign. Closing on state `i` is
  now forfeit-bait (Bob holds the revealing message), but the new state
  was never accepted. Is closing on an unsigned-but-proof-valid state
  legal? This is genuine protocol design, not transcription, and no repair
  is stated in `PROTOCOL.md`.
- **G3 ([#12](https://github.com/dmarzzz/zk-payments-confetti/issues/12)) — challenge-window duration.** Bob's window to challenge a close is
  unspecified.
- **G4 ([#13](https://github.com/dmarzzz/zk-payments-confetti/issues/13)) — what Close verifies about the balance commitment.** The close
  path's proof obligation (the π_close successor) is unspecified.
- **G5 ([#14](https://github.com/dmarzzz/zk-payments-confetti/issues/14)) — forfeit-all proportionality.** Forfeiting the entire deposit in
  honest-limit edge cases interacts with G2; the accounting needs a stated
  rule.

Deliverable: Spec-v2 (new algorithm tuple, payment relation `R_pay`
including `δ ≥ 0`, challenge-evidence validity, the two close timers),
gate-frozen B1-style. The old object took 11 rounds; this object is far
simpler (no fleet, epochs, RLN, or refunds); estimate 4–7 rounds.

## Phase 1+ — theorem obligations (ranked)

1. **Safety core on the new transition machine.** Seed: merge
   `lean/Zkpc/Chain/State.lean` with the netting/forfeit skeleton of
   `lean/Zkpc/Refund/State.lean`. Prove conservation, no-overspend
   (`Σδ ≤ D` via STARK knowledge-soundness through the
   genesis-or-Bob-signed disjunction, chain contiguity, PQ-EUF-CMA, G1
   binding), no-overpay-recovery, honest-close-exact — with
   `Chain/State.lean`'s three disclosed fiats discharged: the
   honest-recipient `settleSplit` guard replaced by an explicit
   challenge-window model, timing de-abstracted, and `δ ≥ 0` added.
   Anti-vacuity: a signature-splicing scheme must lose.
2. **Collision-challenge soundness, de-idealized, both directions.**
   Stale-close-always-challengeable and honest-close-never-challengeable
   with (a) a lazy random-oracle chain model (adapt
   `lean/Zkpc/Crypto/FSRom.lean`) and a *proven* `n²/|N|` collision bound
   (currently docstring-only in `lean/Zkpc/Chain/Collision.lean`), (b)
   commitment binding as an assumption rather than by construction, (c)
   challenge-evidence validity as defined in Spec-v2.
3. **Challenge non-frameability (the T7 successor).** No q-query
   adversary — including Bob with the full transcript, grinding hashes for
   `c` — produces a message revealing an honest Alice's unrevealed
   committed next-nullifier. Probabilistic `~q/|F|`-shaped bound; port the
   secret-averaged deferred-sampling apparatus and query charging
   (`FrameDeferredSamplingAvg`, the `qb.total` accounting) from the FRAME
   campaign. Pointwise-in-secret certificates are refuted
   (`frameDeferredSampling_refuted`); do not attempt them.
4. **Per-request anonymity, full strength (the T4 successor).** Port the
   `Unlink`/`Coupling`/`FlatInstance` framework to the chain view:
   adaptive adversary with oracle access, session vector `q ≥ 2`,
   countersignature-withholding as a charged abort lever, a
   which-parent-hiding clause (the ZK simulator must not need the
   signature witness), close view simulatable from (channel id, final
   split). Plus the calibration battery: must-fail non-hiding balances
   (formalizing `PROTOCOL.md`'s own δ-matching argument — the
   hidden-balance necessity lemma), must-fail clear/bit-identical
   signatures, must-fail linkable nullifiers, must-pass the real scheme;
   plus challenge-fires witnesses (`T4Fires` port). The existing
   `lean/Zkpc/Chain/Anonymity.lean` (two payments, same δ, no oracles) is the
   warm-up, not this.
5. **Close-window liveness.** The two-timer structure (90-day absolute,
   7-day on-request), the G3 challenge window, and AWOL-forfeit under weak
   fairness — upgrading `alice_refund_liveness` from existential-trace to
   guaranteed-under-scheduling, reusing the T5 fairness machinery.
6. **Uniform-genesis refund.** Genesis-close with no payments refunds `D`;
   genesis-close after payments convicts by the same collision rule. The
   no-special-case theorem.
7. **Honest-retry dedup (MC2 successor).** Bit-identical resend is not a
   conflicting reveal; the abort price is at most one δ.
8. **Post-quantum model restatement.** Adversary class stated as
   EC-broken/QPT; every assumption names a PQ instantiation
   (WOTS/XMSS/SPHINCS+/Dilithium); stateful-signature key exhaustion and
   state reuse in the model if a stateful scheme is chosen.
9. **TLA+ v2 model** (parallel to items 1–2): collision-challenge close,
   both timers, forfeit; the broken modes (no `≤ D` check, no genesis
   commitment) as reproducible counterexamples.
10. **ZK bridge and end-to-end composition.** The M1 bridge with
    signature-as-witness (the SigmaInstance technique under a STARK
    idealization), then the one-trace end-to-end theorem
    (`Composition/EndToEnd.lean` pattern).
11. **Stretch (each its own campaign; defer):** shielded-pool integrated
    open/close; recipient-anonymous opens; executable
    refinement/serialization for the new machine.

## What the existing corpus contributes

| Existing material | Role in v2 |
|---|---|
| `lean/Zkpc/Chain/*` | Primary seed (obligations 1, 2, 4). Carries three disclosed fiats to discharge; see module docstrings. |
| `lean/Zkpc/Games/Framework.lean`, T7 generic lemmas (`frame_inner_bound`, `frame_blind_bound`) | Keep verbatim. |
| FRAME deferred-sampling stack (`FrameDeferred*`, `FrameDSCount*`, `FrameGoodSlice*`, `FrameComplete`) | The query-charging engine for obligation 3. |
| `Unlink`/`Coupling`/`FlatInstance`/`T4`/`T4Fires`/`Calibration` | The anonymity engine for obligation 4 (rework against the chain view). |
| `Refund/State.lean` netting + forfeit skeleton, `Core/T5.lean` clock lemmas | Seeds for obligations 1 and 5. |
| `Crypto/FSRom.lean` | The lazy-RO model for obligation 2; hash-based, PQ-compatible. |
| Everything RLN/fleet/refund-cascade/network and the B-instance calibrations | Historical results about the rev-11 object. Keep compiling; no v2 role. |
| `Crypto/{ElGamal,ElGamalDDH,SchnorrSigma,SchnorrReceipt,ThresholdSchnorr,LinearSigma}.lean` | Elliptic-curve constructions, excluded by the PQ constraint. Historical only. |

## Attestation debt

The last clean-machine build attestations are `2fe8354` (full root build,
3,595 jobs) and `e2de071` (target build, per the PR #2 record). The 11
commits merged after `e2de071` (ElGamalDDH, FramePPT, Schnorr*,
ThresholdSchnorr, Serialization, the Network schedulers, the refund
crypto/serialization refinements) have **no build attestation**, and the
branch's own audit (`research/raw/t7-stack-audit-2026-07-10.md`,
finding F1) documents that token-level greps passed while non-compiling
proof code was committed. Before any v2 work builds on those modules, run
a full fresh-clone root build on a machine with resources and record the
result here. Tracked: [#15](https://github.com/dmarzzz/zk-payments-confetti/issues/15).

## Ground rules for a contribution (unchanged)

- Toolchain pinned: `leanprover/lean4:v4.30.0`, mathlib v4.30.0, VCV-io at
  `8f5dc4f`. `make build` from the repo root (the Lean project lives in
  `lean/`); cap parallelism with
  `LEAN_NUM_THREADS=N`.
- Zero `sorry`, zero `admit`, zero `native_decide`, no `axiom` outside
  `lean/Zkpc/Assumptions.lean`. CI greps for all four on every push, including
  comments.
- Every theorem carries an English docstring restating it and citing its
  spec clause (Spec-v2 once frozen; `PROTOCOL.md` sections until then).
- Verify with `#print axioms <thm>`: only `propext`, `Classical.choice`,
  `Quot.sound`.
- Certificates over sampled secrets must be secret-averaged, never
  pointwise (see `CONTRIBUTING.md`).
- A claim of "builds green" requires a recorded fresh-clone build, not a
  grep (see `CONTRIBUTING.md`).
