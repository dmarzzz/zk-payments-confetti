# K7 — Experiment outcome

Task K7 (TASKS.md): log the autoresearch experiment's outcome against the
success and failure shapes README.md named up front. This is an evidence
ledger, not a claim that every acceptance gate has closed: the point of the
repo was never only the theorems, it was the question *how much of a missing
cryptography literature can agents build when the human can evaluate the
definitions but not the proofs?* — and what the failure looks like when it
comes.

## The bet, restated

README's success condition: **a definition the community can attack, and
the first machine-checked unlinkability proof for any channel/credit
construction, with a human having read only `Spec.md`.** The named failure
shapes, to be *logged not hidden*: (1) definitions drifting toward what is
*provable* instead of what is *true*; (2) proofs of trivialities dressed
as theorems; (3) the Lean bet losing to the mature frameworks (SSProve the
documented fallback).

The technical source target and the required acceptance process are distinct.
The agent-run work can establish the former; it cannot certify that the
human-read condition occurred. No non-author human B1/B3/K1 sign-off is
recorded, so the original success condition is not yet fully met.

## What happened, against each shape

### Success condition: FINITE SOURCE TARGETS TECHNICALLY VALIDATED; HUMAN GATES PENDING

- **`T4_flat_unlinkability`: spend-unlinkability advantage exactly 0**,
  kernel-checked, dependent only on the three standard Lean axioms (K2).
  To our knowledge this is the first machine-checked spend-unlinkability
  result for any payment-channel or credit construction — the gap
  ../processed/field-report.md documented ("no machine-checked proof of payment
  unlinkability exists for any channel construction"). It is a session-form
  game (the member's whole epoch session, not one spend), which is
  *stronger* than the single-spend version the internal review started
  with.
- **The definition is attackable, and agent reviewers attacked it.**
  `Spec.md` went through eleven B1 rounds and the T4/T7 games through five
  B3 rounds, each in an independent agent context, plus an agent-run
  statement audit (K1) and a simulated external cryptographer (K4). The full
  counterexample record is `gates.md`. This is useful pre-review evidence,
  not a substitute for the required human sign-off.
- **The rest of the suite is present and technically validated:** T1
  (no-overspend), T2/T3
  (balance security both sides), T5 (closure liveness), T6 (priced
  divergence, fleet), the finite-query T7 endpoint, the refund variant
  (T1-B/T3-B/conservation), and the calibration pair. The repaired final T7,
  composition, and scaling endpoints passed the fresh-clone build and axiom
  audit at source checkpoint `2fe8354`, as recorded in the amendment below.
- **The T7 boundary, logged:** the source endpoint now states the
  secret-averaged finite inequality
  `frameWinProb ≤ (qb.total + 1)/|F|` directly from `FrameQueryBounds`; the
  earlier `hobliv` description is historical. This is not itself an
  asymptotic PPT theorem. The scaling wrapper assumes per-parameter query
  certificates and explicit query/field-growth or negligibility premises;
  it does not prove that PPT adversaries satisfy them.

### Failure shape 1 — definitions drifting toward provability: NO DRIFT FOUND BY AGENT REVIEW; HUMAN GATE PENDING

This is A2L's failure and the one the experiment most feared. It did not
appear in the agent audit, and the reason is instructive: **the simulated
definition gate used independent adversarial agent reviewers to catch
attempts at drift before they reached a proof.** This is not called a human
gate here; the actual human decision is pending. The load-bearing episodes:

- **The gap-index understatement (round 5).** The close mechanism as first
  written let a payer skip index 0, spend at 1..m, and close claiming
  index 0 unused — recovering the full deposit after consuming service.
  This *would have been provable* against the weaker close definition; the
  gate refused it and forced MC20 (verifiable spend count) — the true
  definition, harder to prove, which the proof layer then had to (and did)
  meet.
- **The unsatisfiable UNLINK game (round 1).** The first T4 game was too
  *strong* — every scheme, including the sound ones, lost it (three
  post-challenge distinguishers). A less careful process would have
  quietly weakened the game at proof time until T4 went through, and the
  weakened game would not have met the stated semantic target. The agent
  gate caught it at the definition and prescribed the challenge-terminated
  repair.
- **The simulated external review strengthened, did not narrow (K4).** When
  the outside-cryptographer agent found the q=1 game certified only
  first-spend-per-epoch unlinkability, the response was to *upgrade* the
  game to the session form — more true, not more provable. The calibration
  battery was widened at the same time.

The evidence that the agent process found no drift is the shape of the whole
gate log: findings moved *outward* over the rounds (from the theorem cores, which
held from round 2, into repair periphery), and the definitions got
*stronger* under review, not weaker.

### Failure shape 2 — trivialities dressed as theorems: CHECKED, and defended by construction

- The **calibration pair** is the built-in guard against this, and it
  fires correctly: the *same* UNLINK game gives advantage exactly 1/2
  against B-static (the known-broken static-`E(R)` design) and exactly 0
  against B-rerand (the fix). A game that could not separate a broken
  scheme from a fixed one would be a triviality; this one provably can.
- The **must-catch battery** (index-leak, `nf_e`-reuse, multiplicity-tag)
  each wins at 1/2, and the **must-win FRAME adversaries** (`y=k`,
  `a`-reused) each win at probability 1 — the game punishes real breaks,
  so its silence on the sound scheme means something.
- **K3** (adversarial vacuity review) is the dedicated audit for this
  shape — its verdict is recorded separately in `k3-vacuity-review.md`.

### Failure shape 3 — Lean losing to SSProve: DID NOT HAPPEN

The bet was that Lean 4 + mathlib + VCV-io could carry a game-based
protocol-privacy proof this year, against a survey that put the mature
frameworks (SSProve/CryptHOL) ahead. It carried it: the T4 coupling landed
via VCV-io's `DistEquiv`/`advantage_zero` machinery on the exact template
(`OneTimePad/HeapBasic`) the `vcvio-gap.md` survey predicted, in days not
weeks, and B-rerand reused the same technique. The SSProve fallback was
never needed. Caveat retained honestly: T7 is an exact finite-query theorem
in the ideal random-oracle model. The optional asymptotic lift requires
explicit per-parameter query certificates and scaling hypotheses; a
PPT-to-query theorem and deployed-hash reduction are not formalized.

## The unplanned result: cross-method convergence

Not in the original design, and the strongest single datum for the
autoresearch thesis: the **TLA+ model-checker independently found the
gap-index close hole** (via TLC state exploration) at the same time the
**adversarial gate found it by definition review**, and TLC then
**verified the same MC20-shaped repair** the gate adopted. Two methods
that share no machinery — symbolic model-checking and human-style
definition attack — converged on the same defect and the same fix. When an
agent-run process reaches a real cryptographic hole by two independent
roads, that is evidence the hole is real and the process is not
hallucinating agreement with itself.

## Honest ledger of what is NOT done

- Technical validation of the proof-bearing source completed at checkpoint
  `2fe8354`. The exact final PR head will be recorded externally after the
  documentation/PDF-only release commit; that SHA handoff is not pending
  proof evidence.
- A PPT/runtime model, a theorem deriving polynomial query certificates from
  PPT, and a deployed-hash reduction are not formalized. The asymptotic
  wrapper assumes the required query and field-growth/negligibility facts.
- The non-author human B1/B3/K1 acceptance required by `BRIEF.md` has not
  been logged; K4 is a simulated, not real outside-cryptographer review.
- The refund base transition system is per-channel (N=1). The full
  failed-upgrade cascade and finite-fleet aggregation are proved in
  `Zkpc/Refund/Cascade.lean` and `Zkpc/Refund/Fleet.lean`; those results do
  not turn it into a portable multi-recipient channel.
- Instantiation-B's Lean UNLINK proof is the ideal-model calibration pair.
  The masked, Sigma, and lazy-ROM Fiat–Shamir reference bridges and genesis
  obligations are discharged; a reduction for a production SNARK/encryption
  scheme remains outside the stated boundary — we do not verify circuits.
- The honest-limits the reviews surfaced (retroactive `k`-linkage on
  identity-slash, the stale-close one-session residue, within-epoch
  linkage, spend-count-at-close, fleet-honesty presumption for window
  recovery, multi-recipient as the open problem) are the paper's
  honest-limits section, owed and enumerated, not solved.

## Verdict on the experiment

The agent-run evidence supports the evaluation-asymmetry bet: review effort
concentrated on the substantial definition/game surface, where every
blocking finding arose, while recorded kernel checks handled the audited
proof endpoints. The definitions became stronger under attack rather than
softer, and the proof-bearing source passed the recorded technical release
audit at `2fe8354`. But the experiment's full success verdict is deliberately
withheld until a non-author human accepts the statements. Agent simulation
cannot report that event on the human's behalf; the real K4 outside review is
also still pending.

## T7 outcome amendment — 2026-07-10

The T7 descriptions above are a dated account of the earlier `hobliv` and
run-transfer boundary; they must not be used as the final statement of the
query-bounded result. The final proof interface is deliberately narrower
than an asymptotic cryptographic claim and stronger than that earlier
conditional theorem:

- for every adversary `A` carrying `qb : FrameQueryBounds A`, the live
  endpoint is the **secret-averaged** FRAME probability
  `frameWinProb mclose A ≤ (qb.total + 1)/|F|`;
- `T7_frame_query_bound_unconditional` and the composition wrapper
  `T7Certificate.ofQueryBounds` expose no `hobliv`, coupling, good-slice,
  bad-mass, or deferred-sampling hypothesis beyond `qb` (and the ambient
  finite-field/typeclass data);
- the original pointwise-in-secret `FrameDeferredSampling` certificate was
  not repaired or silently weakened: `frameDeferredSampling_refuted` remains
  the recorded counterexample. `FrameDeferredSamplingAvg` is the sound
  replacement because `frameGame` itself samples the secret uniformly.

At the statement/source level, this closes the finite, explicit
query-accounting target only. The optional
scaling wrapper indexes it by a security parameter but assumes the needed
per-parameter query certificates and ratio/field-growth negligibility facts.
The project does **not** classify adversaries as PPT, derive those
certificates from PPT, prove the scaling premises automatically, or reduce a
deployed hash function to the ideal random-oracle handlers used here.

**Technical-validation completion.** Proof-bearing source checkpoint
`2fe8354` was validated in a fresh clone. The pinned cache restore fetched
8,283 files, and the full root build succeeded on Lean 4.30.0 after 3,595
jobs. Explicit `#print axioms` output covered the full T7 route, both
`T7Certificate` constructors, both flat/refund end-to-end wrappers, both
`FrameAsymptotic` theorems, five `ElGamal.lean` endpoints, six
`ReceiptMac.lean` endpoints, and one `AuthenticatedFleet.lean` endpoint.
Every captured result used only a subset of `propext`, `Classical.choice`,
and `Quot.sound`. Project `rg` scans found no `sorry`, `admit`, or
`native_decide`, and no `axiom` outside `Zkpc/Assumptions.lean`;
`git diff --check` was clean.

The exact final PR head will be recorded externally after the
documentation/PDF-only release commit. That later SHA record is release
bookkeeping, not pending proof, build, scan, or axiom evidence. The remaining
acceptance blockers are the non-author human B1/B3/K1 sign-offs and a real,
not simulated, K4 outside-cryptographer review.
