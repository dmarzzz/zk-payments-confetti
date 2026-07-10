# End-to-end formalization status

Current source checkpoint for the implementation PR. All release-wide claims
in this document are **subject to final release validation**; no validated
build commit or completed release audit is claimed here yet.

## Release theorem boundary

The corrected T7 route is complete at the source level. For every adversary

```text
A : F → OracleComp (frameSpec F M) (Evidence F)
```

with `qb : FrameQueryBounds A`, the public theorem
`T7_frame_query_bound_unconditional` states

```text
frameWinProb mclose A ≤ (qb.total + 1) / |F|,
```

where

```text
qb.total = q_A + q_E + q_Id + q_Nf·q_sig + q_sig².
```

The probability is averaged over the uniformly sampled FRAME secret because
that is the experiment defined by `frameGame`. There are no residual
coupling or counting hypotheses at this public endpoint; the five structural
query certificates are packaged in `FrameQueryBounds`.

The older `FrameDeferredSampling` certificate attempted a stronger
pointwise-in-secret comparison against one secret-independent generator.
`frameDeferredSampling_refuted` formally refutes that certificate shape for
a two-probe adversary whenever `|F| > 5`. The final result instead uses
`FrameDeferredSamplingAvg`, which matches the secret-averaged game and
preserves the same finite query bound.

## Final T7 theorem chain

1. `frameGoodSliceTransfer_of_tape` proves the adaptive good-slice transfer
   in `Zkpc/Games/FrameGoodSliceTapeInduction.lean`.
2. `dsBadMassLe_of_queryBounds` proves the deferred-slope leakage count from
   the five query certificates in
   `Zkpc/Games/FrameDSCountInduction.lean`.
3. `frameRealBadMassLe_of_dsCount` transports the deferred count to the real
   audited run in `Zkpc/Games/FrameRealBadStep.lean`.
4. `frameDeferredSamplingAvg_of_goodSlice_and_realBad` combines the two
   route-B obligations in `Zkpc/Games/FrameTransfer.lean`.
5. `frameDeferredSamplingAvg_holds` and
   `T7_frame_query_bound_unconditional` expose the no-residual endpoint in
   `Zkpc/Games/FrameComplete.lean`.
6. `T7Certificate.ofQueryBounds` packages it for schemes in
   `Zkpc/Composition/EndToEnd.lean`.

The root import graph includes `Games.FrameComplete`; the composition module
imports it rather than rebuilding the proof through a user-supplied
certificate.

## End-to-end composition

`Zkpc/Composition/EndToEnd.lean` defines synchronized labelled products for
the flat Core/Fleet/Network path and the Refund/Network path. It provides:

- one trace and projections for each component machine;
- proof-carrying admission, reconciliation, and settlement links;
- cross-lane accounting equalities at completion;
- operational guarantee records for flat and refund traces;
- `T7Certificate.ofQueryBounds` for the final FRAME theorem; and
- `flat_endToEnd_unconditional` and `refund_endToEnd_unconditional`, which
  combine the trace-derived operational guarantees, the relevant T4 theorem,
  and query-bounded T7 without a residual T7 premise.

These are synchronized reference-model theorems. They do not silently add a
concrete-hash reduction, deployed public-key encryption, a production
threshold signature, or an asymptotic adversary model.

## Implemented reference-model surface

The branch contains source for the following components:

- T1/T2/T3/T5 core safety, exact settlement, payer floor, and close
  liveness;
- T6 fleet priced divergence and reconciliation timing;
- T4 perfect unlinkability, its non-vacuity witness, proof-free and
  proof-bearing reference instances, and ideal Sigma/lazy-ROM FS bridges;
- the corrected secret-averaged, query-bounded T7 theorem above;
- refund safety, finite-fleet aggregation, upgrade cascades, and recovery;
- executable refinement for flat, refund, fleet, and network operations;
- masked-encryption privacy, ElGamal algebra, and narrow independent-key
  receipt-MAC reference bounds;
- portable network accounting, credential admission, and finite threshold
  issuance reference constructions;
- synchronized flat/refund/network composition; and
- the nullifier-chain channel safety, collision, anonymity, and refinement
  results.

This is an implementation inventory. The final clean build and trust audit
remain pending release gates rather than facts inferred from file presence.

## Exact non-claims

The current formal result is deliberately narrower than a deployed security
claim:

- no pointwise-in-secret deferred-sampling certificate is claimed;
- a security-parameter-indexed conditional negligibility lift is present,
  but no PPT/runtime classifier, PPT-to-query-bound theorem, automatic
  field-growth derivation, or deployed-primitive reduction is provided;
- no reduction from a deployed hash function to the ideal lazy-ROM model is
  claimed;
- no production public-key refund-encryption or multi-query authentication
  reduction is claimed; and
- no production threshold-signature or adaptive multi-session network
  security reduction is claimed.

The finite T7 theorem remains substantive: it quantifies over every adaptive
adversary term that carries the declared structural query bounds and charges
all direct-secret, slope-preimage, and signal-collision opportunities in
`qb.total`.

## Final release validation

The release is not validated until all of the following are recorded against
one immutable commit:

1. cold dependency fetch in a fresh checkout;
2. clean full build of the root target;
3. repository forbidden-token/source-placeholder audit;
4. `#print axioms` review for every headline theorem, including
   `T7_frame_query_bound_unconditional`, `T7Certificate.ofQueryBounds`, and
   both unconditional composition endpoints;
5. `git diff --check` and generated-artifact consistency;
6. reconciliation of `Spec.md`, README/status files, paper theorem tables,
   and assumption registries; and
7. the required human statement review recorded separately from automated
   proof validation.

Until those gates finish, use “implemented in source, subject to final
release validation,” not “release-verified.”

## Research roadmap beyond this release

These items extend the reference model and are not residual hypotheses of the
completed T7 route:

1. a concrete-hash Fiat--Shamir reduction with adversarial query semantics;
2. deployed rerandomizable refund encryption and multi-query authentication;
3. adaptive multi-session threshold issuance/network unlinkability and
   production threshold-signature unforgeability;
4. complete the conditional scaling wrapper with an explicit PPT/runtime
   model and PPT-to-query/field-growth derivations; and
5. refinement from deployed contracts, cryptographic implementations, and
   schedulers to the synchronized reference traces.

## Historical checkpoint note

Earlier 2026-07-09/10 versions of this file described T7 as two open transfer
Props, then as one open `DSBadMassLe` candidate. Those descriptions were
work-in-progress lane notes. They are superseded by the theorem chain above.
The pointwise refutation remains a permanent negative result; the open-lane
narratives and ownership claims are historical only.
