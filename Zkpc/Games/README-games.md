# Zkpc.Games — game layer status

This document separates the current game-layer boundary from the historical
rev-9 design record. Current source status is **subject to final release
validation**; no build SHA or completed release audit is claimed here.

## Current release surface

### T4: perfect unlinkability in the reference models

- `T4.lean` exposes `T4_flat_unlinkability`: every adversary has advantage
  exactly zero against the proof-free flat instance.
- `T4Fires.lean` supplies `challengeResp_flat_fires` and
  `challengeResp_flat_never_bot`, making the challenge path non-vacuous for
  positive budgets.
- `FullTicketInstance.lean` connects masked proof-bearing reference views to
  the proof-free game.
- `SigmaInstance.lean` exposes the interactive Sigma and ideal lazy-ROM
  Fiat--Shamir instances and their zero-loss reference-model bridges.
- `BInstances.lean` discharges the refund-instance batch, genesis/receipt,
  capability, rerandomization, and close-view obligations.

These theorems concern the specified ideal reference layers. A reduction for
a deployed hash function or concrete production proof system is not claimed.

### T7: completed secret-averaged query bound

For every

```text
A : F → OracleComp (frameSpec F M) (Evidence F)
qb : FrameQueryBounds A,
```

the public endpoint

```text
T7_frame_query_bound_unconditional mclose A qb
```

bounds `frameWinProb mclose A` by

```text
(qb.total + 1) / |F|,
qb.total = q_A + q_E + q_Id + q_Nf·q_sig + q_sig².
```

`frameGame` samples the secret uniformly, so this is a secret-averaged
probability. The endpoint has no residual coupling or counting hypotheses;
the adversary supplies the five structural certificates in
`FrameQueryBounds`.

The pointwise-in-secret `FrameDeferredSampling` certificate is intentionally
not used. `frameDeferredSampling_refuted` proves that its single
secret-independent-generator shape is unsatisfiable for a two-probe
adversary whenever `|F| > 5`. `FrameDeferredSamplingAvg` is the corrected
socket and matches the probability sampled by the game.

### T7 file map

- `Frame.lean` defines the five-oracle FRAME game and `frameWinProb`.
- `T7.lean` defines `FrameQueryBounds`, its aggregate `total`, the conditional
  endpoints, and the calibration games.
- `FrameDeferred.lean` contains the pointwise refutation, the averaged socket,
  and `T7_frame_query_bound_avg`.
- `FrameAudit.lean`, `FrameIdeal.lean`, and `FrameCoupling.lean` establish the
  audited real/ideal state relations and operation-level coupling substrate.
- `FrameGhost*.lean`, `FrameBadMass.lean`, and `FrameFactor.lean` provide the
  secret-free comparison model, budget kernels, and probability
  factorization.
- `FrameRealBad.lean`, `FrameRealBadTransfer.lean`, and
  `FrameRealBadStep.lean` define the deferred-slope execution and transport
  its bad-mass count to the audited real game.
- `FrameGoodSliceTape.lean` and `FrameGoodSliceTapeInduction.lean` implement
  the pending-slope tape argument and expose
  `frameGoodSliceTransfer_of_tape`.
- `FrameDSCountInduction.lean` implements the adaptive seeded-shadow count
  and exposes `dsBadMassLe_of_queryBounds`.
- `FrameTransfer.lean` combines good-slice and real-bad route B into a
  `FrameDeferredSamplingAvg` certificate.
- `FrameComplete.lean` exposes `frameDeferredSamplingAvg_holds` and the final
  `T7_frame_query_bound_unconditional` theorem.
- `Zkpc/Composition/EndToEnd.lean` consumes that theorem through
  `T7Certificate.ofQueryBounds` and the T7-residual-free flat/refund
  composition endpoints. Those endpoints still require the operational
  trace and completion premises in their signatures.

The load-bearing final chain is:

```text
frameGoodSliceTransfer_of_tape
dsBadMassLe_of_queryBounds
  → frameRealBadMassLe_of_dsCount
  → frameDeferredSamplingAvg_holds
  → T7_frame_query_bound_unconditional
  → T7Certificate.ofQueryBounds.
```

### Release-validation boundary

File presence and focused elaboration are not a release audit. The final
claim must be checked from a clean checkout with a cold dependency fetch,
full root build, repository token scan, headline axiom printouts, and diff
check. Until then, describe the endpoint as implemented in source and subject
to final release validation.

The base endpoint is finite and query-bounded. It does not itself formalize a
security-parameter family, PPT adversary class, asymptotic negligibility, or
a concrete deployed-hash assumption. It is the finite mechanized counterpart
to, not a proof of, `Spec.md`'s literal PPT/negligibility T7 clause.

`FrameAsymptotic.lean` is a conditional lift, not a PPT reduction. It assumes
per-parameter `FrameQueryBounds` and either negligibility of the displayed
query/field-size ratio, or an explicit polynomial numerator bound together
with negligible inverse field size. It supplies no PPT classifier and no
PPT-to-query-bound theorem. Its release status is covered by the same pending
clean-build and axiom-audit boundary above.

---

## Historical record: rev-9 game definitions

This section is retained only as design history. It predates the T4 instance
suite and the completed T7 stack. Its game definitions remain relevant, but
its proof forecast and obligation status are superseded by the current
section above.

### Historical UNLINK surface

The rev-9 UNLINK game introduced a session challenge:

- phase 0 chooses genesis inputs;
- before the challenge the adversary may spend, retry, serve, close, and
  advance the epoch;
- the challenge is a nonempty adversary-selected vector, checked for
  freshness and capability on both candidates before the hidden branch is
  used; and
- the post-challenge continuation produces a pure guess.

The historical per-instance obligations were the proof-bearing ZK bridge,
batch totality, refund genesis/receipt absorption, and close-view
simulatability. The current flat, Sigma/FS, full-ticket, and refund instance
files provide the corresponding reference-model endpoints.

### Historical FRAME surface

The rev-9 FRAME game fixed the current public interface:

- the adversary receives `cm = H_id(k)` at game start;
- operations are `spend`, legacy `close`, `nfAt`, `roA`, `roX`, `roNf`,
  `roE`, and `roId`;
- all oracle calls share lazy-ROM caches; and
- the win predicate is `Slashes k ev`.

Direct `roA`, `roE`, and `roId` probes can test the secret; `roNf` probes can
hit honest slopes; and multiple honest signals can collide. Those are exactly
the terms now charged by `FrameQueryBounds.total`. The nonzero-digest handler
rule excludes the degenerate `x = 0, y = k` honest signal.

### Historical correction to the original proof forecast

The original forecast expected a pointwise handler comparison. The
two-`roId` counterexample showed that this certificate shape cannot hold.
The completed proof instead reasons over the uniform secret already sampled
by `frameGame`, defers pinned slopes with a tape, and counts adaptive roots in
a seeded shadow execution. Old references to open good-slice or
`DSBadMassLe` lanes are historical work notes, not current obligations.
