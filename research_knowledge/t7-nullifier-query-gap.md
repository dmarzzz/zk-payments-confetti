# T7 nullifier-query accounting correction

The concrete FRAME handler publishes `x`, `y = k + a*x`, and
`nf = H_nf(a)` for every honest signal. The earlier query numerator counted
direct candidate-secret probes to `H_a`, `H_e`, and `H_id`, but not direct
`H_nf` queries or the number of honest line points exposed.

Given one signal, an adversary that finds a preimage `a` of its nullifier
computes `k = y - a*x`. With `q_sig` independently sampled honest slopes and
`q_Nf` preimage probes, a conservative multi-target first-hit charge is
`q_Nf*q_sig/|F|`. Separately, two honest slopes may collide; two distinct line
points with a shared slope recover `k`, contributing a birthday term bounded
conservatively by `q_sig^2/|F|`.

Here `q_sig` is a conservative name for every operation that materializes an
honest slope: `spend`, legacy `close`, and `nfAt`. The last case matters even
though it does not immediately expose `y`: the same index can later be spent,
and the real shared cache must remain coupled to the ideal per-index cache.

`Zkpc.Games.frameWinProb_slopeReveal_eq_one` kernel-checks the limiting
calibration `H_nf(a)=a`: one signal then frames with probability one. This is
not the real random oracle, but proves slope hiding is essential and cannot be
replaced by direct-secret query accounting.

The corrected numerator is

`q_A + q_E + q_Id + q_Nf*q_sig + q_sig^2 + 1`,

where `+1` is blind guessing. Tighter collision constants are possible later;
the current expression is deliberately conservative and compositional.

## Status addendum — 2026-07-10 (reconciliation pass)

The numerator above is no longer prose accounting; it is carried
end-to-end by kernel-checked arithmetic:

- `Zkpc.Games.frameQueryCharge_eq` (`Zkpc/Games/T7.lean`) proves the five
  charge terms — `q_A/|F| + q_E/|F| + q_Id/|F| + q_Nf*q_sig/|F| +
  q_sig^2/|F|` — sum to exactly `qb.total/|F|`, with the multi-target and
  birthday terms in the shape this note derived.
- The pointwise per-`k` certificate socket was **refuted**:
  `frameDeferredSampling_refuted` (`Zkpc/Games/FrameDeferred.lean`;
  gates.md Round 4, 2026-07-09) shows a two-probe adversary admits no
  `FrameDeferredSampling` certificate over any field with more than five
  elements — a single secret-independent generator cannot pay two disjoint
  slash slices each forced to near-`1`. The corrected socket is the
  `k`-averaged `FrameDeferredSamplingAvg` (same file), consumed by
  `T7_frame_query_bound_avg` to yield the complete corrected bound
  `(qb.total + 1)/|F|`, and by both assembly routes:
  route A (`Zkpc/Games/FrameAssembly.lean`,
  `frameDeferredSamplingAvg_of_transfers` /
  `T7_frame_query_bound_of_transfers`) and route B
  (`Zkpc/Games/FrameTransfer.lean`,
  `T7_frame_query_bound_of_goodSlice_and_realBad`).
- The eager-read subtlety this note flagged — `nfAt` materializing a slope
  that a later `spend` on the same index consumes — turned out to be
  exactly the obstruction that killed every per-state per-step real/ghost
  coupling. Conditioned on a fixed answer transcript the consumed slopes
  are the deterministic `k`-roots `(y_i - k)/x_i`, correlated through the
  one deferred secret, while ghost slopes are independent uniforms; the
  counterexample recorded in `Zkpc/Games/FrameTransfer.lean` (and
  OPEN-PROOFS §1) shows route A's `FrameBadMassTransfer` is **not
  per-transcript dominated** (real leakage mass exactly `3/|F|` against
  ghost mass `3/|F| - 2/|F|^2` on a generic two-signal transcript with one
  `H_nf` probe). The architectural resolution is consumption-time slope
  deferral: the two-stage plan in OPEN-PROOFS §1 first exchanges the real
  handler for a deferred-slope handler (identical until `FrameLeakBad`)
  whose `spend` draws the hidden slope at consumption time, after which
  `y = k + a*x` is fresh-uniform by the `mulRight` bijection and the
  eager-read obstruction disappears. The atomic form of that exchange is
  already kernel-checked: `initial_nfAt_spend_deferredSecret_ghost_eq`
  (`Zkpc/Games/FrameFactor.lean`) commutes the slope draw from its `nfAt`
  sampling point to the consuming `spend`, distributionally, under the
  deferred secret.
- The ghost-side halves of the numerator are discharged theorems:
  `ghostSlopeBadBounds_holds` closes the hidden-slope preimage
  (`q_Nf*q_sig`) and collision (`q_sig^2`) masses outright for every
  query-bounded adversary, and `ghostFrameRun_leakBad_prob_le` bounds the
  full ghost bad mass by `qb.total/|F|` (both in
  `Zkpc/Games/FrameBadMass.lean`). The master factorization
  `frame_real_le_ghost_plus_bad` (`Zkpc/Games/FrameFactor.lean`) reduces
  the real experiment to these plus the transfers.
- What remains open is exactly two run-level Props (lane claims in
  OPEN-PROOFS §1, both in progress): `FrameGoodSliceTransfer` and
  `FrameRealBadMassLe`. Everything else between the query budgets defined
  here and the unconditional Spec.md §7 T7 endpoint is kernel-checked.

## Closure reconciliation — 2026-07-10

The preceding status addendum is preserved as the history of the two-lane
repair. The final source-level endpoint discharges both lanes and has the
following exact scope:

```text
qb : FrameQueryBounds A
-----------------------------------------------
frameWinProb mclose A ≤ (qb.total + 1) / |F|
```

Here the probability is averaged over the uniformly sampled secret in
`frameGame`; it is not a pointwise-in-`k` assertion. The route is
`frameGoodSliceTransfer_of_tape` plus `dsBadMassLe_of_queryBounds`, through
`frameRealBadMassLe_of_dsCount` and
`frameDeferredSamplingAvg_of_goodSlice_and_realBad`, to
`frameDeferredSamplingAvg_holds` and
`T7_frame_query_bound_unconditional`. The scheme-level wrapper is
`T7Certificate.ofQueryBounds`. Neither public endpoint takes a residual
transfer, coupling, bad-mass, or deferred-sampling premise.

The pointwise socket is still false: `frameDeferredSampling_refuted` is
retained, and no claim here supersedes that refutation. Averaging is the
semantic repair, not a proof convenience.

The displayed result is concrete finite-field/query accounting. The finite
chain itself does not classify PPT machines or instantiate the ideal random
oracles with a deployed hash. `FrameAsymptotic.lean` separately supplies two
security-parameter-indexed conditional lifts—one assumes negligibility of
the explicit query/field-size ratio, and its corollary assumes a polynomial
numerator bound plus negligible inverse field size—but neither derives those
premises from a PPT/runtime model.

**Post-reconciliation evidence status (2026-07-10):** the release audit is
complete at source checkpoint `abb878f`: a fresh Lean 4.30.0 root build
completed 3,595 jobs, the final T7/composition/scaling axiom capture used
only Lean's standard axioms, and the source scans were clean. This later
evidence supersedes the pending-status snapshot above without changing the
recorded statement boundary.
