# Proof inventory and remaining extensions

This file records the current proof boundary. `Spec.md` remains the trust
surface: contributions prove statements against those definitions, and a
statement failure is recorded in `research_knowledge/gates.md` rather than
hidden by weakening the theorem.

The gate record contains independent-agent review rounds. It does not record
the non-author human approval required by `BRIEF.md`; B1, B3, and K1 remain
acceptance gates even though the agent review rounds reached sign-off.

The implementation inventory below is **subject to final release
validation**. The release gate is a cold dependency fetch and clean full
build, followed by the forbidden-token scan, endpoint axiom printouts, and
`git diff --check`. This document does not claim a release SHA or a completed
release audit before those checks finish.

## Contribution rules

- The toolchain is pinned by the repository. Use `lake exe cache get`, then
  `lake build` from a clean checkout for release validation.
- Proof source must contain no unfinished proof terms or new trusted
  declarations. The CI policy is the authoritative token scan.
- Every theorem should have an English docstring that restates its contract
  and cites the corresponding `Spec.md` clause.
- Headline endpoints must be checked with `#print axioms`; the intended trust
  set is Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## T7: completed secret-averaged query bound

For every adversary

```text
A : F → OracleComp (frameSpec F M) (Evidence F)
```

carrying `qb : FrameQueryBounds A`, the public endpoint is

```text
T7_frame_query_bound_unconditional mclose A qb:
  frameWinProb mclose A ≤ (qb.total + 1) / |F|
```

where

```text
qb.total = qb.qA + qb.qE + qb.qId
         + qb.qNf · qb.qSig + qb.qSig · qb.qSig.
```

This is the probability of the actual `frameGame`, which samples the secret
uniformly. It is therefore a secret-averaged statement. It has no residual
coupling or counting hypotheses beyond the five structural query-bound
certificates carried by `FrameQueryBounds`.

This finite inequality is the mechanized counterpart to `Spec.md` T7. It is
not, by itself, a proof of the literal “every PPT adversary has negligible
probability” clause; that requires the runtime/query and scaling facts
described under research extensions.

The final theorem chain is:

| Role | Theorem or definition | File |
|---|---|---|
| Pointwise boundary | `frameDeferredSampling_refuted` | `Zkpc/Games/FrameDeferred.lean` |
| Correct averaged socket | `FrameDeferredSamplingAvg`, `T7_frame_query_bound_avg` | `Zkpc/Games/FrameDeferred.lean` |
| Adaptive good-slice induction | `frameGoodSliceTransfer_of_tape` | `Zkpc/Games/FrameGoodSliceTapeInduction.lean` |
| Adaptive deferred bad-mass count | `dsBadMassLe_of_queryBounds` | `Zkpc/Games/FrameDSCountInduction.lean` |
| Real/deferred transport | `frameRealBadMassLe_of_dsCount` | `Zkpc/Games/FrameRealBadStep.lean` |
| Averaged route-B assembly | `frameDeferredSamplingAvg_of_goodSlice_and_realBad` | `Zkpc/Games/FrameTransfer.lean` |
| Public game endpoint | `frameDeferredSamplingAvg_holds`, `T7_frame_query_bound_unconditional` | `Zkpc/Games/FrameComplete.lean` |
| Scheme-facing certificate | `T7Certificate.ofQueryBounds` | `Zkpc/Composition/EndToEnd.lean` |
| T7-residual-free composition wrappers | `flat_endToEnd_unconditional`, `refund_endToEnd_unconditional` | `Zkpc/Composition/EndToEnd.lean` |

The formerly proposed `FrameDeferredSampling` certificate quantified
pointwise in the secret while requiring one secret-independent generator.
That shape is formally refuted by a two-probe adversary whenever `|F| > 5`.
It is kept as a negative result and is not used by the final theorem. The
refutation does not refute `frameGame` or the secret-averaged `Spec.md`
claim.

The composition wrappers are “unconditional” only with respect to the T7
transfer/counting certificate: they construct it from `FrameQueryBounds`.
They still take the operational trace, honest-key/time, and completion
premises shown in their theorem signatures.

## Current source inventory

The following table is an implementation map, not a substitute for the final
release validation described above.

| Area | Main endpoints | Files |
|---|---|---|
| T1 no-overspend and honest exculpability | `T1_no_overspend`, `honest_never_slashed` | `Zkpc/Core/T1.lean` |
| T2 payee balance | `T2_paid_exact`, `T2_collectable`, `T2_settles_exactly` | `Zkpc/Core/T2.lean` |
| T3 payer balance | `T3_payer_balance_security` | `Zkpc/Core/T3.lean` |
| T5 closure liveness | `T5_payer_close_liveness` | `Zkpc/Core/T5.lean` |
| T6 priced divergence | `T6_priced_divergence`, `T6_slash_within_L` | `Zkpc/Fleet/T6.lean` |
| T4 perfect unlinkability | `T4_flat_unlinkability`, `T4_sigmaFlat_unlinkability`, `T4_fsFlat_unlinkability` | `Zkpc/Games/{T4,SigmaInstance}.lean` |
| T4 non-vacuity | `challengeResp_flat_fires` | `Zkpc/Games/T4Fires.lean` |
| T7 query-bounded FRAME | `T7_frame_query_bound_unconditional` | `Zkpc/Games/FrameComplete.lean` |
| Calibration and must-win checks | `unlinkAdvantage_staticDistinguisher_eq_half`, `frameWinProb_YK_eq_one` | `Zkpc/Games/{Calibration,T7}.lean` |
| RLN algebra | `rln_recover_k`, `rln_single_point_hiding`, `rln_evidence_sound` | `Zkpc/Games/RLN.lean` |
| Ideal Sigma/FS reference layer | simulation, extraction, and collision-bound endpoints | `Zkpc/Crypto/{LinearSigma,FSRom}.lean` |
| Conditional T7 scaling | query/field-size negligibility transfers (no PPT classifier) | `Zkpc/Games/FrameAsymptotic.lean` |
| Refund crypto reference layer | masked-cipher hiding; ElGamal algebra; fixed-pair, deterministic one-query, and independent-key-list MAC bounds | `Zkpc/Crypto/{MaskedEncryption,ElGamal,ReceiptMac}.lean`, `Zkpc/Refund/AuthenticatedFleet.lean` |
| Refund and fleet safety | finite-fleet accounting, cascade, and recovery endpoints | `Zkpc/Refund/{Safety,Fleet,Cascade}.lean`, `Zkpc/Fleet/Recovery.lean` |
| Executable refinement | flat, refund, fleet, and network refinement endpoints | `Zkpc/{Core,Refund,Fleet,Network}/` |
| Portable network reference layer | accounting, credential, and threshold issuance endpoints | `Zkpc/Network/` |
| Nullifier-chain instantiation | safety, collision, anonymity, and refinement endpoints | `Zkpc/Chain/` |
| Synchronized composition | flat/refund operational and T4/T7 bundles | `Zkpc/Composition/EndToEnd.lean` |

## The five reusable proof shapes

1. **Safety invariant over a labelled transition system.** Prove an
   invariant at `init`, preserve it across each transition, and read the
   endpoint from reachability. Template: `Zkpc/Core/T1.lean`.
2. **Perfect indistinguishability by random-oracle coupling.** Reduce the
   game to a distributional equality and use a cache bijection or fresh
   uniform sample. Templates: `Zkpc/Games/Coupling.lean` and
   `Zkpc/Games/FlatInstance.lean`.
3. **Constructive distinguisher or must-win adversary.** Define the adversary
   and compute its advantage. Templates: `Zkpc/Games/Calibration.lean` and
   the calibration section of `Zkpc/Games/T7.lean`.
4. **Reduction / identical-until-bad / union bound.** Couple executions until
   a named event and charge every event to an explicit budget. The completed
   FRAME stack under `Zkpc/Games/Frame*.lean` is the large example.
5. **Field and finite-support algebra.** Use field identities and finite-list
   root counting. Template: `Zkpc/Games/RLN.lean`.

## Research extensions not claimed by this release

These are useful next projects, but they are not hidden hypotheses of the
finite query-bounded T7 theorem above.

- **Deployed Fiat--Shamir reduction.** Relate a concrete hash implementation
  and adversarial query interface to the ideal lazy-ROM reference layer,
  including its knowledge-soundness/forking loss.
- **Production refund cryptography.** The tree now includes additive ElGamal
  correctness/rerandomization algebra and narrow affine-MAC one-query bounds,
  but still needs a DDH/IND-CPA reduction and shared-key, stateful multi-query
  receipt authentication. The independent-key list bound is not the Spec-B
  receipt-signature game.
- **Adaptive multi-session network security.** Lift the local threshold
  issuance and recipient-view results to an adaptive executable network game
  and a production threshold-signature unforgeability reduction.
- **PPT complexity layer.** `Zkpc/Games/FrameAsymptotic.lean` indexes the
  finite result by a security parameter and applies the existing
  negligibility calculus, but it is a conditional scaling wrapper only. Its
  conclusions assume per-parameter
  query certificates and either negligibility of the explicit ratio, or a
  polynomial numerator bound plus negligible inverse field size. It neither
  classifies adversaries as PPT nor derives query certificates from PPT; a
  runtime model and that derivation remain research extensions.
- **Deployed-system composition.** Connect concrete cryptographic
  implementations and schedulers to the synchronized reference traces.

## Release validation still required

Before calling the branch release-verified:

1. fetch dependencies from a clean checkout;
2. run a clean full build of the root target;
3. run the repository's forbidden-token scan over proof source;
4. inspect `#print axioms` for every headline endpoint, including the final
   T7 chain, the flat/refund T7-residual-free wrappers, and the conditional
   scaling endpoints;
5. run `git diff --check` and reconcile all theorem tables and generated
   paper artifacts;
6. record the validated commit only after all checks succeed.

## Historical note: how the final T7 route changed

Earlier 2026-07-09/10 checkpoint notes described two open transfer Props and
later one open deferred-counting lemma. Those were live work notes, not final
claims. The pointwise deferred certificate was refuted; the proof moved to
the secret-averaged socket. The landed route uses a pending-slope tape
induction for the good slice and a seeded adaptive shadow induction for the
deferred bad mass, then transports that count through the real/deferred
coupling. The authoritative current endpoints are the theorem chain listed
above; old lane ownership and “in progress” narratives are historical only.

## Definition and rationale references

- `Spec.md`: object, games, theorem statements, and modeling choices.
- `research_knowledge/gates.md`: adversarial definition-review record.
- `Zkpc/Games/README-games.md`: current game-layer map and rev-9 history.
- `paper/`: systematization and theorem-to-file map.
