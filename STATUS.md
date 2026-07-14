# Status

Last updated: 2026-07-14 (post re-baseline, post PR #2 merge).

## The one-paragraph state

The protocol was re-baselined: `PROTOCOL.md` (post-quantum nullifier-chain
channel) superseded the old encrypted-running-total object (`Spec.md`
rev-11, now `research/raw/Spec.md`). Everything kernel-checked so far is
about the old object, except a seed formalization of the new one in
`lean/Zkpc/Chain/`. The proof campaign for the new protocol has not started; it
is blocked on freezing a Spec-v2 (five open definitional issues, G1–G5 —
see `ROADMAP.md` Phase 0).

## Kernel-checked (Lean, zero `sorry`, standard axioms only)

| About | What | Where |
|---|---|---|
| New protocol (seed) | Balance safety, both directions of collision-based stale-close detection, two-payment anonymity warm-up (advantage 0, idealized: no oracles, injective nullifiers, binding by construction) | `lean/Zkpc/Chain/` |
| Old object (historical) | Safety core T1–T3/T5; T4 spend unlinkability, advantage exactly 0 (session form); T6 fleet bound; secret-averaged finite-query T7, bound `(qb.total+1)/|F|`; calibration batteries; refund layer; ideal-model ZK bridges; end-to-end compositions | `lean/Zkpc/` (rest) |
| Methodology (negative result) | Pointwise-in-secret deferred-sampling certificates are refuted (`frameDeferredSampling_refuted`) | `lean/Zkpc/Games/FrameDeferred.lean` |

The "first machine-checked spend-unlinkability result for any
payment-channel or credit construction" line is a literature claim, not
independently verified.

## Attestation

- Full fresh-clone root builds recorded at `2fe8354` (3,595 jobs) and, for
  targets, `e2de071`.
- **Post-merge attestation (closes the debt):** CI ran the full root
  `lake build` green on clean runners on merged `main`, which imports all
  83 modules — including the 11 commits merged after `e2de071` that
  previously had no recorded build
  ([run 29364041425](https://github.com/dmarzzz/zk-payments-confetti/actions/runs/29364041425),
  on the `lean/` layout). Residual: per-endpoint `#print axioms` audits
  for those modules' theorems are still unrecorded (`make audit THM=...`);
  the CI guardrails do bound the axiom surface meanwhile. They also remain
  EC constructions the new protocol excludes.
- CI builds `main` on every push (guardrail greps + full `lake build`).

## Review state

- Old object: 11 adversarial agent gate rounds + statement/axiom/vacuity
  audits (distilled: `research/processed/decisions.md`). Independent
  *human* sign-off was never logged and is still pending.
- New protocol: pre-freeze. G1–G5 open; G2 (the withheld-countersignature
  wedge) is the critical path and is genuine design work, not
  transcription.

## Near-term

1. Spec-v2 gate rounds on G1–G5 (`ROADMAP.md` Phase 0; issues
   [#10–#14](https://github.com/dmarzzz/zk-payments-confetti/issues), G2 =
   [#11](https://github.com/dmarzzz/zk-payments-confetti/issues/11)).
2. Attestation build of merged `main` on a machine with resources
   ([#15](https://github.com/dmarzzz/zk-payments-confetti/issues/15)).
3. Then the ranked obligations (`ROADMAP.md` Phase 1+), starting with the
   safety core on the new transition machine.
