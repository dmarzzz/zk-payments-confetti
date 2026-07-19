# Status

Last updated: 2026-07-18 (post designer sign-off on the Q1–Q5 defaults,
post Spec-v2 draft round 1).

## The one-paragraph state

The protocol was re-baselined: `PROTOCOL.md` (post-quantum nullifier-chain
channel) superseded the old encrypted-running-total object (`Spec.md`
rev-11, now `research/raw/Spec.md`). On 2026-07-18 the protocol designer
accepted all five proposed defaults (A1–A5, resolving G1–G4 and G6), which
unblocked Phase 0: `Spec-v2.md` (draft, round 1) transcribes
`PROTOCOL.md` + A1–A5, survived one adversarial round (two reviews; five
findings folded in, one new gate finding G7 on genesis anchoring), and the
**Phase 1 safety core on the new machine is now kernel-checked**
(`lean/Zkpc/Chain/V2/`), with the seed machine's three disclosed fiats
discharged. The spec is not yet frozen: G7 and the two [R1] rescopes
(anonymity-until-close, mode-dependent exhibit sets) need designer
sign-off, and 3–6 more gate rounds are expected.

## Kernel-checked (Lean, zero `sorry`, standard axioms only)

| About | What | Where |
|---|---|---|
| New protocol (Spec-v2 draft, safety core) | Clocked machine with explicit challenge window and evidence-based challenge guard (the seed's three fiats discharged); conservation; no-overspend; cooperative-settlement exactness and the safe-close payout floor; the safe-close characterization (genesis iff nothing sent, signed tip iff no ghost, the ghost itself, fresh tip extension); vigilant-Bob challenge-enabledness iff the close is unsafe; unconditional safe-exit liveness for Alice including the withheld-countersignature wedge, at a price of one δ (the G2 repair, conditioned on Spec-v2 §3 frontier injectivity) | `lean/Zkpc/Chain/V2/` |
| New protocol (collision bound) | The lazy-chain birthday bound, proven: the first `n` links collide with probability at most `n(n-1)/(2\|N\|)` (counting form + VCV-io sampling form), discharging the docstring-only `n²/\|N\|` claim | `lean/Zkpc/Chain/V2/CollisionBound.lean` |
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
- New protocol: `Spec-v2.md` draft, round 1 complete (designer accepted
  A1–A5; two adversarial reviews run 2026-07-18, findings F-R1-1..5 folded
  in — see `Spec-v2.md` §11). Open for designer sign-off: G7 (genesis
  anchoring via a channel Merkle tree), the anonymity-until-close rescope,
  and the mode-dependent exhibit sets. Not yet frozen.

## Near-term

1. Designer sign-off on `Spec-v2.md` §11 (G7 + the two [R1] rescopes),
   then remaining gate rounds to freeze.
2. Obligation 2: 2(a) the collision bound is DONE 2026-07-18
   (`CollisionBound.lean`, tighter `n(n-1)/(2|N|)`); residual 2(b–c):
   commitment binding as an assumption rather than by construction, and
   threading the probabilistic event through the machine-level statements.
   Then obligations 3–4 (non-frameability; per-request anonymity,
   unlinkable-until-close scope) per `ROADMAP.md` Phase 1.
3. DONE 2026-07-18: TLA+ v2 model (`tla/ZkpcChainV2.tla`): main config
   green over 152k states; sleeping-Bob, no-parent-reveal, and no-cap
   configs fail on exactly the intended invariant (TLC independently
   reproduces the Q2(iii) rollback fork). Next: obligations 3-4
   (non-frameability; anonymity, unlinkable-until-close scope).
