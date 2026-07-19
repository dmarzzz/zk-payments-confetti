# tla/ — model checking

TLA+ models of the channel state machine, checked with TLC
(`tools/tla2tools.jar`). From the repo root: `make tla` (or
`java -XX:+UseParallelGC -cp tools/tla2tools.jar tlc2.TLC -config
tla/<config>.cfg tla/<model>.tla`).

These models are of the **old rev-11 object**. Their claim to fame: TLC
independently found the deepest definitional hole the adversarial review
also found (the gap-index close understatement) and verified the same
repair — see `research/raw/tla-findings.md` and
`research/processed/decisions.md`. A v2 model of the nullifier-chain
protocol (collision-challenge close, both timers, forfeit) is ROADMAP
obligation 9.

## v2 (Spec-v2, nullifier-chain machine) — added 2026-07-18

`ZkpcChainV2.tla` models the Spec-v2 clocked machine
(`lean/Zkpc/Chain/V2/State.lean`): one-deep unsigned frontier, four close
modes, mode-dependent exhibit sets, evidence-based challenge, both timers,
the challenge window. Vigilance is an explicit eager-challenge scheduling
assumption (see the `Tick` comment).

| Config | Switches | Result |
|---|---|---|
| `ZkpcChainV2.cfg` | all sound | **No error** (152,440 states): Conservation, NoOverspend, EvidenceIffUnsafe, BobFloor, ForfeitAll |
| `ZkpcChainV2SleepyBob.cfg` | `VIGILANT = FALSE` | BobFloor **fails** (stale close settles) — vigilance is an assumption, not a theorem |
| `ZkpcChainV2NoParentReveal.cfg` | `PARENT_REVEAL = FALSE` | BobFloor **fails** via the rollback fork (trace: `research/raw/tla-v2-noparentreveal-trace.txt`) — TLC independently reproduces the Q2(iii)/A2.iii rationale |
| `ZkpcChainV2NoCap.cfg` | `CAP_CHECK = FALSE` | NoOverspend **fails** — PROTOCOL.md's own broken mode |

`EvidenceIffUnsafe` is the model-checked twin of the Lean
`challenge_enabled_iff_unsafe`; two methods, one safe-close characterization.
