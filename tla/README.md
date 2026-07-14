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
