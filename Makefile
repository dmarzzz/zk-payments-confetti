# Convenience targets. Everything the CI does, runnable locally.
# The full build wants a real machine; cap threads on a laptop.

LEAN_NUM_THREADS ?= 4

.PHONY: build guard audit tla

## Fetch mathlib oleans and kernel-check every theorem
build:
	lake exe cache get
	LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake build

## The CI guardrails: no sorry/admit/native_decide, axioms confined
guard:
	@! grep -rn --include='*.lean' -w 'sorry' Zkpc.lean Zkpc/ || (echo 'FAIL: sorry found' && exit 1)
	@! grep -rn --include='*.lean' -w 'axiom' Zkpc.lean Zkpc/ | grep -v '^Zkpc/Assumptions.lean:' || (echo 'FAIL: axiom outside Assumptions.lean' && exit 1)
	@! grep -rnE --include='*.lean' -w 'admit|native_decide' Zkpc.lean Zkpc/ || (echo 'FAIL: escape hatch found' && exit 1)
	@echo 'guardrails clean'

## Axiom audit of a theorem: make audit THM=Zkpc.Games.T4_flat_unlinkability
THM ?= Zkpc.Games.T4_flat_unlinkability
audit:
	@printf 'import Zkpc\n#print axioms $(THM)\n' > .audit.lean
	LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake env lean .audit.lean
	@rm -f .audit.lean

## Model-check a TLA+ config: make tla CFG=tla/ZkpcFlat.cfg MODEL=tla/ZkpcFlat.tla
CFG ?= tla/ZkpcFlat.cfg
MODEL ?= tla/ZkpcFlat.tla
tla:
	java -XX:+UseParallelGC -cp tools/tla2tools.jar tlc2.TLC -config $(CFG) $(MODEL)
