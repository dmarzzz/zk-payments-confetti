# Convenience targets. Everything the CI does, runnable locally.
# The Lean project lives in lean/; these targets handle the cd for you.
# The full build wants a real machine; cap threads on a laptop.

LEAN_NUM_THREADS ?= 4
TLA_JAR = tools/tla2tools.jar

.PHONY: build guard audit tla

## Fetch mathlib oleans and kernel-check every theorem
build:
	cd lean && lake exe cache get
	cd lean && LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake build

## The CI guardrails: no sorry/admit/native_decide, axioms confined
guard:
	@! grep -rn --include='*.lean' -w 'sorry' lean/Zkpc.lean lean/Zkpc/ || (echo 'FAIL: sorry found' && exit 1)
	@! grep -rn --include='*.lean' -w 'axiom' lean/Zkpc.lean lean/Zkpc/ | grep -v '^lean/Zkpc/Assumptions.lean:' || (echo 'FAIL: axiom outside Assumptions.lean' && exit 1)
	@! grep -rnE --include='*.lean' -w 'admit|native_decide' lean/Zkpc.lean lean/Zkpc/ || (echo 'FAIL: escape hatch found' && exit 1)
	@echo 'guardrails clean'

## Axiom audit of a theorem: make audit THM=Zkpc.Games.T4_flat_unlinkability
THM ?= Zkpc.Games.T4_flat_unlinkability
audit:
	@printf 'import Zkpc\n#print axioms $(THM)\n' > lean/.audit.lean
	cd lean && LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake env lean .audit.lean
	@rm -f lean/.audit.lean

## Model-check a TLA+ config: make tla CFG=tla/ZkpcFlat.cfg MODEL=tla/ZkpcFlat.tla
## (downloads the TLC jar on first use; it is not tracked in git)
CFG ?= tla/ZkpcFlat.cfg
MODEL ?= tla/ZkpcFlat.tla
$(TLA_JAR):
	mkdir -p tools
	curl -fsSL -o $(TLA_JAR) https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
tla: $(TLA_JAR)
	java -XX:+UseParallelGC -cp $(TLA_JAR) tlc2.TLC -config $(CFG) $(MODEL)
