# zk-payments-confetti

An experiment in autoresearch. The question: how much of a missing cryptography literature can agents build when the human in the loop can evaluate the definitions but not the proofs?

## Why this domain is the testbed

zk payment channels, the shape underneath BOLT/zkChannels, Anonymous Credit Tokens, and ZK API Usage Credits, have no dedicated literature: no systematization, no formal definition as a distinct object, no machine-checked privacy proof for any instance. That gap is the opportunity, but the reason it suits autoresearch is the evaluation asymmetry. Agent-produced research usually dies at review, because checking it costs as much as producing it. Machine-checked proofs invert the economics: if `lake build` passes with zero `sorry`, the proofs are right, and the only thing left for human judgment is whether the theorem statements say what we meant. The trust surface shrinks from everything to a page of definitions.

The field has already demonstrated the one failure mode that survives this setup: A2L's privacy model passed S&P peer review in 2021, and a year later two counterexamples showed it admitted completely insecure instantiations. Wrong definitions, correctly proved. That is exactly where the human eyes stay in this experiment, and nowhere else.

## The experiment

Three phases, each with more riding on the agents than the last.

1. **The sweep** (done): a 13-agent research swarm across six literature angles, every load-bearing claim adversarially verified against primary sources. Output is `RESEARCH.md`, with the residual unverified claims listed rather than laundered.
2. **The definition and the paper**: a systematization whose contribution is the formal definition of the object (Setup, Open, Spend, Redeem, Close, Dispute, plus security games), placed against BOLT/zkChannels, Chaumian ecash and credit tokens, and hub constructions.
3. **The proofs**: Lean 4, protocol layer over an idealized ledger, crypto axiomatized in one file. No-overspend, balance security both sides, spend unlinkability as an indistinguishability game, closure liveness. The concrete target is the flat-ticket RLN credit protocol, arguably the smallest machine-checkable unlinkability target in the literature. A TLA+ model of the state machine runs first as cheap insurance.

`BRIEF.md` is the executor's contract: model boundary, theorem targets, milestones, acceptance criteria, and the two human review gates.

## What success and failure look like

Success is narrow and checkable: a definition the community can attack, and the first machine-checked unlinkability proof for any channel or credit construction, with a human having read only `Spec.md`. Failure has known shapes and gets logged, not hidden: definitions drifting toward what is provable instead of what is true, proofs of trivialities dressed as theorems, or the Lean bet losing to the mature frameworks (SSProve is the documented fallback). Any of those outcomes is a result about autoresearch, which is the point.

## Status

Sweep done, brief written, proofs not started. Nothing in this repo is verified until the kernel says so, and this README will not claim otherwise.

## Layout

| Path | What it is |
|---|---|
| `RESEARCH.md` | Verified field report: six literature angles, ten open problems |
| `BRIEF.md` | The executor's contract: deliverables, theorem targets, prover choice, milestones, gates |

## Provenance

Born from the payment-design question in the [reputation-gated egress post](https://reputation-gated-egress.vercel.app) ([dmarzzz/reputation-gated-onion-egress](https://github.com/dmarzzz/reputation-gated-onion-egress)) and a conversation about whether zk payment channel literature should exist. The sweep, the brief, and this README were produced agentically; the definitions will be reviewed by humans, which is the entire design.
