# zk-payments-confetti

The zk payment channel workstream: build the missing literature, then machine-check it.

## The object

A zk payment channel is a two-party channel where the payee cannot link any spend to any other spend or to the payer's identity, while keeping balance security and double-spend resistance. The shape exists in deployed and specified systems (BOLT/zkChannels, Anonymous Credit Tokens, ZK API Usage Credits) but has no dedicated literature: no systematization, no formal definition as a distinct object, and no machine-checked privacy proof for any instance. This repo exists to produce all three.

## Deliverables

1. **The paper.** A systematization whose contribution is the definition: algorithms (Setup, Open, Spend, Redeem, Close, Dispute) plus security games, placed precisely against BOLT/zkChannels, Chaumian ecash and credit tokens, and hub constructions. See `BRIEF.md`.
2. **The proofs.** Lean 4 formalization of the protocol layer: no-overspend, balance security both sides, spend unlinkability as an indistinguishability game, closure liveness. The smallest concrete target is the flat-ticket RLN credit protocol. A TLA+ model of the state machine comes first as cheap insurance. See `BRIEF.md` for the model boundary, milestones, and acceptance criteria.

## Status

Research done, proofs not started. Nothing in this repo is verified until `lake build` says so; the README will not claim otherwise.

## Layout

| Path | What it is |
|---|---|
| `RESEARCH.md` | Verified field report: six literature angles, adversarially checked against primary sources, ten open problems |
| `BRIEF.md` | The task brief: deliverables, theorem targets, prover choice, milestones, acceptance criteria |

## Provenance

`RESEARCH.md` was produced by a multi-agent research sweep (July 2026) in which every load-bearing claim was adversarially verified against primary sources; residual unverified claims are listed explicitly at the end of the report. Related: the [reputation-gated egress post](https://reputation-gated-egress.vercel.app) whose payment design question motivated this, and [dmarzzz/reputation-gated-onion-egress](https://github.com/dmarzzz/reputation-gated-onion-egress).
