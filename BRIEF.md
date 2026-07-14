> **Historical (rev-11 scoped).** This contract governed the original
> campaign against `Spec.md` rev-11; kept as provenance. The design of
> record is now `PROTOCOL.md`. If a v2 brief is written, the T4
> calibration requirement re-targets to the new must-fail/must-pass pair
> (non-hiding balances and clear signatures must fail; the real scheme
> must pass), and the refund-variant workstream disappears: the new
> protocol has no refund variant, genesis-close is the refund.

# Task brief: zk payment channels, the literature and the proofs

The executor's contract for the autoresearch experiment described in README.md. The executor is an agent (or agent swarm); the human reviews theorem statements and security-game definitions at the marked gates, and nothing else; the audience for the outputs is the applied-zk research community. Where this brief says "prove," it means kernel-checked, not argued.

## Context

The ZK API Usage Credits construction (ethresear.ch/t/24104) lets a client deposit once and spend anonymously against one provider, with double-spend detection via nullifiers. The construction is, structurally, a zk payment channel bound to one recipient (the channel mapping is stated in the thread itself, and RESEARCH.md verifies it against BOLT), and zk payment channels have essentially no dedicated literature. This brief scopes the two artifacts that would create that literature: a systematization paper and a machine-checked formalization.

Companion input: `RESEARCH.md` (field report from a verified research sweep across BOLT/zkChannels, hub privacy, Chaumian ecash, state-channel capital efficiency, and the formal-verification landscape). Read it first; do not re-derive the map.

## Deliverable 1: the paper (SoK plus definition)

A short systematization with one new object in it.

1. **Define the object.** "zk payment channel": a two-party channel where the payee learns nothing about payer identity across spends (unlinkability within the channel population) while retaining balance security and double-spend resistance. Give the definition as a tuple of algorithms (Setup, Open, Spend, Redeem, Close, Dispute) plus security games. This is the contribution; the rest of the paper exists to defend it.
2. **Place it against the modern lineage, not just BOLT.** BOLT (2017) named the object and then the line went dormant, zkChannels stayed DRAFT, libzkchannels was archived 2023. So BOLT is the historical anchor and, via its §1.4 abort attacks, the sharpest threat model, but it is not the construction to model on. The living toolkit is newer: keyed-verification credit tokens (ACT, ARC, both 2025 IETF drafts, BBS-style) are the modern "anonymous balance at one verifier"; the hub-privacy line (A2L+ CCS 2022, BlindHub S&P 2023, Accio CCS 2023) is where the privacy definitions were modernized and stress-tested; adaptor signatures got formal foundations in 2024. The definition is scheme-agnostic security games; the placement table compares against this modern set with BOLT as origin. State precisely which property each prior system lacks.
3. **Honest limits section.** Recipient-boundness, capital lockup per counterparty, funding-graph leakage at open (batch-open and shielded funding as mitigations), and what a multi-recipient generalization would require (this is the open problem, name it, do not pretend to solve it).

Format: 8 to 12 pages, ethresear.ch-postable long form first, arXiv-able second. Every claim about prior work cites the primary source.

## Deliverable 2: the Lean formalization

Lean 4 + mathlib, building with `lake build` clean.

**Model boundary, stated up front in the repo README:** we formalize the protocol layer over an idealized ledger and idealized cryptography. The SNARK, the hash, and the signature scheme enter as axioms/assumptions in one file (`Assumptions.lean`), each with a comment naming the standard property it encodes (proof-system knowledge soundness, zk simulation, PRF security, EUF-CMA). We are not verifying circuits. Anyone claiming otherwise about this repo is misreading it.

**Theorems, in priority order:**

- T1 **No overspend.** Sum of accepted spends on a channel never exceeds the deposit. (Safety, provable early, forces the state model to be right.)
- T2 **Payee balance security.** An honest payee closing a channel obtains exactly the sum of redeemed spends, against an arbitrary payer.
- T3 **Payer balance security.** An honest payer never loses more than the sum of spends it authorized; the remainder is refundable at close.
- T4 **Spend unlinkability.** Game-based: adversarial payee, two candidate payers with open channels, cannot distinguish which one produced a challenge spend, under the zk simulation assumption. This is the theorem nobody has machine-checked for any channel construction; it is the headline. **The adversarial payee must have an abort/evict oracle** (BOLT §1.4: a paid counterparty can shrink the anonymity set by inducing aborts and link a member by aborting mid-sequence). A game without it proves a guarantee the real gateway walks around, which is the A2L failure shape. **Calibration requirement:** the game, instantiated on the refund-bearing variant (below), must *fail* against the original static encrypted-refund-total design and *pass* against the re-randomized fix (the omarespejel linkability finding and its patch). A game that cannot tell those two apart is wrong, and this is the built-in test that it is not.
- T5 **Closure liveness.** Under the idealized ledger with a timeout, an honest party can always settle.
- T6 **Priced divergence (fleet).** Across N gateways sharing the spent set with reconciliation lag L and per-epoch rate limit r, the value a member can extract by double-spending before detection is bounded by a function of (L, r) that stays below the deposit D. This is the theorem that justifies "the async window is priced by the deposit"; it is open problem 1 in RESEARCH.md and it is the fleet's actual security argument.
- T7 **Exculpability under collusion (fleet).** Up to N−1 gateways pooling their transcripts cannot fabricate a valid double-spend proof against a member that did not double-spend, because forging a second point on the RLN line requires the secret. Open problem 5; it is what makes the automatic slash safe.

**Prover choice, stated honestly.** The verified literature sweep (RESEARCH.md, formal verification section) says: Lightning's machine-checked record lives in UC pen-and-paper (Kiayias-Litos), Why3 (fund safety), and TLA+ (state-machine checking); no machine-checked unlinkability proof exists for any channel or credit construction in any prover; and the mature crypto-game frameworks are SSProve (Rocq) and CryptHOL (Isabelle), with Lean's game-based layer young. We stay in Lean anyway, for three stated reasons: the request is to build Lean literature, not to reuse Isabelle's; agent-assisted proving has the deepest tooling and training coverage in Lean 4 + mathlib; and VCV-io (eprint 2026/899, github.com/Verified-zkEVM/VCV-io) plus ArkLib are already verifying SNARK components in Lean, so the ecosystem is arriving from below. The hedge is M0.5 below: a TLA+ model first, days of work, catches the state-machine bugs before any Lean line is written. If T4 stalls in Lean, the documented fallback is SSProve, and the paper does not wait for it.

**Two instantiations, in order.** Formalize the general channel object once, then instantiate the theorems twice.
1. *Flat-ticket RLN credit protocol* (deposit D, flat price C, solvency inequality (i+1)·C ≤ D, per-index nullifier, slash on reuse): no refunds, no revocation, one inequality. The smallest machine-checkable unlinkability target in the literature, and the protocol the egress fleet runs. T1-T4, plus T6-T7 which only exist here.
2. *Refund-bearing variant* (server-signed refund tickets, re-randomized encrypted running total): this is the variant the upstream use case needs (LLM cost variance, the 100x-overhead argument from the public thread), and refunds are where the construction's only known privacy bug lived. Answering the thread means covering this, not just flat-ticket. It carries the T4 calibration test above.

Complete flat-ticket first; the refund variant is what makes the paper answer the thread rather than a simplification of it.

**Engineering notes for the executor:**

- Build the game framework on VCV-io rather than from scratch; what VCV-io lacks (adversary classes, advantage bookkeeping for indistinguishability games), add minimally. Keep additions under a thousand lines; resist generality.
- Process lesson from A2L (S&P 2021 privacy model broken by CCS 2022 counterexamples): the definitions are the risk surface, not the proofs. The M0 human review gate reviews the security *games* line by line; a wrong game proved correctly is the failure mode that has already happened to this field once.
- `sorry` count must be zero at every milestone boundary. Axioms live only in `Assumptions.lean`; CI greps for both.
- Statements are the trust surface. Each theorem gets a docstring restating it in English; the human review step is those docstrings plus the definitions, nothing else needs human eyes.

M0's `Spec.md` should formalize *this* protocol, not a reinvented one: its prose sources are the wire-protocol and application sections of the egress post (reputation-gated-egress.vercel.app) and the application section of RESEARCH.md. Toolchain is pinned in `lean-toolchain` and `lakefile`; CI runs `lake build` on a fixed mathlib + VCV-io revision.

## Milestones

- M0: repo scaffold + `Spec.md` with all seven theorem statements in English. **Human review gate here** (this is the gate that could be handed to an external reviewer who did not write it).
- M0.5: TLA+ model of the protocol state machine (open, spend, nullifier check, reconcile, slash, close), model-checked at small scope. Cheap insurance; the Lightning TLA+ work shows the method scales past our simpler protocol.
- M1: state model + T1 (flat-ticket).
- M2: T2, T3.
- M3: T4 (the game framework lands here), flat-ticket instantiation.
- M4: T6, T7 (the fleet theorems, spent-set model lands here).
- M5: refund-bearing variant + T4 with the E(R) calibration test passing (fails static, passes re-randomized).
- M6: paper draft integrating the formalization; the definition, the placement table, the honest-limits section, and the theorems as its spine.

## Acceptance

`lake build` clean, zero `sorry`, axioms confined and named, T1-T4 and T6-T7 proved on flat-ticket, T4 proved on the refund variant with the calibration test passing, statements reviewed at M0 by at least one human who did not write them. T5 is stretch. The paper stands alone without the proofs; the proofs make it citable. Completing this answers the upstream thread: the literature exists, it is in Lean, and the headline theorem is a first.
