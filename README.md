# zk-payments-confetti

> **Read this first.** This project is AI-driven end to end. The research
> sweeps, the definitions, the Lean proofs, the reviews, and most of the
> prose in this repository were produced by agents, and agent-produced
> research contains mistakes; treat every claim here that the Lean kernel
> has not checked as unverified. The repository is also a relay point for
> several people's work: the protocol design, review feedback, and proof
> campaigns from external collaborators arrive through the maintainer's
> agent and land under the maintainer's commits. Commit authorship
> (`dmarzzz`) therefore must not be read as credit for the ideas in this
> repository — in particular, the protocol design in `PROTOCOL.md` is an
> external contribution recorded verbatim, and the large proof campaign
> merged in PR #2 is `lalalune`'s.

Three things, in order: write the missing literature on zk payment
channels, formalize the protocol, and formally verify it in Lean 4.

zk payment channels are the object underneath BOLT/zkChannels, Anonymous
Credit Tokens, and the ZK API Usage Credits construction, yet they have no
dedicated literature: no systematization, no formal definition of the
object in its own right, and (before this project) no machine-checked
privacy proof for any instance.

## The protocol

**`PROTOCOL.md` is the design of record.** It defines a unidirectional
payment channel with per-request anonymity (the recipient cannot link two
payments to the same sender or channel), hidden balances, payment-channel
safety (the recipient never loses money earned; his worst case is
receiving the entire deposit), and unilateral liveness for the payer — in
a **post-quantum setting**: STARKs, hashes (Poseidon/Blake), and a
signature scheme whose verification is cheap inside a STARK. No elliptic
curves, no FHE, no recursive STARKs.

The design's single load-bearing mechanism is a nullifier chain
`N_{i+1} = H(N_i, c)` doing two jobs at once: each revealed nullifier is a
duplicate-detection tag, and each state's committed next-nullifier is a
precommitment that makes stale closes detectable **by collision** rather
than by the recipient producing a later state (which anonymity forbids).
Balance hiding uses commitments; payment validity uses a ZK proof that the
new state extends the on-chain genesis or a recipient-signed state, with
the signature verified inside the proof. The genesis is just a state, so
refund and close follow one uniform rule.

This design supersedes the repository's earlier object (`Spec.md`,
frozen revision 11), which reached the same privacy goals through a
re-randomizable additively homomorphic encrypted running total. The
redesign removes that primitive entirely: commitments plus
signature-verification-inside-the-proof structurally eliminate the
linkability surface the old design had to patch, and the machinery is
post-quantum, which the old instantiations (ElGamal, Schnorr) were not.

## Status after the re-baseline

The repository is mid-pivot from the old object to the new one. Honestly
stated:

- **Proved and kernel-checked, about the old object (historical, still
  valid as stated).** Everything `Spec.md` rev-11 scoped: the T1–T3/T5
  safety core, T4 spend unlinkability with advantage exactly zero (to our
  knowledge the first machine-checked spend-unlinkability result for any
  payment-channel or credit construction), the T6 fleet bound, the
  secret-averaged finite-query T7 endpoint
  `T7_frame_query_bound_unconditional` with bound `(qb.total + 1)/|F|`,
  the calibration batteries, the refund safety layer, ideal-model ZK
  bridges, and end-to-end compositions. These remain true theorems about
  the rev-11 object; they are no longer the project's target.
- **Proved and kernel-checked, about the new protocol (seed only).**
  `Zkpc/Chain/` formalizes the nullifier-chain channel's core: balance
  safety, both directions of collision-based stale-close detection, and a
  two-payment anonymity warm-up (advantage exactly zero, but in an
  idealized model far weaker than the old T4 apparatus: no oracle access,
  ideal injective nullifiers, commitment binding by construction). This is
  a starting point, not the result.
- **Refuted, load-bearing for anyone extending T7-style proofs.**
  Pointwise-in-secret deferred-sampling certificates are formally refuted
  (`frameDeferredSampling_refuted`); only secret-averaged certificates are
  sound. See `PROVING.md`.
- **Merged but not attested.** PR #2's final 11 commits (the
  ElGamalDDH/Schnorr/threshold/scheduler/serialization modules) have no
  recorded clean-machine build; the last attested checkpoints are
  `abb878f` (full root build) and `cfd1f74` (target build). Those modules
  are also elliptic-curve constructions, which the new protocol's
  post-quantum constraint excludes. Treat them as unverified historical
  material until an attestation build runs.
- **Not yet done at all.** The new protocol's real verification targets:
  see `OPEN-PROOFS.md`. Five definitional questions (G1–G5, recorded in
  `research_knowledge/gates.md`) must be resolved into a gate-frozen
  Spec-v2 before the proof campaign starts; the withheld-countersignature
  wedge (G2) is the critical-path item and is genuine protocol design, not
  transcription.

## The general classes of proofs

The formalization is a set of theorems falling into reusable shapes, each
with a worked template in the tree. Anyone extending the verification is
writing one of these shapes:

- **Safety invariants over a transition system** (induction on a
  reachability predicate). Templates: `Zkpc/Core/T1.lean` (old object),
  `Zkpc/Chain/State.lean` (new protocol).
- **Game-based perfect indistinguishability by random-oracle coupling**
  (reduce advantage to one per-challenge distributional equality, then a
  measure-preserving bijection on the oracle cache). Templates:
  `Zkpc/Games/{Coupling,FlatInstance,T4}.lean`; this apparatus is the
  intended engine for the new protocol's per-request anonymity theorem.
- **Constructive distinguishers and must-win adversaries** (build one
  explicit adversary, compute its advantage exactly). Template:
  `Zkpc/Games/Calibration.lean`.
- **Reductions, game hopping, and query charging** (bound advantage by a
  chain of hops with named bad events and charged oracle queries).
  Templates: `Zkpc/Games/T7.lean` with the FRAME campaign
  (`Zkpc/Games/Frame*.lean`); the secret-averaged deferred-sampling
  apparatus there is what the new protocol's non-frameability bound needs
  against a hash-grinding recipient.
- **Field and algebra lemmas.** Template: `Zkpc/Games/RLN.lean`
  (historical: the new protocol has no RLN layer).

## Separating definition review from proof checking

The whole method rests on an evaluation asymmetry. Agent-produced research
usually dies at review because checking it costs as much as producing it.
Machine-checked proofs invert that: if `lake build` passes with no `sorry`
and the axiom audit is clean, the proofs are correct, and the only thing
left for human judgment is whether the theorem statements and model say
what was meant. That judgment surface is concentrated in the definition
documents (`PROTOCOL.md` now, `Spec.md` historically) and the
security-game statements.

The old object's definitions were hardened by eleven rounds of adversarial
agent review (`research_knowledge/gates.md`, every counterexample
recorded), the games by more, plus statement, axiom, and vacuity audits.
Those exercises were agent-run; they strengthened the definitions but do
not substitute for independent human review, which remains pending. The
field has already shown why the distinction matters: A2L's privacy model
passed peer review in 2021 and was shown a year later to admit insecure
instantiations. Wrong definition, correct proof. The new protocol gets the
same treatment: G1–G5 are the round-0 findings of its gate series.

One unplanned result worth flagging for anyone assessing the method: a
TLA+ model checker independently found the deepest definitional hole in
the old object (a close-mechanism understatement attack) and verified the
same repair the adversarial review adopted. Two methods with no shared
machinery converged on the same defect and the same fix.

## Layout

| Path | What it is |
|---|---|
| `PROTOCOL.md` | **The design of record** (verbatim external contribution): the post-quantum nullifier-chain channel. Pre-freeze; open definitional issues G1–G5. |
| `OPEN-PROOFS.md` | The v2 worklist: definitional prerequisites, theorem obligations, ranked plan, and what the historical corpus contributes. |
| `Spec.md` | The superseded rev-11 definition (historical object A/B). Referent of the historical theorems; do not extend. |
| `Zkpc/Chain/` | The new protocol's Lean seed (state machine, collision mechanism, anonymity warm-up, executable refinement). |
| `Zkpc/` (rest) | The historical formalization plus the reusable game/coupling/query-charging apparatus. |
| `paper/` | The systematization. Currently scoped to the historical object; restructure pending. PDF removed pending rebuild. |
| `RESEARCH.md` | The verified field report: six literature angles, ten open problems. |
| `PROVING.md` | Contributor guide: model boundary, rules, proof-engineering conventions. |
| `BRIEF.md` / `TASKS.md` | The original executor contract and task log (historical, rev-11-scoped; kept as provenance). |
| `research_knowledge/` | Gate record, audits, T7 stack audit, TLA+ findings, experiment outcome. |
| `tla/` | The TLA+ model of the old object; a v2 model is on the worklist. |

## Provenance

Born from the payment-design question in the reputation-gated egress post
(reputation-gated-egress.vercel.app,
github.com/dmarzzz/reputation-gated-onion-egress) and a conversation about
whether zk payment channel literature should exist. The research sweep,
the brief, the definitions, and the proofs were produced agentically; the
definitions were reviewed adversarially by independent agents; the
protocol design and the largest proof campaign came from external
collaborators, as the disclaimer above states. Independent human review of
the definitions remains the standing acceptance gate.
