# zk-payments-confetti

Two things at once: writing the missing literature on zk payment channels,
and formally verifying it in Lean 4.

zk payment channels are the object underneath BOLT/zkChannels, Anonymous
Credit Tokens, and the ZK API Usage Credits construction, yet they have no
dedicated literature. There is no systematization, no formal definition of
the object in its own right, and no machine-checked privacy proof for any
instance. This repo builds both halves of what is missing:

1. **The literature.** A systematization whose contribution is a formal
   definition of the object as a tuple of algorithms (Setup, Open, Spend,
   Redeem, Close, Dispute) plus security games, placed against BOLT and
   zkChannels, Chaumian ecash and keyed-verification credit tokens (ACT,
   ARC), and the hub-privacy line (A2L+, BlindHub, Accio). The definition
   is the contribution; the rest of the paper defends it. This lives in
   `Spec.md` (the precise definition and the seven theorem statements) and
   `paper/` (the systematization at paper altitude).

2. **The verification.** A Lean 4 formalization of that definition over an
   idealized ledger, with cryptography represented by explicit ideal
   reference constructions. The
   headline is spend unlinkability proved with advantage exactly zero, to
   our knowledge the first machine-checked spend-unlinkability result for
   any payment-channel or credit construction. Alongside it: no-overspend,
   balance security on both sides, closure liveness, a fleet
   priced-divergence bound, an exculpability bound, and the refund variant
   with a built-in definitional test. The Lean lives in `Zkpc/`.

## The general classes of proofs

The formalization is not a single monolithic proof. It is a set of
theorems that fall into five reusable shapes, each with a worked template
in the tree. Anyone extending the verification is writing one of these
shapes:

- **Safety invariants over a transition system** (induction on a
  reachability predicate). Covers no-overspend, both balance-security
  theorems, closure liveness, the fleet bound, and the refund safety
  layer. Template: `Zkpc/Core/T1.lean`.
- **Game-based perfect indistinguishability by random-oracle coupling**
  (reduce advantage to one per-challenge distributional equality, then a
  measure-preserving bijection on the oracle cache). Covers the
  unlinkability headline and the refund re-randomized variant. Template:
  `Zkpc/Games/{Coupling,FlatInstance,T4}.lean`.
- **Constructive distinguishers and must-win adversaries** (build one
  explicit adversary, compute its advantage exactly). Covers the
  calibration battery and the exculpability breaks. Template:
  `Zkpc/Games/Calibration.lean`.
- **Reductions and game hopping** (bound advantage by a chain of hops with
  a named bad event). This is the hardest shape. Template:
  `Zkpc/Games/T7.lean`, with the FRAME campaign files
  (`Zkpc/Games/Frame{Factor,Assembly,Transfer}.lean`) as the worked
  large-scale example.
- **Field and algebra lemmas** (the RLN line arithmetic). Template:
  `Zkpc/Games/RLN.lean`.

## Proof status and remaining scope

`OPEN-PROOFS.md` is now a proof inventory and extension worklist. The main
change in this release is the completed, corrected T7 route. For every
adversary `A` carrying `qb : FrameQueryBounds A`, the public theorem
`T7_frame_query_bound_unconditional` bounds the secret-averaged FRAME win
probability by

```text
(qb.total + 1) / |F|,
where qb.total = q_A + q_E + q_Id + q_Nf·q_sig + q_sig².
```

This endpoint has no residual coupling or counting hypotheses. The proof
chain is split across the adaptive good-slice induction
(`frameGoodSliceTransfer_of_tape` in
`Zkpc/Games/FrameGoodSliceTapeInduction.lean`), the deferred bad-mass count
(`dsBadMassLe_of_queryBounds` in
`Zkpc/Games/FrameDSCountInduction.lean`), their assembly in
`Zkpc/Games/FrameComplete.lean`, and the scheme-facing constructor
`T7Certificate.ofQueryBounds` in `Zkpc/Composition/EndToEnd.lean`.

The older pointwise-in-secret deferred-sampling certificate is not part of
this claim. It is formally refuted by `frameDeferredSampling_refuted` in
`Zkpc/Games/FrameDeferred.lean`; the security game itself samples the secret,
so the corrected theorem works at exactly that secret-averaged level.

The source-level release claim above is **subject to final release
validation**: a cold dependency fetch, clean full build, forbidden-token
scan, endpoint axiom printout, and diff check. The formalization also does
not claim an asymptotic PPT/negligibility theorem or a reduction for a
deployed hash function. The Fiat--Shamir results are for the stated ideal
lazy-ROM reference model; concrete-hash, production refund cryptography, and
adaptive multi-session threshold/network reductions remain separate research
extensions.

If you are extending the project, start from `OPEN-PROOFS.md`, the template
for the relevant proof class, the corresponding `Spec.md` clause, and the
gate record in `research_knowledge/gates.md`.

## Why the definitions can be trusted before the proofs are read

The whole design rests on an evaluation asymmetry. Agent-produced research
usually dies at review because checking it costs as much as producing it.
Machine-checked proofs invert that: if `lake build` passes with no `sorry`
and the axiom audit is clean, the proofs are correct, and the only thing
left for human judgment is whether the theorem statements say what was
meant. The trust surface shrinks from everything to one page, `Spec.md`.

That page was hardened accordingly. It went through eleven rounds of
adversarial definition review (the full record, with every counterexample,
is `research_knowledge/gates.md`), the security games through three more,
an independent statement audit, an axiom audit, a vacuity review, and a
simulated external-cryptographer review that strengthened the unlinkability
game rather than narrowing it. The field has already shown the one failure
mode that survives this setup: A2L's privacy model passed peer review in
2021 and was shown a year later to admit insecure instantiations. Wrong
definition, correct proof. That is precisely where the review effort was
concentrated here.

One unplanned result is worth flagging for anyone assessing the method: a
TLA+ model checker independently found the deepest definitional hole (a
close-mechanism understatement attack) and verified the same repair the
adversarial review adopted. Two methods with no shared machinery converged
on the same defect and the same fix.

## Status

The definition is frozen (`Spec.md`, revision 11, gate-signed). The source
tree contains the core safety theorems, perfect unlinkability and its
challenge-fires witness, fleet and refund results, ideal-model ZK bridges,
executable refinements, network reference constructions, the nullifier-chain
instantiation, and the completed secret-averaged T7 endpoint described above.
`Zkpc/Composition/EndToEnd.lean` consumes T7 through
`T7Certificate.ofQueryBounds` and exposes premise-free flat and refund
end-to-end constructors.

The precise T7 claim is finite and query-bounded: for every `A` with
`qb : FrameQueryBounds A`, `frameWinProb` is at most
`(qb.total + 1) / |F|`. It is not a pointwise-in-secret statement, an
asymptotic PPT theorem, or a deployed-cryptography claim. Release-wide build
and axiom status remain subject to final release validation; nothing should
be described as release-verified until that validation completes.

## Layout

| Path | What it is |
|---|---|
| `Spec.md` | The definition and the seven theorem statements. The trust surface. |
| `OPEN-PROOFS.md` | Proof inventory, completed theorem chains, reusable templates, research extensions, and release gates. |
| `Zkpc/` | The Lean formalization (`lake build` kernel-checks it). |
| `Zkpc/Chain/` | Instantiation C: the nullifier-chain channel (state machine, collision bound, anonymity, executable refinement). |
| `paper/` | The systematization, the placement table, the theorem-to-file map, the ethresear.ch post form. |
| `RESEARCH.md` | The verified field report: six literature angles, ten open problems. |
| `BRIEF.md` | The original executor contract: model boundary, theorem targets, milestones, gates (kept as provenance; `Spec.md` cites it). |
| `PROVING.md` | One-page contributor guide: model boundary, rules, how to add a theorem. |
| `research_knowledge/` | The gate record, the audits (K1 statement, K2 axiom, K3 vacuity, K4 external, T7 stack), the VCV-io prover-choice survey, the TLA+ findings, the experiment outcome. |
| `tla/` | The TLA+ model and its model-checking configs. |

## Provenance

Born from the payment-design question in the reputation-gated egress post
(reputation-gated-egress.vercel.app,
github.com/dmarzzz/reputation-gated-onion-egress) and a conversation about
whether zk payment channel literature should exist. The research sweep, the
brief, the definitions, and the proofs were produced agentically; the
definitions were reviewed adversarially, which is the entire design.
