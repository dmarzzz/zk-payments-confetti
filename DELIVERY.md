# Delivery — what got proved

Task K6 (TASKS.md): the delivery package. This note is the two-paragraph
"what got proved" summary plus the package manifest. **The
repo-visibility decision (flip to public / invite) and any outbound
message are left to the operator** — this file is the artifact, not the
send.

## The two paragraphs (for a reader who evaluates definitions, not proofs)

This repo defines the *zk payment channel* as a distinct cryptographic
object — a tuple of algorithms (Setup, Open, Spend, Redeem, Close,
Dispute) plus security games — and machine-checks its security in Lean 4
over an idealized ledger and idealized cryptographic constructions. The
headline: **spend unlinkability is proved with advantage exactly 0**
(`T4_flat_unlinkability`), the first machine-checked spend-unlinkability
result for any payment-channel or credit construction, against a
session-form game (a member's whole epoch session, not one spend) that an
adversarial payee plays with abort/evict power. Alongside it: no-overspend
(T1), balance security both sides (T2/T3), closure liveness (T5), the
fleet's priced-divergence bound (T6), and a concrete query-bounded
exculpability bound (T7): for every adversary carrying `FrameQueryBounds`,
the secret-averaged FRAME win probability is at most
`(qb.total + 1)/|F|`, with no residual coupling or counting hypothesis.
The refund variant has a **built-in definitional test** — the same game
gives advantage 1/2 against the known-
broken static-encrypted-refund design and 0 against the re-randomized fix,
which is the evidence the game captures something real rather than a
triviality. Every theorem depends on only the three standard Lean axioms
(K2 audit); nothing is `sorry`'d.

The trust surface is one page — `Spec.md` — because the kernel checked the
rest. That page was hardened by eleven rounds of adversarial definition
review (record in `research_knowledge/gates.md`), an independent statement
audit (K1), a simulated external-cryptographer review that *strengthened*
the unlinkability game rather than narrowing it (K4), and a TLA+
model-checker that independently found the deepest definitional hole and
verified the same repair the review adopted. What is deliberately not
claimed is enumerated in the paper's honest-limits section and
`experiment-outcome.md`: T7 is a concrete finite-query theorem rather than
a formal asymptotic PPT/negligibility result or deployed-hash reduction;
the refund layer is single-channel; circuit verification is out of scope,
and the privacy is contingent (a slash that
runs the line algebra publishes the secret; multi-recipient is the named
open problem).

## Package manifest

| Artifact | Path |
|---|---|
| Definition (the trust surface, frozen rev-11) | `Spec.md` |
| Verified field report (the map) | `RESEARCH.md` |
| Executor contract | `BRIEF.md` |
| Lean formalization (verification command below) | `Zkpc/`, `lakefile.lean`, `lean-toolchain` |
| Theorem-to-file map + reproducibility | paper §7 / `paper/` |
| The paper (SoK + definition), 12 pages | `paper/paper.pdf`, `paper/paper.md`, `paper/paper.tex` |
| ethresear.ch post form | `paper/post.md` |
| Claims ledger (no orphan claims) | `paper/claims-ledger.md` |
| Gate record (11 B1 + 4 B3 rounds) | `research_knowledge/gates.md` |
| K1 statement audit | `research_knowledge/k1-statement-audit.md` |
| K2 axiom audit | `research_knowledge/k2-axiom-audit.md` |
| K3 vacuity review | `research_knowledge/k3-vacuity-review.md` |
| K4 external definition review | `research_knowledge/k4-external-review.md` |
| K7 experiment outcome | `research_knowledge/experiment-outcome.md` |
| TLA+ model + findings (incl. the convergence) | `tla/`, `research_knowledge/tla-findings.md` |
| VCV-io gap survey (the prover-choice evidence) | `research_knowledge/vcvio-gap.md` |

## Reproduce

```
git clone <repo> && cd zk-payments-confetti
lake exe cache get          # mathlib oleans
LEAN_NUM_THREADS=4 lake build   # kernel-checks every theorem
# axiom audit:
LEAN_NUM_THREADS=4 lake env lean <(printf 'import Zkpc\n#print axioms Zkpc.Games.T4_flat_unlinkability\n')
```

Toolchain pinned: `leanprover/lean4:v4.30.0`, mathlib v4.30.0, VCV-io
`8f5dc4f`. CI (`.github/workflows/ci.yml`) runs the build plus the
zero-escape-hatch guardrail on every push.

## K5 clean-room rebuild — pending refresh for this PR

The repository records an earlier clean-room build of the pre-T7-closure
tree. It is not evidence for the current PR head. Before delivery, rerun
`lake exe cache get`, the full build, the escape-hatch greps, and the axiom
prints from a fresh clone of the exact merge candidate, then record that
commit and output here. No current-PR clean-room result is claimed yet.

## Operator to-do (not automated)

- Decide repo visibility (currently private) and whether to invite / post.
  (README + `OPEN-PROOFS.md` are already written for an external proof
  swarm; the Shaw handoff summary was sent to the Hermes agent.)
- The synchronized paper sources now render to a 12-page PDF; all pages were
  visually checked for clipping, overlap, broken tables, and unreadable text.
