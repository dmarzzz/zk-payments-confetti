> **Superseded target (2026-07-14).** Everything below was delivered
> against `Spec.md` rev-11, now historical: the design of record is
> `PROTOCOL.md` (the post-quantum nullifier-chain channel). PR #2
> (lalalune, 100 commits) is merged; it completed the secret-averaged
> finite-query T7 endpoint, ideal-model ZK bridges, the compositions, and
> the nullifier-chain seed (`Zkpc/Chain/`), and kernel-refuted
> pointwise-in-secret T7 certificates. Attestation state: source
> validated at `2fe8354` (full root build) and `e2de071` (target build);
> the 11 commits merged after `e2de071` carry no build attestation (see
> `ROADMAP.md`, "Attestation debt"). `../paper/paper.pdf` was removed
> pending a rebuild from the current source. The "first machine-checked
> spend-unlinkability" line below is a literature claim that has not been
> independently verified. The live worklist is `ROADMAP.md`.

# Delivery — what got proved

Task K6 (TASKS.md): the delivery package. This note is the two-paragraph
"what got proved" summary plus the package manifest. The repository is public
at the URL below. **Any invitation, post, or other outbound message is left
to the operator** — this file is the artifact, not the send.

## The two paragraphs (for a reader who evaluates definitions, not proofs)

This repo defines the *zk payment channel* as a distinct cryptographic
object — a tuple of algorithms (Setup, Open, Spend, Redeem, Close,
Dispute) plus security games — and implements its security arguments in
Lean 4 over an idealized ledger and idealized cryptographic constructions.
The repaired final T7, composition, scaling, and refund-reference endpoints
were source-validated at checkpoint `2fe8354` by the clean-room and axiom
audit recorded below. The headline is **spend unlinkability proved with
advantage exactly 0** (`T4_flat_unlinkability`), the first machine-checked
spend-unlinkability result for any payment-channel or credit construction,
against a session-form game (a member's whole epoch session, not one spend) that an
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
triviality. The exact K2 capture for the final T7/composition/scaling chain
and the newly root-imported refund endpoints reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; the source scans and diff
hygiene checks are clean. This validates the Lean source at `2fe8354`. The
synchronized PDF was rebuilt from a clean TeX pass to 12 pages, with no
undefined references/citations or layout warnings, and every page was
visually inspected. The exact final artifact SHA is recorded in the PR and
issue closeout rather than self-referenced here.

The judgment surface is concentrated in `Spec.md` and the game definitions;
`Spec.md` is a substantial revision-controlled document, not a one-page
artifact. It was hardened by eleven rounds of adversarial **agent** review
(record in `gates.md`), an agent-run statement audit (K1),
a simulated external-cryptographer review (K4), and a TLA+ model-checker that
independently found the deepest definitional hole and verified the same
repair. Those reviews do not satisfy the required non-author human B1/B3/K1
sign-off, which remains pending. What is deliberately not claimed is
enumerated in the paper's honest-limits section and
`experiment-outcome.md`: T7 is a concrete finite-query theorem rather than
an unconditional PPT/negligibility result or deployed-hash reduction; the
refund base transition system is per-channel, with the failed-upgrade cascade
and finite-fleet aggregation proved separately; circuit verification is out
of scope, and the privacy is contingent (a slash that
runs the line algebra publishes the secret; multi-recipient is the named
open problem).

## Package manifest

| Artifact | Path |
|---|---|
| Definition (agent-reviewed rev-11; human acceptance pending) | `Spec.md` |
| Verified field report (the map) | `../processed/field-report.md` |
| Executor contract | `BRIEF.md` |
| Lean formalization (verification command below) | `Zkpc/`, `lakefile.lean`, `lean-toolchain` |
| Theorem-to-file map + reproducibility | paper §7 / `paper/` |
| Synchronized paper sources and visually checked 12-page PDF | `../paper/paper.pdf`, `../paper/paper.md`, `paper/paper.tex` |
| ethresear.ch post form | `../paper/post.md` |
| Claims ledger (no orphan claims) | `../paper/claims-ledger.md` |
| Agent gate record (11 B1 + 5 B3 rounds; human acceptance pending) | `gates.md` |
| K1 agent statement audit (human component pending) | `k1-statement-audit.md` |
| K2 axiom audit (final source endpoints captured at `2fe8354`) | `k2-axiom-audit.md` |
| K3 vacuity review | `k3-vacuity-review.md` |
| K4 simulated external-definition review (real outside review pending) | `k4-external-review.md` |
| K7 experiment outcome | `experiment-outcome.md` |
| TLA+ model + findings (incl. the convergence) | `tla/`, `tla-findings.md` |
| VCV-io gap survey (the prover-choice evidence) | `vcvio-gap.md` |

## Reproduce

```
git clone https://github.com/dmarzzz/zk-payments-confetti.git
cd zk-payments-confetti
lake exe cache get          # mathlib oleans
LEAN_NUM_THREADS=4 lake build   # kernel-checks every theorem
# axiom audit:
LEAN_NUM_THREADS=4 lake env lean <(printf 'import Zkpc\n#print axioms Zkpc.Games.T4_flat_unlinkability\n')
```

Toolchain pinned: `leanprover/lean4:v4.30.0`, mathlib v4.30.0, VCV-io
`8f5dc4f`. CI (`.github/workflows/ci.yml`) runs the build plus the
zero-escape-hatch guardrail on pushes to `main` and on pull requests; it does
not run for every push to an arbitrary branch.

## K5 clean-room rebuild — completed for the source checkpoint

Source checkpoint `2fe8354` was checked from a fresh checkout on the pinned
Lean 4.30.0 toolchain. `lake exe cache get` restored 8,283 cached files, and
the full root build completed all 3,595 jobs successfully. The accompanying
release audit reproduced the forbidden-token and project-axiom scans, ran
`git diff --check`, and captured `#print axioms` for the complete T7 chain,
the flat/refund composition wrappers, both conditional scaling theorems, and
the ElGamal/receipt-MAC/authenticated-fleet reference endpoints. Every
captured theorem used only a subset of `propext`, `Classical.choice`, and
`Quot.sound`.

This is exact evidence for the source checkpoint, not a self-referential SHA
claim about these later documentation edits. The regenerated 12-page PDF was
rendered and checked page by page; the exact final release head is recorded
in the PR and issue closeout after that commit exists.

## Operator to-do (not automated)

- The repository is already public. Decide whether and when to invite
  reviewers or publish the post/PDF; no outbound delivery is claimed here.
- Obtain and log the independent non-author human reviews required for B1,
  B3, and K1, and obtain a real outside K4 definition review. Agent and
  simulated-external exercises do not close those gates.
- Leave acceptance and merge of the final candidate to a repository
  maintainer after the human gates; no merge authority is claimed by this
  package.
- The synchronized PDF has been regenerated and every one of its 12 pages
  visually checked. Record the exact artifact commit in the PR/issues when
  publishing or merging.
