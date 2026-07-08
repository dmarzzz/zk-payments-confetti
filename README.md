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
   idealized ledger, with cryptography axiomatized in one file. The
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
  a named bad event). This is the hardest shape and where the largest open
  work sits. Partial template: `Zkpc/Games/T7.lean`.
- **Field and algebra lemmas** (the RLN line arithmetic). Template:
  `Zkpc/Games/RLN.lean`.

## Proofs that still need writing

`OPEN-PROOFS.md` is the worklist. It lists every proved theorem with its
Lean name and file, the five classes with their templates, and the open
obligations ranked by value. The short version of what is open:

- the unconditional form of the exculpability bound (T7), currently proved
  under a stated good-event hypothesis; discharging it is the hardest and
  highest-value open proof;
- the zero-knowledge bridge that carries the perfect unlinkability result
  from the idealized view to the real wire protocol;
- the remaining per-instance obligations for the refund variant;
- extending the refund safety layer from a single channel to the fleet;
- a small challenge-fires lemma that hardens the headline's non-vacuity by
  construction (a good first task).

If you are pointing a swarm at this, start from `OPEN-PROOFS.md`, read the
template file for the class you are taking, and read the relevant `Spec.md`
clause and `research_knowledge/gates.md` entry so you are proving against
the intended definition rather than around it.

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

The definition is frozen (`Spec.md`, revision 11, gate-signed). The core
theorems, the unlinkability headline, the fleet and exculpability bounds,
the calibration pair, and the refund safety layer are proved and
kernel-checked; the axiom audit shows only the three standard Lean axioms
(`research_knowledge/k2-axiom-audit.md`). The open obligations in
`OPEN-PROOFS.md` are the remaining work. Nothing in this repo is verified
until the kernel says so, and this README does not claim otherwise.

## Layout

| Path | What it is |
|---|---|
| `Spec.md` | The definition and the seven theorem statements. The trust surface. |
| `OPEN-PROOFS.md` | The proof worklist: proved theorems, the five classes with templates, open obligations. |
| `Zkpc/` | The Lean formalization (`lake build` kernel-checks it). |
| `paper/` | The systematization, the placement table, the theorem-to-file map, the ethresear.ch post form. |
| `RESEARCH.md` | The verified field report: six literature angles, ten open problems. |
| `BRIEF.md` | The executor contract: model boundary, theorem targets, milestones, gates. |
| `DELIVERY.md` | What got proved, in two paragraphs, plus the package manifest. |
| `research_knowledge/` | The gate record, the audits (K1 statement, K2 axiom, K3 vacuity, K4 external), the VCV-io prover-choice survey, the TLA+ findings, the experiment outcome. |
| `tla/` | The TLA+ model and its model-checking configs. |

## Provenance

Born from the payment-design question in the reputation-gated egress post
(reputation-gated-egress.vercel.app,
github.com/dmarzzz/reputation-gated-onion-egress) and a conversation about
whether zk payment channel literature should exist. The research sweep, the
brief, the definitions, and the proofs were produced agentically; the
definitions were reviewed adversarially, which is the entire design.
