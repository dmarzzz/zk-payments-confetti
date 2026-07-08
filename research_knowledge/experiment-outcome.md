# K7 — Experiment outcome

Task K7 (TASKS.md): log the autoresearch experiment's outcome against the
success and failure shapes README.md named up front. This is the result,
not a status report: the point of the repo was never only the theorems,
it was the question *how much of a missing cryptography literature can
agents build when the human can evaluate the definitions but not the
proofs?* — and what the failure looks like when it comes.

## The bet, restated

README's success condition: **a definition the community can attack, and
the first machine-checked unlinkability proof for any channel/credit
construction, with a human having read only `Spec.md`.** The named failure
shapes, to be *logged not hidden*: (1) definitions drifting toward what is
*provable* instead of what is *true*; (2) proofs of trivialities dressed
as theorems; (3) the Lean bet losing to the mature frameworks (SSProve the
documented fallback).

## What happened, against each shape

### Success condition: MET (with one honestly-scoped deferral)

- **`T4_flat_unlinkability`: spend-unlinkability advantage exactly 0**,
  kernel-checked, dependent only on the three standard Lean axioms (K2).
  To our knowledge this is the first machine-checked spend-unlinkability
  result for any payment-channel or credit construction — the gap
  RESEARCH.md documented ("no machine-checked proof of payment
  unlinkability exists for any channel construction"). It is a session-form
  game (the member's whole epoch session, not one spend), which is
  *stronger* than the single-spend version the internal review started
  with.
- **The definition is attackable, and was attacked.** `Spec.md` went
  through eleven B1 gate rounds and the T4/T7 games through three B3
  rounds, each by a fresh reviewer with no stake in the prior text, plus
  an independent statement audit (K1) and a simulated external
  cryptographer (K4). The full counterexample record is `gates.md`. A
  community reviewer inherits a definition that has already survived that.
- **The rest of the suite** landed too: T1 (no-overspend), T2/T3 (balance
  security both sides), T5 (closure liveness), T6 (priced divergence,
  fleet), T7 (exculpability bound), the refund variant (T1-B/T3-B/
  conservation), and the calibration pair — all kernel-checked, all
  axiom-clean.
- **The one deferral, logged:** T7's bound is proved as "≤ 1/|F| under the
  RO-oblivious good event `hobliv`." The remaining half — bounding the
  `q/|F|` random-oracle-hit terms that discharge `hobliv` for an unbounded
  interactive adversary — is the "estimated-hard 20%" the VCV-io survey
  (`vcvio-gap.md`) flagged, and it is scoped behind a stated hypothesis
  with a GATE-NOTE, not smuggled into an axiom. This is exactly the
  "logged, not hidden" discipline the README demanded.

### Failure shape 1 — definitions drifting toward provability: DID NOT HAPPEN, and we can show why

This is A2L's failure and the one the experiment most feared. It did not
occur, and the reason is instructive: **the human gate (simulated by
independent adversarial reviewers, per the operator's instruction) caught
every attempt at drift before it reached a proof.** The load-bearing
episodes:

- **The gap-index understatement (round 5).** The close mechanism as first
  written let a payer skip index 0, spend at 1..m, and close claiming
  index 0 unused — recovering the full deposit after consuming service.
  This *would have been provable* against the weaker close definition; the
  gate refused it and forced MC20 (verifiable spend count) — the true
  definition, harder to prove, which the proof layer then had to (and did)
  meet.
- **The unsatisfiable UNLINK game (round 1).** The first T4 game was too
  *strong* — every scheme, including the sound ones, lost it (three
  post-challenge distinguishers). A less careful process would have
  quietly weakened the game at proof time until T4 went through, and the
  weakened game would never have passed a human. The gate caught it at the
  definition and prescribed the challenge-terminated repair.
- **The external review strengthened, did not narrow (K4).** When the
  simulated outside cryptographer found the q=1 game certified only
  first-spend-per-epoch unlinkability, the response was to *upgrade* the
  game to the session form — more true, not more provable. The calibration
  battery was widened at the same time.

The evidence that drift did not happen is the shape of the whole gate log:
findings moved *outward* over the rounds (from the theorem cores, which
held from round 2, into repair periphery), and the definitions got
*stronger* under review, not weaker.

### Failure shape 2 — trivialities dressed as theorems: CHECKED, and defended by construction

- The **calibration pair** is the built-in guard against this, and it
  fires correctly: the *same* UNLINK game gives advantage exactly 1/2
  against B-static (the known-broken static-`E(R)` design) and exactly 0
  against B-rerand (the fix). A game that could not separate a broken
  scheme from a fixed one would be a triviality; this one provably can.
- The **must-catch battery** (index-leak, `nf_e`-reuse, multiplicity-tag)
  each wins at 1/2, and the **must-win FRAME adversaries** (`y=k`,
  `a`-reused) each win at probability 1 — the game punishes real breaks,
  so its silence on the sound scheme means something.
- **K3** (adversarial vacuity review) is the dedicated audit for this
  shape — its verdict is recorded separately in `k3-vacuity-review.md`.

### Failure shape 3 — Lean losing to SSProve: DID NOT HAPPEN

The bet was that Lean 4 + mathlib + VCV-io could carry a game-based
protocol-privacy proof this year, against a survey that put the mature
frameworks (SSProve/CryptHOL) ahead. It carried it: the T4 coupling landed
via VCV-io's `DistEquiv`/`advantage_zero` machinery on the exact template
(`OneTimePad/HeapBasic`) the `vcvio-gap.md` survey predicted, in days not
weeks, and B-rerand reused the same technique. The SSProve fallback was
never needed. Caveat retained honestly: T7's PPT tail is the one place the
young Lean game layer showed its age (the identical-until-bad accounting
the survey called the hard 20%), and it is deferred, not claimed.

## The unplanned result: cross-method convergence

Not in the original design, and the strongest single datum for the
autoresearch thesis: the **TLA+ model-checker independently found the
gap-index close hole** (via TLC state exploration) at the same time the
**adversarial gate found it by definition review**, and TLC then
**verified the same MC20-shaped repair** the gate adopted. Two methods
that share no machinery — symbolic model-checking and human-style
definition attack — converged on the same defect and the same fix. When an
agent-run process reaches a real cryptographic hole by two independent
roads, that is evidence the hole is real and the process is not
hallucinating agreement with itself.

## Honest ledger of what is NOT done

- T7's unconditional (query-term) bound — scoped behind `hobliv`,
  deferred.
- The refund symbolic layer is single-channel (N=1) and models one
  close-dispute round, not the full upgrade cascade (GATE-NOTE).
- Instantiation-B's Lean UNLINK proof is the ideal-model calibration pair;
  the model-to-real bridges (`zkBridgeObligation`, genesis obligations)
  are stated obligations, not discharged per a concrete SNARK/encryption
  scheme (that is out of the stated model boundary — we do not verify
  circuits).
- The honest-limits the reviews surfaced (retroactive `k`-linkage on
  identity-slash, the stale-close one-session residue, within-epoch
  linkage, spend-count-at-close, fleet-honesty presumption for window
  recovery, multi-recipient as the open problem) are the paper's
  honest-limits section, owed and enumerated, not solved.

## Verdict on the experiment

The evaluation asymmetry the README bet on held up: the human-equivalent
effort concentrated on a page of definitions (which the gate rounds show
was where all the danger lived — every blocking finding was a definitional
one), and the kernel absorbed the proof-checking (K2: nothing but the
three standard axioms). The definitions got harder and truer under attack
rather than drifting soft, the headline theorem is real and first, and the
one hard remainder is labelled as such. The failure modes the field has
actually suffered were the ones the process was built to catch, and it
caught them.
