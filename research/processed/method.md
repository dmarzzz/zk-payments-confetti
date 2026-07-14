# The method

Why agent-produced proofs can be trusted at all, and where human judgment
still has to sit.

## The evaluation asymmetry

Agent-produced research usually dies at review because checking it costs
as much as producing it. Machine-checked proofs invert that: if
`lake build` passes with no `sorry` and the axiom audit is clean, the
proofs are correct, and the only thing left for human judgment is whether
the theorem statements and the model say what was meant. The judgment
surface is concentrated in the definition documents (`PROTOCOL.md` now,
`raw/Spec.md` historically) and the security-game statements — pages, not
the proof corpus.

That is why the definitions get the adversarial treatment described in
[`decisions.md`](decisions.md), and why a failed proof is routed back to
the gate record instead of into a weakened theorem.

Two hard-won process rules live in the top-level `CONTRIBUTING.md`:
certificates over game-sampled secrets must be secret-averaged (the
pointwise shape is kernel-refuted), and "builds green" claims require a
recorded fresh-clone build, because token greps have passed twice over
non-compiling proof code.

## The independent-convergence datum

One unplanned result is worth flagging for anyone assessing the method: a
TLA+ model checker, built with no shared machinery with the adversarial
review, independently found the deepest definitional hole in the old
object (the gap-index close understatement — see `decisions.md`, round 5)
and verified the same repair the review had adopted. Two methods, one
defect, one fix.

## The five proof classes

The formalization is a set of theorems falling into reusable shapes, each
with a worked template in the tree. Anyone extending the verification is
writing one of these:

- **Safety invariants over a transition system** (induction on a
  reachability predicate). Templates: `lean/Zkpc/Core/T1.lean` (old object),
  `lean/Zkpc/Chain/State.lean` (new protocol).
- **Game-based perfect indistinguishability by random-oracle coupling**
  (reduce advantage to one per-challenge distributional equality, then a
  measure-preserving bijection on the oracle cache). Templates:
  `lean/Zkpc/Games/{Coupling,FlatInstance,T4}.lean`; the intended engine for
  the new protocol's per-request anonymity theorem.
- **Constructive distinguishers and must-win adversaries** (build one
  explicit adversary, compute its advantage exactly). Template:
  `lean/Zkpc/Games/Calibration.lean`. This is also the anti-vacuity
  discipline: every game ships with schemes it must catch and schemes it
  must pass.
- **Reductions, game hopping, and query charging** (bound advantage by a
  chain of hops with named bad events and charged oracle queries).
  Templates: `lean/Zkpc/Games/T7.lean` plus the FRAME campaign
  (`lean/Zkpc/Games/Frame*.lean`), whose secret-averaged deferred-sampling
  apparatus is what the new protocol's non-frameability bound needs.
- **Field and algebra lemmas.** Template: `lean/Zkpc/Games/RLN.lean`
  (historical; the new protocol has no RLN layer).

## Where humans are still required

The recorded gate sign-offs are agent sign-offs. The standing acceptance
gates — non-author human review of the theorem statements and
security-game definitions, and a real outside cryptographer attacking the
definitions — have never been logged and remain open. The A2L precedent
is the reason these are not optional.
