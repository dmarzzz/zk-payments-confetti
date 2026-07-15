# The gates, distilled

The unabridged record is `../raw/gates.md` (~550 lines). This page is what
you actually need from it.

## What a "gate" is

The project's thesis is that with machine-checked proofs, definitions are
the only real risk surface: the kernel guarantees the proofs, so the only
way to be wrong is to prove the wrong statement (the A2L failure mode:
peer-reviewed privacy model, correct proofs, insecure instantiations
found a year later). So before any proving starts, the definitions go
through **adversarial review rounds**: a fresh reviewer (here: independent
agents that did not write the artifact) attacks the spec and must produce
a **concrete counterexample** for every blocking finding. The spec is
revised; the next round re-verifies the fixes and attacks again. When a
full round produces no blocking finding, the definition is **frozen** and
proving begins against it. A proof that later fails is treated as a
finding about the definition and goes back to the gate, never into a
weakened theorem.

Caveat that applies to everything below: all recorded sign-offs are
**agent** sign-offs. The contract's independent-human review was never
logged and is still pending.

## What the rev-11 series decided (11 rounds, 2026-07-06/07)

The old object (encrypted-running-total design, instantiations A and B)
took 11 rounds and forced ~20 modeling choices (MC1–MC20). The findings
that mattered most, each a real attack with a numerical or mechanical
witness:

- **Round 1: the canonical wrong-definition case.** T6 was false via
  bit-identical cross-gateway ticket replay (excess ≈ (N−1)·D against a
  claimed bound of r·L·C). Fix: bind every message to its target gateway
  (MC14). All three independent reviewers found it. Also round 1: the
  unlinkability game as written was unsatisfiable (post-challenge oracles
  leaked the bit against *every* scheme), fixed by challenge-terminating
  the game (MC15).
- **Rounds 2–4: conservation.** Instantiation B's pooled escrow paid out
  more than was deposited along several adversary schedules
  (sweeps + refund-bearing close; unbounded close index). Fixes: settle
  once at close with payouts that conserve D by construction (MC18), plus
  two verified caps in the close relation (R ≤ j·C_max, j·C_max ≤ D + R).
- **Round 5: the deepest hole.** Nothing enforced spend-index contiguity;
  a payer could skip index 0, spend at 1..m, close at the unused index 0
  and recover the full deposit after consuming service. Root cause: the
  ledger had no verifiable spend count. Fix: MC20 (close by
  unused-nullifier enumeration in A; receipt-certified counts in B). A
  TLA+ model checker later **independently rediscovered this same hole
  and verified the same repair** — the run's strongest evidence that the
  method works (see `../raw/tla-findings.md`).
- **Rounds 6–8: close-time games.** Stale-receipt closes (recover value
  from spends after the receipt you close on) and the
  receipt-withholding wedge (the payee controls receipt supply, so naive
  fixes let the payee frame an honest payer at close). Fix: closes reveal
  the next nullifier, disputes open an upgrade sub-window instead of
  slashing immediately, and escalation converges at the true count.
  Agent sign-off at rev-8.
- **Rounds 9–11: the external-review strengthening.** The simulated
  outside-cryptographer review (K4) found the challenge form too weak
  (single-spend unlinkability certified while lifetime linkage passed) —
  fixed by session-form challenges (a whole epoch session, not one
  spend), a close-view simulatability obligation, and a wider must-catch
  calibration battery. One honest limit was scoped rather than hidden:
  in B, a stale close's conviction mechanism *is* a one-session linkage;
  the upgrade path restores funds, not privacy. Final agent sign-off at
  rev-11.

Everything above is about the **superseded** object. Its value to the new
protocol is the method (rounds, counterexamples, calibration batteries,
must-win adversaries) and the reusable Lean machinery — not the specific
modeling choices.

## The v2 series (open): G1–G5 against `PROTOCOL.md`

Opened 2026-07-14. The new design is simpler (no fleet, epochs, RLN, or
refunds), but five definitional questions are open, and by the project's
own rules no proving starts until they are resolved and Spec-v2 freezes:

| # | Issue | Why it matters |
|---|---|---|
| G1 | What exactly does Bob sign? | Must bind channel id + recipient, or cross-channel signature splicing rebuilds the round-1 attack shape against no-overspend. |
| G2 | **Withheld countersignature (critical path).** Alice reveals `N_{i+1}`, Bob refuses to sign. Closing on the parent is forfeit-bait; the child was never accepted. What close is legal? | The old object's round-7 wedge, reborn. Genuine design work; `PROTOCOL.md` states no repair. |
| G3 | How long is Bob's challenge window? | Unspecified; liveness theorems need it. |
| G4 | What does Close verify about the balance commitment? | The close-time proof obligation is unspecified. |
| G5 | Forfeit-all proportionality in honest-limit edge cases. | Interacts with G2; needs a stated accounting rule. |

Counterexamples and repair proposals for these are the highest-value
contribution right now. Estimated 4–7 rounds to a freeze. The five
questions, each with a proposed default, are packaged for the designer in
[`design-questions.md`](design-questions.md).
