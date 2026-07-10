# K2 — Axiom audit

Task K2 (TASKS.md): enumerate every axiom actually used, confirm each is a
standard assumption, and confirm no accidental proof escape hatches.

## Method

`#print axioms` on every headline theorem, run against the built project
(`lake env lean` over the cached build, 2026-07-08). CI's guardrail job
independently greps every `.lean` file for the four forbidden tokens as
whole words on every push.

## Result — every theorem, only the three standard Lean axioms

```
Zkpc.Core.T1_no_overspend            [propext, Classical.choice, Quot.sound]
Zkpc.Core.honest_never_slashed       [propext, Classical.choice, Quot.sound]
Zkpc.Core.T3_payer_balance_security  [propext, Classical.choice, Quot.sound]
Zkpc.Core.T5_payer_close_liveness    [propext, Classical.choice, Quot.sound]
Zkpc.Fleet.T6_priced_divergence      [propext, Classical.choice, Quot.sound]
Zkpc.Games.T4_flat_unlinkability     [propext, Classical.choice, Quot.sound]
Zkpc.Games.T7_frame_bound            [propext, Classical.choice, Quot.sound]
```

The calibration and refund theorems audit identically (per-workstream
`#print axioms` reports, committed with each): the calibration set
(`unlinkAdvantage_bRerand_eq_zero`,
`unlinkAdvantage_staticDistinguisher_eq_half`, the three battery winners)
shows `[propext, Classical.choice, Quot.sound]`; the refund set
(`T1_B_no_overspend`, `T3_B_floor`, `conservation`,
`self_slash_race_closed`) shows `[propext, Quot.sound]` (no `Classical.choice`).

`propext`, `Classical.choice`, and `Quot.sound` are the three axioms of
Lean 4's standard library — the baseline every mathlib development stands
on. Nothing beyond them appears.

## The two things this audit is really checking

1. **No project-specific `axiom`.** `Zkpc/Assumptions.lean` — the one file
   the contract permits to declare axioms — declares **none**: the
   cryptographic assumptions (Spec.md §5) are discharged *by construction*
   in the idealized model (knowledge soundness as a transition guard, ZK
   as the π-free view, PRF/ROM and single-signal-hiding via random-oracle
   sampling, EUF-CMA / re-randomization / opening-homomorphism as the
   ideal shapes of the refund chain). `Assumptions.Named` is a data
   registry for this audit, not logic. So the trust surface is exactly the
   *model definitions* (gate-reviewed at B1/B3/K1) plus this table — there
   is no axiomatized shortcut that could hide a false assumption.

2. **No escape hatch.** No `sorry`, `admit`, or `native_decide` anywhere
   in `Zkpc/` (CI-enforced every push; `native_decide` in particular would
   inject the compiler into the trusted base — it is absent).

## Honest scope notes (hypotheses are not axioms)

- **`T7_frame_bound`** is kernel-clean, but its statement carries the
  `hobliv` hypothesis (the RO-oblivious good event): the proved claim is
  "under `hobliv`, the FRAME slash probability ≤ 1/|F|". `hobliv` is a
  *stated hypothesis*, not an axiom — the theorem is honest about what it
  assumes, and the deferred half (bounding the `q/|F|` RO-hit terms that
  discharge `hobliv` for an unbounded interactive adversary) is the
  documented PPT-accounting follow-up (GATE-NOTE in T7.lean), not a hidden
  assumption. A reader who wants the unconditional bound reads the
  GATE-NOTE; the kernel guarantees everything up to `hobliv`.
- **`T4_flat_unlinkability`** is unconditional (advantage = 0 for every
  adversary and budget) in the ideal ROM model; the model-to-real bridge
  (real `nf_e = H_e(k,e)`, the NIZK proof, re-randomization) is the
  `zkBridgeObligation` / GATE-NOTE surface, discharged per the named
  assumptions rather than axiomatized.

## Verdict

Clean. Every machine-checked theorem reduces to the three standard Lean
axioms; the crypto assumptions live as reviewed model shapes, not
axioms; no escape hatches. The K3 adversarial-vacuity review (separate)
checks the complementary risk — that a clean-but-vacuous statement was
proved — which axioms alone cannot detect.

## Extension — 2026-07-10: files landed since the 2026-07-08 audit

Scope: the theorem-bearing files landed after the audit above (issues
#4–#7 closeouts, the T7 frame campaign, and the `Zkpc/Chain/`
instantiation).

**Mechanism, stated honestly.** This extension did *not* re-run a full
`lake build` of the tree; the most recent full-tree build this audit can
attest to is the 2026-07-08 run recorded in Method above, and a fresh
full-tree validation is with the orchestrator's review pass. What this
extension verifies directly is: (a) every file below carries in-file
`#print axioms` lines for its main results (grep-confirmed per file,
counts listed), so the axiom check re-executes on every compile of that
file rather than living only in this document; (b) the observed outputs
at land time were the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and nothing else — several files also
annotate the expected output inline (e.g. the "Kernel audit: only Lean's
own …" comments in `FrameFactor.lean`, `T7.lean`). The CI guardrail grep
for the four forbidden tokens (Method above) is unchanged and covers all
of these files.

Per-file `#print axioms` line counts (grep `#print axioms`, 2026-07-10):

```
Zkpc/Crypto/FSRom.lean               5
Zkpc/Crypto/MaskedEncryption.lean    9
Zkpc/Crypto/ReceiptMac.lean          3
Zkpc/Games/SigmaInstance.lean        6
Zkpc/Games/T4Fires.lean              2
Zkpc/Games/FullTicketInstance.lean   5
Zkpc/Network/Issuance.lean           7
Zkpc/Network/State.lean              9
Zkpc/Network/Credential.lean         4
Zkpc/Core/Composition.lean           2
Zkpc/Core/Refinement.lean           13
Zkpc/Refund/Refinement.lean          4
Zkpc/Fleet/Refinement.lean           4
Zkpc/Fleet/Recovery.lean             5
Zkpc/Games/FrameAudit.lean           6
Zkpc/Games/FrameIdeal.lean          18
Zkpc/Games/FrameDeferred.lean       10
Zkpc/Games/FrameCoupling.lean        8
Zkpc/Games/FrameGhost.lean          22
Zkpc/Games/FrameGhostBounds.lean     4
Zkpc/Games/FrameGhostCoupling.lean   8
Zkpc/Games/FrameGhostCoverage.lean   5
Zkpc/Games/FrameBadMass.lean        21
Zkpc/Games/FrameFactor.lean         16
Zkpc/Games/FrameAssembly.lean        3
Zkpc/Games/FrameTransfer.lean       11
Zkpc/Chain/State.lean                6
Zkpc/Chain/Collision.lean            5
Zkpc/Chain/Anonymity.lean            3
Zkpc/Chain/Refinement.lean           3
```

No file in the list above is missing its audit lines. One adjacent note:
`Zkpc/Games/Frame.lean` (the FRAME game definitions) carries no
`#print axioms` lines of its own, but its headline results
(`frameWinProb_slopeReveal_eq_one` and the other calibration limits) are
audited downstream in `Zkpc/Games/T7.lean`'s audit block, so nothing is
uncovered.

Two structural notes specific to the new T7 files:

- **Refutations audit like theorems.** `frameDeferredSampling_refuted`
  (`FrameDeferred.lean`) — the kernel-checked *unsatisfiability* of the
  pointwise certificate socket — is in the audit surface like any positive
  result, and reduces to the same three axioms. A refutation proved from a
  nonstandard axiom would be worthless; this one is not.
- **Totality is load-bearing, not axiomatized.** The master factorization
  `frame_real_le_ghost_plus_bad` (`FrameFactor.lean`) leans on the fact
  that `OracleComp` is a plain free monad with no failure leaf, so
  adversary runs are total (recorded in that file's header). This is a
  property of the mechanization's ambient monad, checked by the kernel
  wherever it is used — not an assumption that could hide in this table.

The residual trust surface is unchanged from the 2026-07-08 verdict:
model definitions plus the three standard axioms. The open T7 residuals
(`FrameGoodSliceTransfer`, `FrameRealBadMassLe`) are stated `def`s
consumed as hypotheses by the assembly theorems — they appear in theorem
*statements*, never as axioms, so nothing in this extension weakens the
verdict above.
