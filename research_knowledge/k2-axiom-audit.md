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
