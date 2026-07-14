# K1 — Independent statement audit (task K1)

**Auditor:** K1 statement auditor (agent; wrote none of the audited text).
**Date:** 2026-07-07.
**Scope read:** README.md, BRIEF.md, PROVING.md, Spec.md **revision 8** in full, and the
statements/docstrings (proof bodies skipped) of `Zkpc/Core/{State,T1,T2,T3,T5,Flat}.lean`,
`Zkpc/Fleet/{Basic,T6}.lean`, `Zkpc/Games/{RLN,Framework,Unlink,Frame}.lean`,
`Zkpc/Assumptions.lean`, `Zkpc/Games/README-games.md`.
**Question answered:** does the formal chain — Spec.md definitions plus Lean theorem
statements — mean what README/BRIEF promise? Not: are the proofs right (kernel's job),
not: are the games internally sound (B3's job).

**Audit condition:** the Core files were being reworked to rev-8 close semantics *while
this audit ran* (State/T1/T2/T3 changed under me mid-read; the settlement-time
`settleVoid` branch landed during the audit). Verdicts below are against the file
contents at final read (mtimes ≈ 01:08). `Core/T5.lean` and `Core/Flat.lean` were still
on the pre-MC20 machine at final read and are classified expected-rework, not drift.

---

## 1. Per-theorem verdict table

| Thm | Lean location (statement) | Verdict | One-line basis |
|---|---|---|---|
| T1 | `Core/T1.lean` `T1_no_overspend` | **FAITHFUL** (flat; refund clause pending H) | Exactly Spec T1's L=0 flat statement, `C·#accepted(k) ≤ D` over all reachable states, adversary = arbitrary interleaving |
| T2 | `Core/T2.lean` `T2_paid_exact`/`T2_upper`/`T2_collectable`/`T2_settles_exactly` | **FAITHFUL-WITH-NOTES** | Spec's temporal "settled exactly C·|T| by t_done" rendered as unconditional upper bound + always-enabled unilateral sweep strategy; all deltas carried in file GATE-NOTEs 1–3 |
| T3 | `Core/T3.lean` `T3_payer_balance_security` (bundle) | **FAITHFUL-WITH-NOTES** | Floor proved as equality (stronger than spec's "at least", documented); no-framing clause symbolic with probabilistic content correctly deferred to T7 |
| T4 | `Games/Unlink.lean` (game defs only) | **FAITHFUL-WITH-NOTES** (game); theorem **NOT YET STATED** | Game is a clause-by-clause transcription of Spec T4 incl. b-first sampling, challenge-time freshness, challenge-termination by type; obligations honestly registered |
| T5 | `Core/T5.lean` `T5_payer_close_liveness` | **EXPECTED-REWORK** (statement intent faithful) | File still on the pre-MC20 machine (`mclose`, scalar close index); statement shape (Δ-folding, exact `max(now, t+τ)` bound, explicit fairness) matches Spec T5 payer half |
| T6 | `Fleet/T6.lean` `T6_priced_divergence` + `T6_slash_within_L` | **FAITHFUL-WITH-NOTES** | Bound is Spec's exact discrete form `⌊D/C⌋·C + N·b·(⌈L/T_e⌉+1)·C`; clause (ii) is deliberate unfolding of the FleetFair model guarantee, said so in the docstring |
| T7 | `Games/Frame.lean` (game defs only) + `Games/RLN.lean` (algebra, proved) | **FAITHFUL-WITH-NOTES + 1 DRIFT FLAG** (game); theorem **NOT YET STATED** | Game dominates the spec adversary on every documented axis, but the adversary's view omits `cm = H_id(k)` / any `H_id` oracle — the one *undocumented weakening* found (D1 below) |

No theorem in the tree is stated-with-`sorry`; pending theorems are absent rather than
faked. `grep` confirms zero `sorry`/`admit`/`native_decide`/`axiom` declarations
repo-wide (Assumptions.lean is a data registry, no axioms — consistent with its own
stated design).

---

## 2. Deltas, with classification

### T1 (`T1_no_overspend`)
- Ticket ≡ extracted witness, nullifier ≡ `(k,i)`, adversary cannot emit for honest
  secrets (`emitAdv` guard `¬ honest k`): the symbolic absorption of assumptions 1/3/3′,
  exactly the scheme Assumptions.lean's table declares. **faithful-encoding** (documented
  in State.lean header; probabilistic backing correctly assigned to T7).
- Refund-variant clause of Spec T1 (Σcℓ ≤ D under tag-bound receipts) not present —
  **known-pending** (task H4), not silent: T3 GATE-NOTE 3 and TASKS.md say so.
- Rate budgets absent from the D1 machine: strictly strengthens T1–T3 (documented).
  **faithful-encoding**.

### T2
- **GATE-NOTE 1 (documented):** ledger Δ folded to instantaneous inclusion; the spec's
  deadline clause becomes "no `tick` in `SweepStar`" — settlement needs zero time.
  Faithful under the stated time interpretation.
- **GATE-NOTE 2 (documented):** "follows the sweep protocol" (MC16 monitoring, rev-6
  close-window disputing) becomes hypotheses `sweepOpen` / `¬ sweepBarred`, with the
  duties' dischargers proved as enabledness theorems (`sweepOne_enabled`,
  `false_claim_disputable`, `honest_payer_tickets_never_barred`). This converts a
  per-execution guarantee into duty-conditional collectability — the honest reading of
  "follows the protocol", and the loss-bearer decision (stale-checkpoint loss on the
  tardy gateway) is carried verbatim. **documented-GATE-NOTE**, sign-able.
- **GATE-NOTE 3 (documented):** N=1 makes `acc` the always-current pre-close checkpoint,
  so Spec's "checkpoints current" proviso is auto-true and the staleness/in-flight facet
  has no content until the fleet model. Correct and honest — but note the fleet-side T2
  scope (dispute-window documented-conflict claims, remainder caps) is **not formalized
  anywhere yet**; it is Spec-prose only. Flagged in §4.
- T2-B (close-time netting, upgrade cascade): **known-pending** (H tasks).

### T3
- "At least" → equality (`paid + j·C = D`), stated additively to kill ℕ-truncation
  ambiguity. Strictly stronger; **documented-GATE-NOTE 1**.
- `j` = emission counter, close charges no index, `|U| = cap − j` arithmetic proved
  separately (`close_payout_arith`). Matches Spec T3 scope note (iii) and MC2.
  **faithful-encoding**.
- No-framing clause: in the symbolic machine this is true *by the `emitAdv` guard* —
  i.e., by the model's embodiment of `single_signal_hiding` — not by a probabilistic
  argument. The docstrings (T1 header, T3 bundle, State.lean header) say this plainly
  and point at T7 as the probabilistic complement. A reviewer signing T3 must understand
  the clause's real content lives in the **unproved** T7. Correctly labeled everywhere;
  **documented-GATE-NOTE**, but I record it as the largest single deferral in the
  proved set.
- The new `honest_settleVoid_never` (rev-8 two-sided bar, honest side) correctly extends
  the exculpability story to the settlement-time void branch; `settleClose_enabled`
  consumes it, so the honest path stays dispute-free per Spec T5's "voided branch never
  fires" clause. **faithful-encoding** of the rev-8 repair.

### T4 game (`Unlink.lean`)
Checked clause-by-clause against Spec §7 T4: hidden bit sampled first ✓; two candidates,
equal deposits, batch open (single `openCh`, two draws) ✓; adversary = payee incl. B
genesis-receipt issuance (`phase0`) ✓; oracles spend/retry/serve/close/tick ✓; abort =
withholding `serve`, evict = never serving (native; `withEvict` also exists as the E4
component) ✓; freshness as a *challenge-time transcript predicate* (rev-2 NEW-5) via
`lastSig`/monotone epoch ✓; capability = both candidates, ⊥ on either failing ✓;
⊥ in-band (`Option`, not failure mass) so ⊥-paths contribute exactly ½ ✓;
challenge-termination structural (`ChalAdversary.guess` pure) ✓; advantage
verbatim `|Pr[b'=b] − ½|` ✓.
- Retry gives no freshness update and is answered post-close: **documented-GATE-NOTE**,
  correct (a bit-identical re-send carries the original epoch's pseudonym; MC2).
- "Open ∧ unslashed" reduced to true with the Mi2 no-circularity note:
  **documented-GATE-NOTE**.
- Epochs as an adversary `tick` oracle: maximal-power reading of §6 scheduler control;
  **documented-GATE-NOTE**.
- Proof-free `View` + `zkBridgeObligation(Sfull, Sfree, εZK)`: the file itself names
  this the K2 smell and makes the bridge a stated obligation, with the `root`/`e`
  droppability argument and the `nf_e` non-droppability written down.
  **documented-GATE-OBLIGATION** — acceptable at definition stage, but T4's headline is
  NOT achieved until a full-ticket instance exists and the bridge is discharged; K2/K3
  must hold that line.
- Calibration pair (B-static winnable by a constructive term, B-rerand negligible):
  **known-pending** (H3), correctly registered in README-games.md.

### T5 (`Core/T5.lean`) — expected-rework
- File is on the pre-MC20 machine (parameters `mclose`, `closedAt = some (j, t)` with
  scalar `j`); it cannot typecheck against current State.lean. The rework must also
  thread the new `settleVoid` branch through `settleClose_stable` and consume
  `honest_settleVoid_never`. **expected-rework**, not drift — statement intent (exact
  `max(now, t+τ)` machine-time bound, GATE-NOTE Δ-folding, negl-caveat pushed to T7,
  fairness as constructive continuation + persistence with the weak-fairness reading in
  the header) is a faithful rendering of Spec T5's payer half.
- Payee-sweep half delegated to T2 (`T2_collectable`, zero ticks) — Spec itself does
  this. B force-close/upgrade-window halves: **known-pending** (H/I).

### T6 (`Fleet/T6.lean`, `Fleet/Basic.lean`)
- Value bound is Spec's exact discrete form, including the rev-1 `⌈L/T_e⌉+1` correction
  (`epochs_in_window` proves the straddle fact). **faithful-encoding**.
- Count form needs `0 < C`, value form does not; the GATE-NOTE gives the explicit
  `C = 0` counterexample. `0 < T_e` hypothesis flagged as implicit-in-spec.
  **documented-GATE-NOTE**, both.
- Clause (ii) `T6_slash_within_L` is quantifier-unfolding of `FleetFair` — the docstring
  says so *deliberately* and gives the converse (`Inv.slash_sound`: slash ⇒ real
  conflicting pair) as the non-trivial content. The reviewer must understand clause (ii)
  is a model guarantee restated, per Spec §6's own boundary ("L is a guarantee of honest
  infrastructure"). **documented-GATE-NOTE**, sign-able as stated.
- Single-member machine: Spec's "coalitions sum linearly per member" is a prose claim;
  the linear-summation step itself is not formalized. **documented** (Basic.lean
  modeling-choices list); acceptable, flagged in §4.
- Spec T6's recovery clauses (remainder-capped, checkpoint-gated window claims) are
  explicitly NOT claimed by the Lean statement — the docstring says they are Spec-level
  consequences. Matches Spec's own hedging (no unprofitability, no universal recovery).
  **faithful-encoding by explicit exclusion**.
- `FleetFair` satisfiability: trivially satisfiable (conflict-free runs; prompt-slash
  runs), so the trace hypothesis is not vacuous. `accept` guards mutually satisfiable
  for `C ≤ D`, `b > 0`. Non-vacuous.

### T7 game (`Frame.lean`, `RLN.lean`)
- RLN algebra: two-point recovery, unique-coefficient one-point hiding (x ≠ 0),
  evidence completeness/soundness — matches Spec §1/§2 exactly; the `x = 0` degeneracy
  is isolated and (contra RLN.lean's own GATE-NOTE, which is now stale) **already
  adopted by Spec rev-6+ §1** (`H_x` into `F_p \ {0}`). Minor doc staleness only.
- Frame game dominance arguments (legacy close = surplus power; `nfAt` ⊇ MC20 reveal;
  no solvency gate; win predicate drops ancillary checks; MC2 re-send omitted as
  deterministic replay): all individually correct and all documented.
  **documented-GATE-NOTEs**.
- **D1 — the one UNDOCUMENTED-DRIFT finding.** The FRAME adversary's view contains no
  `cm = H_id(k)` and the game has no `H_id` random oracle (caches: `roA`, `roX`,
  `roNf`, `roE` only). In the real protocol `cm` is public from `Open` (Spec §2:
  "`Open` is a public ledger event naming `cm`") and again at close, and `Dispute`
  checks `cm = H_id(k)`. Every other divergence in this file is argued
  "strictly more adversary power"; this one is strictly *less adversary information*,
  and unlike the analogous `nf_e` gap (which got the Mi1 `roE` + simulation note), it
  is nowhere acknowledged. In ROM the gap is almost certainly negligible-mass (querying
  `H_id` at `k` ≡ knowing `k`, the very event T7 bounds), so this is repairable at
  definition level: add an `roId` cache + deliver `cm = roId k` at game start (or write
  the Mi1-style simulation GATE-NOTE). **Must be fixed or documented before the T7
  proof lands**; a T7 proved over the current game is a theorem about an adversary that
  never saw the victim's public commitment.

### Cross-cutting
- `Core/Flat.lean` (D5 scheme instantiation): **expected-rework** — body still
  implements the superseded close-as-final-spend (`mclose` signal at index `j`,
  scalar `closedAt`), which MC20 replaced and which cannot typecheck against current
  State.lean. Because Flat.lean is the traceability link from the gate-reviewed
  `Zkpc/Spec/Object.lean` signatures to the machine, its rework must not be forgotten.
- `Assumptions.lean` entry 5 (re-randomizable AH encryption) omits
  **opening-homomorphism**, which Spec rev-8 (F8-m1) added as load-bearing for B.
  Registry is one revision behind. **expected-rework** (B is unbuilt, so nothing proved
  depends on it yet); K2 should re-check when H lands.
- Core file headers still cite "rev-7" while carrying rev-8 content (two-sided bar):
  cosmetic, but the header revision stamps should be bumped when the rework settles.

---

## 3. Vacuity spot-checks (audit question 2)

- **T1/T2/T3/T5 machine:** `init → openCh k → emitHonest → accept → …` is enabled for
  any `C ≤ D`; accepting, sweeping, closing, settling executions all exist. `honest` is
  a free parameter; both all-honest and mixed instantiations produce nontrivial runs.
  No contradictory guard pair found: `settleClose`'s new `hswbar` and `settleVoid`'s
  `hover` are exact complements over the same timing guards (settlement is total:
  every expired unslashed close either settles or voids), and
  `honest_settleVoid_never` shows the honest side always takes the settle branch.
  Not vacuous.
- **T2_settles_exactly** hypothesis (`hall`) satisfiable (any run with no slashes and no
  settled closes). Not vacuous.
- **T6:** `FleetFair` satisfiable; `accept` reachable; the count-form `0 < C` guard is
  justified by an explicit counterexample in the file. Not vacuous. (The matching
  lower-bound attack of Spec's anti-vacuity note is not formalized — Spec does not
  require it to be.)
- **UNLINK:** `challengeResp` returns a real ticket on the empty transcript for any
  instance whose fresh state is `capable` — the ⊥-branch is not the whole game. The
  capable-but-spend-⊥ residual is registered as obligation Mi3 rather than hidden.
  Non-vacuous at definition level; per-instance vacuity is K3's to re-check at H3.
- **FRAME:** `recoverSecret_line` (proved) is exactly the anti-vacuity witness — genuine
  double-signs do win the game, so the win predicate is satisfiable and exculpability is
  not "true because nobody can ever be slashed".

## 4. Docstring accuracy (audit question 3)

Spot-checked every theorem docstring against its Lean statement. All accurately restate
their statements, including the deltas (the T2/T3/T5/T6 docstrings state their own
weakenings/strengthenings rather than paraphrasing the spec). Two corrections needed,
both minor: (a) RLN.lean's GATE-NOTE claims Spec §1 does not exclude `x = 0` — Spec
rev-6+ does (credit its own G4 loop); (b) Frame.lean's clause-2 claim that the adversary
"effectively reads every signal" overstates the view by omitting the `cm`/`H_id` surface
(finding D1). Otherwise a reviewer could sign from Spec.md + docstrings alone, which is
the PROVING.md contract.

## 5. Promise-chain map (audit question 4)

BRIEF acceptance: T1–T4 + T6–T7 proved flat-ticket; T4 on refund variant with the
calibration pair; T5 stretch; zero `sorry`; axioms confined.

| Item | Status at audit |
|---|---|
| T1 flat | **Stated + proved** (rev-8-current machine) |
| T2 flat | **Stated + proved** (bound + collectability suite; deltas documented) |
| T3 flat | **Stated + proved** (bundle; no-framing symbolic, probabilistic content = T7) |
| T4 flat | Game **defined** (B3 shape); theorem **not yet stated**; zkBridge + Mi3 obligations open |
| T4 refund + calibration | **Not yet stated** (all of instantiation B absent from Lean; tasks H) |
| T5 | Payer half proved on the **stale** machine — rework in flight; B halves absent |
| T6 | **Stated + proved** (clauses i & ii; recovery clauses deliberately not claimed) |
| T7 | Game **defined** + RLN algebraic core **proved**; theorem (`frameWinProb ≤ negl`) **not yet stated** |
| Zero `sorry` / axioms confined | No `sorry`/`admit`/`native_decide`/`axiom` anywhere; but the tree as a whole cannot currently build (T5/Flat vs new State) until the rework completes |

Nothing is silently missing beyond the known-pendings above. Items that are Spec-prose
only (no Lean statement planned yet, worth tracking so they don't vanish): the fleet-side
T2 scope clause (dispute-window claims, remainder caps), T6's per-member linear
summation, pool conservation as a global invariant, and everything in instantiation B.

## 6. Sign-off

**Signed off — FAITHFUL-WITH-NOTES overall — with three conditions:**

1. **(D1, drift)** Fix or document FRAME's missing `cm`/`H_id` surface before any T7
   proof is accepted (add `roId` + deliver `cm`, or write the Mi1-style simulation
   GATE-NOTE).
2. **(rework completion)** T5.lean and Flat.lean must be brought to the rev-8 machine
   (thread `settleVoid` through `settleClose_stable`; rebuild Flat's `payerClose` on
   close-by-unused-enumeration) and the whole tree must build green before any
   "proved" claim is published; bump the rev-7 header stamps.
3. **(registry currency)** Add opening-homomorphism to Assumptions.lean entry 5
   (rev-8 F8-m1) before instantiation B work starts.

With those conditions, the statements as written say what README/BRIEF promise, at the
scope actually claimed: the flat-ticket safety/liveness core and the fleet bound are
faithfully transcribed and non-vacuous; the two headline games are faithful,
maximal-power transcriptions with their deferrals honestly registered as obligations
rather than hidden; and the repo nowhere claims T4/T7/refund results it does not have.

— K1 auditor, 2026-07-07

## Follow-up statement reconciliation — 2026-07-10

This follow-up does not rewrite the 2026-07-07 audit; it records the final
T7 statement after the later pointwise-certificate refutation and averaged
repair.

The live theorem interface is faithful to the finite query-bounded FRAME
experiment: for arbitrary `A` and `qb : FrameQueryBounds A`,
`T7_frame_query_bound_unconditional` concludes the secret-averaged bound
`frameWinProb mclose A ≤ (qb.total + 1)/|F|`. The composition theorem
`T7Certificate.ofQueryBounds` packages exactly that conclusion. Their
statements have no residual `hobliv`, transfer, coupling, counting,
good-slice, bad-mass, or deferred-sampling premise. Ambient finite-field
and decidability instances are model parameters, not adversary-specific
security assumptions.

This is the right statement direction. `frameGame` samples `k` uniformly,
so an averaged certificate compares the same experiment the public theorem
bounds. The stronger pointwise `FrameDeferredSampling` socket is not part
of the final promise chain and remains refuted by
`frameDeferredSampling_refuted`; keeping that result visible prevents the
repair from being misreported as a proof of the false pointwise claim.

The reconciliation also narrows the English promise: the exact theorem is
a finite query-budget inequality in the ideal random-oracle model. It is
not, by itself, a formal PPT/asymptotic-negligibility theorem and it is not a
reduction for a deployed hash function. Any prose saying simply
“unconditional PPT T7” must be read or rewritten with that limitation.

**Post-handoff status (2026-07-10):** statement inspection was complete at
this handoff, and the release audit subsequently closed the technical
evidence at source checkpoint `abb878f`: the fresh Lean 4.30.0 root build
completed 3,595 jobs and the final endpoint `#print axioms` capture used only
Lean's standard axioms. Required non-author human K1 acceptance remains
pending; this technical addendum does not substitute for it.
