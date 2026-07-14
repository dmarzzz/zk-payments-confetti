# K3 — Adversarial vacuity review

Task K3 (TASKS.md): a skeptic reads only the theorem *statements* and the
*definitions* (transition guards, reachability predicates, game
challenge/win predicates) and asks the one question the axiom audit (K2)
cannot see: **does any theorem pass while proving nothing** — because a
hypothesis is unsatisfiable (vacuous) or a definition trivializes the
claim? Method: for each theorem I traced, by reading the transitions and
not by building, whether the interesting antecedent is *reachable /
satisfiable* and whether the quantified object (an accepted set, a fired
challenge, a slashable evidence pair, an inhabited honest hypothesis) can
actually be non-trivial. No `lake build`, TLC, or heavy tool was run, per
the resource rule; two residual build-checks are flagged at the end.

Verdict legend: **NON-VACUOUS** (with the witnessing reachable
configuration) / **FLAGGED** (needs a build-check) / **VACUOUS** (argument
given) / **SCOPED** (non-vacuous but the Lean statement is materially
weaker than the Spec.md statement, disclosed).

---

## Core safety machine (`Zkpc/Core/State.lean` guards)

The single-gateway machine's `accept` guard is satisfiable, which is the
root fact all of T1/T2/T3/T5 non-vacuity hangs on. Trace to a reachable
state with **non-empty `acc`** (parameters `C ≤ D`, any `honest`):

- `openCh k` (guard `k ∉ opened`, holds at `init`) → `k ∈ opened`.
- a signal for `k`: `emitAdv k 0 m` (guard `¬ honest k`) *or*, for honest
  `k`, `emitHonest k m` (guards `honest k`, `live k`, `(0+1)·C ≤ D`).
  `live k` holds after `openCh` (`slashedAt = none`, `closedAt = none` at
  `init`). So `(k,0,m) ∈ sigs`.
- `accept k 0 m`: guards `hsig` ✓, `hlive` ✓, `hsolv : (0+1)·C ≤ D` ✓
  (needs `C ≤ D`), `hfresh` ✓ (acc empty). Result `acc = {(k,0,m)}`.

The one degenerate parameter regime is `D < C` (then `cap = ⌊D/C⌋ = 0`,
solvency `(i+1)·C ≤ D` fails for all `i`, `acc` is forever empty and T1 is
vacuously true). This is a non-instantiation (a channel that cannot afford
one spend); the meaningful regime `C ≤ D` reaches a genuine accepted
ledger, so every theorem below is quantifying over a live state space.

### T1 — No overspend (`T1_no_overspend`) — **NON-VACUOUS**
Bounds `C·|accOf k| ≤ D` over a state space that provably contains
non-empty `acc` (witness above). The bound is a real count constraint:
the `accept` guard's `hsolv` caps each accepted index below `⌊D/C⌋` and
`hfresh` forces per-index uniqueness, so the ≤ is tight, not `0 ≤ D`. The
Spec.md anti-vacuity attacks (skip-check-6 replay; missing solvency
conjunct; tagless receipts) all correspond to *removing* one of these
guards, and the machine's guards are exactly those. `honest_never_slashed`
is likewise non-vacuous: `slash` genuinely fires for adversarial `k` (two
`emitAdv` at one index, different `m`), and is proved *unreachable* for
honest `k` because `emitHonest` increments the counter (one message per
index). The claim discriminates.

### T2 — Payee balance security (`T2_settles_exactly`, `T2_upper`, `T2_collectable`) — **NON-VACUOUS**
`T2_settles_exactly` yields `paidGw = C·|acc|` over the reachable
non-empty `acc`; `sweepOne_enabled` shows the sweep step is actually
enabled (guards `hacc`, `hdedup`, `sweepOpen`, `¬ sweepBarred` all
dischargeable from a fresh accept). The upper bound `paidGw ≤
C·#distinct-nullifiers` is unconditional and the collectability theorem
constructs a real `SweepStar` sequence, so "exactly `C·|T|`" is about a
populated `T`, not an empty one.

### T3 — Payer balance security (`T3_payer_balance_security`, `T3_settled_amount`, `T5`) — **NON-VACUOUS**
The load-bearing question was whether the `honest k` hypothesis is
inhabited on reachable states *and* whether an honest payer can actually
spend/close/settle. It can: with `honest = (fun _ => True)`, `openCh k →
emitHonest k m (×j) → payerClose k U → settleClose k` is a reachable run;
`payerClose`'s `hUeq` forces the honest `U` to the exact unused
enumeration, and `T5_payer_close_liveness` *constructs* the settling
continuation reaching `closeSettled = true` with `paidPayer k = D − j·C`.
So the floor is stated about a payer that genuinely reaches settlement,
and `honest_never_slashed` / `honest_close_undisputable` make the "no
framing" clauses real exclusions (the `slash` and `closeDispute` steps are
proved unenabled against honest `k`, not absent from the alphabet).

### T5 — Closure liveness — **NON-VACUOUS**
`tick_progress` shows any window-expiry time is reachable and
`settleClose_stable` shows the settlement stays enabled under every other
action, so the "settled by `t+τ`" bound is about an event that provably
occurs, not a vacuous timeout. Honest voiding branches
(`honest_closeDispute_never_fires`, `honest_settleVoid_never_fires`) are
proved *unreachable*, which is the right shape.

---

## Fleet machine (`Zkpc/Fleet/Basic.lean`, `T6.lean`)

### T6 — Priced divergence (`T6_priced_divergence`, `T6_accept_count`, `T6_slash_within_L`) — **NON-VACUOUS**
The `FStep.accept` guard is satisfiable (`hslash` holds at `finit`;
`hsolv` needs `C ≤ D`; `hrate` needs `b > 0`), so `log` is genuinely
populated and `acceptedValue = C·|log|` is a real quantity. `FleetFair` is
jointly satisfiable with a large log: a conflict-free log satisfies it
trivially (no deadline predicate fires), and a conflict + `slash` also
satisfies it — so the bound is not proved over an empty `FleetFair`
region. **The conflicting-pair antecedent is reachable**: `accept` at
gateway `g` index `i` then `accept` at gateway `g' ≠ g` index `i` (the
`hfresh` guard only blocks same-index-same-gateway) yields two `Ev` with
equal `idx`, distinct `msg` (gateway component differs, MC14) — a
`Conflict` — enabling `slash` (guard `hconf`). So clause (ii)
(`T6_slash_within_L`) fires on real evidence and `Inv.slash_sound` gives
the converse (no slash without a real pair). The GATE-NOTE honestly
records that the *count* form needs `0 < C` (at `C = 0` the bound is false
and only the trivial value form survives) — that is disclosed, not
smuggled. The bound is a matching upper bound on the one-window
double-spend attack, not `0 ≤ f`.

---

## The UNLINK game and T4 (the headline; hunts 2 & 3)

This is where a vacuous "advantage 0 because the challenge never fires"
would live. It does not. The decisive structural facts:

**The challenge genuinely fires with real, bit-dependent tickets.** The
challenge guard `challengeResp` (defined once, instance-generic, in
`Unlink.lean`) is `!mstars.isEmpty && epochFresh && challengeCapable`. At
`GSt.init` (`epoch = 0`, `lastSig = none`), `epochFresh = true` by `rfl`,
and `challengeCapable` reduces to `capableFor q` on both fresh candidates,
which is `decide (0 + q ≤ budget)` (flat) / `decide (q·Cmax ≤ D)` (B) —
satisfiable for `q ≤ budget` / `q·Cmax ≤ D`. This is not hand-waved: the
calibration lemmas `challengeResp_bStatic_init`, `challengeResp_leak_init`,
`challengeResp_multTag_init` each **prove the guard `= true`** (they
discharge `hfresh`, `hcap`, and take the passing `split` branch, closing
the failing branch with `absurd hguard hc`) and deliver a concrete
non-`⊥` batch `some [...]` of real ticket views. So the game's
challenge-firing machinery is constructively exercised, and the secure
instances (flat, B-rerand) share that identical machinery.

### T4-A flat unlinkability (`T4_flat_unlinkability = 0`) — **NON-VACUOUS**
The `0` comes from *genuine coupling*, not a constant/`⊥`. On the passing
guard branch, `challengeResp_flat_bitfree` rewrites **both** candidates'
batches to `flatFreshBatch ms` via `evalDist_spendBatch_flat`;
`flatFreshBatch` is structurally all-`some` (`flatFreshBatch_none_not_mem`,
`flat_spendBatch_none_zero`), i.e. the adversary receives `q` real fresh
tickets, and `P₀`'s and `P₁`'s are identically distributed. So advantage 0
means "the two candidates' real challenge batches are indistinguishable,"
which is the intended perfect-indistinguishability claim.

*Load-bearing caveat (recorded, not a defect):* the closer
`unlinkAdvantage_eq_zero_of_challenge_bitfree` consumes only bit-freeness,
which *would* also hold vacuously for a hypothetical instance whose
challenge always returned `⊥`. The non-vacuity of T4-A therefore does
**not** follow from the secure theorem in isolation — it rests on the
shared challenge machinery being provably live, which is exactly what the
calibration/battery `..._init` lemmas establish constructively. This is
why the calibration pair is load-bearing and why Spec.md §7 makes it a
binding requirement; the formalization includes it. (`flat_spendBatch_none_zero`
additionally pins that the flat instance's own batch is `⊥`-free on
solvent states, so its passing branch delivers real tickets.)

### T4-B B-rerand (`unlinkAdvantage_bRerand_eq_zero = 0`) — **NON-VACUOUS**
Same structure via `challengeResp_bRerand_bitfree` / `bFreshBatch`
(all-`some`, `bRerand_spendBatch_none_zero`). Real batch, genuine
coupling.

### The calibration pair — **NON-VACUOUS, and the decisive evidence (hunt 3)**
`bStatic Cmax D = bIdeal H Cmax D false` and `bRerand Cmax D = bIdeal H
Cmax D true` are **the same `UnlinkScheme` skeleton differing only in the
`spend` body's presented component** (echo `st.ct` vs sample fresh `h`) —
identical `capableFor`, identical `openCh`, identical `close`, hence
identical `challengeCapable` / `epochFresh` / `challengeResp` firing
condition. So the 1/2-vs-0 separation cannot be an artifact of different
challenge conditions:
- `unlinkAdvantage_staticDistinguisher_eq_half = 1/2`:
  `challengeResp_bStatic_init` proves the challenge fires and returns
  `pure (some [if b then h1 else h0])` — a **real, bit-dependent** batch;
  `staticDistinguisher_run` shows the run outputs `pure b`. The break is
  Spec.md §4's genesis-anchor echo, constructive.
- `unlinkAdvantage_bRerand_eq_zero = 0`: same game, same firing condition,
  advantage 0 because re-randomization severs the presented component.

This is the paper's headline definitional test and it genuinely tests
something: the game separates the echoed from the re-randomized
presentation, differing in nothing but `View`.

### The must-catch / must-win battery — **NON-VACUOUS**
`aIndexLeak`, `nfeReuse` (both via `leakScheme` + `leakDistinguisher`) and
the `q=2` `multTag` variant each get a constructive distinguisher proved
at advantage `1/2` through `unlinkAdvantage_eq_half_of_run_determined`,
with the challenge provably firing (`challengeResp_leak_init`,
`challengeResp_multTag_init`). `multTag` genuinely needs `q = 2` (its
first ticket carries `none`, the tag surfaces only in the second),
witnessing that the session form closes K4 Concern 1. These confirm the
game *catches* real leaks — the win side is not always-⊥.

---

## The FRAME game and T7 (hunt 5)

### Must-win battery (`frameWinProb_YK_eq_one`, `frameWinProb_aReuse_eq_one`) — **NON-VACUOUS**
Both prove FRAME's win predicate `Slashes` is satisfiable with
probability 1 against the two degenerate signal schemes (`y = k`; `a`
reused), via concrete evidence `⟨0,1,k,0,k⟩` / two points on one line.
`recoverSecret` of these is provably `k` (`recoverSecret_line`). So the
FRAME win condition is a real, reachable event — T7's bound is bounding
something that *can* happen (against a broken scheme), not an impossible
predicate. This defends against "T7 is trivial because `Slashes` never
holds."

### T7 FRAME bound (`T7_frame_bound ≤ 1/|F|`) — **NON-VACUOUS but SCOPED (flag)**
The hypothesis `hobliv : ∀ k, 𝒟[frameEvidence mclose A k] = 𝒟[gen]` — the
adversary's evidence distribution is independent of the secret `k` — is
**satisfiable and non-trivial**: any adversary that ignores `cm` and its
oracle answers and outputs fixed evidence satisfies it (`gen = pure ev`),
and the bound `1/|F|` is *tight* (such an adversary matching a fixed
`recoverSecret ev` against uniform `k` wins with exactly `1/|F|`). So the
theorem proves a real thing (blind-guess exculpability) over a real
adversary class. It is **not** vacuous in the unsatisfiable-hypothesis
sense.

However `hobliv` is doing heavy lifting: it *assumes* the RO-obliviousness
("no query hit `k`") that a full T7 would have to *prove*. The Lean bound
is therefore materially **weaker** than Spec.md T7 (`Pr[slash] ≤ negl(λ)`
for every PPT adversary): the full explicit bound is
`(q_A + q_Id + q_E + 1)/|F|`, and only the `+1` blind-guess term is
machine-checked; the `q_·/|F|` identical-until-bad query terms are
scoped behind `hobliv` and deferred (the module GATE-NOTE and
`vcvio-gap.md §3` disclose this as the estimated-hard 20%). This is an
**honest scoping gap, disclosed in the docstring**, not a hidden vacuity —
but a reviewer trusting "T7 is proved" should know the machine-checked
statement is the conditional blind-guess bound, and the unconditional PPT
theorem is a follow-up task. Recommend it be logged as a follow-up task
(consistent with the DoD "anything found becomes a task").

---

## Refund machine (`Zkpc/Refund/State.lean`, `Safety.lean`)

### T1-B (`T1_B_no_overspend`), conservation, T3-B floor, H5 — **NON-VACUOUS**
The `accept` guard is satisfiable (`init`: `(0+1)·Cmax ≤ D` needs
`Cmax ≤ D`), so `sumc` and `R` are genuinely grown; `close` reaches a
`settled ∧ ¬slashed` state (`init → accept → close`), so `T3_B_floor`'s
hypotheses are jointly inhabited on a reachable state and the floor
`payerPay + sumc = D` is about a real cooperative close. Note the two
settlement caps (`R ≤ j·Cmax`, `j·Cmax ≤ D+R`) are **not** `close` guards
but are proved as reachable invariants (`reach_inv`), so the ℕ-subtraction
payouts are exact (no truncation artifact) — conservation is genuine.
`forceClose_forfeit` gives the slashed path `payeePay = D`, and
`T3_B_floor`'s `¬slashed` hypothesis correctly excludes it (the floor is
not over-claimed for the forfeit path). The GATE-NOTE honestly scopes out
the multi-round upgrade cascade (single close round modeled) — a
completeness scoping, not a vacuity.

---

## Assumptions / axiom hygiene

`Zkpc/Assumptions.lean` contains **no `axiom`** — every §5 assumption is
discharged by construction (`Named`/`Discharge` are audit *data*, inert).
Cross-checked with the `#print axioms` lines appended to T4, T7, the
calibration battery, and the refund theorems (each asserts only Lean's own
`propext`/`Classical.choice`/`Quot.sound`). This is K2's territory; noted
here only because "no escape hatch" is a precondition for the vacuity
question being the *only* residual risk.

---

## Overall judgment

**No vacuous or trivializing theorem found.** Every safety theorem
(T1, T2, T3, T5, T6, T1-B/T3-B/conservation) quantifies over a state space
whose interesting antecedent (`accept`/`slash`/`close`/`conflict`) is
reachable — I traced a concrete witnessing run for each. The headline T4
is the strongest case: its advantage-0 is genuine coupling of
provably-live, all-`some` real batches, and the B-static/B-rerand
calibration pair (identical game, differ only in `View`, 1/2 vs 0) is a
constructive proof that the game separates a broken scheme from a fixed
one — the exact anti-vacuity Spec.md §7 demands. The FRAME must-win
battery confirms the T7 win predicate is satisfiable, so T7 bounds a real
event.

**One item to log as a follow-up task (not a vacuity defect):**
`T7_frame_bound` is the *conditional* blind-guess bound `≤ 1/|F|` under
the `hobliv` (RO-oblivious) hypothesis, which is materially weaker than
Spec.md T7's unconditional PPT `negl(λ)`. The gap (`q_·/|F|` query terms
via identical-until-bad accounting) is honestly disclosed in the docstring
and `vcvio-gap.md`; it should be tracked as the deferred hard half of T7,
not read as "T7 fully machine-checked."

### Flagged build-checks (I did not run these, per the resource rule)

1. **Confirm no secure T4 instance has a dead challenge.** The
   non-vacuity of `T4_flat_unlinkability` / `unlinkAdvantage_bRerand_eq_zero`
   rests on their `challengeResp` firing on some reachable `GSt`, argued
   above from the shared instance-generic machinery and the
   parallel `..._init` firing lemmas. To make this airtight in-tree rather
   than by-analogy, add (and `lake build`) a one-line lemma per secure
   instance mirroring `challengeResp_bStatic_init`, e.g.
   `challengeResp (flatInstance budget) (GSt.init …) b [m] = pure (some […])`
   for `budget ≥ 1` — proving the flat/bRerand challenge fires with a real
   batch, closing the "bit-free ⇒ 0 could be vacuous" residue directly.
2. **Confirm `hobliv` non-triviality in-tree (optional).** Add and build a
   witness instance of `T7_frame_bound` (e.g. the constant-evidence
   adversary) achieving the `1/|F|` bound, to demonstrate the hypothesis
   class is inhabited by a concrete adversary rather than argued in prose.

## T7 vacuity follow-up — 2026-07-10

The `hobliv` discussion above remains an accurate audit of the earlier
conditional theorem, but it is not the final query-bounded endpoint. The
final statement takes an arbitrary `A` with `qb : FrameQueryBounds A` and
concludes

`frameWinProb mclose A ≤ (qb.total + 1)/|F|`

through `T7_frame_query_bound_unconditional`; the composition wrapper is
`T7Certificate.ofQueryBounds`. Neither theorem has a residual `hobliv`,
good-slice, coupling, bad-mass, counting, or averaged-certificate premise.

The repaired claim is non-vacuous for the same structural reasons already
audited: `FrameQueryBounds` is a per-path bound on actual oracle operations,
the in-tree two-probe adversary has a nonzero certificate and a real winning
slice, and broken FRAME schemes still win the same `Slashes` predicate with
probability one. Secret averaging is not an empty-hypothesis trick: it is
the probability space of `frameGame`, which samples `k` uniformly. In
contrast, the pointwise `FrameDeferredSampling` class really is empty for
the recorded two-probe counterexample over sufficiently large fields, and
`frameDeferredSampling_refuted` remains part of the audit surface.

No vacuity verdict here upgrades the theorem to an unformalized claim. A
concrete bound for a certified finite query count does not itself quantify
over PPT adversary families or prove asymptotic negligibility, and the lazy
random-oracle handlers are not a deployed hash instantiation.

**Post-review kernel status (2026-07-10):** the release audit later completed
at source checkpoint `2fe8354`: the fresh Lean 4.30.0 root build completed
3,595 jobs and the final T7/composition/scaling axiom capture used only
Lean's standard axioms. This evidence is recorded independently of the
statement-shape audit rather than inferred from declaration presence.
