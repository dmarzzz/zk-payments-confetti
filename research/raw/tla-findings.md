# TLA+ findings (tasks C1–C5, M0.5)

Models: `tla/ZkpcFlat.tla` (instantiation A, N=1, escrow/close/dispute
mechanics; C1–C3) and `tla/ZkpcFleet.tla` (N=2..3 gateways, gossip lag,
merge-time evidence, T6 shape; C4). Configs in `tla/*.cfg`, full TLC logs in
`tla/runs/*.log`. TLC 2.20 (tla2tools.jar), `-deadlock`, 4–8 workers.

**Revision history of this file:** first pass modeled Spec.md **rev 2** and
found the close-mechanics hole below; the model was then aligned to
**rev 9** (MC20), which is now `ZkpcFlat`'s default mode
(`CloseMode = "mc20"`). The rev-2 close survives as the reproducible
historical counterexample (`CloseMode = "rev2"` / `"rev2root"`,
`ZkpcFlatLiteralRev2*.cfg`).

---

## 1. FINDING — close-as-final-spend (revs 1–5) unsound. **CONVERGED-WITH-GATE (round 5 → MC20)**

**Status: real protocol bug in the rev-2 `Close` (MC1), found here by model
checking on 2026-07-06 concurrently with gate round 5's adversarial review
of rev-5 (`gates.md`, Round 5, blocking finding
"gap-index understatement"). Two independent methods hit the same hole and
the same repair: this model's proposed unspent-nullifier publication is,
up to mechanics, the MC20-A close-by-unused-enumeration the gate adopted
in rev-6 and hardened through rev-8. Spec.md is now rev 9 and the default
model implements it; no gate re-open needed — the gate got there on its
own.**

`PoolSolvency` (pool never negative) is **violated** in the rev-2 model.
TLC found three adversary routes, all through payer-close. The T1
statement itself (accepted value attributed to k ≤ D) is *not* violated —
the hole is the gap between T1 and pool solvency: the close payout was
keyed to the close *index* j, but nothing forces the indices of accepted
spends to lie below j (the ledger has no verifiable spend count — the
gate's root-cause phrasing).

Mapping to the gate record and rev-9:

| model route | trace | gate/rev-9 counterpart |
|---|---|---|
| Route 2: index-skipping close — spend accepted at idx 1 only, close at j=0, no collision exists, "understating convicts itself" is false | `runs/flat-literalrev2-rootonly.log` (rev2root mode: survives root-rotation-at-close) | = Round 5's **gap-index understatement** (blocking), verbatim. Fixed by MC20-A enumeration: the closer must reveal the nullifiers of its claimed-unused indices; a false claim is disproven by checkpoint bit-match or the settlement U∩RedeemedNF check |
| Route 1: withheld-collision close — close at a double-signed index while withholding the colliding signal until after settlement; `Dispute` needs an open cm, so post-settlement evidence has no venue | `runs/flat-literalrev2.log`, depth 7 | = MC20's **dispute-window mechanics**: the checkpoint dispute + the settlement-time U∩RedeemedNF on-ledger disproof close the timing gap (under MC20 there is no close signal to collide with at all; the lie surface moves entirely into U and is checkable) |
| Route 3: post-close spending — rev-2 close did not remove cm from the tree (MC5 rotated only on slash), so a closed-and-refunded payer keeps spending | (subsumed; reachable in rev2 mode) | = MC20's **eviction at settlement** ("closed and evicted from the tree, root rotates, in-flight tickets die") — the gate's "secondary hole the repair surfaced" |

Historical runs (kept reproducible; C2 task scope MEMBERS={a,z}, D=3C,
B=2, MAXEPOCH=3):

| config | mode | result |
|---|---|---|
| `ZkpcFlatLiteralRev2.cfg` | rev2 (revs 1–5 literal) | **PoolSolvency violated**, Route 1, depth 7, 52s |
| `ZkpcFlatLiteralRev2RootOnly.cfg` | rev2 + root rotation at close submission | **PoolSolvency violated**, Route 2, depth 7, 61s — rotation alone is not a repair |
| `ZkpcFlatLiteralRev2Safe.cfg` (D=2C, B=1, ME=2) | rev2, PoolSolvency excluded | **green** — the other invariants were already clean in the rev-2 state machine |

Difference between this model's original repair sketch and canonical
MC20, for the record: the sketch rejected published-unused nullifiers at
*Redeem* time; MC20 instead allows in-window acceptances (an in-flight
acceptance is structurally un-checkpointable) and bars them at
*settlement/sweep* with the two-sided bar, pricing the residue as the
gateway's acceptance-in-transit exposure with checkpoint cadence as the
gateway's own lever. The default model implements the MC20 semantics,
including the in-window acceptance window (see `SweepSettles`'s barred
disjunct below).

## 2. Rev-9 default model (MC20): all safety invariants green, PoolSolvency included

`ZkpcFlat.cfg` (default; `CloseMode = "mc20"`, MEMBERS={a,z}, Byz={z},
D=2C, B=1, MAXEPOCH=2): **green** — `TypeOK`, `NoOverspend` (T1 shape at
L=0), `NoDoubleAccept`, `SlashOnlyOnRealDoubleSpend` (slashed ⇒ real
double-sign ∨ real false-U-claim — MC20's self-conviction, exculpability
kept), `HonestNeverSlashed`, **`PoolSolvency`** (rev-9 MC16: "pool
solvency is what T1 plus the MC20 sweep bar protect" — now model-checked),
`Conservation`. 2,419,298 states generated, 416,702 distinct, depth 25,
4min25s. `runs/flat-rev9-default.log`.

The MC20 mechanics modeled: U-enumeration close with no close signal;
`falseCk` = pre-close-checkpoint disproof (perfect cadence: checkpoint =
accepted set at the close transaction); window dispute on false claims
(bounty path); **settlement-time U∩RedeemedNF check** voiding + slashing
with `noBounty` (settlement-detected slash has no evidence submitter; the
post-window remainder stays in the pool, rev-8 F8-m4); recorded-U forward
sweep bar; eviction from the tree at settlement; payout
C·|U| + (D − cap·C).

Liveness (C3), `ZkpcFlatLive.cfg` (mc20, D=2C, B=2, MAXEPOCH=1), weak
fairness on the progress-action disjunction: **green** —
`HonestCloseSettles` (an honest closer settles exactly
C·|U| + (D − cap·C) = D − j·C) and `SweepSettles`, stated rev-9-faithfully
as (accepted) ~> (swept ∨ sweep-barred): the barred disjunct is exactly
the priced in-flight exposure of rev-9's honest-limits note — an
in-window acceptance at an index in U, unswept at settlement, is eaten by
the racing gateway, permanently. TLC reaches that branch (Byzantine close
then in-window spend at a claimed-unused index), so the exposure is
model-witnessed, not hypothetical. Run stats in `runs/flat-rev9-live.log`.

## 3. Fleet model (C4): T6 shape holds; both rev-1 counterexamples reproduce on demand

`ZkpcFleet.tla` (unchanged by the rev-9 alignment — close/escrow live in
the flat model): one Byzantine member, N gateways, discrete time, epochs
of length TE, end-to-end lag L (MC11) encoded as guards on `Tick`,
per-epoch budget B per gateway, `GwBind` (MC14) and `MergeEv` (MC17)
switchable.

Invariants: `ExcessBound` — C·(total accepts) ≤ ⌊D/C⌋·C +
N·B·(⌈L/TE⌉+1)·C — and `ConflictSlashed` — a cross-accepted conflicting
pair implies a fleet-wide slash within L of the second acceptance (T6
clauses (i) and (ii)).

Green runs (MC14 + MC17 on):

| config | scope | states (distinct) | depth | time |
|---|---|---|---|---|
| `ZkpcFleet.cfg` | N=2, D=5C, B=1, L=1, TE=1, T≤7 | 1,558,730 | 25 | 14s (re-run in rev-9 pass: `runs/fleet-main-rev9pass.log`) |
| `ZkpcFleetS2.cfg` | N=2, D=3C, B=2, L=2, TE=2, T≤8 | 556,642 | — | 7s |
| `ZkpcFleetS3.cfg` | N=2, D=2C, B=1, L=0, TE=1, T≤4 | 701 | — | 0s |
| `ZkpcFleetN3.cfg` | N=3, D=2C, B=1, L=2, TE=2, T≤6 | 5,848,923 | 26 | 1min26s |

Validation runs (deliberate violations — the model can express the rev-1
attacks, so the green runs are not vacuous):

- **(a) MC14 disabled** (`ZkpcFleetNoBind.cfg`, N=2, D=5C, B=1, L=1,
  TE=1): **ExcessBound violated**, 9s, 850,248 distinct states at stop.
  Trace = the canonical rev-1 counterexample: bit-identical cross-gateway
  replay, one index per epoch, staggered inside each gossip window — both
  gateways accept all five indices (extraction 10C > bound 9C), signals
  never conflict, no evidence ever, no slash (`evKnown = FALSE` at the
  violating state). `runs/fleet-nobind.log`.
- **(b) MC17 disabled** (`ZkpcFleetNoMergeEv.cfg`, N=2, D=3C, B=2, L=1,
  TE=1): **ConflictSlashed violated**, 0s, depth 10. Trace: idx 0 accepted
  at g1 (x=g1) and g2 (x=g2) at t=3 — a genuine conflicting pair — merges
  land silently at t=4, no evidence generated, the clock passes pairT + L
  with `slashed = FALSE`: the one-pair-per-index adversary is never
  slashed and T6(ii) is vacuous, exactly the rev-1 blocking finding.
  `runs/fleet-nomergeev.log`.

Tightness note: at these scopes the T6 bound has slack (max reachable
extraction with MC14 on is ~2·B·(⌈L/TE⌉+1)·C of excess before the forced
slash), so the green runs confirm the bound's direction and run (a)
confirms the model exceeds it when the premise (MC14) is cut. Several
green scopes violate the *deployment condition* f(L) < D (e.g. D=3C with
f=8C) — that condition gates exposure recoverability, not the bound,
consistent with T6's statement.

## 4. Modeling choices / deviations from Spec.md (all deliberate)

1. **Idealized crypto**: signals are records [member, index, payload];
   nf ≡ (member, index); x ≡ payload. Knowledge soundness = only emitted
   signals exist and redeemable tickets satisfy the solvency conjunct;
   evidence validity = two genuinely emitted conflicting signals (forgery
   excluded, per T7's lemma). A Byzantine member can always self-slash.
   MC20's U is structural: distinctness/well-formedness/i<cap are
   proof-enforced, so the only expressible lie is claiming a spent index
   unused.
2. **Flat model tickets carry no epoch stamp** (Redeem check 3 collapses;
   the budget counts against the redeem-time epoch). Over-approximates
   acceptance (safety-safe). Epoch/lag mechanics are in the fleet model.
3. **Check 4 is trivial at N=1**; gateway binding is exercised in the
   fleet model (it IS the `GwBind` switch).
4. **Check order verified against rev-9**: budget check (5) strictly
   before nullifier logic (6); the rate counter increments on accepts
   only. The model matches. Residual observation (unchanged in rev-9): an
   over-budget presentation of a *conflicting* signal is a plain reject
   and produces no protocol-mandated evidence; the model gives the
   gateway the permissionless-`Dispute` power over signals it has seen,
   which covers it. Worth one spec sentence eventually; not
   safety-relevant in any run.
5. **Honest spends use one fixed payload**; Byzantine members choose from
   two (enough to double-sign).
6. **τ and Δ are collapsed**: window expiry is an explicit action; the
   MC16 monitoring duty = "no gateway-known dispute pending" as an expiry
   guard plus fairness on the dispute actions. Checkpoint cadence is
   perfect (checkpoint = accepted set at the close transaction); the
   tardy-gateway residual loss of rev-9's cadence note is therefore not
   reachable in-model, but the racing (in-flight) exposure is — see
   `SweepSettles`.
7. **State reduction**: the gateway forgets presented tickets that were
   neither accepted nor in conflict with anything previously observed
   (plain rejects / bit-identical duplicates leave no trace and can be
   re-presented). Removes a dead state dimension (the unreduced rev-2 run
   exceeded 60M states without converging). Evidence pairs where neither
   signal was ever accepted or public are not retained — dropping them
   only removes slashings of the adversary, i.e. is adversary-favorable.
8. **MC4 documented-conflict claims** cannot arise at N=1; the fleet
   model covers cross-gateway conflict accounting via `ExcessBound`, and
   deliberately omits the escrow pool (the flat model owns it).
9. **Byzantine rev2-mode close index bounded** to 0..⌊D/C⌋ (payout
   flooring for overstated closes not modeled; historical mode only).
10. **Scopes**: violations logged at the C2 task scope (MEMBERS=2, D=3C,
    B=2, MAXEPOCH=3); exhaustive green runs at D=2C (safety: B=1,
    MAXEPOCH=2; liveness: B=2, MAXEPOCH=1 — epoch dynamics are irrelevant
    to the C3 properties and B=cap keeps full extraction reachable). All
    close/dispute/claim/bar mechanics are reachable at these scopes.
    Liveness fairness is a single WF on the disjunction of progress
    actions (each strictly decreases a finite settlement measure and
    never re-enables itself, so no starvation; per-action WF blew up the
    liveness tableau).

## 5. Consequences for D1 (Lean state model)

- Model `Close` per rev-9 MC20-A (U-enumeration, checkpoint dispute,
  two-sided sweep bar, `noBounty` settlement-detected slash, eviction at
  settlement). The TLA+ default mode is the executable reference.
- Pool solvency is its own invariant (rev-9 MC16 wording already reflects
  this: T1 *plus the MC20 sweep bar*); at model scope it is now checked,
  with the settlement-time U∩RedeemedNF check load-bearing.
- Exculpability's statement widens under MC20: slash ⇐ real double-sign
  ∨ real false-unused-claim. The model's `SlashOnlyOnRealDoubleSpend`
  carries both disjuncts; T3/T7's Lean statements should too.
- The accepted-value invariant (T1), no-double-accept, and the T6 bound
  shape survived adversarial model checking unchanged — safe to formalize
  as stated.
