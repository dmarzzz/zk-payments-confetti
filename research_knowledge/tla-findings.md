# TLA+ findings (tasks C1–C5, M0.5)

Models: `tla/ZkpcFlat.tla` (instantiation A, N=1, escrow/close/dispute
mechanics; C1–C3) and `tla/ZkpcFleet.tla` (N=2..3 gateways, gossip lag,
merge-time evidence, T6 shape; C4). Configs in `tla/*.cfg`, full TLC logs in
`tla/runs/*.log`. TLC 2.20 (tla2tools.jar), 8 workers, `-deadlock`.

Source of truth: `Spec.md` revision 2. Every deviation between the model and
the spec text is listed in §4.

---

## 1. FINDING-FOR-LEAN — MC1 close-as-final-spend is unsound as written

**Status: real protocol bug in Spec.md §2 (`Close`, MC1), not a modeling
artifact. Recommend re-opening the B1 gate for a rev-3 of MC1. The Lean
state model (D1) must NOT transcribe MC1 as written.**

`PoolSolvency` (pool never negative — the property §2/MC16 assigns to T1:
"Pool solvency is exactly what T1 protects") is **violated** in the literal
model. TLC finds three distinct adversary routes, all through payer-close.
The T1 statement itself (accepted value attributed to k ≤ D) is *not*
violated — the hole is precisely the gap between T1 and pool solvency: the
close payout is keyed to the close *index* j, but nothing forces the
indices of accepted spends to lie below j.

### Route 1 — withheld-collision close (`runs/flat-literal.log`, depth 7, D=3C)

1. `Open(z)` (pool = 3) →
2. z emits spend signal at idx 0, **never delivers it** →
3. z closes at j = 0 (close signal at idx 0 — a genuine double-sign, but
   the gateway has never seen the colliding spend, so `ExpireCloseWindow`'s
   no-evidence guard passes) →
4. window expires, automatic payout D − 0·C = 3 (pool = 0) →
5. z **now** delivers the withheld idx-0 spend: `Redeem` accepts (cm is
   still in the tree — MC5 rotates the root only on slash; nf fresh) →
6. gateway sweeps: pool = **−1**.

The spec's argument "closing at an already-spent index collides with an
existing signal and is slashable" fails on *timing*: the colliding signal
can surface after settlement, and `Dispute` requires "some **open** cm in
the tree" — a closed channel has no dispute venue. Evidence exists;
recourse does not.

### Route 2 — index-skipping close (`runs/flat-rootonly.log`, depth 7, D=3C)

1. `Open(z)` → z emits at idx 1 **only** (the solvency conjunct
   (i+1)·C ≤ D constrains the index *value*, not sequentiality — a payer
   need never have emitted indices 0..i−1) →
2. idx-1 spend delivered and accepted →
3. z closes at j = 0. This is NOT a double-sign — no signal at idx 0
   exists at all, so "understating convicts itself" is simply false for an
   index-skipping payer →
4. payout 3, then sweep of the accepted idx-1 ticket: pool = **−1**.

This route survives `RepairRoot` (close rotates the root at submission):
the acceptance predates the close. It kills the §2 claim "the pool retains
j·C from that close, which is exactly the ceiling on what can still be
swept" — here the close retains 0 and C is swept.

### Route 3 — post-close spending (subsumed by Route 1's mechanism)

Close does not remove cm from the tree (MC5 rotates only on slash) and
`Redeem` cannot check channel status (tickets are unattributable by
design). So a payer can close at j = 0 (collect D) and *then* emit and
deliver fresh spends at idx 0..⌊D/C⌋−1; all verify against the current
root and get accepted and swept: extraction up to 2D per channel. Maximum
combined extraction (skip idx 0, spend the rest, close at 0): 2D − C.

**Who pays:** the payee still settles (T2 holds); the deficit is drawn
from the commingled pool, i.e. from *other members' deposits* — honest
payers' close payouts and T3/T5 floors are eventually unfunded. At
MEMBERS=2 the honest member's deposit is the victim.

### Model-verified repair candidate ("unspent-nullifier publication")

`RepairUnspentNf` flag in `ZkpcFlat.tla`: payer-close at index j
additionally publishes the nullifiers of all unclaimed indices
nf_i = H_nf(H_a(k,i)) for i ∈ [j, ⌊D/C⌋) (provable in zero knowledge from
k; O(D/C) proof size). Ledger semantics:

- `Redeem`/sweep reject any nullifier published unspent-at-close;
- a gateway holding an *accepted* tuple whose nf the closer declared
  unspent presents it during the window as documented close-fraud
  evidence → the closer is convicted and the close-payout cancelled
  (Route 2 and pre-close variants of Route 1);
- post-settlement deliveries of published nullifiers are inert (Routes 1
  and 3).

Privacy note: an honest closer's published unspent nullifiers were never
emitted anywhere, are pseudorandom, and link to nothing (same epistemic
status as the spend-count leak already accepted in MC15).

TLC results at MEMBERS={a,z}, D=3C, B=2, MAXEPOCH=3 (violations) and
D=2C, B=1, MAXEPOCH=2 (exhaustive green):

| config | repairs | result |
|---|---|---|
| `ZkpcFlat.cfg` (D=3C) | none (literal Spec.md) | **PoolSolvency violated**, Route 1, depth 7, 0s |
| `ZkpcFlatRootOnly.cfg` (D=3C) | RepairRoot only | **PoolSolvency violated**, Route 2, depth 7, 1s — root rotation at close is insufficient |
| `ZkpcFlatRepaired.cfg` (D=2C) | RepairUnspentNf only | **all invariants green**, 218,198 distinct states, depth 25, 12s |

The repair needs its own MC entry and review — it is new protocol in the
same category as MC1/MC4; the model checks its state-machine consequences,
not its ZK realizability (the publication proof is standard, but that
judgement is the reviewer's).

## 2. Everything else in the flat model is clean

`ZkpcFlatSafe.cfg` (literal model, PoolSolvency excluded; MEMBERS={a,z},
Byz={z}, D=2C, B=1, MAXEPOCH=2): **green** — `NoOverspend` (T1 shape at
L=0), `NoDoubleAccept`, `SlashOnlyOnRealDoubleSpend` (a slashed member
really emitted two conflicting signals; exculpability/T7 shape),
`HonestNeverSlashed`, `Conservation` (money conservation), `TypeOK`.
2,213,170 states generated, 306,902 distinct, depth 25, 17s.

Liveness (C3), `ZkpcFlatLive.cfg` on the repaired model (D=2C), weak
fairness on the honest-infrastructure progress actions: **green** —
`HonestCloseSettles` (a closing honest payer eventually settles exactly
D − j·C) and `SweepSettles` (every accepted ticket is eventually settled
to the gateway, through the sweep or the slash-window claim path).
218,198 distinct states, 9 temporal branches, 4min04s.

Note the interplay that makes `SweepSettles` true: slash-window claims
never starve at N=1 because the remaining deposit D − C·|redeemed(m)|
always covers the member's outstanding accepted tickets (accepted nf are
distinct indices ≤ ⌊D/C⌋). This is the T2 arithmetic and it checks out.

## 3. Fleet model (C4): T6 shape holds; both rev-1 counterexamples reproduce on demand

`ZkpcFleet.tla`: one Byzantine member, N gateways, discrete time, epochs
of length TE, end-to-end lag L encoded as guards on `Tick` (merges land by
accept-time + L; once evidence exists the slash is effective by
pair-time + L), per-epoch budget B per gateway, `GwBind` (MC14) and
`MergeEv` (MC17) as switchable constants.

Checked invariants: `ExcessBound` — C·(total accepts) ≤ ⌊D/C⌋·C +
N·B·(⌈L/TE⌉+1)·C — and `ConflictSlashed` — a cross-accepted conflicting
pair implies a fleet-wide slash within L of the second acceptance (T6
clauses (i) and (ii)).

Green runs (MC14 + MC17 on):

| config | scope | states (distinct) | depth | time |
|---|---|---|---|---|
| `ZkpcFleet.cfg` | N=2, D=5C, B=1, L=1, TE=1, T≤7 | 1,558,730 | 25 | 14s |
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
  never conflict, no evidence ever, no slash, `evKnown = FALSE` at the
  violating state. `runs/fleet-nobind.log`.
- **(b) MC17 disabled** (`ZkpcFleetNoMergeEv.cfg`, N=2, D=3C, B=2, L=1,
  TE=1): **ConflictSlashed violated**, 0s, depth 10. Trace: idx 0 accepted
  at g1 (x = g1) and at g2 (x = g2) at t=3 — a genuine conflicting pair —
  merges land silently at t=4, no evidence generated, clock passes
  pairT + L with `slashed = FALSE`: the one-pair-per-index adversary is
  never slashed and T6(ii) is vacuous, exactly the rev-1 blocking finding.
  `runs/fleet-nomergeev.log`.

Tightness note: at these scopes the T6 bound has slack (max reachable
extraction with MC14 on is ~2·B·(⌈L/TE⌉+1)·C of excess before the forced
slash, well under f(L) + entitlement), so green runs confirm the bound's
direction, and run (a) confirms the model can exceed the bound when the
premise (MC14) is cut. Also note: several green scopes violate the
*deployment condition* f(L) < D (e.g. D=3C with f=8C) — that condition
gates exposure *recoverability*, not the bound itself, consistent with
T6's statement.

## 4. Modeling choices / deviations from Spec.md (all deliberate)

1. **Idealized crypto**: signals are records [member, index, payload];
   nf ≡ (member, index); x ≡ payload. Knowledge soundness = only emitted
   signals exist and redeemable tickets satisfy the solvency conjunct;
   evidence validity = two genuinely emitted conflicting signals (forgery
   excluded, per T7's lemma). A Byzantine member can always self-slash.
2. **Flat model tickets carry no epoch stamp** (Redeem check 3 collapses;
   the rate budget counts against the redeem-time epoch). This
   over-approximates acceptance (safety-safe). Epoch/lag mechanics are
   modeled properly in the fleet model.
3. **Check 4 is trivial at N=1**; gateway binding is exercised in the
   fleet model (it IS the `GwBind` switch).
4. **Honest spends use one fixed payload**; Byzantine members choose from
   two (enough to double-sign). Message content is otherwise irrelevant.
5. **τ and Δ are collapsed**: window expiry is an explicit action; the
   MC16 monitoring duty is the guard "no gateway-known evidence" on close
   expiry plus fairness on `GwDispute`, and "claims before bounty" on
   slash-window expiry.
6. **State reduction**: the gateway forgets presented tickets that were
   neither accepted nor in conflict with anything previously observed
   (plain rejects / bit-identical duplicates leave no trace and can be
   re-presented). Removes a dead state dimension (the unreduced literal
   run exceeded 60M states without converging; reduced runs converge in
   seconds). Consequence: evidence pairs where *neither* signal was ever
   accepted or public are not retained — such pairs only enable extra
   slashing of the adversary, so dropping them is adversary-favorable.
7. **Spec observation (minor, worth a rev-3 sentence)**: Redeem's check
   order puts the budget check (5) before nullifier logic (6), so an
   over-budget presentation of a *conflicting* signal is a plain reject
   and produces no protocol evidence. The gateway saw a slashable signal
   and the protocol mandates nothing. Permissionless `Dispute` lets it act
   anyway (the model gives the gateway that power), but the spec should
   either say evidence generation is unconditional on budget or swap
   checks 5/6.
8. **MC4 documented-conflict claims** cannot arise at N=1 (RedeemedNF
   entries come from the same gateway's own tuples); the fleet model
   covers the cross-gateway conflict accounting via `ExcessBound`, and the
   fleet model deliberately omits the escrow pool (flat model owns it).
9. **Byzantine close index bounded** to 0..⌊D/C⌋ (an overstating close
   with j > ⌊D/C⌋ would need payout flooring at 0 — the spec's "overstating
   only donates" needs a max(0, ·); noted, not modeled).
10. **Scopes**: violations logged at the task scope (MEMBERS=2, D=3C,
    B=2, MAXEPOCH=3); exhaustive green runs at D=2C, B=1, MAXEPOCH=2 to
    stay in the minutes budget (all mechanics — skip-route, disputes,
    claims, budget saturation, epoch reset — still reachable at that
    scope). Liveness fairness is a single WF on the disjunction of
    progress actions (each strictly decreases a finite settlement measure
    and never re-enables itself, so no starvation; per-action WF blew up
    the liveness tableau).

## 5. Consequences for D1 (Lean state model)

- Model `Close` with the unspent-nullifier publication (or whatever rev-3
  of MC1 lands on) — **not** the rev-2 text. Without it, D1's transition
  system makes pool solvency unprovable and T3/T5's funding assumption
  false.
- Pool solvency must be stated as its own invariant, not derived from T1;
  the gap between "accepted value ≤ D" and "pool ≥ 0" is exactly where the
  MC1 bug lives.
- The accepted-value invariant (T1), no-double-accept, exculpability, and
  the T6 bound shape all survived adversarial model checking unchanged —
  safe to formalize as stated.
