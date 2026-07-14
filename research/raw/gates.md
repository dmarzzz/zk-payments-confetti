# Definition-gate record (agent simulation; human acceptance pending)

Per the executor contract, the human gates review definitions only. In this
run, independent reviewer agents that did not write the artifact simulated
those reviews; each round is logged here verbatim-in-summary. Historical
`SIGN-OFF` labels below mean **agent-review sign-off only**. They do not
satisfy `BRIEF.md`'s requirement that at least one non-author human review the
M0 statements, nor the human B1/B3/K1 tasks. No such human approval is logged
here, so those acceptance gates remain pending.

## Gate B1 — Spec.md theorem statements (M0)

### Round 1 — 2026-07-06, three-lens panel vs Spec.md rev-1: REVISE (3/3)

Panel: (i) adversarial game-definition reviewer, (ii) protocol-fidelity
reviewer (against the egress post + ../processed/field-report.md + BRIEF.md), (iii)
theorem-statement/arithmetic reviewer. Independent contexts; none saw the
others' findings.

**Blocking findings (all fixed in rev-2):**

1. **T6 false via bit-identical cross-gateway replay** (found independently
   by all three lenses). A replayed ticket produces no (x, x′) conflict,
   never starts the slash clock; per-index private L-windows accumulate
   excess ≈ (N−1)·D against a claimed bound of r·L·C. Numerical witnesses:
   N=3, b=100, T_e=1d, L=1min, D=1000C → excess 2000C vs bound ~0.2C;
   N=10, D/C=100 → 900C vs ~2.8C. **Fix: MC14 gateway-bound messages**
   (m = (G, m̂), Redeem check 4), the payment-layer form of the egress
   post's own "bind the message to the target" note. This is the run's
   canonical wrong-definition-nearly-proved case.
2. **T4 UNLINK unsatisfiable as written** (game lens; statement lens
   concurring with the same three distinguishers). Post-challenge oracles
   leak the bit against every scheme including sound ones: O-retry replays
   the challenge ticket verbatim; solvency-exhaustion probing detects which
   candidate's index advanced; O-close publishes the spend count j.
   B-rerand fails its own calibration under the rev-1 game. **Fix: MC15
   challenge-terminated game**, b sampled at game start (⊥-branch
   advantage well-defined, contributes exactly 1/2), calibration
   distinguisher rewritten to equal-totals ciphertext bit-matching
   (verified end-to-end by the game reviewer against the fixed game).
3. **Merge-time evidence generation missing** (statement lens). Evidence
   was only produced by Redeem-on-ticket; a staggered one-conflicting-pair-
   per-index adversary was never slashed; T6's slash clause did not follow
   from the model. **Fix: MC17** — gateways emit evidence on merging
   conflicting tuples; required protocol behavior.
4. **Refund receipts not channel-bound** (statement lens, T1-B). Honestly
   issued receipts farmed on channel 1 splice into channel 2's solvency
   proofs; R grows unboundedly (solvency degenerates to C_max ≤ D at c≈0).
   **Fix: MC7 expansion** — ciphertexts encrypt (H_tag(k), R); the spend
   relation proves tag-witness consistency; T1-B's proviso now reads
   "honestly issued to this channel."

**Major findings (all fixed in rev-2):** sweep front-running (payer sweeps
its own tickets; fix: MC16 gateway-authenticated sweeps); pooled-escrow
accounting implicit (fix: MC16 explicit commingled pool + payee monitoring
duty); receipt witness gap (payer cannot prove solvency without increment
randomness; fix: MC7 receipts carry r′); T6 discrete bound off by an epoch
straddle (fix: N·b·(⌈L/T_e⌉+1)·C); L defined gossip-only but used
end-to-end (fix: MC11 end-to-end redefinition); "attacker's net never
positive" unprovable (fix: replaced by boundedness + recoverable-exposure
claim); D_residual undefined (fix: dissolved into MC16 window claims);
T5's O(Δ) not formal (fix: exact t+Δ+τ, automatic settlement pinned, roles
split); T4 ⊥-branch advantage ill-defined (fix: b sampled up front);
FRAME lacks the close signal (fix: O_close added; T3's clause and T7 now
share one exculpability lemma); "no valid evidence exists" literally false
(fix: computational phrasing); ℕ-vs-F_p sort confusion (fix: §1 sorts
paragraph); genesis receipt unspecified (fix: MC7 genesis at Open);
single-signal hiding does not follow from standard PRF security (KDM-style
key use; fix: named assumption `single_signal_hiding` in §5.3).

**Minor findings (fixed):** MC1 relabeled [repair]; root-freshness
semantics pinned (current root only, staleness noted in MC5); rate counter
increments on accept only; relationship anonymity added to out-of-scope;
R_close has no solvency conjunct (stated); omarespejel
settlements-vs-spends transposition acknowledged in MC7; T2/T5 circular
cross-citation dissolved (T2 carries its own deadline); T6 baseline
tightened to ⌊D/C⌋·C; corrupt payers' no-interaction-surface remark added
to UNLINK.

**Reviewer conclusions endorsed without change:** T1-flat arithmetic sound
(no off-by-one, D non-multiple-of-C traced); T3 close-index arithmetic
sound (close signal uncharged at index j); MC6 epoch-freshness does not
smuggle weakness (adversarial probe failed to construct a
cross-epoch-linkable scheme that passes); MC3, MC8–MC10, MC12 stand as
faithful; proof order T1 → exculpability lemma → T2/T3 → T5 → T6 → T4 → T7.

### Round 2 — 2026-07-06, fresh reviewer vs Spec.md rev-2: REVISE

Every round-1 finding verified genuinely fixed (all 4 blocking re-derived —
the reviewer walked the rev-1 adversary schedules against the repaired
protocol and could not break T6/T4/T7's cores; the rewritten equal-totals
B-static calibration distinguisher was re-verified end-to-end). New
findings, all in the repair periphery:

- **NEW-1 (blocking):** instantiation B's pooled escrow does not conserve
  funds — per-nullifier sweeps at C_max PLUS refund-bearing close pays
  D + R out of a D deposit, and pre-slash unattributability blocks
  per-channel netting; T2-B/T3-B/pool-solvency jointly unsatisfiable.
  **Fix (rev-3): MC18** — B settles once, at close: payer gets
  (D+R) − j·C_max, payee gets j·C_max − R = Σc at the same event
  (conserves exactly D by construction); no nullifier sweeps in B; silent
  payers handled by force-close-with-forfeit after a response window.
- **NEW-2 (blocking):** post-slash, k is public, so the claim that T7's
  lemma protects the claims window from gateway forgery is false — a
  registered gateway can mint conflicts and old-root proofs freely.
  **Fix (rev-3): MC19** — per-epoch on-ledger checkpoints of accepted-set
  commitments; window claims verify against a pre-slash checkpoint; false
  justification sentence deleted; claim seniority pinned (sweeps before
  conflicts, pro-rata within class).
- **NEW-3 (major):** T6's "recoverable whenever f(L) < D" over-claimed —
  exhaust-then-burst leaves a near-zero remainder; recovery is
  remainder-capped and the operational lever is sweep cadence. Fixed in
  T6 and T2's fleet scope note.
- **NEW-4..7 (minor, all fixed):** B-static genesis anchor upgrades the
  break to first-spend identity linkage (acknowledged in §4); sk_E stated
  as not output at Setup; T4 freshness restated as a challenge-time
  predicate; sweeps verify R_spend specifically (close signals not
  sweepable); EUF-CMA usage list includes T2-B.
- Wording nit on §1's L clause (ii) fixed (covers Redeem-time and
  merge-time evidence).

### Round 3 — 2026-07-06, fresh reviewer vs Spec.md rev-3: REVISE

All rev-2 findings verified genuinely fixed (MC18 conservation arithmetic
re-derived; MC19's core post-slash-minting attack confirmed closed; NEW-3
remainder capping and all four minors verified). Three new majors, all in
the MC18/MC19 second-order periphery, all with local fixes:

- **R3-1 (major):** nothing enforced R ≤ j·C_max at B's close — a payee
  colluding with a corrupt payer signs inflated R and the close drains
  other channels' deposits from the commingled pool. Fix (rev-4):
  R_close^B verifies R ≤ j·C_max as a conjunct (harmless to honest payers).
- **R3-2 (major):** MC18's "no sweeps in B" left the slash path uncovered —
  a B payer could consume service, self-slash, and collect the remainder
  as its own bounty (the exact race MC4 closed in A). Fix (rev-4): B
  retains slash-window per-nullifier claims at C_max against pre-slash
  checkpoints; no double-pay since a frozen channel never closes; T2-B
  scoped to cover the slash path.
- **R3-3 (major):** per-epoch checkpoint cadence left every L-window
  conflict un-checkpointed at slash time whenever L < T_e, hollowing out
  MC19's recovery. Fix (rev-4): checkpoint at any time (≥ once/epoch);
  checkpoint cadence named as a recovery lever; T6/T2 recovery clauses
  conditioned on checkpoint freshness.
- Minors R3-4..R3-9 (all fixed in rev-4): τ > Δ constraint stated + payer
  ledger-monitoring duty; T2-B "cooperative" defined as a transcript
  predicate (≥ Σc, equality iff latest receipt at true count); status
  header updated; provenance rows for MC18/MC19; T5 payee clauses labeled
  per instantiation + B force-close bound; MC4 seniority aligned; MC19
  honest-limits note (window recovery presumes fleet honesty — collusion
  crowd-out documented for the paper's honest-limits section).

### Round 4 — 2026-07-06, fresh reviewer vs Spec.md rev-4: REVISE (one major)

R3-2..R3-9 verified genuinely fixed and mutually consistent (the B
self-slash race was walked once more under rev-4 mechanics and confirmed
closed modulo checkpoint freshness, which the theorems condition on).
Residuals:

- **F1 (major):** R3-1's cap was one-sided — nothing bounded the close
  index j in B, so a Byzantine payer closing at an arbitrary overstated
  fresh index (undisputable: collides with nothing) made the ledger pay
  the payee j·C_max − R unboundedly beyond the channel's D from the
  commingled pool; the payer-side payout was also negative/undefined in ℕ.
  **Fix (rev-5):** second verified conjunct j·C_max ≤ D + R in R_close^B
  (an honest closer's last spend proved exactly this; full spend-down
  still closes at payout 0); A's close needs no such cap because it pays
  nobody but the closer.
- **F2 (minor, fixed):** no-double-pay wording widened — no close of any
  kind, cooperative or forfeit, executes on a frozen channel; a pending
  ForceClose window is voided by the freeze.
- **F3 (minor, fixed):** §4 settlement bullet restates both caps.
- **F4 (minor, fixed):** seniority provenance tags unified to MC19.

### Round 5 — 2026-07-06, fresh reviewer vs Spec.md rev-5: REVISE (one blocking)

F1's conjuncts verified present, honest-safe (j=0 and full-spend-down
edges walked), and arithmetically sound (payouts in [0,D], sum D). The
Byzantine (j,R) sweep found the run's deepest hole:

- **Gap-index understatement (blocking):** nothing enforces index
  contiguity — solvency is per-index, indices are hidden. A payer skips
  index 0, spends at 1..m, closes at j=0 (smallest UNUSED index, so
  compliant with the strictest reading and colliding with nothing) and
  recovers the full D after consuming service. Falsifies T2's floor in
  both instantiations, voids MC1's self-conviction argument, and (flagged
  in passing) breaks A's "pool retains j·C" sweep-ceiling claim the same
  way. Root cause: the ledger has no verifiable spend count.
  **Fix (rev-6): MC20** — A closes by unused-nullifier enumeration
  (reveal PRF-fresh nullifiers of claimed-unused indices, in-circuit
  well-formedness, false claims disproven by bit-match against pre-close
  checkpoints — which also protect honest closers, since genuinely-unused
  nullifiers are PRF-hidden until the close reveals them); B certifies
  the count in the receipt chain ((tag, R, n), R_spend^B proves
  index = n, contiguity by construction). Closed channels are evicted
  from the tree at settlement (kills post-close ticket replay, a
  secondary hole the repair surfaced). That A and B need structurally
  different repairs is a design-space finding for the paper.
- **T5/F2 consistency (major):** a freeze mid-ForceClose-window voids the
  forfeit, so T5-B's bound needs the freeze carve-out. Fixed in rev-6.
- Minors fixed: "both with equality" wording, MC18 one-cap restatement,
  §2 seniority tag → MC19.

Also folded into rev-6 from the Lean G4 workstream (gate-note): H_x maps
into F_p \ {0} — at x = 0 the signal is y = k, the secret outright;
single_signal_hiding is conditioned on x ≠ 0 (§1, §5.3).

### Round 6 — 2026-07-07, fresh reviewer vs Spec.md rev-6: REVISE (two blocking)

MC20-A's core verified (gap-index closed, checkpoint disputes work,
privacy clean, honest-path conservation exact); MC20-B's contiguity
verified. Two blockings in the periphery:

- **B stale-receipt close (blocking):** the circuit proves j equals the
  count of *some* signed receipt, so a payer with 5 spends closes on its
  n=2 receipt and recovers the later spends' value; the payee cannot
  rebut without attribution. **Fix (rev-7):** B's close also reveals
  $nf_j$ (in-circuit: the nullifier of the first index beyond the
  declared count). Contiguity (MC20-B) makes the reveal decisive: a stale
  receipt's nf_j is an already-used nullifier sitting in a pre-close
  checkpoint → bit-match dispute → void + slash. An honest closer's nf_j
  is PRF-hidden pre-close → unforgeable dispute. The rev-1
  close-as-final-spend self-conviction idea, resurrected soundly on top
  of certified contiguity.
- **A used-but-uncheckpointed claim + sweep double-pay (blocking):** a
  false unused-claim uncaught (stale checkpoint) was paid as refund AND
  remained sweepable — pool paid D + j·C. **Fix (rev-7):** the ledger
  records U at settlement and bars sweeps of nf ∈ U; the pool conserves
  and the tardy gateway bears exactly its un-checkpointed tickets
  (cadence as that gateway's own lever); T2-A conditioned accordingly;
  A gets the symmetric in-flight honest-limits note.
- **Majors fixed in rev-7:** checkpoint pinned as a binding Merkle set
  commitment with membership-witness openings (the honest-closer
  protection argument now has something to bite on); T2-B scoped to
  spends accepted before close inclusion (racing) and the inverted rev-3
  "stale receipt only overpays" parenthetical retracted; §2 Open / §4
  triple formulas (tag, R, n) aligned; R_spend^B gains the index = n
  conjunct in §4's authoritative text; T7/T3/MC16 close-signal dangles
  rewritten to MC20 semantics; MC18 restates both caps + MC20 xref;
  §6 duties include checkpointing; header rewritten (was two revisions
  stale — same class as R3-6, twice; noted for the K-phase process log).

### Round 7 — 2026-07-07, fresh reviewer vs Spec.md rev-7: REVISE

All 19 round-6 checklist items verified present (nf_j reveal, sweep bar,
checkpoint binding, every dangle, header). Two residuals:

- **F7-1 (blocking): the nf_j reveal weaponized by receipt withholding.**
  Receipt supply is adversary-controlled: a payee that accepts-but-
  withholds ρ wedges the honest payer's certified count one behind its
  true count; its only possible close reveals an accepted, checkpointed
  nullifier → disputed → slashed (or forfeited under ForceClose). Worse,
  checkpoints were self-declared, so a payee could checkpoint a merely-
  seen (aborted) ticket; and genesis withholding made j=0 closes
  impossible outright. **Fix (rev-8):** receipt-bearing checkpoint
  entries (full tuple: presented ct*, c, r′, ct′, σ_S(ct′), publicly
  cross-checkable — binds the entry to a payer-produced ticket); a
  stale-close dispute must open the full tuple; a valid dispute does NOT
  slash but opens an upgrade sub-window — the dispute publishes the
  withheld receipt, the closer re-closes one count higher; only failure
  to upgrade slashes; escalation converges at the true count (one count
  per round, by contiguity); honest gap ≤ 1 so honest cost ≤ one C_max
  (already priced by T3 note (i)); j=0 closes carry no receipt conjunct
  (kills the genesis-withholding forfeit).
- **F7-2 (major): sweep bar was one-directional** — sweep-first then
  false-claim still double-paid the pool. **Fix (rev-8):** two-sided:
  settlement checks U against RedeemedNF (on-ledger disproof → void +
  slash, no checkpoint needed) before recording U and barring forward
  sweeps; pool conserves in every ordering.
- Minors: MC20 B-entry now carries the reveal + discipline; MC19 notes
  receipt-bearing B checkpoints; provenance row added; T3/T5 carry the
  close-dispute exculpability and upgrade-round bounds; MC2 B scope
  note; header rewritten as rev-8.

### Round 8 — 2026-07-07, fresh agent reviewer vs Spec.md rev-8: **AGENT SIGN-OFF**

Both round-7 repairs verified with full attack walks: the
receipt-withholding wedge is dead in all three variants (withholding,
fabricated acceptance of a rejected ticket — walked to a zero marginal
delta over accept-and-withhold, inside T3's priced-abort allowance —
and genesis withholding); the upgrade cascade converges at the true
count with each dispute publishing the next round's receipt; the
two-sided sweep bar conserves the pool in every ordering with the
loss-bearer correctly named; no deadlock or double-settlement among the
upgrade sub-window, ForceClose, and the slash freeze. Five ride-along
minors, all applied in the signed text (F8-m1 opening-homomorphism
stated in assumption 5 + Used-by list; F8-m2 T5-B off-by-Δ; F8-m3 T2-B
deadline anchored to the final re-close; F8-m4 settlement-detected
slash remainder stays in the pool; F8-m5 header dangle).

**B1 AGENT-REVIEW GATE: SIGN-OFF on Spec.md rev-8.** The M0 definitions are
frozen for the next agent round.
Any future change to §2/§7/§8 re-opens this gate.

### Round 9 (scoped re-open) — 2026-07-07, rev-9 K4 amendments: pending

The K4 external review (simulated outside cryptographer; report at
k4-external-review.md) found two definitional holes the internal rounds
could not see from inside: (1) the q=1 challenge certifies only
first-spend-per-epoch unlinkability — a second-spend-only tag leak
passes while being lifetime-linkable at the fleet's real usage; (2)
challenge termination blinds the game to close-time content — a close
publishing USED nullifiers would pass. Adjudication: strengthen, not
narrow (the T4 proof had not started; cheapest-ever moment). Rev-9:
session-form challenge (vector of q spends in the fresh epoch; certifies
whole-session unlinkability); CloseView-simulatability obligation in
MC15; calibration battery widened (must-catch index-leak + nf_e-reuse,
must-win degenerate-RLN FRAME adversaries); fund-slash vs identity-slash
taxonomy recorded (close-dispute slashes never publish k). K4 Concerns
3 and 6 (composed deployment statement; slash-publishes-k retroactive
linkage) routed to the paper's honest-limits; Concern 4 disposition:
A's close-dispute exculpability is kernel-checked in the Core layer,
B's upgrade-path safety is spec-level — stated as such in the paper.
Scoped B1 round 9 verifies exactly these deltas.

Round-9 result (2026-07-07): session form PASS (K4 construction walked
to defeat; non-adaptive vector + symmetric capable-for-q noted as
load-bearing), CloseView obligation PASS (minor F9-m1: joint-transcript
judging + NIZK-ZK for π_close), battery PASS (minor F9-m2: add the
multiplicity-tag must-catch), header PASS — and one MAJOR, F9-1: the
slash taxonomy is TRUE but exposed that fund-slashes cannot run the
k-gated settlement machinery: (a) A's checkpoint-dispute slash had no
stated remainder rule (bounty would break conservation — the member's
other used nullifiers can't be enumerated or barred without k); (b) B's
failed-upgrade slash stranded the payee's revenue (R3-2 claims are
k-gated; only nf_j is attributable). REVISE.

### Round 10 — 2026-07-07, rev-10: REVISE (one major)

F9-1a PASS (conservation re-derived on all four per-channel paths; the
no-bounty dispute incentive verified coherent — the disputing gateway
protects its own sweep-bar exposure, duty-as-hypothesis framing stands).
F9-1b PASS (forfeit path walked end-to-end; honest-unreachability chain
complete). F9-m2 PASS. **F10-1 (major):** the rev-10 joint-transcript
sharpening flipped MC15's "both closes satisfy it" to FALSE for B — a
stale close's revealed nf_j bit-matches the member's own transcript
ticket (that match IS the conviction mechanism), and an honest
receipt-deprived payer reaches the path. **F10-m1 (minor):** MC18 still
carried the unscoped pre-rev-10 slash rule.

### Round 11 — 2026-07-07, rev-11: **AGENT SIGN-OFF (final agent revision)**

F10-1 scoping verified with a full mechanics walk (the residue is true:
one spend / one epoch session, via the revealed nf_j matching the
emitted ticket and its nf_e; the upgrade path restores funds, not
privacy — the first close is on-ledger and permanent, and no text
claims otherwise); F10-m1 verified consistent across MC18/§2/T2-B.
Two wording nuances routed to the paper's honest-limits, not the spec:
(i) a payee that declines to dispute keeps the receipt unpublished and
gets the linkage at the cost of only one forgone c ≤ C_max — the
publication prices the payee's recovery, not the linkage; (ii) the
session extension of the linkage requires the ticket transcript, which
in B only the payee holds.

**B1 AGENT-REVIEW GATE: SIGN-OFF on Spec.md rev-11.** Eleven
rounds, six reviewers-equivalent of independent context, every blocking
finding a concrete counterexample, two auxiliary agent audits (K1, K4) and one
independent method (TLC) converging on the same repairs. “Final” here means
the agent-reviewed revision; independent-human acceptance is still pending.

### (superseded round-10 plan entry)

Fixes: A checkpoint-dispute remainder stays pooled, no bounty, ordinary
sweeps continue (extends F8-m4); B slash path scoped to identity-slashes,
fund-slash settles by forfeit of D to the sole payee (proven cheater or
abandoner declined its own published upgrade; mirrors ForceClose-forfeit;
Σc ≤ D conservation-safe); T2-B split accordingly; CloseView obligation
judged jointly with the transcript; multiplicity-tag calibration point.

## Gate K1 — independent-agent statement audit

2026-07-07: **FAITHFUL-WITH-NOTES agent sign-off** (k1-statement-audit.md).
No theorem states less than its docstring; all deltas documented
GATE-NOTEs except one drift finding: FRAME omits cm = H_id(k) from the
adversary view (strictly less information, unacknowledged) — routed to
the games agent with the rev-9 batch. Expected-rework items (T5/Flat on
the pre-MC20 machine, assumption-5 opening-homomorphism, header stamps)
were already in flight.

## Gate K4 — external definition review (simulated)

2026-07-07: **REVISE → adjudicated into rev-9** (see B1 round 9 entry).
Survived angles recorded in the report: bit-first/⊥-accounting, abort
teeth, freshness-as-predicate, adversary-issued genesis, FRAME nfAt
superset, unconditional-tag schemes. The ⊥-branch anonymity accounting
endorsed as field-standard; the gap was missing arithmetic, not wrong
accounting.

## Gate B3 — security-game definitions in Lean (agent review; human acceptance pending)

### Round 1 — 2026-07-07, fresh reviewer vs Framework/Unlink/Frame.lean: REVISE

Verified sound (the cores this gate exists to check): advantage
normalization exactly |Pr[b'=b] − 1/2| with the VCVio factor-of-2 bridge
correct; b sampled before the adversary runs, ⊥-paths contribute exactly
1/2; challenge termination STRUCTURAL (post-challenge guess is a pure
function; all three rev-1 leak channels pre-challenge-only; no residual
channel found); the roA cache-keying question — the adversary querying
the shared random oracle at (k', i) hits an independent slot, so reading
the honest a-values requires already knowing k — clean; FRAME's win
predicate omitting Dispute's side checks is a genuine strengthening; RLN
cross-file algebra consistent; x = 0 handling conservative.

Required before T4/T7 proofs (fix list): **M1** — UnlinkScheme.View drops
π at the definition level, so NIZK-ZK is never exercised and the theorem
would be about a proof-stripped protocol (the exact K2 smell §5 bans);
fix: full ticket in View or a named ZK-bridging lemma obligation, with
root/e disposition stated. **M2** — B's genesis receipt is
challenger-sampled but the payee (= adversary) issues it in the real
protocol; extend the interface or record the WLOG-honest-genesis
obligation; T4-A unaffected. **D1** — Frame's close still emits the
rev-4 close signal (harmless surplus, subsumed by one spend query) but
does NOT expose the MC20 unused-nullifier reveals, which the deployed
adversary sees and cannot derive from any oracle — add an nfAt oracle
(strict superset of any close's reveal). **D2** — Unlink close docstrings
rewritten to MC20 (behavior provably immaterial: closed ⇒
challenge-incapable). **D3** — spec-side dangles: fixed in rev-7.
Minors Mi1–Mi4 recorded (nf_e omission in FRAME + named proof
obligations), recommended not gating.

### Round 2 — 2026-07-07: **AGENT SIGN-OFF** on the M1/M2/D1/D2 fixes

zkBridgeObligation verified as the correct bridging Prop (right shape,
right direction, discoverable); adversary-issued genesis walked incl.
the asymmetric-malformed case (⊥ structurally b-independent); nfAt
verified as a strict superset of any MC20 reveal with no new line
points; close docstrings MC20-faithful with the lastSig no-op argument
airtight; no regressions in the round-1 verified cores; O1–O3 register
approved as the right residual obligations.

### Round 3 — 2026-07-07: **AGENT SIGN-OFF** on the rev-9 batch (session form,
O4, FRAME cm)

Session challenge: non-adaptivity STRUCTURAL (one-move List submission,
closed spendBatch fold, no mid-batch views); capable-for-q both-checked
before b is consulted; unfaithful-instance mid-batch ⊥ covered by the
O2 obligation, explicit. O4 adjudicated SUFFICIENT: the per-state
marginal form subsumes rev-10's joint-transcript judging (close coins
fresh given state; two-states-same-summary separation gives the
exclusion teeth; F10-1 is the empirical confirmation). FRAME cm: roId
keyed at the preimage, no new k-extraction channel. Minors O4-a..d
(docstring/register syncs, incl. aligning O4's satisfaction text to
rev-11's true-count scoping) routed to the H-phase alongside instance
work. **The T4/T7 proof phase is unblocked.**

### Round 4 — 2026-07-09: **FINDING** — the pointwise deferred-sampling
certificate is unsatisfiable (T7 composition layer)

`FrameDeferredSampling` (Zkpc/Games/T7.lean) demands one secret-independent
`idealEvidence` dominating the real conditional slash probability
**pointwise in `k`** up to `qb.total/|F|`. Kernel-checked refutation
(`Zkpc/Games/FrameDeferred.lean`, `frameDeferredSampling_refuted`): the
two-probe adversary (`roId` at constants `c₁ ≠ c₂`, budget `qId = 2`,
`total = 2`) wins with probability `1` at `k = c₁` and `≥ 1 − 1/|F|` at
`k = c₂`; since `Slashes c₁ ·` and `Slashes c₂ ·` are disjoint evidence
events, any single generator can grant the two slices total mass at most
`1`, forcing `|F| ≤ 5`. So no certificate exists over any field with more
than five elements. The game definitions and `Spec.md` T7 are untouched:
the flaw is only in the *shape* of the (unconsumed-in-any-final-theorem)
certificate structure, whose pointwise `close` field was strictly stronger
than what `T7_frame_query_bound` needs. Corrected socket landed in the
same file: `FrameDeferredSamplingAvg` states the comparison averaged over
the uniform secret (exactly what the FRAME experiment produces and what a
lazy-ROM identical-until-bad argument yields), `T7_frame_query_bound_avg`
composes it to the full corrected bound `(qb.total + 1)/|F|`, and
`FrameDeferredSampling.toAvg` proves the averaged form is implied by the
pointwise one, so the composition endpoint loses nothing. The remaining
open T7 work is constructing `FrameDeferredSamplingAvg` from `frameImpl`
for query-bounded adversaries.

### Round 5 — 2026-07-10: **RESOLUTION SHAPE ACCEPTED BY AGENT REVIEW; RELEASE EVIDENCE PENDING**

The Round-4 finding is preserved: the pointwise certificate remains
refuted and must not return as the advertised endpoint. The repair closes
the statement in the probability space the game actually uses. For every
`A` with `qb : FrameQueryBounds A`,
`T7_frame_query_bound_unconditional` concludes the secret-averaged bound
`frameWinProb mclose A ≤ (qb.total + 1)/|F|`, and
`T7Certificate.ofQueryBounds` exposes the same result at the composition
boundary. Neither statement accepts a residual good-slice, coupling,
bad-mass, counting, `hobliv`, or deferred-sampling premise.

The accepted architecture is:

1. `frameGoodSliceTransfer_of_tape` discharges the general good slice;
2. `dsBadMassLe_of_queryBounds` discharges the adaptive deferred-slope
   count, which `frameRealBadMassLe_of_dsCount` transports to the real bad
   mass;
3. `frameDeferredSamplingAvg_holds` assembles the corrected averaged
   certificate; and
4. `T7_frame_query_bound_avg` yields the public endpoint.

Scope condition: this is a concrete finite-query/finite-field inequality in
the ideal random-oracle model. It does not itself classify PPT adversaries or
establish the scaling facts needed for asymptotic negligibility, and it does
not instantiate a deployed hash. A separate scaling wrapper can only transfer
the bound under explicit per-parameter query and field-growth/negligibility
hypotheses.

Gate status remains **pending**, not sign-off, until a final clean build and
axiom audit are attached. No SHA, command result, or axiom output is
asserted by this entry.

#### Technical-validation addendum — source checkpoint `2fe8354`

The pending release-evidence status in Round 5 is preserved above as the
status when that agent review concluded. It was subsequently closed for the
proof-bearing source at checkpoint `2fe8354`: in a fresh clone, the pinned
cache restore fetched 8,283 files and the full root build succeeded on Lean
4.30.0 after 3,595 jobs. Explicit `#print axioms` output covered the full T7
route, both `T7Certificate` constructors, both flat/refund end-to-end
wrappers, both `FrameAsymptotic` theorems, five `ElGamal.lean` endpoints, six
`ReceiptMac.lean` endpoints, and one `AuthenticatedFleet.lean` endpoint.
Every captured declaration used only a subset of `propext`,
`Classical.choice`, and `Quot.sound`.

Project `rg` scans found no `sorry`, `admit`, or `native_decide`, and no
`axiom` outside `Zkpc/Assumptions.lean`; `git diff --check` was clean. The
exact final PR head will be recorded externally after the
documentation/PDF-only release commit. That SHA handoff is release
bookkeeping, not pending
proof evidence. This technical completion does **not** satisfy or replace any
human-review gate.

## Current acceptance status

- **B1 human gate:** pending; eleven independent-agent rounds are recorded,
  but no non-author human sign-off is logged.
- **B3 human gate:** pending; five agent rounds are recorded, including the
  T7 pointwise-certificate finding and repair review.
- **K1 human component:** pending; the recorded K1 report is agent-run.
- **K4 outside-cryptographer task:** pending if the full task ledger is to be
  closed; the recorded K4 exercise is explicitly simulated.
- **T7 technical release evidence:** complete for proof-bearing source
  checkpoint `2fe8354`; the exact final PR head after the
  documentation/PDF-only release commit is an external release record, not
  pending proof evidence.

## Gate series v2 — PROTOCOL.md (the nullifier-chain design of record)

Opened 2026-07-14. The rev-11 series above is closed as historical; its
sign-offs do not transfer to the new object. Round-0 findings, from the
re-baseline review (five-analyst swarm plus synthesis, 2026-07-14):

- **G1 — signature channel-binding.** The spec must state exactly what
  Bob signs; it must bind channel id and recipient, or cross-channel
  signature splicing rebuilds the rev-1 attack shape against the
  no-overspend analogue.
- **G2 — withheld-countersignature wedge (critical path).** Alice reveals
  `N_{i+1}`, Bob refuses to countersign: closing on the parent state is
  forfeit-bait while the child was never accepted. Legality of closing on
  an unsigned-but-proof-valid state is undefined. Genuine design work; no
  repair stated in `PROTOCOL.md`.
- **G3 — challenge-window duration.** Bob's post-close challenge window is
  unspecified.
- **G4 — close-time commitment verification.** What the close path proves
  about the committed balance is unspecified.
- **G5 — forfeit-all proportionality.** Entire-deposit forfeiture in
  honest-limit edge cases needs a stated accounting rule; interacts with
  G2.

Freeze rule unchanged from the rev-11 series: Spec-v2 is drafted, then
adversarially reviewed B1-style round by round (every blocking finding a
concrete counterexample) until a full round produces no blocking finding,
then frozen before the proof campaign starts.
