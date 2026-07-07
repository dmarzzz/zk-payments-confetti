# Human-gate record

Per the executor contract, the human gates review definitions only. In this
run the gates are executed by independent reviewer agents that did not write
the artifact under review, per the operator's instruction to simulate the
human gate; each round is logged here verbatim-in-summary, and the operator
(dmarz) can re-open any gate by re-reading the artifact against this record.

## Gate B1 — Spec.md theorem statements (M0)

### Round 1 — 2026-07-06, three-lens panel vs Spec.md rev-1: REVISE (3/3)

Panel: (i) adversarial game-definition reviewer, (ii) protocol-fidelity
reviewer (against the egress post + RESEARCH.md + BRIEF.md), (iii)
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

### Round 6 — pending

Rev-6 (MC20 + carve-outs + x ≠ 0) submitted for verification.
