# Spec-v2 gate round 1 (2026-07-18): two adversarial reviews

Run against `Spec-v2.md` draft round 1 (post A1-A5 acceptance) by two
independent review agents, one targeting safety, one targeting
anonymity/linkage. Findings distilled into `Spec-v2.md` section 11 as
F-R1-1..F-R1-5; this file is the unabridged record.

Verdicts: safety review found no Bob-theft on any probed surface; one
liveness/hypothesis defect (F-R1-1, sibling double-send self-wedge),
repaired by the normative frontier-injectivity rule. Privacy review found
the close-split subset-sum linkage (F-R1-2, anonymity claim rescoped to
unlinkable-until-close), the root-choice fingerprint (F-R1-3, epoch-root
rule), the challenge-tuple disclosure (F-R1-4), and the leak-composition
gap (F-R1-5).

---

## Review A: safety

I have everything I need. My analysis is complete.

# Adversarial Review: Spec-v2 Payment-Channel Safety/Liveness

## Bottom line

I found **no Bob-theft** on any probed surface: under the rules as written (with the stated crypto assumptions), a cheating Alice cannot settle for less than Bob's earned balance without a valid challenge witness existing. The design is tight primarily because (a) `cid,D` live inside the commitment and are anchored by G7 membership, (b) the chain equation `N_{i+1}=H(N_i,c)` makes the opened next-nullifier *deterministic* in the parent-reveal, so forks cannot dodge collision, and (c) Bob is a **blind signer** who knows neither `c` nor the openings of commitments he signed, which kills every forge/mint path.

I found **one real finding**, and it is a **liveness/theorem-hypothesis defect, not fund-theft**: an honest-but-not-perfectly-disciplined Alice can wedge herself out of *every* safe close, making Section 7's liveness clause false as stated. Detail below.

---

## FINDING 1 (real, proof-blocking) — Frontier double-send is an inescapable self-re-wedge; Section 7 liveness is unconditionally false

**Claim attacked:** Section 7, "Liveness for Alice, wedge included": *"From every live state, whatever Bob has done ... a safe close exists."* This is written unconditionally over reachable states.

**Action sequence (concrete):**
1. `D = 100`. Alice opens channel `cid`, deposits 100, samples `c`. Chain `N_1=H(cid,c)`, `N_2=H(N_1,c)`, `N_3=H(N_2,c)`.
2. Payment 1: `delta_1=10`, `m_1=(reveal N_1, 10, C_1=Com(cid,100,10,N_2;r_1), pi_1)`. Bob countersigns `sigma_1`. Now `len=1`, `earned=bal_1=10` (Section 7 defns).
3. At frontier 2 Alice emits **two distinct commitments to the same logical state** (e.g. a crash-retry that re-randomizes before persisting, Section 9): `m_2=(reveal N_2, 5, C_2=Com(cid,100,15,N_3;r_2), pi_2)` and `m_2'=(reveal N_2, 5, C_2'=Com(cid,100,15,N_3;r_2'), pi_2')`. Both are proof-valid (R_pay, signed parent = state 1). Bob receives both; by dedup (Section 3) he signs **neither**, but retains both.
4. Alice now enumerates every close:
   - *Signed close on state 1:* `E={N_2}` (Section 4). Bob holds `m_2`, `N_{m}=N_2 ∈ E`, `C_2 ≠ C_1` ⇒ **valid challenge** (Section 5 rules 2,3). Forfeit.
   - *Genesis close:* `E={N_1}`; `m_1` reveals `N_1` ⇒ forfeit.
   - *Unsigned close on `C_2`:* `E={N_2,N_3}`. Same-state exception excludes `C_2`, but Bob holds `m_2'` with `C_2' ≠ C_2` revealing `N_2 ∈ E` ⇒ **valid challenge**. Forfeit.
   - *Unsigned close on `C_2'`:* symmetric, `m_2` challenges it. Forfeit.
   - *Fresh unsigned tip fork (child of state 1, `delta=0`):* reveals `N_2` as parent-reveal, `E={N_2,N_3}`; `m_2` reveals `N_2` ⇒ forfeit.

   No close object exists that admits no valid witness.

**Clauses that permit each step:** Section 3 (both `m_2,m_2'` are R_pay-valid children of the signed state 1; dedup forces both unsigned); Section 4 (unsigned-close exhibit set includes parent-reveal `N_x`); Section 5 rule 2 (`C_m ≠ C_x` — the two siblings are valid evidence *against each other*) and rule 3 (`N_m ∈ E`).

**Payout vector:** every close ⇒ challenge ⇒ Bob `D=100`, Alice `0`. Property violated: **Section 7 liveness** ("a safe close exists" — here none does).

**Self-refutation (survives, but only as a liveness/hypothesis defect):**
- Bob **cannot induce** this — he cannot manufacture a second sibling (no `c`, and he doesn't know the opening of the state-1 commitment he blind-signed). So it is **not Bob-theft**; it is Alice self-harm. As a safety (Bob-never-loses) attack it *fails*.
- Is the wedged state reachable by an *honest* Alice? Section 5 says a bit-identical resend is "the same message," and Section 9 says persist-before-send. Together they *intend* frontier-injectivity — but the spec **never states** "Alice emits at most one commitment per parent" as a protocol rule, and a crash/retry *before* the persist step (exactly the window Section 9 flags as indistinguishable-from-cheating) produces two distinct commitments. So the state is reachable under the operational model the spec itself describes.
- Therefore the finding **survives as a proof-campaign blocker**: Section 7's liveness lemma cannot be transcribed to Lean as written. It needs an explicit hypothesis — *frontier-injectivity*: Alice's map (parent state ↦ emitted commitment) is a partial function — promoted from operational note (Section 9 / Section 5) to a stated precondition. With that hypothesis the wedge is unreachable and liveness should go through. Without it the theorem is simply false.

**Recommended fix for the gate:** add to Section 3 a normative rule "Alice MUST NOT emit two distinct commitments extending the same parent," and condition Section 7's liveness on it.

---

## Surfaces probed that HOLD (with the one-line reason each)

**Mode-dependent exhibit sets (Section 4) — signed/genesis exhibit only `N_{x+1}`.** No Bob-theft. For a stale *signed* close on `x`, Bob's earned-more evidence is always a descendant of `x`, whose first hop is a signed main-chain child revealing exactly `N_{x+1} ∈ E`; the omitted parent-reveal `N_x` is never the load-bearing witness. Omitting it costs Bob nothing.

**The prompt's headline ghost scenario (Bob holds ghost δ=5; Alice closes a different tip fork δ=0, fresh randomness).** Caught. The chain equation forces every child of state `len` to open the *same* `N_{len+2}=H(N_{len+1},c)` and reveal the *same* parent `N_{len+1}`; the unsigned close's `E={N_{len+1},N_{len+2}}` therefore contains the ghost's `N_m=N_{len+1}` (Section 5 rule 3). Alice's *only* safe close is the ghost itself, paying `earned+δ_ghost` — matching Section 7's "recovers `D−earned−δ_ghost`." Even a *signed* close on `len` is caught here, because the ghost reveals exactly `N_{len+1}=E`.

**Challenge minting/replay against an honest close (Section 5, Q5).** Blocked twice over. To forge a witness revealing an exhibited `N`, Bob must author a successor: the R_pay chain equation needs `c` (hidden in `C_open`), and the signed-parent branch needs the opening `(r,bal,cid,D)` of a commitment Bob only *blind-signed*. Bob has neither. Non-frameability (Section 7) holds.

**Cross-channel challenge (different `cid`, same Alice/Bob).** Blocked. `N_1=H(cid,c)` seeds chains per-`cid`; a foreign message's revealed nullifier lands in this channel's `E` only via hash collision (out of scope, absorbed into the collision bound as the spec states). The no-channel-binding challenge rule is safe for exactly this reason.

**`C_m ≠ C_x` exception exploited by Alice with two same-content commitments.** For a *signed* close, `N_x ∉ E` so a re-randomized sibling is irrelevant; for an *unsigned* close the sibling becomes a *valid* witness — which hurts Alice, never Bob. This is the mechanism behind Finding 1, not a theft.

**G7 / phantom channels and cross-channel splice at close.** Blocked. `cid,D` sit inside every commitment; the genesis branch requires real Merkle membership and the signed branch copies `cid,D` from a validly-signed parent (traceable to a real genesis). Binding ⇒ a channel-1 commitment opens with `cid_1≠cid_2`, so it cannot satisfy channel-2's close relation. `D` is always the real deposit, so `bal ≤ D` protects Bob against the real cap; Bob never over-delivers (Σδ = bal_len ≤ D).

**Signed parent from a CLOSED/SETTLED channel.** Inert. `cid` is fixed through the chain; the only way to *use* such an extension is to close its `cid`, but "one close per channel" forbids re-closing a settled channel. No value extraction.

**Mixed splice (parent `cid_1`, output `cid_2`).** Impossible: R_pay's output binding (clause 4) and signed-parent branch both use a single `cid` copied from the parent — no proof spans two `cid`s.

**Value rules (δ≥0, bal≤D, settlement pays bal).** Sound. A δ<0 unchallengeable refund is blocked by clause 3 (`delta_i ≥ 0`, A2.ii); `bal_i=bal_{i-1}+δ_i` with real propagated `D` prevents both over- and under-statement; the only unchallengeable low close is the fresh tip extension, which has `bal ≥ earned`.

**Timers / sequencing (Sections 4/6).** No stall, no Bob lockout. A pending close resolves within `tau=7d` (challenge ⇒ terminal `D` to Bob, or unchallenged ⇒ `bal≥earned` to Bob); "one close per channel" forbids chaining pending closes, so Alice cannot suspend `T_abs` indefinitely. Timeout-forfeit pays *Bob*, so Alice can never invoke it; once a close is pending Bob cannot double-dip via timeout. `requestClose`-then-immediate-timeout is impossible (`T_req` must elapse). Every branch leaves Bob with ≥ earned.

**Genesis uniformity / fake-refund after payments.** Caught. Genesis close (or unsigned close on a child-of-genesis) exhibits `N_1`; if any payment was made, `m_1` reveals `N_1 ∈ E` ⇒ challenge.

---

## One lower-confidence note for the gate (not an attack)

- **GN-1 must pin the record to `cid`.** The signed branch "reads `pk_B` from *a* member channel record." Since `pk_B` is Bob's global key this is harmless for same-recipient channels, but the Lean transcription should require that the membership record is the **`cid`-matched** one (not merely *some* Bob record), so the property composes cleanly if two channels ever name different recipients. The stated resolution ("same as genesis branch") is fine; just make the `cid`-match explicit.
- **Finalization trigger** for deferred payout (Section 4 sequencing) is unspecified — assume either party can finalize after `tau`; if only Alice could, a passive Alice could delay (not deny) Bob's `earned`. Worth pinning, though not a safety break.

Relevant files: `/Users/clawbox/cleavelabs/zk-payments-confetti/Spec-v2.md` (Sections 3–7 are where Finding 1 lands), `/Users/clawbox/cleavelabs/zk-payments-confetti/research/processed/design-questions.md` (A2.iii and the persist-before-send note bear on Finding 1's hypothesis gap).

---

## Review B: anonymity/linkage

I have all three files. Let me work through the attack surface systematically. I have enough to produce the review without further tool calls.

---

# Adversarial Privacy Review — Spec-v2 Section 8 anonymity claim

Target claim: payment public inputs `(delta, N_i, C_i, root)` are "none channel-linkable"; acknowledged leaks are ONLY ghost-wedge (one edge), unsigned-close delta, and the PROTOCOL.md boundary leaks.

## SURVIVORS

### F1 — Close-split subset-sum retroactively links a channel's payments (headline; breaks the base-protocol claim)

**(1) Observables.** The multiset of `delta_i` from every payment message over the epoch (public payment input, Section 2/3); the set of published close balances `{bal_k}` (Section 4 signed/unsigned close publishes `bal_x`, Section 6 pays `bal`); per-channel open/close timestamps (public boundary, conceded).

**(2) Distinguisher.** For each closed channel `k` with revealed `bal_k` and lifetime window `[open_k, close_k]`, restrict to the deltas Bob observed in that window and solve subset-sum for a subset summing to `bal_k` (multiple-knapsack across concurrent channels, pruned hard by the timing windows). With high-entropy deltas the summing subset is w.h.p. unique, so the recovered subset *is* channel `k`'s payment set. Remove it, repeat; each solved channel eases the rest.

**(3) What it links / bound exceeded.** It assigns individual payment messages to their channel (and, since one channel = one Alice-open, to the same sender). This is exactly the linkage Section 8 asserts impossible ("`(delta, N_i, C_i, root)`, none channel-linkable"). It is the mirror image of PROTOCOL.md's own hidden-balance argument: hiding balances *during* the channel is void once the *final cumulative balance* (= the sum of that channel's deltas) is published in the clear at close, because the deltas are public and high-entropy → the sum is uniquely invertible. PROTOCOL.md says high-entropy δ makes matching "more reliable"; here that works FOR Bob.

**(4) Refutation attempt (why it survives).** Section 8 concedes "public D and final split." But conceding that `bal_k` is public is NOT the same as conceding that payments become channel-linkable — and the two statements are jointly inconsistent for the base protocol: the published split *determines* the delta partition. Computational-hardness defense fails: timing windows shrink instances to a handful of deltas, and unique-solution dense subset-sum is efficiently solvable. The only genuine mitigations are low-entropy/quantized deltas (contradicting PROTOCOL.md's high-entropy stance) or many overlapping same-size channels (partial: isolated-sum channels still fall), or the shielded variant (split hidden in pool notes) — which is an *extension*, not the base protocol the theorem targets. **The draft must retract "none channel-linkable" for the base protocol at close, or scope the per-request-anonymity theorem to the shielded variant only. As written the claim is false and this is not in the acknowledged-leak list.**

### F2 — `root` choice leaks client/channel-age fingerprint (unrecorded; contradicts the G7 "links nothing" claim)

**(1) Observables.** The `root` public input Bob reads off every payment proof (Section 3), plus the public, block-timestamped history of root values (roots update on every open, so `root_0, root_1, …` is a public timeline).

**(2) Distinguisher.** GN-3 permits any root within a `tau` = 7-day staleness window, and the legal root-set for a payment is `[max(open_channel, now−tau), now]` — it must postdate that channel's open and be ≤ tau old. (a) *Client fingerprint:* clients that cache-and-reuse a root emit the same exact stale root value across all their payments for up to 7 days; the population pinned to a given k-day-stale root shrinks with age, so payments sharing an identical stale root form a small linked cluster. (b) *Channel-age bound:* a channel younger than `tau` cannot cite any root older than its open, so a policy of "cite the oldest still-acceptable root" forces young channels onto systematically newer roots — Bob distinguishes young- from old-channel payments by whether they ever cite a root older than `X`. Intersecting the legal windows across a payment cluster pins the channel's open epoch.

**(3) What it links / bound exceeded.** Links multiple payments to the same client instance / channel (and bounds channel age), from a value Section 8 lists as a *non-linking* public input. The draft's assertion (Section 3 / G7: "`root` … is global, common to every channel, so it links nothing") is only true if every proof cites the *identical newest* root — which the 7-day staleness allowance explicitly permits proofs NOT to do. Not in the acknowledged-leak list.

**(4) Refutation attempt (why it survives).** If ALL conforming clients deterministically cite the single newest root, `root` collapses to a coarse global clock and leaks nothing beyond timing. But the spec does NOT mandate that: GN-3 defers root selection to implementation and permits the full window, and the anonymity theorem quantifies over *conforming* clients — so a conforming client MAY cite stale roots. A theorem that holds only under one unspecified client policy is unstatable. **Fix: mandate a canonical, public, deterministic root-selection function (e.g., "newest root at proof time") in the frozen spec, or add `root`-choice to the acknowledged leaks.** Until then this is both a live linkage and a definitional gap.

### F3 — The anonymity theorem is not jointly simulatable from `(cid, D, final split, close mode, close time)` (definitional gaps to record)

Listing every observable in Sections 3/4/5/6 a close-view simulator cannot produce from that tuple alone:

- **G-a (`root` per payment).** Not producible without a canonical selection function (F2). The simulator cannot reproduce which root each intermediate payment cited from the close tuple.
- **G-b (`delta_x` on unsigned close).** The tuple gives `final split = bal_x`, not the tip increment `delta_x = bal_x − bal_{x−1}`; the simulator doesn't know `bal_{x−1}`. Must be added to the input (this is conceded leak #2, but the probe's input tuple omits it).
- **G-c (ghost-edge attribution).** The unsigned close's parent-reveal `N_x` must equal the `N_m` inside Bob's held ghost message; to stay consistent the simulator must be handed *which* held message is the ghosted tip. Not in the tuple (conceded leak #1, but again the tuple omits it).
- **G-d (joint payment↔split assignment — the killer).** The per-request-anonymity simulator must produce the *payment view* (all deltas) AND be consistent with the *close view* (each channel's published split). By F1 the split determines the delta partition, so the joint distribution encodes the linkage: the simulator cannot freely choose the delta-to-channel assignment: it must be given it. Hence per-request anonymity is **not simulatable in composition with base-protocol close.** This is F1 stated as a formal obstruction: the theorem cannot be proven with the payment-view and close-view adversary combined.
- **G-e (challenge tuple).** If the theorem covers adversarial-Alice runs, the on-chain-published `m = (N_m, delta_m, C_m, pi_m)` requires feeding the simulator `delta_m`, `root_m`, and the `N_m ∈ E` consistency (see F4).

**Record for the proof campaign:** the per-request-anonymity simulator's input must be explicitly enumerated, and it must either (i) exclude the close-split view (theorem = "unlinkable *until* close") or (ii) target only the shielded variant. The current Section 8 wording ("public inputs … none channel-linkable") with the close view in scope is unprovable.

### F4 — The challenge transaction publishes a payment's full public tuple (incl. `root`) on-chain; "only" list is incomplete

**(1) Observables.** A challenge publishes `m = (reveal N_m, delta_m, C_m, pi_m)` on-chain (Section 5); `pi_m`'s public inputs include `root_m`.

**(2) Distinguisher.** Any chain observer (not just Bob) reads `delta_m`, `C_m`, and `root_m`, and — because the challenge is valid, `N_m ∈ E` — ties that payment tuple to the challenged `cid`.

**(3) What it links / bound exceeded.** It binds a specific payment's `(delta_m, C_m, root_m)` to `cid` *publicly to the whole chain*, and exposes `root_m` (feeding F2). Section 8's acknowledged leaks are framed as Bob-only and enumerated as "only" ghost-parent-reveal + unsigned-delta + boundary. The challenge-transaction leak (a) is third-party, not Bob-only, and (b) exposes `root_m`, and is absent from the list.

**(4) Refutation attempt (why it survives, weakly).** It fires only on a *cheating* close (stale/forked), where Alice already forfeits everything and `cid` is already public, so the incremental linkage is one dead channel's tuple. Marginal, but the "only-these-leaks" completeness claim is literally false, and the `root_m` exposure is non-marginal given F2. **Record it in the leak list.**

### F5 — Multi-ghost + close-timing composes the "one edge" leak into a linked cluster (conceded bound understates composition)

**(1) Observables.** Per ghosted channel: the unsigned close's parent-reveal `N_x` and published `delta_x` (conceded leak #1/#2); plus close *timing* (conceded boundary leak).

**(2) Distinguisher.** Bob withholds the len+1 countersignature on many concurrent suspected-same-Alice channels. Each forced unsigned close yields one (cid, held-tip-message, delta) edge. A single Alice client typically closes her channels in a correlated burst (shutdown, batch); Bob reads the *set* of unsigned closes clustered in time, each carrying its held-message edge, and stitches them into one linked cluster of (channel, tip-delta) triples.

**(3) What it links / bound exceeded.** Per-channel the leak is literally "one edge," but Section 8 presents the three leaks as independent single-channel one-liners. Composed — n ghost-edges + close-timing correlation + F1 subset-sum — they are not additively bounded: they yield cross-channel sender reconstruction. The draft never states a *composition* bound.

**(4) Refutation attempt (why it survives, moderately).** Bob induces the unsigned closes himself, so "which closes are unsigned" tests no hypothesis; and close-timing correlation is already conceded. The genuine survivor is narrow: the draft's leak accounting is per-close and additive, but the leaks compose, and the ghost-edge specifically upgrades a *timing-only* correlation into a *content* (delta + tip commitment) correlation. **Record a composition clause: the leak bound must be stated jointly, not as three independent single-edge concessions.**

## SURFACES PROBED THAT HOLD

- **Cross-channel dedup linkage:** defeated by `N_1 = H(cid, c)` seeding ([R1], Section 2) — two channels of one Alice have independent chains, so no nullifier ever collides across channels; dedup fires only within one chain. Holds.
- **Dedup as a driveable oracle:** Bob can only *refuse*; refusal is observable to Alice, not third parties, and reveals nothing linking Alice's channels. Re-presenting a held message to himself hits only his own store. Holds.
- **Multi-key/multi-service Bob:** dedup is per-key (GN-2); different services use different `pk_B` and different `cid` → no cross-service collision. Holds.
- **Consecutive-nullifier unlinkability:** `N_{i+1}=H(N_i,c)` is RO-unlinkable without `c`. Holds.
- **`C_i` hiding / blind signature:** `sigma_i = Sign(sk_B, C_i)` on a hiding joint commitment reveals no `cid`/`bal`; simulator can produce a random commitment. Holds.
- **Signed/genesis close attribution-freeness:** exhibit set `{N_{x+1}}` only, which appears in no held message absent a ghost (Section 4 [R1]). Holds.
- **Payment public inputs, individually:** `delta` (conceded public), `N_i` (RO-unlinkable), `C_i` (hiding) each hold; `root` is the lone leaker (F2).
- **Challenge cross-channel false positives:** require a hash collision between independent chains; absorbed into the collision bound (Section 5). Holds.

## BOTTOM LINE FOR THE GATE

F1 is blocking: the base-protocol Section 8 claim "`(delta, N_i, C_i, root)` none channel-linkable" is **false** in composition with the conceded public close-split, and F3/G-d shows the corresponding anonymity theorem is not jointly simulatable — the per-request-anonymity theorem must be scoped to "unlinkable until close" or to the shielded variant before proving starts. F2 is a second blocking gap: `root` is a client-chosen windowed value, not a global constant, so the G7 "links nothing" line must be replaced by either a mandated canonical root-selection function or an explicit `root`-choice leak. F4 and F5 are corrections to the "only these leaks" completeness claim (add challenge-tuple/`root_m` exposure; state the leak bound as a composition, not three independent single edges).

Relevant files: `/Users/clawbox/cleavelabs/zk-payments-confetti/Spec-v2.md` (Sections 3, 4, 8, GN-3, G7), `/Users/clawbox/cleavelabs/zk-payments-confetti/PROTOCOL.md` (Goals hidden-balance argument, Privacy properties), `/Users/clawbox/cleavelabs/zk-payments-confetti/research/processed/design-questions.md` (A2/A5 context).
