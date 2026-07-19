# Spec-v2 (draft, round 1): the nullifier-chain channel, frozen for proving

Status: **DRAFT, pre-freeze.** This document transcribes `PROTOCOL.md` (the
design of record) plus the five defaults proposed in
`research/processed/design-questions.md` and accepted verbatim by the protocol
designer on 2026-07-18 ("I agree with all five proposed defaults"). The
accepted defaults are recorded as **A1..A5** (answering Q1..Q5). Everything
this document adds beyond `PROTOCOL.md` + A1..A5 is marked **[R1]** (round-1
resolution) and is a choice of ours, not the designer's, per the packet's
ground rule. Gate rounds run against this document; when they close, it
freezes and the proof campaign targets it.

Design intent carried over unchanged from `PROTOCOL.md`: per-request
anonymity, hidden balances, payment-channel safety, liveness for Alice,
post-quantum setting (STARKs + hashes + a PQ signature verified inside the
proof; no elliptic curves).

## 1. Parties, parameters, primitives

- **Alice** (payer, opens the channel), **Bob** (recipient), the **contract**
  (the on-chain verifier and escrow).
- `H`: a hash modeled as a random oracle (Poseidon/Blake class).
- `Com`: a hiding, binding commitment (hash-based).
- `Sig = (KeyGen, Sign, Verify)`: a PQ-EUF-CMA signature whose verification is
  cheap inside a STARK (WOTS/XMSS/SPHINCS+/Dilithium; stateful schemes carry
  their state discipline as an explicit assumption).
- A STARK proof system with knowledge soundness **and zero-knowledge** for
  the relations below. ZK of `π_close` is load-bearing: the signed-close
  proof (Section 4, per the F-R2-1 repair) carries the state commitment and
  countersignature as private witnesses, so a non-ZK `π_close` would leak
  them and re-open the attribution channel the repair closes.
- Time constants: `T_abs` = 90 days (absolute close deadline), `T_req` =
  7 days (close-on-request deadline), `tau` = 7 days (challenge window, A3).
- Nullifier space `N` = the hash range; `|N|` superpolynomial.

## 2. Data model

**Chain secret and nullifier chain.** Alice samples a chain secret `c`. With
`cid` the channel id (assigned at open):

```
N_1     = H(cid, c)
N_{j+1} = H(N_j, c)      for j >= 1
```

**[R1]** The seed is `cid`, so distinct channels of one Alice have independent
chains even under chain-secret reuse; honest Alice still samples fresh `c` per
channel.

**Channel record** (on-chain, created at open):

```
ch = (cid, D, pk_B, C_open)     with C_open = Com(c ; r_open)
```

`D` is the deposit, `pk_B` Bob's public key. `C_open` binds the chain secret
at open (A5). The contract maintains a Merkle tree over all channel records;
`root` denotes its root. **[R1, G7]** This tree is what payment proofs anchor
to; see R_pay.

**State commitment** (A1 + A4 + **[R1, G7]**). State `i >= 1` of a channel is
carried by the joint hiding commitment

```
C_i = Com(cid, D, bal_i, N_{i+1} ; r_i)
```

- Joint, per A4: opening the state at close opens balance and next-nullifier
  together. The genesis carries no balance commitment (bal_0 = 0 by
  definition, A4); its committed next-nullifier is `N_1`, derivable from
  `C_open` via the chain equation.
- Contains `cid`, per A1: the channel binding is hidden inside the
  commitment. Bob never sees it opened; the close-time contract, which knows
  its own `cid`, checks it.
- Contains `D`, **[R1, G7]**: `D` must be an authenticated in-circuit value
  (the `bal <= D` cap protects Bob only if `D` is the real deposit), and no
  per-channel public input may carry it (anonymity). So `D` rides in the
  commitment and propagates inductively: the genesis branch of R_pay reads it
  from the on-chain channel record under `root`; the signed branch copies it
  from the Bob-signed parent commitment. A payment proof therefore speaks
  about the real channel's `D` or about no channel at all.

**Payment message** `i >= 1`:

```
m_i = (reveal N_i, delta_i, C_i, pi_i)
```

`N_i` and `delta_i` are in the clear to Bob; `pi_i` is a STARK for R_pay.
Bob, on accepting, countersigns: `sigma_i = Sign(sk_B, C_i)` (A1: Bob signs
the commitment; he is a blind signer of an Alice-supplied digest).

## 3. The payment relation R_pay

Public inputs: `(delta_i, N_i, C_i, root)`. (**[R1, G7]** `root` is the only
on-chain anchor and is global, common to every channel, so it links nothing.
The contract accepts any sufficiently recent root; staleness bound is an
implementation parameter.)

Private witness: `cid, D, c, r_open, bal_{i-1}, r_i`, and the parent branch
data below.

`pi_i` proves, for the claimed public inputs:

1. **Parent branch** (the flat disjunction, hiding which case):
   - *Genesis:* a channel record `(cid, D, pk_B, C_open)` is a Merkle member
     of `root`; `C_open` opens to `c`; `bal_{i-1} = 0`; `N_i = H(cid, c)`.
   - *Signed parent:* there exist `C_{i-1}, sigma_{i-1}, r_{i-1}` with
     `Verify(pk_B, C_{i-1}, sigma_{i-1})` and
     `C_{i-1} = Com(cid, D, bal_{i-1}, N_i ; r_{i-1})`. (The parent's
     committed next-nullifier IS the revealed `N_i`; cid and D are copied
     from the parent, and pk_B is read from the member channel record in
     both branches. [R1: the signed branch also carries the channel-record
     membership for pk_B; see gate note GN-1.])
2. **Chain equation** (A5): `N_{i+1} = H(N_i, c)` with `c` the value
   committed in `C_open`.
3. **Value update**: `delta_i >= 0` (A2.ii), `bal_i = bal_{i-1} + delta_i`,
   `bal_i <= D`.
4. **Output binding**: `C_i = Com(cid, D, bal_i, N_{i+1} ; r_i)`.

**Bob's acceptance rule.** Bob verifies `pi_i` against the current `root`,
checks `delta_i` equals the price of the service, and refuses to countersign
if the revealed `N_i` was ever revealed to him before (dedup; necessarily
global across his inbox, since he cannot attribute messages to channels).
Consequence: a payment message needs a Bob-signed parent or the genesis, so
**an unsigned frontier is at most one message deep**, and any state extending
a non-tip parent (a fork) can never become Bob-signed (its reveal is a dedup
hit).

**Frontier injectivity (normative, [R1] from gate finding F-R1-1).** Alice
MUST NOT emit two distinct commitments extending the same parent state; a
retry MUST be bit-identical to the persisted original (which is what makes
persist-before-send, Section 9, a hard requirement rather than advice). Two
re-randomized siblings are valid challenge evidence against *each other*, so
violating this rule leaves Alice with no safe close whatsoever: it is
self-wedging, harms only Alice, and cannot be induced by Bob (he can author
no sibling without `c` and the parent opening). The liveness property of
Section 7 is conditioned on this rule.

**Root selection (normative, [R1] from gate finding F-R1-3).** The contract
maintains epoch-quantized roots (epoch length `T_root`, recorded default
1 day): proofs MUST cite the root of the current epoch, and verifiers accept
the current and immediately previous epoch's roots only. A freely chosen
root within a 7-day staleness window is a client fingerprint (payments
citing the same rare stale root cluster; legal-window intersection bounds a
channel's open date), which would break unlinkability through a value the
proof publishes. Epoch quantization collapses the fingerprint to a public
clock; the residual leak (epoch granularity of proof-generation time) is
recorded in Section 8.

## 4. Close

A close is a contract transaction naming the channel `cid`. Three modes.
Every mode publishes the closing commitment `C_x` (or genesis marker) and the
exhibited nullifiers defined below; a close proof `pi_close` covers the mode's
relation. Closing is legal on **signed states, the genesis, and
unsigned-but-proof-valid states** (A2.i).

- **Genesis close** (full refund). Publishes `reveal N_1` with a proof:
  `C_open` (of this channel's on-chain record) opens to `c` and
  `N_1 = H(cid, c)`. Payout claim: `bal = 0`.
  Exhibit set `E = { N_1 }`.
- **Signed close** on state `x`. Publishes `reveal N_{x+1}` (the committed
  next-nullifier, opened) and `bal_x` ONLY, with a proof: knowledge of
  `C, r, sigma` with `C = Com(cid, D, bal_x, N_{x+1} ; r)` for THIS
  channel's `cid, D`, and `Verify(pk_B, C, sigma)` — the commitment and
  signature are private witnesses, exactly as in R_pay's signed branch.
  Exhibit set `E = { N_{x+1} }`.
  **[R2, F-R2-1]** An earlier draft published `C_x` in the clear; that is
  an attribution leak (Bob holds every commitment he countersigned and
  matches), found in the close-view anonymity proof attempt and repaired
  here. Signed closes need no same-state exception (their own message's
  revealed `N_x` is never in `E`), so nothing in the challenge relation
  needs `C_x`.
- **Unsigned close** on state `x` (A2). Publishes `C_x`, `reveal N_x`
  (parent-reveal), `reveal N_{x+1}` (opened), `bal_x`, `delta_x`, with a
  proof: the full R_pay relation for `C_x` (parent branch, chain equation,
  `delta_x >= 0`, `bal_x <= D`) against this channel's `cid, D`.
  Exhibit set `E = { N_x, N_{x+1} }`.

**[R1] Mode-dependent exhibit sets** (refining A2.iii). A2.iii as accepted
says the challenge fires on any nullifier the close exhibits, opened and
parent-reveal both. The parent-reveal clause exists to catch rollback forks,
and forks are inherently unsigned (Section 3, dedup). Signed and genesis
closes therefore exhibit only the opened next-nullifier, which keeps a fully
countersigned honest close attribution-free (nothing it publishes ever
appeared in a message). Unsigned closes exhibit both. Privacy consequence
recorded in Section 8.

**Sequencing** (A3): the close starts a challenge window of length `tau`.
Payout is deferred until the window elapses unchallenged; after expiry
**either party** may trigger finalization ([R1]: were it Alice-only, a
passive Alice could delay Bob's payout indefinitely). One close per channel;
a successful challenge is terminal.

**Timers.** Alice must close by `T_abs` after open. Bob may request close at
any time, after which Alice must close within `T_req`. If neither deadline is
met and no close is pending, Bob may claim the entire deposit
(timeout-forfeit). A pending close suspends the timers; its outcome is
decided by the challenge window alone.

## 5. Challenge

Within the window, Bob submits a held payment message
`m = (reveal N_m, delta_m, C_m, pi_m)`. The challenge is **valid** iff

1. `pi_m` verifies under R_pay against a root the contract accepts (A5:
   challenge-witness validity is proof validity; the chain equation inside
   R_pay is what makes witnesses unforgeable without `c`);
2. the **same-state exception**, per close mode (refined for F-R2-1, since
   signed closes no longer publish `C_x`): for an **unsigned** close, `C_m
   != C_x` (the closed commitment is public); for a **genesis** close there
   is no closed commitment and every valid `m` qualifies; for a **signed**
   close no exception is needed and none is checkable — the closed state's
   own message revealed `N_x`, never the exhibited `N_{x+1}`, so it can
   never be its own challenge witness (proved inert in
   `lean/Zkpc/Chain/V2/Close.lean`);
3. `N_m ∈ E` (the revealed nullifier of `m` collides with an exhibited
   nullifier of the close).

A valid challenge forfeits the entire deposit to Bob (A2 bundle; G5 closed:
forfeit-all is intended, graded penalties are structurally impossible).

**[R1]** No channel-binding check on `m`: the contract cannot know which
channel `m` belongs to (that is the design). Cross-channel false positives
require a hash collision between independent chains and are absorbed into the
collision bound. **[R1]** Bit-identical resend of `m_x` by Alice is the same
message, not new evidence (C_m equality), matching ROADMAP obligation 7.

## 6. Settlement values

Unchallenged close of claimed balance `bal`: Bob receives `bal`, Alice
receives `D - bal`. (`bal <= D` is enforced in every close mode's relation,
so the contract never over- or under-pays; there is no clamping rule.)
Challenge or timeout-forfeit: Bob receives `D`, Alice `0`.

## 7. Safety properties (the theorem targets)

With `len` = latest Bob-signed state index, `msgs ∈ {len, len+1}` = messages
sent, `earned = bal_len`:

- **Conservation.** Every settlement splits exactly `D`.
- **No overspend.** Every proof-valid state has `bal <= D` with the real `D`.
- **Evidence characterization.** For every proof-valid close object `x`, a
  valid challenge witness exists iff `x` is not in the safe set:
  `{genesis iff msgs = 0} ∪ {signed tip iff msgs = len} ∪ {the ghost message
  itself iff msgs = len + 1} ∪ {a fresh unsigned tip extension iff
  msgs = len}`. In particular every stale or forked close is challengeable,
  and each of the listed safe closes admits no valid witness (assuming
  chain collision-freedom).
- **Bob never loses.** Every safe close pays Bob at least `earned`; every
  challenge and timeout pays him `D >= earned`. *Two layering caveats, per
  the modeling review.* (i) This is the **on-chain settlement** property; it
  is conditional on the two probabilistic crypto kernels holding — the
  collision bound (`safe_iff` assumes chain collision-freedom) and
  non-frameability (a forged witness would slash an honest close). The
  machine-level theorem and each kernel are proved separately; the fused
  "never slashed except with probability ≤ `n(n-1)/2|N| + q_C/|C| +
  q_N/|N|`" statement is the acknowledged unfused residual. (ii) The
  forward "unsafe ⇒ challengeable" direction also assumes Bob **retained**
  every message he was sent (an honest-recipient store), alongside the
  vigilance assumption of Section 9.
- **Just-closed-channel service loss (bounded, disclosed).** Because the
  epoch-root rule (Section 3) accepts the current and previous epoch's
  roots, Bob may accept a payment whose channel closed up to ~2 epochs ago;
  such a payment can never be settled, so Bob renders service he cannot
  collect on. This sits outside the single-channel "Bob never loses" model.
  Bounded by service value per 2 epochs per channel; the mitigation is to
  accept only the current-epoch root at close, traded against anonymity-set
  width (GN-3). Flagged for the designer.
- **Liveness for Alice, wedge included (the G2 repair).** From every live
  state, whatever Bob has done (including withholding the last
  countersignature), a safe close exists and Alice plus the clock can drive
  the channel to an unchallenged settlement. If Bob signed everything she
  recovers `D - earned`; under a ghost she recovers `D - earned - delta_ghost`
  (the abort price is at most one delta, and requires her persisted copy of
  the ghosted message).
- **Genesis uniformity.** The refund close is the `i = 0` instance of the
  same rules: safe iff no message was ever sent.
- **Non-frameability** (A5, probabilistic): no q-query adversary given the
  full transcript and an honest close's published openings produces a valid
  challenge witness against it; bound of shape `q_C/|C| + q_N/|N|` (secret
  probes and target guesses, one guess per held cross-channel message —
  `q_N` is not 1).

## 8. Privacy properties

**The claim, scoped ([R1], rescoped by gate finding F-R1-2): per-request
anonymity holds *until close*.** During the channel's lifetime Bob cannot
link two payments to the same sender or channel: payment public inputs are
`(delta, N_i, C_i, root)` with `N_i` RO-unlinkable, `C_i` hiding, `root` an
epoch-public value common to all channels; parenthood, balances, and cid are
hidden. **At close, the base protocol's published split retroactively leaks
linkage**: the split equals the sum of that channel's deltas, deltas are
public per payment, and with high-entropy deltas the summing subset is
w.h.p. unique inside the channel's lifetime window, so Bob can partition his
inbox by subset-sum as channels close. This is `PROTOCOL.md`'s own
delta-matching argument turned against the close boundary, and it is
intrinsic to any base-protocol close that reveals the split in the clear.
The per-request-anonymity theorem is therefore stated as
*unlinkable-until-close* (equivalently: the adversary's view excluding
close-split disclosures, or full-strength under the shielded-pool extension,
which hides the split and is the complete fix).

**Leak record ([R1]; these compose, and the eventual theorem must state the
joint bound, not three independent single-edge concessions):**

1. *Ghost-wedge attribution.* An unsigned close exhibits its parent-reveal
   nullifier, so when Alice closes on a ghosted message, Bob links that one
   held message (and its `delta`) to the channel. Signed closes leak nothing
   held. Per channel: one edge, only at close, only when Bob withheld — but
   Bob can induce ghosts across many suspected-same-sender channels and
   correlate the forced unsigned closes with close timing.
2. *Unsigned-close delta disclosure.* The unsigned close publishes `delta_x`
   on-chain (part of its close relation).
3. *Close-split subset-sum.* The headline rescope above.
4. *Challenge-tuple disclosure.* A challenge publishes the witness message
   `(N_m, delta_m, C_m, pi_m)` and its cited root on-chain, binding that
   payment tuple to the cid for every chain observer (not just Bob). Fires
   only on cheating closes, where cid attribution is already forfeit.
5. *Root epoch.* Every payment proof reveals its root epoch (~1-day
   granularity of proof-generation time).
6. Everything else Bob sees at close he could already see on-chain (cid, D,
   split).

**Simulator inputs for the anonymity theorem** (recorded so the Lean
statement cannot silently overclaim): the close-view simulator is given
`(cid, D, final split, close mode, close time, and for unsigned closes the
tip edge: the ghosted message identity and delta_x)`; the payment-view
simulator gets `(delta, root epoch)` per payment and must produce the rest.
Unlinkable-until-close means the joint view excluding item 3.

## 9. Operational notes (not protocol)

- **Persist-before-send** (A2/G5 residue): Alice must durably store a payment
  message before transmitting it; a crash between send and persist makes her
  latest safe close unknowable to her, and the contract cannot distinguish
  her stale close from cheating.
- Bob should verify payment proofs against a root at most one staleness bound
  old, observe the chain at least once per `tau`, and challenge immediately
  on evidence.

## 10. Gate notes (disclosed modeling choices for round 1)

- **GN-1.** The signed branch of R_pay reads `pk_B` via channel-record
  membership, same as the genesis branch, and the membership record MUST be
  the `cid`-matched one (the record whose cid equals the one inside the
  parent commitment), not merely some record naming the same recipient —
  explicit so the property composes across channels with different
  recipients. Alternative: bake `pk_B` into the state commitment like
  `cid, D`. Equivalent under binding; membership form chosen to keep the
  commitment layout minimal. Gate rounds may flip this.
- **GN-2.** Bob's dedup store is global and append-only for the lifetime of
  his key. Garbage collection of nullifiers from closed channels is possible
  (post-close, Bob can attribute nothing, but closed channels' chains are
  dead) and deferred to implementation.
- **GN-3.** Superseded by the normative epoch-root rule in Section 3
  (finding F-R1-3): root selection is no longer implementation-deferred.
  The epoch length `T_root` (default 1 day) trades anonymity-set width
  against acceptance of payments from just-closed channels.

## 11. New findings this round (for the gate record)

- **G7 (genesis anchoring / phantom channels), found in transcription.**
  Neither `PROTOCOL.md` nor the packet says what anchors a payment proof to a
  real deposit. Any per-channel public input breaks anonymity, so the anchor
  must be a global-root membership proof in the genesis branch with `cid, D`
  propagating inductively through signed parents (Section 2/3). Without it,
  Alice fabricates a phantom channel record as a private witness, Bob blind-
  signs a chain against a deposit that does not exist, and payment-channel
  safety fails totally at close. Resolution adopted in this draft; needs
  designer sign-off since it adds the channel Merkle tree to the base
  protocol (PROTOCOL.md's "no Merkle tree" remark concerned states, not
  channels).
- **Mode-dependent exhibit sets** (Section 4) as the minimal reading of
  A2.iii that preserves attribution-free honest closes; the blanket reading
  (every close exhibits parent-reveal) leaks the tip edge on every close.

Round-1 red-team findings (two adversarial reviews, safety and privacy, run
2026-07-18 against this draft; both reviews' full text in
`research/raw/spec-v2-gate-round1.md`):

- **F-R1-1 (safety review; proof-blocking for liveness as drafted).**
  Sibling double-send self-wedge: two re-randomized commitments extending
  the same parent are valid challenge witnesses against each other, leaving
  Alice no safe close. Not Bob-inducible, not theft; repaired by the
  normative frontier-injectivity rule (Section 3) and by conditioning the
  liveness theorem on it. The safety review found **no Bob-theft** on any
  probed surface (splices, minted witnesses, forks, value rules, timers,
  genesis; each with a stated reason).
- **F-R1-2 (privacy review; blocking for the anonymity theorem as
  drafted).** Close-split subset-sum retroactively partitions Bob's inbox;
  "none channel-linkable" was an overclaim. Repaired by rescoping the claim
  to unlinkable-until-close (Section 8), full strength under the shielded
  extension.
- **F-R1-3 (privacy review).** Client-chosen roots inside a staleness
  window fingerprint clients and bound channel age. Repaired by the
  normative epoch-root rule (Section 3).
- **F-R1-4 (privacy review).** Challenge transactions publish the witness
  tuple to all chain observers; added to the leak record (Section 8).
- **F-R1-5 (privacy review).** The leak record composes (multi-ghost plus
  close-timing correlation); the theorem must state a joint bound
  (Section 8).
- Also pinned from the safety review: either-party finalization
  (Section 4), cid-matched membership in GN-1.

Round-2 findings (from the proof campaign itself, per the method: a failed
proof is a finding about the definition):

- **F-R2-1 (found in the close-view anonymity proof attempt).** The round-1
  draft's signed close published `C_x` in the clear; Bob holds every
  commitment he countersigned, so matching `C_x` attributes the closed tip
  message even on a fully countersigned honest close — contradicting the
  [R1] attribution-freeness claim of Section 4. Repaired: signed closes
  publish only `(bal_x, N_{x+1})` and prove knowledge of a signed opening
  (Section 4); the proof of close-view unlinkability then goes through
  (`lean/Zkpc/Chain/V2/CloseView.lean`). Unsigned closes still publish
  `C_x` (the same-state exception needs it) and already concede the tip
  edge.

Round-3 findings (independent Fable-5 modeling review of the proof corpus,
2026-07-18; the kernel checks the proofs, this pass checks the
statements). Wording/coverage corrections applied; two rigor items opened:

- **R3-1 (applied; correctness).** The frame game's single target guess
  understated the adversary: a real challenger has one guess per held
  cross-channel message. Fixed to a guess *list*, bound now `q_C/|C| +
  q_N/|N|` (Section 7; `lean/Zkpc/Chain/V2/Frame.lean`).
- **R3-2 (applied; the `adaptive_frame_bound` defect).** The stage-2
  "adaptive frame bound" summed two disjoint experiments as one advantage.
  Renamed and reworded to state exactly the two separate hidden-target
  terms; the fused adaptive game is the FrameDeferred residual, not claimed
  (`lean/Zkpc/Chain/V2/FrameAdaptive.lean`).
- **R3-3 (applied; overclaim).** The liveness module claimed
  "guaranteed under fairness"; it proves enabledness + deadlock-freedom
  only. Reworded; obligation 5's temporal wrapper is explicitly still open.
- **R3-4 (applied; disclosure).** Signed-close "advantage 0" carries the
  ideal-commitment and ZK-of-`π_close` qualifiers; the latter is now a named
  primitive (Section 1).
- **R3-5 (applied; the just-closed-channel loss and the conditional-on-
  kernels framing of "Bob never loses", Section 7).**
- **R3-6 (open; rigor).** The chain theorems assume `Function.Injective nul`
  over all of `ℕ` (inherited from the seed `Chain/Collision.lean`), which is
  unsatisfiable at a finite nullifier type. Only indices `≤ msgs + 2` are
  ever used, so the fix is to weaken to `Set.InjOn nul (Set.Iic (msgs+2))`
  with a one-line prefix bridge; tracked as a ROADMAP rigor item (does not
  affect any current proof, but closes the gap between the assumed and the
  probabilistically-established hypothesis).
- **R3-7 (open; rigor).** The `linkable_leak_detected` calibration proves
  distributional separation; strengthening it to "a concrete adversary has
  positive advantage in the played `anonGame`" is one further lemma, tracked
  alongside the anonymity battery.
