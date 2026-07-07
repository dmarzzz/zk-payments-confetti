# Spec: the zk payment channel object and theorems T1–T7

Status: **revision 11.** Round 10 passed F9-1a/b and F9-m2 and found the
rev-10 joint-transcript sharpening flipped MC15's satisfaction claim for
B — a stale close's $nf_j$ transcript-match is the conviction mechanism
itself, so it cannot be jointly simulatable; rev-11 scopes the claim to
true-count closes and records the receipt-withholding one-session
linkage residue as an honest limit (MC15, T4), plus scopes MC18's slash
rule (F10-m1). Prior: Round 9 verified the session-form challenge
end-to-end (the K4 construction now loses; ⊥ stays b-independent via the
non-adaptive vector and symmetric capable-for-$q$) and found one major:
the new slash taxonomy exposed that the $k$-gated MC4/R3-2 settlement
machinery cannot run for fund-slashes — rev-10 states the A
checkpoint-dispute remainder rule (pool-retained, no bounty) and scopes
B's per-nullifier claims to identity-slashes with fund-slashes settling
by forfeit; plus the F9-m1 joint-transcript sharpening of the CloseView
obligation and the F9-m2 multiplicity-tag calibration point. Rev-8 was
SIGNED OFF at gate B1 (round 8); rev-9/10
are scoped, gate-tracked amendments from the K4 external review
(simulated outside cryptographer attacking the definitions): the T4
challenge upgraded from single-spend to **session form** (the $q=1$ game
certified only first-spend-per-epoch unlinkability — a definitional
hole for the fleet's real usage), the **CloseView-simulatability
obligation** added to MC15 (challenge termination blinds the game to
close-time content), the calibration battery widened, and the
fund-slash/identity-slash distinction recorded. Scoped re-review of
exactly these deltas: B1 round 9. Prior history: round 7 verified
all of round 6's fixes and found the $nf_j$ reveal weaponizable by
receipt withholding (→ receipt-bearing checkpoint disputes with an
upgrade sub-window; $j{=}0$ closes receipt-free) and the sweep bar
one-directional (→ two-sided, with on-ledger disproof at settlement) —
both repaired in this revision. Earlier gate history, six
rounds so far, every round by a fresh reviewer who did not write the text:
rev-1, three-lens panel, 3× REVISE — T6 false via cross-gateway replay
(→ MC14), UNLINK unsatisfiable (→ MC15), merge evidence missing (→ MC17),
receipt splicing (→ MC7 tags); rev-2 verified plus two new blockings — B
fund conservation (→ MC18), post-slash claim forgery (→ MC19); rev-3
verified plus three majors (→ R_close-B caps, B slash path, checkpoint
cadence); rev-4 verified plus the j-side drain (→ second close cap);
rev-5 verified plus the gap-index understatement, the run's deepest hole
(→ MC20: A closes by unused-nullifier enumeration, B by certified count);
rev-6 verified MC20's shape plus the B stale-receipt door (→ the $nf_j$
reveal, in rev-7) and the A sweep-bar/loss-bearer decision (rev-7), with
the checkpoint commitment pinned as a binding Merkle set commitment.
The full review record with every counterexample is
`research_knowledge/gates.md`. This document is the trust surface of the
formalization. A reviewer reads this file and the security-game docstrings,
and nothing else; every Lean definition in the repo must be traceable to a
sentence here, and every ambiguity here is a potential
wrong-definition-proved-correctly failure. The protocol formalized is the one
described in the egress post's wire-protocol and payment sections and in
RESEARCH.md's application section — not a reinvention. Where those sources
are ambiguous or the panel found them broken as transcribed, the resolution
is recorded in §8 (Modeling choices) and the reviewer is asked to check each
one; entries marked **[repair]** change protocol behavior rather than merely
disambiguate.

Contents: §1 notation, §2 the algorithm tuple, §3 flat-ticket instantiation,
§4 refund-bearing instantiation, §5 model boundary, §6 adversary conventions,
§7 theorems T1–T7, §8 modeling choices, §9 provenance.

---

## 1. Notation and parameters

**Sorts.** Two kinds of quantity, never conflated (a rev-1 reviewer caught a
genuine fork here):

- **Integers/naturals (ℕ):** spend indices $i$, monetary quantities
  $C, C_{max}, D, R, c$, counters, budgets, times. All solvency and payout
  inequalities are integer inequalities.
- **Prime field $F_p$:** the signal algebra only — secrets $k$, line values
  $x, y, a$. Indices enter hashes as naturals (with $i < p$, so the embedding
  is injective).

$\lambda$ is the security parameter; "PPT" means probabilistic polynomial
time in $\lambda$; $negl(\lambda)$ is a negligible function.

Fixed public parameters (chosen at `Setup`, constants thereafter):

| symbol | meaning |
|---|---|
| $C$ | flat price per spend (instantiation A) |
| $C_{max}$ | maximum price per spend (instantiation B); actual cost $c \le C_{max}$ is declared by the payee per request |
| $D$ | deposit escrowed per channel at `Open` |
| $d$ | Merkle tree depth; membership set capped at $2^d$ |
| $T_e$ | epoch length (wall-clock duration of one RLN rate epoch) |
| $b$ | per-gateway, per-epoch rate budget (max *accepted* spends per epoch pseudonym per gateway; see §2 Redeem) |
| $N$ | number of gateways in the fleet (instantiation A only; $N=1$ for B) |
| $L$ | reconciliation lag, **end-to-end** (MC11): max time from an acceptance at any honest gateway to (i) the accepted tuple's presence in every other gateway's spent set, (ii) ledger inclusion of any `Dispute` evidence that acceptance triggers — at `Redeem` time (check 6) or at merge time (MC17) — and (iii) fleet-wide effect of the resulting slash (root rotation visible to all gateways). Folds gossip, $\Delta$, and propagation into one parameter. |
| $\tau$ | close/dispute window duration |
| $\Delta$ | idealized-ledger inclusion delay for honest transactions |

Parameter constraint: $\tau > \Delta$ — every response window must outlast
the inclusion delay, or the ForceClose response path (MC18) and the dispute
windows are vacuous for honest parties (rev-3 R3-4). Honest payers monitor
the ledger for events naming their $cm$ (ForceClose, Dispute), symmetric to
the payee's MC16 monitoring duty.

Hash functions, all domain-separated (MC9): $H_{id}$ (identity commitment),
$H_a$ (RLN line coefficient), $H_x$ (message digest), $H_{nf}$ (spend
nullifier), $H_e$ (epoch nullifier), $H_{tag}$ (refund-chain tag,
instantiation B, MC7). A member's long-term secret is $k \in F_p$; its
identity commitment is $cm = H_{id}(k)$.

**Messages are gateway-bound (MC14, [repair]).** A spend message is a pair
$m = (G, \hat{m})$: the identity of the serving gateway and the request
payload. $H_x$ hashes the pair. `Redeem` at gateway $G$ rejects tickets whose
message names a different gateway. Consequence: serving the same index at two
gateways forces different messages, hence conflicting signals — this is what
makes T6's detection argument sound, and it extends the egress post's own
production note that the proof's message field should bind the target.

**The RLN signal.** For secret $k$, spend index $i \in \mathbb{N}$, and
message $m$:

$$a = H_a(k, i), \quad x = H_x(m), \quad y = k + a \cdot x, \quad nf = H_{nf}(a),$$

with $H_x$ mapping into $F_p \setminus \{0\}$ (rev-6, from the Lean G4
work: at $x = 0$ the signal degenerates to $y = k$ — the secret outright —
so single-signal hiding is conditioned on $x \ne 0$ and the deployment
domain-separates $H_x$ away from zero).

The *signal* is $s = (x, y, nf)$. Two well-formed signals on the same $(k,i)$
with $x \ne x'$ are two points on the line $Y = k + aX$: anyone can compute
$a = (y - y')/(x - x')$ and $k = y - a\cdot x$. One signal reveals nothing
about $k$ beyond the assumptions of §5 (the *single-signal hiding*
assumption; this asymmetry is the entire content of T7 and the slash
mechanism). This is the ticket-index-as-RLN-scope algebra of the source
construction: the spend index plays the role RLN's epoch plays in the
rate-limiting deployment.

The *epoch pseudonym* for epoch $e$ is $nf_e = H_e(k, e)$. It is linkable by
design within an epoch (it is what the gateway counts requests against) and
unlinkable across epochs. Payment tickets carry both nullifiers; the
consequences for the unlinkability theorem are stated in T4, MC6, and MC15.

---

## 2. The object: algorithm tuple

A **zk payment channel scheme** is a tuple of algorithms
$(Setup, Open, Spend, Redeem, Close, Dispute)$ over three kinds of principal:
**payers** (members), **payees** (gateways; $N$ of them sharing one logical
payee role in the fleet setting), and an **idealized ledger** $\mathcal{L}$
(§5). State touched is named explicitly per algorithm.

**Ledger accounting (MC16, [repair] — rev-1 left this implicit and two
theorems silently depended on it).** The ledger holds one **commingled
escrow pool**: `Open` adds $D$ to the pool against $cm$; sweeps draw from the
pool per fresh nullifier (pre-slash, a nullifier is by design unattributable
to any $cm$, so no per-channel draw is possible); payer-close pays the
MC20 refund ($C$ per proven-unused index plus the sub-ticket residue —
$D - j\cdot C$ on the honest path) out of the pool, and refunded
nullifiers are barred from sweeps. Pool solvency is what T1 plus the MC20
sweep bar protect.
Sweep transactions are **authenticated to the gateway roster** fixed at
`Setup`: only registered gateways may sweep (otherwise a payer front-runs
the sweep of its own tickets and T2 falls — rev-1 finding), and the sweep
verifier checks the tuple's proof against $\mathcal{R}_{spend}$
specifically — the close signal's $(nf_j, \pi_{close})$, public on-ledger,
is not sweepable (rev-2 finding NEW-6). `Dispute` remains permissionless.
**Instantiation B settles differently (MC18, [repair]):** rev-2 review
proved the sweep-plus-close mechanics above cannot conserve funds in B
(sweeps pay $C_{max}$ per nullifier *and* close pays the refund $R$ — $D+R$
out of a $D$ deposit, with pre-slash unattributability blocking any
per-channel netting). B therefore has **no unilateral nullifier sweeps**;
the payee's revenue settles per channel at close time (see §2 Close and
§4).

**$Setup(1^\lambda, params) \to pp$.**
Run once, honestly (trusted setup is axiomatized, §5). Outputs public
parameters: the NIZK common reference string, hash descriptions, the field,
the constants of §1, the **gateway roster** (the $N$ sweep-authorized payee
identities), and (instantiation B only) the payee's signature keypair
$(vk_S, sk_S)$ and the re-randomizable encryption public key $pk_E$ (MC7) —
whose decryption key $sk_E$ is **not output to any party** (rev-2 NEW-4:
B-rerand's genesis-tie-breaking argument needs this stated, not implied).
Touches: nothing; creates $pp$.

**$Open(pp, D;\ \text{payer}) \to (cm, st_P)$.**
Run by a payer. Samples $k \leftarrow F_p$, computes $cm = H_{id}(k)$,
submits $(cm, D)$ to $\mathcal{L}$. The ledger appends $cm$ to the Merkle
membership tree (producing a new root), adds $D$ to the escrow pool against
$cm$, and marks the channel *open*. Payer's private state initializes to
$st_P = (k, i{=}0, R{=}0, \text{refund evidence} = \varnothing)$.
Instantiation B additionally runs the **genesis receipt** exchange (MC7):
the payer sends $ct_0 = Enc(pk_E, (H_{tag}(k), 0, 0);\ r_0)$ — the triple
$(tag, R{=}0, n{=}0)$, rev-6 count certification — with a NIZK that $ct_0$
encrypts it for the $k$ committed in $cm$ (no anonymity loss: `Open` is a
public event naming $cm$ anyway); the payee verifies and returns
$\sigma_S(ct_0)$. In instantiation A one `Open` binds the payer to
the whole fleet (the "channel" is payer-to-fleet); in B it binds payer to the
single payee. Touches: ledger tree, escrow pool, payer state. Note: `Open`
is a public ledger event; hiding *that* a party opened a channel
(funding-graph leakage) is explicitly out of scope (§5).

**$Spend(pp, st_P, m) \to (t, st_P')$.**
Run by the payer, off-ledger, at its current index $i$, on gateway-bound
message $m = (G, \hat{m})$. Produces the ticket

$$t = \big(\pi,\ root,\ e,\ nf_e,\ s = (x, y, nf)\ [,\ \text{certified } E(R) \text{ presentation in B}]\big)$$

where $\pi$ is a NIZK proof of the spend relation $\mathcal{R}_{spend}$
(stated per instantiation in §3/§4: membership of $cm=H_{id}(k)$ under
$root$, solvency at index $i$, well-formedness of $s$ and $nf_e$ w.r.t.
$(k, i, m, e)$). If the solvency conjunct is unsatisfiable at index $i$,
`Spend` outputs $\bot$ (it cannot produce a proof; the T4 game references
this behavior). Emitting $t$ advances the payer's index: $i' = i + 1$.
Index consumption is bound to *emission*, not acceptance: re-sending the
bit-identical ticket after an abort is permitted and safe (same point on the
line, same gateway by MC14); emitting a *different* message at a used index
is self-slashing (MC2). In A, `Spend` is non-interactive (one message, no
payee countersignature). In B it has an interactive tail: the payee returns
a refund receipt (§4). Touches: payer state only.

**$Redeem(pp, st_G, t) \to (\text{verdict}, st_G'\ [,\ \rho])$.**
Run by a payee $G$ holding local state $st_G = (SS_G, \text{rate counters})$
where $SS_G \subseteq \{(nf, x, y)\}$ is its spent set. Checks, in order
(the egress wire protocol's admission checks, with the transport-policy
check narrowed to the gateway-binding component, MC13/MC14):

1. $\pi$ verifies;
2. $root$ equals the current ledger root (the model refreshes honest payers'
   roots instantly; staleness across rotations is a liveness wrinkle noted
   in MC5, not a security property);
3. $e$ is the current epoch (clock skew is not modeled, MC12);
4. the ticket's message names this gateway: $m = (G, \cdot)$ (MC14);
5. the rate counter for $nf_e$ is strictly under budget $b$ (else reject);
6. nullifier logic against $SS_G$:
   - $nf \notin SS_G$: **accept**; $SS_G \mathrel{+}= (nf, x, y)$; the rate
     counter for $nf_e$ increments **now** (accepts only — rejects and
     duplicates consume no budget; rev-1 fidelity finding, and T6 counts
     accepts);
   - $(nf, x, y) \in SS_G$ (bit-identical): **reject-duplicate** (no slash —
     this is the abort-retry path, MC2);
   - $nf \in SS_G$ with $x' \ne x$: **evidence** — output
     $ev = (nf, (x,y), (x',y'))$ and forward to `Dispute`.

In B, acceptance additionally declares $c \le C_{max}$ and returns the
refund receipt $\rho$ (§4). Fleet (A only): gateways exchange accepted
tuples; every accepted tuple reaches every $SS_{G'}$ within lag $L$ (§5).
**Merge-time evidence (MC17, [repair]):** when a gateway merges an incoming
tuple $(nf, x', y')$ and finds $(nf, x, y) \in SS_G$ with $x \ne x'$, it
outputs $ev = (nf, (x,y), (x',y'))$ and forwards it to `Dispute`
immediately. This is required protocol behavior — without it, a
cross-gateway double spend (one conflicting pair, never a third signal)
would never generate evidence and T6's slash clause would be vacuous (rev-1
blocking finding). Verdicts of `Redeem` by an honest payee define the
*accepted-spend ledger* that T1, T2, and T6 quantify over. Touches: payee
state; (via `Dispute`) ledger.

**$Close(pp, \text{role}, st, \mathcal{L}) \to \text{settlement}$.**
Either side, at any time.

- *Payer close* — instantiation A ("close-by-unused-enumeration", MC20
  [repair], **replacing** revs 1–5's close-as-final-spend): rev-5 killed
  the old design with the *gap-index understatement*: nothing enforces
  index contiguity, so a payer could skip index 0, spend at indices
  $1..m$ (indices are hidden witnesses), close at $j = 0$ — colliding
  with nothing, hence undisputable — and recover the full $D$ after
  consuming the service. The root cause is that the ledger has no
  verifiable spend count. Repair: the payer submits
  $(cm, U, \pi_{close})$ where $U$ is the set of **revealed nullifiers of
  its claimed-unused indices**, and $\pi_{close}$ proves $cm = H_{id}(k)$
  and that each $nf \in U$ equals $H_{nf}(H_a(k, i))$ for a distinct
  index $i < cap := \lfloor D/C \rfloor$, for the same witness $k$.
  Revealed unused nullifiers are PRF-fresh values never emitted anywhere,
  so past spends stay unlinkable; $|U|$ reveals the spend count, exactly
  the leak MC15 already scopes. During the window $\tau$: (a) a
  registered gateway holding an *acceptance whose nullifier is in $U$,
  checkpointed before the close transaction*, presents it — the claim is
  proven false, the close is voided, and the channel is slashed (a false
  unused-claim is the new self-conviction; the pre-close-checkpoint
  requirement blocks post-hoc fabrication, since an honest closer's
  genuinely-unused nullifiers are PRF-hidden until the close reveals
  them, so no pre-close checkpoint can contain them). **A
  checkpoint-dispute slash is a fund-slash — $k$ stays hidden (rev-10
  F9-1a): its remainder stays in the pool with no submitter bounty (a
  bounty would break conservation, since the member's remaining used
  nullifiers cannot be enumerated or barred without $k$), and ordinary
  sweeps continue against the pool with no deadline** — the same rule as
  the settlement-detected slash (F8-m4). (b) Ordinary `Dispute` evidence
  freezes the channel and voids the close as usual (that path recovers
  $k$ and is an identity-slash with the full MC4 window mechanics).
  At expiry the ledger **automatically** pays
  $C \cdot |U| + (D - cap \cdot C)$ — for an honest closer with $j$
  emitted indices, $|U| = cap - j$ and the payout is exactly
  $D - j \cdot C$, the same floor as before — **with a two-sided sweep
  bar (rev-6 + rev-7): at settlement the ledger first checks $U$ against
  $RedeemedNF$, and any $nf \in U$ already swept — pre-close or during
  the window — is a proven-false claim with the disproof on-ledger,
  voiding the close and slashing, no checkpoint needed — a
  settlement-detected slash has no evidence submitter, and its
  post-window remainder stays in the pool (rev-8 F8-m4); it then records
  $U$ and thereafter refuses sweeps of any $nf \in U$** (rev-6 blocking
  find: without the forward bar, a false claim uncaught by a stale
  checkpoint is paid twice, refund plus sweep, and the commingled pool
  bears it; rev-7 found the forward-only bar leaves the sweep-first
  ordering double-paying identically. With both directions the pool
  conserves in every ordering; the residual loss from a stale
  checkpoint — a false claim neither checkpointed nor yet swept — lands
  on the tardy gateway, which is the honest reading of checkpoint
  cadence as that gateway's own lever), and the channel is
  closed **and evicted from the tree (root rotates)**, so post-close
  spend proofs fail and in-flight tickets die; gateways have the window
  to redeem in-flight tickets and checkpoint. A's honest-limits note,
  symmetric to B's racing note (rev-6): an acceptance in flight at the
  close transaction is structurally un-checkpointable pre-close, so even
  perfect cadence cannot protect it — the gateway's exposure is bounded
  by its acceptance-in-transit volume at any close event. A fully spent-down payer closes with
  $U = \varnothing$ at payout $D - cap\cdot C$ (the sub-ticket residue);
  over-claiming *fewer* unused indices than it has only donates.
- *Payer close* — instantiation B (certified-count close with nullifier
  reveal, MC18/MC20): the payer submits $(cm, j, nf_j, \pi_{close})$
  where $\pi_{close}$ proves $cm = H_{id}(k)$, that a payee-signed
  receipt certifies $(H_{tag}(k), R, j)$ — the receipt chain certifies
  the count and $\mathcal{R}_{spend}^B$ proves each spend's index equals
  its receipt's certified $n$, so B spends are **contiguous by
  construction** — and that $nf_j = H_{nf}(H_a(k, j))$: the revealed
  nullifier of the first index *beyond* the declared count ($j = 0$
  closes carry no receipt conjunct — $cm$ plus the $nf_0$ proof suffice;
  rev-7: otherwise a payee that withholds the genesis signature wins $D$
  by ForceClose). Contiguity is what makes the reveal decisive (rev-6
  blocking find): a stale receipt's $j$ is an already-spent index, its
  nullifier sits in the payee's pre-close checkpoint, and the dispute
  convicts. **The dispute discipline (rev-7 blocking find — receipt
  supply is adversary-controlled, so a bare nullifier match would let a
  receipt-withholding payee wedge an honest payer into a slashable
  close):** B checkpoint entries are *receipt-bearing* — the tuple
  carries the accepted ticket's presented ciphertext, declared cost $c$,
  increment randomness $r'$, and the signed successor
  $ct' = ct^* \boxplus Enc(pk_E, (0, C_{max}-c, 1); r')$ with
  $\sigma_S(ct')$, all publicly checkable against each other — and a
  stale-close dispute must open the **full tuple** for $nf_j$ from a
  pre-close checkpoint, not membership alone. A valid dispute does
  **not** slash: it opens a response sub-window of duration $\tau$
  ($> \Delta$, §1) in which the closer may re-close at count $j+1$ —
  the dispute itself just *published the withheld receipt*, and the
  payer reconstructs its opening from its own ticket opening plus the
  public $(c, r')$. Only failure to upgrade voids the close and slashes.
  Escalation is capped by contiguity: a receipt at $n = j+2$ requires a
  payer-produced ticket certifying $j{+}1$, so each round moves one
  count, cheaters converge to their true count or slash, and an honest
  payer — whose receipt-vs-accepted gap is at most 1, again by
  contiguity — upgrades at most once, losing at most the one $C_{max}$
  that T3 scope note (i) already prices per abort. An honest closer at
  its true count faces no valid dispute at all: its $nf_j$ is PRF-hidden
  pre-close, and a fabricated receipt-bearing tuple would need a
  payer-produced ticket at index $j$ that was never emitted (knowledge
  soundness). Neither gap-index (contiguity), stale-receipt (reveal +
  checkpoint), nor receipt-withholding (upgrade sub-window) attacks
  survive. $\mathcal{R}_{close}^B$
  additionally verifies the two settlement caps: $R \le j\cdot C_{max}$
  (rev-3 R3-1: else a colluding payee signs inflated $R$ and drains the
  pool) and $j\cdot C_{max} \le D + R$ (rev-4 F1: else an overstated
  index pays the payee unboundedly from the pool; an honest closer's last
  spend proved exactly this inequality, so it never blocks). With both
  caps the payouts are well-defined naturals: the payer receives
  $(D+R) - j\cdot C_{max} \in [0, D]$, the payee receives
  $j\cdot C_{max} - R \le D$ at the same event — its exact net
  $\sum c_\ell$ when the chain is honest — and the two sum to $D$:
  conservation per channel by construction. The window $\tau$ admits
  ordinary `Dispute` evidence and the stale-receipt dispute above;
  understatement self-convicts (contiguity + reveal), overstatement is
  capped. Close-racing exposure
  (honest limitation): service accepted between a close's inclusion and
  its settlement cannot be netted (the closing channel is unattributable
  among tickets); the payee's exposure is bounded by its acceptance rate
  times $\tau$, and an implementation shortens it by pausing acceptance
  while any close window is open. The close reveals $cm$ and the spend
  count $j$ (MC15).
- *Payee close* — instantiation A ("sweep"): a **registered gateway**
  (MC16) submits redeemed tuples $(nf, x, y, \pi)$ to $\mathcal{L}$ at any
  time; the ledger verifies $\pi$ against $\mathcal{R}_{spend}$
  specifically (close transactions carry $\pi_{close}$, which is not
  sweepable — rev-2 NEW-6 — and nullifiers recorded in a settled close's
  $U$ are sweep-barred, rev-6), keeps a global set $RedeemedNF$, dedups
  by $nf$, and pays $C$ per fresh $nf$ from the pool. Sweeping is
  unilateral: it requires no payer cooperation. Sweeps of tickets
  accepted before a payer-close remain payable after it: the close
  refunds only claimed-unused indices and bars them from sweeps, so the
  pool retains at least $C$ per used-and-unclaimed index — the ceiling
  on what can still be swept, now exact on the honest path and
  conservative under false claims (rev-5 found the old declared-$j$
  close broke this claim via gap indices; MC20 + the sweep bar restore
  it). **The honest sweep protocol includes monitoring:** an honest gateway
  watches `Dispute` events and sweeps its outstanding tickets of a slashed
  member within that window (T2 depends on this duty; rev-1 finding).
- *Payee close* — instantiation B ("force-close", MC18 [repair]): B has no
  unilateral nullifier sweeps (rev-2 blocking finding NEW-1: sweep-plus-
  refund-close pays $D + R$ out of a $D$ deposit, and pre-slash
  unattributability blocks per-channel netting). Instead the payee may
  submit $\text{ForceClose}(cm)$ at any time; the ledger opens a window
  $\tau$ for the payer to respond with its own close (settling as above).
  If the payer stays silent past the window, the channel settles by
  **forfeit**: the full $D$ goes to the payee. An honest payer always
  responds in time — it monitors the ledger for its $cm$ (§1) and
  $\tau > \Delta$ guarantees its response lands — so forfeit only
  transfers value from payers that abandoned the protocol.
  **B slash path (rev-3 R3-2; scoped to identity-slashes in rev-10,
  F9-1b):** a *slashed* B channel is frozen and never closes, so
  close-time netting cannot settle it. For an **identity-slash**
  (`Dispute`-proper, $k$ public), B retains the slash-window
  per-nullifier claims — the payee claims $C_{max}$ per checkpointed
  accepted nullifier of the slashed member against the remaining deposit
  (no refund netting: a cheater forfeits its refunds); attribution runs
  on the public $k$. For a **fund-slash** (failed upgrade, $k$ hidden —
  rev-9's taxonomy exposed that the per-nullifier claims cannot run
  here, since B-rerand makes acceptances unlinkable and only the
  disputed $nf_j$ is attributable): the channel settles by **forfeit of
  $D$ to the payee** — the slashed party is a proven cheater or
  protocol-abandoner that declined its own published upgrade path, the
  payee is B's sole counterparty, and the forfeit mirrors the
  ForceClose-forfeit and covers the payee's otherwise-stranded revenue
  ($\sum c \le D$ by T1-B; conservation-safe). No double-payment arises because **no close of any kind —
  cooperative or forfeit — executes on a frozen channel**; a pending
  ForceClose window is voided by the freeze (rev-4 F2). Without this path, a B payer consumes
  service, self-slashes, and collects the remainder as its own `Dispute`
  bounty — the same race MC4 closed in A.

Touches: escrow pool, $RedeemedNF$, channel status.

**$Dispute(pp, ev, \mathcal{L}) \to \{\text{slash}(cm), \bot\}$.**
Run by *anyone* holding evidence $ev = (nf, (x,y), (x',y'))$, $x \ne x'$.
The ledger recovers $a = (y-y')/(x-x')$ and $k = y - a\cdot x$, checks
$nf = H_{nf}(a)$ and $cm = H_{id}(k)$ for some open $cm$ in the tree. On
success: the channel is frozen and $cm$ removed from the tree (root rotates;
future spend proofs for $k$ fail, MC5); a reconciliation window $\tau$ opens
in which **registered gateways** (MC16) may claim, against the member's
remaining deposit: (i) sweeps of outstanding redeemed tuples of this member
— attribution is now possible because $k$ is public, so the member's
nullifiers $nf_i = H_{nf}(H_a(k,i))$ are enumerable (MC4); and (ii)
*documented conflicting acceptances*: a gateway holding an accepted ticket
whose $nf$ is dedup-blocked in $RedeemedNF$ under a different $x$ presents
the evidence pair and is paid $C$ per documented conflict. Claim seniority
when the remainder is short: (i) before (ii), pro-rata within each class
(MC19). **Window-claim provenance (MC19, [repair]):** both claim
kinds are valid only for acceptances *checkpointed before the slash
transaction* — each gateway posts a commitment to its accepted set to the
ledger **at any time it chooses, and at least once per epoch** (rev-3
R3-3: a fixed per-epoch cadence would leave every L-window conflict
un-checkpointed at slash time whenever $L < T_e$, hollowing out the
recovery this mechanism exists to protect — checkpoint cadence is
therefore the second operational recovery lever, alongside sweep cadence),
and a window claim must open against a pre-slash checkpoint. **The
checkpoint is a binding set commitment — concretely, a Merkle root over
the gateway's accepted tuples — and every claim or close-dispute opens it
with a membership witness against the pre-slash (resp. pre-close) root**
(rev-6 required fix: without pinned binding semantics, the
honest-closer-protection argument — "a genuinely-unused nullifier is
PRF-hidden until revealed, so no pre-close checkpoint contains it" — has
nothing to bite on; binding is collision resistance, assumption 3, so an
opening for a value chosen post-close fails). Without this, the window is forgeable by the fleet itself: once
`Dispute` publishes the evidence pair, $k$ is recomputable by anyone, so a
malicious *registered* gateway could mint fresh "conflicts" and old-root
spend proofs at will (rev-2 blocking finding NEW-2 — the rev-2 text
wrongly cited T7's lemma here; T7 protects only members whose $k$ is still
secret). After the window, the remainder of $D$ goes to the evidence
submitter as bounty. **Slash taxonomy (rev-9, K4):** `Dispute`-proper
slashes run the line algebra and **publish $k$** — retroactively linking
the member's entire spend history (the honest-limits cost of
detect-and-slash, owed a paragraph in the paper); close-dispute and
settlement-detected slashes (MC20) run bit-matches and receipt
exhibitions only — **$k$ stays hidden**, so they are fund-slashes, not
identity-slashes. Touches: escrow pool, tree, $RedeemedNF$, checkpoint
log.

---

## 3. Instantiation A: flat-ticket RLN credit protocol

The protocol the egress fleet runs. No refunds, no revocation, one
inequality.

- Price is flat: every ticket costs $C$.
- Spend relation $\mathcal{R}_{spend}^A$, with public input
  $(root, e, nf_e, x, y, nf)$ and witness $(k, i, \text{Merkle path})$:
  1. $cm = H_{id}(k)$ is a leaf under $root$ (Merkle path valid);
  2. **solvency**: $(i+1)\cdot C \le D$ (integer inequality, §1);
  3. $a = H_a(k,i)$, $y = k + a\cdot x$, $nf = H_{nf}(a)$, with
     $x = H_x(m)$ for the gateway-bound $m$ (MC14);
  4. $nf_e = H_e(k, e)$.
- `Spend` is one message; there is no payee-held per-payer state and no
  payee countersignature, so a payee cannot corrupt a payer's channel state
  by aborting — an abort is exactly a denial of service (relevant to T4's
  abort oracle).
- Fleet: $N$ gateways each hold $SS_G$ and reconcile within $L$, generating
  evidence at merge time (MC17). Double spends across gateways are
  *detected and priced*, not prevented: this is the "async window is priced
  by the deposit" design, and T6 is its statement.
- Theorems instantiated here: T1–T5 with $N=1$ or synchronous $SS$
  (see T1 scope note), T4, and T6–T7 (which only exist here).

## 4. Instantiation B: refund-bearing variant

The variant the source construction needs for variable request cost (LLM
metering; the 100x cost-variance argument). Single payee ($N = 1$), holding
signature keypair $(vk_S, sk_S)$.

- Per accepted spend the payee declares actual cost $c \le C_{max}$ and owes
  a refund of $C_{max} - c$. The payer maintains a running refund total
  $R = \sum (C_{max} - c_\ell)$ over its accepted spends.
- **Certified refund chain (MC7, revised after two rev-1 findings; count
  added in rev-6/MC20).** The certified object is a ciphertext $ct$
  encrypting the *triple* $(tag, R, n)$ under $pk_E$, where
  $tag = H_{tag}(k)$ **binds the chain to the channel** — without the tag,
  honestly issued receipts from one channel splice into another channel's
  solvency proofs and T1 falls (rev-1 blocking finding) — and $n$ is the
  **certified spend count** (rev-6: without it, spends need not be
  contiguous and understatement closes exist). The chain: genesis $ct_0$
  certified at `Open` (§2); per accepted spend the payee computes
  $ct' = ct \boxplus Enc(pk_E, (0, C_{max}-c, 1);\ r')$ — incrementing
  both the refund total and the count — and returns the receipt
  $\rho = (ct', \sigma_S(ct'), r', c)$; the increment's encryption
  randomness $r'$ travels in the receipt, so the payer can maintain the
  full opening of its certified ciphertext and prove consistency in zero
  knowledge (without $r'$ the honest payer cannot form any solvency
  witness after its first refund — rev-1 finding). The payer tracks
  $(R, n)$ in plaintext; no honest algorithm ever decrypts.
- **Solvency** becomes $(i+1)\cdot C_{max} \le D + R$, proven in-circuit
  against the certified $ct$: the witness includes
  $(k, R, n, \text{opening})$, and $\mathcal{R}_{spend}^B$ additionally
  proves the ciphertext's tag component equals $H_{tag}(k)$ for the same
  $k$ as the membership witness (chain binding), **that the spend's index
  $i$ equals the certified count $n$** (rev-6/MC20 contiguity conjunct),
  and that a valid $\sigma_S$ covers the presented ciphertext.
  Withholding $\rho$ is the payee's abort lever in this instantiation: it
  stalls the growth of $R$ and can render a payer insolvent for future
  $C_{max}$-spends (T4's evict oracle has real teeth here). Rev-7 found
  withholding also wedges the close at the stale count, weaponizing the
  $nf_j$ dispute against honest payers; the §2 upgrade sub-window repairs
  it — a dispute publishes the withheld receipt and the payer re-closes
  one count higher, so the abort lever costs the payer at most one
  $C_{max}$ and can never slash it.
- Two representations of the certified total, both formalized:
  - **B-static**: the payer presents, at its next spend, the ciphertext $ct$
    bit-identical to the one the payee last signed, with the signature
    verified in the clear. The payee can match the presented $ct$ against
    its own issuance transcript, linking consecutive spends into a chain
    (and, transposed to the original construction, linking across
    settlements — the omarespejel finding; MC7). This is the original
    design and it is *broken*: T4's game must be winnable against it (the
    calibration requirement, T4 below).
  - **B-rerand**: the payer re-randomizes, presenting
    $ct^* = Rerand(ct; r^*)$, and proves in zero knowledge that $ct^*$ is a
    re-randomization of *some* payee-signed ciphertext whose tag component
    matches its $k$ (signature verified in-circuit, original $ct$ hidden).
    This is the patched design and T4 must pass against it.
- Settlement (MC18): the channel settles once, at close. The payer's
  payout is $(D + R) - j\cdot C_{max}$, proven against its latest certified
  receipt, with both settlement caps $R \le j\cdot C_{max}$ and
  $j\cdot C_{max} \le D + R$ enforced in $\mathcal{R}_{close}^B$ (rev-3
  R3-1, rev-4 F1); the payee's payout is $j\cdot C_{max} - R = \sum c_\ell$
  at the same event. There are no per-nullifier sweeps in B outside the
  slash window; a silent payer is handled by the payee's
  force-close-with-forfeit path (§2). Rev-2 NEW-1 established that A's
  sweep mechanics cannot conserve funds in B; this close-time netting
  conserves exactly $D$ per channel by construction.
- B-static's genesis anchor (rev-2 NEW-4): $ct_0$ is certified against
  $cm$ at `Open`, and B-static presents it *bit-identically at the first
  spend* — so the break in B-static is not merely spend-to-spend chaining
  but direct first-spend-to-identity linkage. This is part of the intended
  broken-variant behavior and the T4 calibration distinguisher may use it.
- Theorems instantiated here: T1–T5, and T4 in both representations with the
  calibration pair.

---

## 5. Model boundary

We formalize the **protocol layer** over an idealized ledger and idealized
cryptography. Everything below enters as named assumptions in
`Assumptions.lean`, each annotated with the standard property it encodes.
We do **not** verify circuits: the NIZK relation $\mathcal{R}_{spend}$ is
the mathematical statement written in §3/§4, and the fidelity of any circuit
to that statement is out of scope. Anyone claiming this repo verifies SNARKs
is misreading it.

**Idealized ledger $\mathcal{L}$.** A single, totally ordered, atomically
executed transaction log. Honest transactions submitted at time $t$ are
included by $t + \Delta$. No reorgs, no censorship beyond $\Delta$, contract
logic (escrow pool, tree, $RedeemedNF$, windows, slashing, automatic
close settlement) executes exactly as specified in §2. The adversary may
submit arbitrary transactions and observe the full log, but cannot violate
the above.

**Cryptographic assumptions** (one per primitive; theorems cite which they
use; the Lean formalization works in the random-oracle model and each
assumption below names the Lean declaration that carries it):

1. **NIZK knowledge soundness.** From any accepted proof, an extractor
   obtains a witness in $\mathcal{R}_{spend}$. Used by: T1, T2, T3, T6, T7.
2. **NIZK zero-knowledge.** Proofs are simulatable without the witness.
   Used by: T4.
3. **PRF/ROM idealization of the hash family**, with pairwise domain
   separation (MC9): distinct indices give independent-looking $a$'s;
   nullifiers across indices/epochs are unlinkable; collision resistance
   throughout; $H_{id}$ hiding/binding as a commitment. Stated consequence
   carried as its **own named assumption** (rev-1 finding: standard PRF
   security does not by itself yield it, because $y = k + a\cdot x$ uses the
   key additively — a KDM-flavored use): **`single_signal_hiding`** — one
   point $(x,\ k + H_a(k,i)\cdot x)$ per index, with $x \ne 0$ (§1,
   rev-6), reveals nothing about $k$: algebraically, one observation is
   consistent with *every* candidate secret via a unique coefficient
   (`rln_single_point_hiding` in `Zkpc/Games/RLN.lean` proves exactly
   this). Used by: T4, T7 (and index-injectivity in T1).
4. **EUF-CMA signatures** for the payee's refund key $sk_S$ (B only).
   Used by: T1, T2, T3 in instantiation B (rev-2 NEW-7: forged receipts
   would inflate $R$ at the settlement, so T2-B uses it too).
5. **Re-randomizable additively homomorphic encryption**: IND-CPA, correct
   homomorphic addition, re-randomization producing ciphertexts
   distributed independently of the input ciphertext, and
   **opening-homomorphism** — openings of summands combine to an opening
   of the $\boxplus$-sum (rev-8 F8-m1: implicitly load-bearing since the
   rev-2 receipt-randomness fix, and load-bearing twice over for the
   rev-8 upgrade-path reconstruction; every standard instantiation has
   it, but the Lean assumption must carry it). (B only.) Used by: T4 on
   B-rerand; honest-completeness of B spends and closes; the T3-B/T5-B
   upgrade clauses. Its *absence of use* is what breaks B-static.
6. **Blind-signature unforgeability and blindness.** Declared in
   `Assumptions.lean` per the executor contract; **unused** by
   instantiations A and B (they would be exercised by a BOLT-style
   blind-signed-state instantiation, which is not in scope here). Their
   presence must not be silently load-bearing; the axiom audit (task K2)
   checks this.

Axioms are stated reduction-shaped where they bound adversaries (for every
PPT $\mathcal{A}$ there is a bound), and T4's Lean statement must be a
*reduction to* assumptions 2/3/5, never a per-scheme "advantage is
negligible" axiom — that would assume the theorem (K2 checks this
specifically).

**Explicitly out of scope** (the theorems say nothing about these):
circuit correctness; network-level timing, latency, token-count, and content
fingerprints (the traffic-analysis relinking surface); the deposit-edge
linkage of `Open` on a public ledger (funding-graph leakage; the sources
prescribe shielded funding, we do not model it); a global passive adversary
correlating both ends; **relationship anonymity** — which destinations a
member reaches — which is the Tor transport layer's property, not the
payment layer's; the Tor transport beneath the protocol; denial of service
against the ledger; the policy stake $S$ of the source construction (MC8);
the spend-count-at-close side channel (MC15).

---

## 6. Adversary conventions

All adversaries are PPT, adaptive, and rushing (they see honest messages
before choosing their own within a round). Corruption is static per game
(the corrupted set is fixed at game start) — see MC10. The adversary always
controls message scheduling between parties, subject to the ledger's
$\Delta$ and the fleet's $L$ (which are guarantees of the *model*, i.e., of
honest infrastructure, not of the adversary). "Controls a party" means it
runs arbitrary code in that party's place, holding all its keys and state.
Oracles named in a game are the *only* interfaces to honest parties; honest
parties otherwise follow the protocol exactly, including the abort-retry
rule of MC2, the sweep-monitoring duty of MC16, the checkpointing duty of
MC19 (rev-6: load-bearing for slash recovery *and* close protection), and
the payer's ledger-monitoring duty of §1.

---

## 7. Theorems

Each theorem: statement with quantifiers, the adversary it holds against,
what violating it means, and an anti-vacuity note (why the statement is
non-trivial). "Accepted" always means: an honest payee's `Redeem` returned
**accept**. Attribution of an accepted ticket to a member secret $k$ means:
the knowledge-soundness extractor, applied to the ticket's proof, returns a
witness containing $k$ (well-defined per ticket; $H_{id}$ binding and
collision resistance pin one $k$ per $cm$ and per $nf$).

**Proof order** (no circularity; rev-1 reviewer's sequencing adopted):
T1 → single-signal exculpability lemma → T2/T3 → T5 → T6 → T4 → T7.

### T1 — No overspend

**Statement.** For every PPT adversary $\mathcal{A}$ controlling all payers
and the scheduler, interacting with a single honest payee (equivalently: a
fleet whose spent sets are perfectly synchronized, $L = 0$), and for every
member secret $k$ with open deposit $D$: at every point of every execution,
the total value of accepted tickets attributed to $k$ is at most $D$.
Flat-ticket: $C \cdot |\{\text{accepted tickets attributed to } k\}| \le D$.
Refund variant: $\sum_\ell c_\ell \le D$ over accepted tickets attributed to
$k$, where $c_\ell$ are the payee-declared actual costs, provided the
refund receipts summed into any accepted solvency proof were honestly issued
**to this channel** — i.e., carry this channel's chain tag $H_{tag}(k)$
(MC7 binding; EUF-CMA excludes forged receipts, the tag excludes spliced
ones).

**Adversary.** Arbitrary payer coalition: chooses all messages, indices,
proofs, timing; may attempt replays, index reuse, forged proofs, forged or
cross-channel refund receipts. No control of the payee or ledger.

**Violation.** Some reachable state where the attributed accepted value of
one deposit exceeds $D$.

**Scope note.** T1 is the $L = 0$ statement. With reconciliation lag
$L > 0$ the invariant is genuinely false during the lag window — that
relaxation is not a bug but the design, and its exact price is T6.

**Anti-vacuity.** The adversary class includes real attacks: against a payee
that skips check 6 (nullifier logic), replaying one index at two messages
spends $2C$ from a budget of $C$; against a circuit lacking the solvency
conjunct, index $\lceil D/C \rceil + 7$ verifies fine; against the tagless
rev-1 receipt design, receipts farmed on a cheap channel pump a second
channel's $R$ without bound (the recorded rev-1 counterexample). All three
broken schemes lose, so the statement discriminates.

### T2 — Payee balance security

**Statement (A).** For every PPT adversary $\mathcal{A}$ controlling all
payers and the scheduler: an honest payee that accepted a set $T$ of
tickets and follows the sweep protocol (including the MC16 monitoring
duty) has, by every time $t_{done} \ge$ (its last sweep submission for
$T$) $+ \Delta$ plus, where a slash intervened, the close of that dispute
window, settled from the ledger exactly $C \cdot |T|$, regardless of payer
behavior — including payers who close early, close with false
unused-claims (MC20), or deliberately trigger their own slash (the
self-slash race), *given the modeled `Dispute` with its gateway-priority
window* (MC4/MC16) *and given the payee's checkpoints are current at every
payer-close* (rev-6: a used index falsely claimed unused is caught only
from a pre-close checkpoint; with the MC20 sweep bar, a stale checkpoint
costs the tardy gateway exactly the un-checkpointed refunded tickets, and
the in-flight facet — acceptances in transit at the close transaction —
is structurally unprotectable and bounded by transit volume, §2).
The deadline is T2's own; T5 covers the close path (rev-1 de-circularization).
The upper bound ("exactly", not "at least") holds unconditionally: the
ledger's $nf$-dedup and per-ticket price cap it.

**Statement (B, under MC18 close-time netting).** For every PPT adversary
controlling all payers and the scheduler: an honest payee that follows the
protocol (issuing honest receipts, checkpointing, force-closing abandoned
channels) settles, per channel, **at least** $\sum_\ell c_\ell$ over that
channel's spends **accepted before the close's ledger inclusion** (rev-6:
a spend accepted between a close's inclusion and its settlement is
structurally unattributable and unpaid — the racing exposure §2 scopes,
bounded by acceptance rate times $\tau$; the rev-3 claim that a stale
receipt "only overpays the payee" was inverted by the rev-6 count
coupling and is retracted — stale-receipt closes are now *caught*, not
absorbed, via the $nf_j$ reveal) — with equality exactly when the payer
closes *cooperatively*, defined as a transcript predicate: the close
presents the latest receipt at the true spend count —
and exactly $D$ (a forfeit, $\ge \sum_\ell c_\ell$ by T1-B) when the payer
abandons; each within $\Delta + \tau$ of the channel's **final**
(re-)close or force-close event — against a stale or cheating close the
upgrade cascade adds up to one round per understated count before that
final close (rev-8 F8-m3; the honest-payer case has at most one round,
T5). A B channel hit by an **identity-slash** settles through the
slash-window per-nullifier claims (§2 MC18/R3-2), recovered up to the
remaining deposit against pre-slash checkpoints, exactly as in A; one hit
by a **fund-slash** (failed upgrade) settles by forfeit of $D$ to the
payee (§2, rev-10 F9-1b — the per-nullifier claims are $k$-gated and
cannot run when $k$ stays hidden). Forged-receipt
inflation of $R$ is excluded by EUF-CMA (§5.4) and receipt inflation by a
*colluding* payee is capped by $\mathcal{R}_{close}^B$'s enforced
$R \le j\cdot C_{max}$ (rev-3 R3-1).

**Adversary.** Arbitrary payer coalition; may submit any ledger
transactions, including racing the payee's sweep with payer-closes and
self-slashes. No control of the payee or ledger. (Sweep front-running by
payers is excluded by MC16's gateway authentication — rev-1 finding; without
it this theorem is false.)

**Violation.** An execution in which the honest payee's settled total for
$T$ differs from the stated amount after the stated deadline.

**Scope note.** Stated for a single honest payee ($N = 1$, both
instantiations). In the fleet, cross-gateway replays are rejected outright
(MC14), and conflicting acceptances at distinct gateways are compensated
through the `Dispute` window's documented-conflict claims **only up to the
member's remaining deposit at slash time, and only for acceptances already
checkpointed when the slash lands** (rev-2 NEW-3, rev-3 R3-3: an
exhaust-then-burst member leaves a near-empty remainder, and
un-checkpointed L-window conflicts are unclaimable); the aggregate
uncompensated exposure is bounded by T6's $f(L)$, and the deployment
levers that shrink it are sweep cadence and checkpoint cadence, not
$f(L) < D$.

**Anti-vacuity.** Against the raw source construction — where a slash pays
the whole deposit to the first claimant with no gateway-priority window —
the self-slash race is a winning adversary: consume service, self-slash,
race the sweep, and the payee's settled amount falls short. Against
permissionless sweeps, the payer front-runs its own tickets' sweep. The
theorem is exactly as strong as those two repairs (MC4, MC16), which is why
both are flagged for review.

### T3 — Payer balance security

**Statement.** For every PPT adversary $\mathcal{A}$ controlling the payee
(in the fleet: all $N$ gateways), all other payers, and the scheduler: an
honest payer with deposit $D$ that has emitted $j$ spend tickets (its
authorized spends; emission is the authorization event, MC2) can always,
via `Close` and the elapse of the dispute window, recover at least
$D - j\cdot C$ (flat) resp. $D - j\cdot C_{max} + R$ where $R$ is the total
of refund receipts it actually holds (refund variant); and **no PPT
adversary produces `Dispute` evidence that slashes an honest payer**, except
with probability $negl(\lambda)$ — formally the FRAME game of T7 with the
adversary strengthened to control all $N$ gateways, discharged by the same
single-signal exculpability lemma (an honest payer emits at most one signal
per index — under MC20 the close emits **no** signal at all, only
PRF-fresh nullifier reveals with no line point; producing a second point
on any of its lines requires $k$) — **and no close-dispute path slashes
it either** (rev-7/8: in A an honest $U$ contains only never-emitted
nullifiers, undisputable by checkpoint binding; in B an honest closer at
its true count faces no valid receipt-bearing dispute, and a
receipt-deprived closer upgrades within the sub-window at a cost of at
most one $C_{max}$, per §2's dispute discipline). Rev-1 note: "no valid evidence *exists*" was the prior
wording and is literally false — evidence always exists mathematically; what
is negligible is any adversary *producing* it.

**Adversary.** Malicious payee coalition with full protocol deviation:
refusing service, aborting at any point, withholding refund receipts,
declaring $c = C_{max}$ always, submitting arbitrary sweeps and disputes,
colluding with other payers.

**Violation.** Either the honest payer's final ledger balance is below the
stated floor, or an honest payer's deposit is slashed.

**Scope notes.** (i) The floor is stated against *emitted* tickets: a payee
that accepts a ticket and refuses service still gets paid for it. Value lost
to aborted-but-emitted indices is bounded by $C$ (resp. $C_{max}$) per
abort, and the theorem makes this explicit rather than hiding it. (ii) In
the refund variant the floor uses receipts *held*: refunds withheld by a
malicious payee are lost value, bounded by the per-spend refund; disputing
an under-declared $c$ is out of scope (it deanonymizes, per the sources).
(iii) The close charges no index (rev-6/MC20: A's close reveals the
nullifiers of the $cap - j$ unused indices, B's reveals $nf_j$ — neither
emits a signal): payout arithmetic is over the $j$ spends at indices
$0..j{-}1$, via $|U| = cap - j$ in A; the rev-1 off-by-one audit's
conclusion carries over.

**Anti-vacuity.** Against a BOLT-style scheme where closing on a stale state
forfeits the whole balance, a payee that induces one confusion about state
wins everything; against a variant where honest abort-recovery re-emits at a
*fresh* index with the same message, the payer silently burns budget under
abort griefing, violating the floor. The stated retry rule (MC2) is
load-bearing, and the game detects its absence.

### T4 — Spend unlinkability (the headline)

**Game $\mathsf{UNLINK}$ (challenge-terminated; MC15 records why).** The
challenger samples the hidden bit $b \leftarrow \{0,1\}$ at game start and
runs `Setup`. $\mathcal{A}$ plays the payee — all $N$ gateways, all payee
keys — and may additionally create and control arbitrarily many corrupt
payers (their secrets known to it; they have no interaction surface with
the candidates — payers never interact peer-to-peer — so their presence is
maximality at zero cost). The challenger creates two honest candidate
payers $P_0, P_1$, each with an open channel, equal deposits $D$, opened in
batch at the same time. **Pre-challenge oracles** (unrestricted):

- $\mathcal{O}spend(u, m)$, $u \in \{0,1\}$: $P_u$ runs `Spend` on
  gateway-bound message $m$ at its next index; the ticket is delivered to
  $\mathcal{A}$ (if `Spend` outputs $\bot$ on insolvency, $\mathcal{A}$ is
  told so). $\mathcal{A}$ responds accept/abort as it pleases (it is the
  payee); on abort $P_u$ follows the retry rule (MC2).
- $\mathcal{O}retry(u)$: $P_u$ re-sends its last emitted ticket unchanged.
- **Abort/evict powers** (the BOLT §1.4 oracle, required): aborting any
  interaction mid-protocol is subsumed by $\mathcal{A}$'s accept/abort
  choice above; eviction is $\mathcal{A}$ refusing all service to a chosen
  candidate from any point on. In instantiation B the abort lever is
  concrete: withholding the refund receipt $\rho$ stalls $R$ and can make a
  candidate insolvent for future $C_{max}$-spends.
- $\mathcal{O}close(u)$: directs $P_u$ to close (its close is a public
  ledger event $\mathcal{A}$ sees, revealing $cm_u$ and its spend count).

**Challenge and termination (session form, rev-9 — from the K4 external
review).** $\mathcal{A}$ outputs a message **vector**
$\vec{m}^* = (m^*_1, \ldots, m^*_q)$, $q \ge 1$ of its choice, at some
time; let $e^*$ be the current epoch. The game checks **at challenge
time** that neither candidate has emitted any signal during $e^*$ (rev-2
NEW-5: freshness is a challenge-time predicate on the transcript, not a
foreknowledge condition on the oracles), and outputs $\bot$ otherwise; see
MC6. The game checks both candidates are *challenge-capable for $q$*:
open, unslashed, unclosed, and solvent for $q$ more spends under their
current certified state (A: $(j_u+q)\cdot C \le D$ for $P_u$'s next index
$j_u$; B: $(j_u+q)\cdot C_{max} \le D + R_u$ against the receipts $P_u$
holds). If either is not, $\mathcal{A}$ receives $\bot$ instead of
tickets (a candidate it evicted into insolvency shrinks the capable set —
the game charges that to the anonymity set, not to the scheme; this is
precisely the calibrated content of the abort attack). Otherwise $P_b$
emits the challenge tickets $t^*_1..t^*_q$ for $\vec{m}^*$ at its next
$q$ indices, all within $e^*$ (sharing the session pseudonym
$nf_{e^*}$), and $\mathcal{A}$ receives the batch. **The game then
ends**: $\mathcal{A}$ outputs its guess $b'$ immediately; no oracle
answers after the challenge (or after $\bot$). Why the session form: the
K4 external review showed the single-spend challenge ($q = 1$) certifies
only *first-spend-per-epoch* unlinkability — a scheme leaking a
persistent cross-epoch tag only on second-and-later spends within an
epoch passed the $q=1$ game while being lifetime-linkable for any member
that spends twice per epoch (the deployed fleet's normal usage). With
the session challenge, such a tag surfaces inside the challenge batch
and matches the pre-challenge transcript, so the game catches it; what
is certified is the unlinkability of a member's **whole epoch session**
to its identity and its other epochs, with within-session linkage via
$nf_{e^*}$ remaining by design (MC6).
Because $b$ is sampled up front, the advantage is well-defined on every
execution path, and $\bot$-executions contribute exactly $\tfrac12$
(rev-1 finding: the prior game sampled $b$ after the capability check,
leaving the advantage conditioned on an event where $b$ did not exist).

$$\mathsf{Adv}^{\mathsf{UNLINK}}_{\mathcal{A}} = \left| \Pr[b' = b] - \tfrac12 \right|.$$

**Statement.** For every PPT $\mathcal{A}$:
$\mathsf{Adv}^{\mathsf{UNLINK}}_{\mathcal{A}} \le negl(\lambda)$, under NIZK
zero-knowledge and `single_signal_hiding`/ROM (instantiation A), plus
IND-CPA and re-randomizability (instantiation B-rerand).

**Why challenge-terminated (MC15, [repair of the game, not the protocol]).**
Rev-1's game answered oracles after the challenge, and that game is
unsatisfiable — three distinguishers win it against *every* scheme,
including the sound ones: replay the challenge via $\mathcal{O}retry$;
probe post-challenge solvency exhaustion (the challenge consumed one index
of $P_b$ only); read the spend count $j$ off a subsequent close. All three
exploit that the challenge advances only $P_b$'s state. Ending the game at
challenge delivery removes the bit-dependent continuation while keeping
full pre-challenge abort/evict power, which is where the BOLT §1.4 content
lives. The residual real-world leak is stated honestly: **the aggregate
spend count revealed at close is a side channel this theorem does not
cover** (same epistemic status as MC6's within-epoch linkage) — a member
that closes immediately after a spend correlates its count with observed
traffic. The paper's honest-limits section must carry this.

**Calibration battery (rev-9, K4 Concern 5: one bit of separation is
thin evidence; the battery adds must-catch and must-win points).** Beyond
the B-static/B-rerand pair below, the H-phase formalization must also
exhibit: a **must-catch A-index-leak variant** (tickets carry the index
in the clear — the game must be winnable against it) and a **must-catch
$nf_e$-reuse variant** (the epoch pseudonym derivation reused across
epochs — winnable via cross-epoch matching); and FRAME's battery gains
**must-win degenerate-RLN adversaries** (against $y = k$ and against
$a$ reused across indices, concrete adversaries must win FRAME with
probability 1 — the anti-vacuity notes' breaks, made constructive); and a
**must-catch multiplicity-tag variant** (rev-10 F9-m2: a persistent tag
leaked only on second-and-later spends within an epoch — the K4
construction that motivated the session form; a $q = 2$ session
distinguisher must win against it, constructively witnessing that the
session challenge closes Concern 1).

**Calibration requirement (definitional test, binding on the Lean game).**
Instantiated on **B-static**, the game must be *winnable*: there is a
concrete PPT distinguisher with advantage $\tfrac12 - negl(\lambda)$ —
pre-challenge, it runs accept cycles issuing refund receipts with **equal
totals** to both candidates (rev-1 correction: the prior text said
"different refund totals," which the fixed game makes unnecessary and a
symmetry precondition would forbid; equal totals suffice); the receipts'
ciphertexts still differ by encryption randomness, and the adversary
generated both. The challenge ticket in B-static presents the last-signed
ciphertext bit-identically, so the distinguisher matches $t^*$'s presented
$ct$ against its own issuance transcripts and outputs the owner. This
distinguisher uses no post-challenge queries, so it survives the game
repair (verified end-to-end in rev-1 review). Instantiated on **B-rerand**,
the same game must yield negligible advantage for all PPT adversaries. A
game definition that cannot separate these two variants is wrong, and this
pair is the built-in test that ours is not. The B-static attack must be a
constructive term in the formalization, not an unproven gap.

**What is NOT claimed** (stated so the theorem cannot be over-read): spends
within one epoch share the epoch pseudonym $nf_e$ and are linkable *to each
other* by design — that is the rate-limiting mechanism; T4 claims
unlinkability of spends to member identity and across epochs, and the
game's epoch-freshness condition is the formal expression of that scope
(MC6). The spend count revealed at payer-close is not covered (MC15);
nor is the B stale-close residue — under receipt withholding, an honest
payer's forced stale close links $cm$ to one epoch session at the price
of the payee publishing the withheld receipt (rev-11 F10-1, MC15).
Timing, content, and volume fingerprints are out of scope (§5).

**Anti-vacuity.** Three-fold: (i) the B-static/B-rerand calibration pair
means the game provably distinguishes a broken scheme from a fixed one;
(ii) without the freshness condition the game is trivially winnable via
$nf_e$ against *every* variant, including the sound ones — so the condition
is doing real, visible work rather than smuggling in weakness (rev-1
adversarial probe: attempts to build a cross-epoch-linkable scheme that
passes the game failed — persistent tags surface in $t^*$ against the
pre-challenge transcript); (iii) the abort oracle is exercised: in B,
eviction-to-insolvency reaches the $\bot$-branch, and the proof must show
$\mathcal{A}$ gains nothing *beyond* that branch.

### T5 — Closure liveness

**Statement.** Against every PPT adversary controlling the counterparty
(and, for a closing payer, all $N$ gateways and all other payers) and the
scheduler, but subject to the idealized ledger's $\Delta$-inclusion:

- *Payer close:* an honest payer initiating `Close` at time $t$ is settled
  its T3-floor amount by $t + \Delta + \tau$ exactly (inclusion by
  $t+\Delta$, window $\tau$, settlement automatic at expiry — §2 pins the
  automatic execution, so there is no second transaction and no $O(\cdot)$
  slack; rev-1 finding: "$O(\Delta)$" is not a formal statement). An
  honest closer's window admits no valid dispute in A (MC20: its
  claimed-unused nullifiers are PRF-hidden pre-close, so no pre-close
  checkpoint contains them; its double-sign evidence cannot exist per
  T3), so the voided-close branch never fires for honest A payers. In B
  (rev-7/8): an honest closer at its true count likewise faces no valid
  receipt-bearing dispute; a receipt-deprived honest closer faces at
  most **one** upgrade round (its count gap is at most 1 by contiguity),
  extending the bound once by $\tau + \Delta$ — so the honest-B bound is
  $t + \Delta + \tau$ plain, or $t + 2\Delta + 2\tau$ under a
  receipt-withholding dispute (dispute at window end, re-close included
  within $\Delta$, fresh window $\tau$; rev-8 F8-m2 fixed an off-by-$\Delta$
  here), and the voided branch never fires.
- *Payee sweep (A only):* a sweep submitted at $t$ is included and paid by
  $t + \Delta$ (no window). The payee's *reactive* duties (window
  monitoring) are part of T2, not liveness of its own close.
- *Payee force-close (B, MC18):* a force-close submitted at $t$ settles —
  by the payer's responsive close or by forfeit — by $t + \Delta + \tau$,
  **unless the channel is frozen mid-window by a valid `Dispute`** (only
  possible against a payer that double-signed), in which case settlement
  routes through the slash window and completes by the slash time
  $+ \tau + \Delta$ (rev-5 consistency finding: the freeze voids the
  forfeit, so the force-close bound carries this carve-out; for an honest
  counterparty no valid `Dispute` exists and the plain bound stands).

Counterparty silence, garbage submissions, and concurrent disputes cannot
extend these bounds; except with probability $negl(\lambda)$, no transaction
alters the payout within the window, because producing valid `Dispute`
evidence against an honest party is excluded by T3's exculpability clause
and valid sweeps only move funds the closer was never owed.

**Adversary.** As in T2/T3 respectively, plus full control of when (and
whether) the counterparty ever appears on the ledger.

**Violation.** An execution where the honest party's close has not settled
by the stated bound.

**Anti-vacuity.** Any settlement rule requiring counterparty cooperation
(2-of-2 signing without timeout) fails instantly against a silent
counterparty; the theorem is a statement about the timeout structure, and
schemes without one lose.

### T6 — Priced divergence (fleet; instantiation A only)

**Setting.** $N$ honest gateways, each enforcing `Redeem` with its local
$SS_G$, gateway-bound messages (MC14), merge-time evidence (MC17), and
per-epoch budget $b$ per epoch pseudonym; reconciliation guarantee: the
end-to-end lag bound $L$ of §1 (tuples propagate, evidence lands, slash
takes effect fleet-wide, all within $L$).

**Statement.** For every PPT adversary controlling one member (secret $k$,
deposit $D$) and the scheduler: (i) the total value of accepted tickets
attributed to $k$ over the entire execution is at most
$\lfloor D/C \rfloor \cdot C + f(L)$, where

$$f(L) = N \cdot b \cdot \left(\left\lceil L / T_e \right\rceil + 1\right) \cdot C$$

(the smooth reading is $f \approx r \cdot L \cdot C$ with
$r = N b / T_e$, but the discrete form is the theorem: an $L$-window can
straddle $\lceil L/T_e \rceil + 1$ epochs, each with fresh budgets — rev-1
found the prior form undercounted by up to 2×); and (ii) if two conflicting
signals (same $nf$, different $x$) are both accepted by honest gateways,
the member is slashed — evicted fleet-wide — within $L$ of the second
acceptance. The fleet's uncompensated exposure is bounded by $f(L)$
unconditionally, and is recoverable through the `Dispute` window's
documented-conflict claims (MC16/MC19) **up to the member's remaining
deposit at slash time, for acceptances checkpointed pre-slash** (rev-2
NEW-3, rev-3 R3-3: recovery is remainder-capped and checkpoint-gated — an
exhaust-then-burst schedule leaves a near-zero remainder and its window
losses uncompensated; the operational levers on recovery are sweep cadence
and checkpoint cadence, echoing the sources' own mitigation for the
self-slash race). The
deployment condition

$$f(L) < D$$

prices the window in the boundedness sense — the maximal burst never
exceeds one deposit — and is necessary for full recovery in the
fresh-deposit case; it does not guarantee recovery in general, and this
theorem does not claim attacker unprofitability (rev-1) or universal
recoverability (rev-2).

**Why the bound has this shape.** Gateway-bound messages make every
cross-gateway reuse of an index a *conflicting* pair (different gateway ⇒
different $m$ ⇒ different $x$), and within one gateway a reused index is
either bit-identical (reject-duplicate, no value) or conflicting. So all
value beyond the solvency entitlement $\lfloor D/C \rfloor \cdot C$ comes
from conflicting acceptances. From the first conflicting acceptance, the
second signal reaches some honest spent set and MC17 generates evidence;
within $L$ (end-to-end) the slash lands and the root rotates, so every
excess acceptance fits in one window of length $L$. Within that window the
fleet-aggregate acceptance rate for one member is capped by the epoch
pseudonym counters: $nf_e$ is the same at every gateway, the window meets
at most $\lceil L/T_e \rceil + 1$ epochs, and each gateway accepts at most
$b$ per epoch — $N b (\lceil L/T_e \rceil + 1)$ acceptances, each worth
$C$. **Without MC14 this theorem is false** — the rev-1 record contains the
counterexample (bit-identical replay across gateways: no conflict, no
evidence, no slash, excess $\approx (N{-}1) \cdot D$ accumulated across
per-index private windows); it is kept in `research_knowledge/gates.md` as
the canonical wrong-definition-nearly-proved case.

**Adversary.** One corrupted member (coalitions: the bound applies
per-member and sums linearly, each deposit separately); adaptive choice of
gateways, indices, messages, timing; cannot delay reconciliation (that is an
honest-fleet guarantee), cannot forge proofs (knowledge soundness).

**Violation.** An execution with attributed accepted value exceeding
$\lfloor D/C \rfloor \cdot C + f(L)$, or a conflicting-acceptance pair whose
member is never slashed.

**Anti-vacuity.** The bound is non-trivially positive: the one-window
double-spend attack (reuse each solvent index at all $N$ gateways inside
$L$, each with that gateway's message) really extracts
$\Theta(\min(N b (\lceil L/T_e\rceil{+}1),\ N \lfloor D/C \rfloor)) \cdot C$
of excess, so the theorem is a matching upper bound on a real attack, not
$0 \le f$. And the priced-ness is discriminating: with slashing deleted
(RLN counting only), the same attack repeats every epoch forever at no cost
— a scheme the theorem rejects. With MC17 deleted, the staggered
one-pair-per-index adversary is never slashed — also rejected.

### T7 — Exculpability under collusion (fleet; instantiation A only)

**Game $\mathsf{FRAME}$.** Challenger runs `Setup` and creates one honest
member with secret $k$, open deposit $D$. $\mathcal{A}$ controls $N - 1$
gateways (all their spent sets, transcripts, and keys), arbitrarily many
corrupt members, and the scheduler; the $N$-th gateway is honest (its
accepted tuples reach $\mathcal{A}$ through reconciliation anyway, so
$\mathcal{A}$ effectively reads every signal the honest member ever emits).
Oracles:

- $\mathcal{O}spend(m)$ — the honest member emits its next-index ticket on
  gateway-bound message $m$ of $\mathcal{A}$'s choice, delivered to
  $\mathcal{A}$.
- $\mathcal{O}close$ — the honest member closes: under MC20 (rev-6) the
  close emits **no signal** — it publishes $(cm, U)$, the PRF-fresh
  nullifiers of the member's unused indices, on the public ledger,
  visible to $\mathcal{A}$. The rev-1 rationale stands — the close is the
  moment $cm$ goes public and the member is most targetable, so FRAME
  must cover it — but what the adversary now gains is nullifier values
  with **no line points** (no $(x, y)$ was ever emitted for an unused
  index), strictly less material than rev-4's close signal. The oracle
  stays in the game to keep the framing window covered and to feed the
  reveal into the adversary's view.

The honest member never emits two signals at the same index with different
messages (it is honest; identical re-sends under the retry rule are
permitted; the close emits no signal under MC20). $\mathcal{A}$
outputs $ev^* = (nf, (x, y), (x', y'))$.

**Statement.** For every PPT $\mathcal{A}$: the probability that
$Dispute(pp, ev^*, \mathcal{L})$ slashes the honest member's $cm$ is
$\le negl(\lambda)$, under `single_signal_hiding` and collision resistance.
The algebraic core: a valid slash requires two distinct points on the line
$Y = k + H_a(k, i) X$ for some index $i$; $\mathcal{A}$ holds at most one
honest point per index (spends and the close signal alike); one point
$(x, k + a x)$ with pseudorandom $a$ determines nothing about $k$
(`single_signal_hiding`); producing a second point is equivalent to
computing $k$ (or $a$), which breaks the assumption. This is what makes the
*automatic, anyone-can-submit* slash safe to deploy, and it is the lemma
T3's second clause instantiates with all $N$ gateways corrupted.

**Adversary.** The maximal insider coalition short of everyone: $N-1$
gateways pooling all transcripts, plus corrupt members (whose own secrets
they hold and may freely slash — that is not a win), with an adaptive spend
oracle and a close trigger on the victim.

**Violation.** The ledger slashes a member that never double-signed.

**Anti-vacuity.** Against a degenerate RLN with $y = k$ (no line masking) or
$a$ reused across indices, one observed spend hands $\mathcal{A}$ the secret
and the frame succeeds with probability 1; the game detects both breaks. The
adversary class is the protocol's actual threat model — the fleet's own
operators — not a strawman.

---

## 8. Modeling choices (ambiguities in the sources, resolved here)

Each of these is a place where the prose sources underdetermine the protocol
and this spec commits. Entries marked **[repair]** change behavior relative
to a literal transcription; the rev-1 panel required each repair to be
labeled and its necessity witnessed by a concrete counterexample (recorded
in `research_knowledge/gates.md`). **The M0 reviewer is asked to check every
item.**

- **MC1 — Close mechanics. [repair; superseded in part by MC20]**
  Settlement cadence and payer-withdrawal mechanics are underspecified in
  the source construction (RESEARCH.md open problem 8; the thread comment
  on claiming "the fair share" is unanswered). Revs 1–5 adopted
  "close-as-final-spend" (close signal at the next unused index, so
  understatement self-convicts); **rev-5 broke it** with the gap-index
  counterexample (no contiguity ⇒ closing at a skipped index collides
  with nothing) and **MC20 replaced it**: A closes by unused-nullifier
  enumeration, B closes at its receipt-certified count. What survives of
  MC1: unilateral $nf$-deduped sweeps (A), automatic settlement at window
  expiry, and the commingled-pool substrate (MC16).
- **MC2 — Abort-retry rule.** Neither source specifies honest payer behavior
  when the payee aborts mid-spend. We adopt: the index is consumed at
  *emission*; the honest payer may re-send the bit-identical ticket (same
  point on the line, same gateway per MC14, unslashable, and `Redeem`
  treats it as reject-duplicate, not evidence); switching messages requires
  the next index. Consequence, made explicit in T3: authorized value counts
  emitted tickets, so abort griefing costs the payer up to one ticket price
  per abort. Rev-7 scope note for B: an abort that withholds the receipt
  additionally wedges the certified count one behind — the §2 upgrade
  sub-window keeps the close safe, at the same ≤ one-ticket price.
- **MC3 — Rate-limit semantics for T6.** The egress post notes the epoch
  pseudonym is not gateway-scoped, so the fleet-wide budget is silently $N$
  times the per-gateway budget. We take that at face value and define the
  T6 rate as the aggregate ceiling ($N b$ per epoch fleet-wide), rather
  than pretending a fleet-wide counter exists.
- **MC4 — Slash payout with gateway-priority window. [repair]** The source
  says $D$ is "claimable by anyone presenting the recovered secret," which
  as written admits the self-slash race (RESEARCH.md open problem 2,
  unresolved in the thread). We adopt: `Dispute` freezes the channel, opens
  a window $\tau$ in which registered gateways claim (i) sweeps of the
  slashed member's outstanding redeemed tickets — attribution is possible
  post-slash because $k$ is public and the member's nullifiers are
  enumerable — and (ii) documented conflicting acceptances (dedup-blocked
  service); seniority (i) before (ii), pro-rata within class (MC19);
  the *remainder* goes to the submitter.
  T2 and T6's exposure clause are conditioned on this repair, and T2's
  anti-vacuity note records what breaks without it.
- **MC5 — Slash consequence is fleet-wide eviction.** We model the slashed
  commitment's removal from the tree (root rotation), so post-slash spend
  proofs fail everywhere within the reconciliation bound. The sources imply
  but never state this; T6's "career ends at detection" needs it. Related
  minor: `Redeem` check 2 accepts the *current* root only; honest payers'
  roots refresh instantly in the model, and root-staleness across rotations
  is a liveness wrinkle outside the theorems (rev-1 fidelity note — the
  post's static-tree reading, "root loaded at boot," has no rotation to go
  stale against; ours does).
- **MC6 — Epoch-freshness condition in T4.** Payment tickets carry the
  rate-limiting epoch pseudonym $nf_e$, which links a member's spends
  *within* an epoch by design (the PoC's own wire format). An unlinkability
  game ignoring this would be trivially winnable against every variant; a
  claim of within-epoch unlinkability would be false of the deployed
  protocol. We therefore scope the challenge to an epoch in which neither
  candidate makes any other spend. Rev-1 adversarially probed whether this
  condition lets a cross-epoch-linkable scheme pass and concluded it does
  not (persistent tags still surface against the pre-challenge transcript).
  The alternative (modeling payment tickets without $nf_e$) would formalize
  a protocol the fleet does not run.
- **MC7 — Certified refund chain: key structure, binding tag, randomness,
  genesis. [repair, expanded in rev-2]** The source thread never states
  whose key $E$ is under or how the total is certified. We model:
  encryption of the pair $(H_{tag}(k), R)$ under a setup-generated $pk_E$
  whose decryption key no honest algorithm uses (the ciphertext functions
  as a certified hiding container); the payee certifies by signing after
  each homomorphic update and **returns the increment's encryption
  randomness in the receipt** (else the honest payer holds no witness —
  rev-1 blocking finding); the chain tag binds receipts to the channel
  (else cross-channel receipt splicing breaks T1-B — rev-1 blocking
  finding); the chain initializes with a genesis receipt at `Open`, proven
  against $cm$ where linkability is free anyway. B-static vs B-rerand
  differ only in whether the presented ciphertext is bit-identical to a
  signed one or re-randomized with an in-circuit equivalence proof.
  Rev-6 (MC20): the chain also certifies the spend count — ciphertexts
  encrypt $(tag, R, n)$, receipts increment $n$, and
  $\mathcal{R}_{spend}^B$ proves its index equals the certified $n$,
  making B spends contiguous by construction.
  Transposition note (rev-1 fidelity): omarespejel's finding was linkage
  across *settlements*; B-static exhibits the same mechanism across
  consecutive *spends* — same tag, broader venue, acknowledged as such.
- **MC8 — Policy stake $S$ excluded.** The source's dual stake ($D$
  claimable, $S$ burnable via a separate policy mechanism) is orthogonal to
  T1–T7; we model $D$ only. Nothing in the theorems depends on $S$.
- **MC9 — Domain separation assumed.** The dual-nullifier circuit (index
  nullifier and epoch nullifier over the same $k$, jointly revealing
  nothing) is open problem 4 in RESEARCH.md; we *assume* domain-separated
  derivations as part of assumption 3 rather than proving joint security of
  a concrete circuit. This is inside the stated model boundary (we do not
  verify circuits) but worth the reviewer's attention because it is
  assumption, not theorem.
- **MC10 — Static corruption.** Corrupted sets are fixed per game. Adaptive
  corruption (a gateway turning malicious mid-execution) is not modeled;
  the sources do not discuss it.
- **MC11 — $L$ is end-to-end.** Rev-1 found §1's gossip-only definition
  contradicted T6's use (detection-to-eviction). Resolved by redefining $L$
  end-to-end in §1: tuple propagation, evidence inclusion, and slash effect
  all within $L$. T6's window argument uses exactly this.
- **MC12 — No clock skew.** The wire protocol accepts one epoch of skew; the
  model uses ideal synchronized epochs. A skew-tolerant model would enlarge
  the T6 budget by a small constant factor; we note it and omit it.
- **MC13 — Transport target policy narrowed, not dropped.** Rev-1 retracts
  the prior claim that the message content has "no bearing on payment
  security": the gateway-binding component of $m$ is load-bearing (MC14,
  T6). What remains out of scope is the payload policy (the `host:443`
  check), which is application-layer.
- **MC14 — Gateway-bound messages. [repair]** $m = (G, \hat{m})$; `Redeem`
  rejects other gateways' tickets (§1, §2). Without it, bit-identical
  cross-gateway replay extracts $\approx (N{-}1)\cdot D$ with no slash ever
  (rev-1 blocking counterexample, all three reviewers independently or on
  review concurring), and T6's bound is false. The egress post's production
  note ("bind the proof's message field to the target") is the same move
  one layer down; this repair is its payment-layer form.
- **MC15 — Challenge-terminated UNLINK; spend-count side channel.
  [repair of the game]** Rev-1's post-challenge oracles made the game
  unsatisfiable (three universal distinguishers: challenge replay via
  retry, solvency-exhaustion probing, close-count reading). The game now
  ends at challenge delivery, retaining full pre-challenge abort/evict
  power. The honest residue: the spend count revealed at payer-close —
  as $j$ in B, as $cap - |U|$ in A's MC20 enumeration (same information)
  — is a real side channel the theorem does not cover, stated in T4's
  what-is-NOT-claimed and owed an honest-limits paragraph in the paper.
  A's close additionally reveals the unused nullifiers themselves; these
  are PRF-fresh values never used anywhere, so they carry no linkage
  beyond the count. **CloseView-simulatability obligation (rev-9, K4
  Concern 2; sharpened rev-10 F9-m1):** because the game terminates at
  the challenge, close-time content is outside its view — so every
  instantiation owes the stated obligation that its close output is
  simulatable from $(cm, \text{spend count})$ alone, **judged jointly
  with the member's spend transcript** (marginally, even a
  used-nullifier close looks uniform; the exclusion bites because the
  simulator's output must remain correct when correlated against the
  transcript's tickets) and with the simulator granted NIZK-ZK for the
  $\pi_{close}$ component. A's close satisfies it on every path (honest
  $U$ contains only never-emitted PRF-fresh values, receipt-independent);
  **B's satisfies it for true-count closes only** (rev-11 F10-1: a
  *stale* close's revealed $nf_j$ bit-matches the member's own
  transcript ticket at index $j$ — that match *is* §2's conviction
  mechanism, so it is definitionally not jointly simulatable, and an
  honest receipt-deprived payer reaches this path whenever the payee
  withholds the last receipt). The residue is stated as an honest limit:
  **under receipt withholding, the resulting stale close publicly links
  $cm$ to one spend — and via that ticket's $nf_e$ to one epoch session
  — at the price of the payee publishing the withheld receipt**; same
  epistemic class as the count leak, carried in T4's what-is-NOT-claimed
  and owed to the paper's honest-limits section. A hypothetical close
  that published *used* nullifiers wholesale — total retroactive
  deanonymization — remains exactly what the obligation excludes.
- **MC16 — Pooled escrow; authenticated sweeps; monitoring duty.
  [repair]** The ledger's fund accounting (commingled pool) was implicit in
  rev-1 and two theorems silently depended on it; sweep authentication to
  the `Setup` roster is required or T2 falls to payer sweep-front-running;
  the honest payee's duty to monitor `Dispute` windows is part of "follows
  the sweep protocol." All three now explicit in §2.
- **MC17 — Merge-time evidence generation. [repair]** `Redeem`-on-ticket
  was the only evidence producer in rev-1, so a one-pair-per-index
  staggered adversary was never slashed and T6's clause (ii) was vacuous.
  Gateways now emit evidence when merging conflicting tuples. Required
  behavior, stated in §2.
- **MC18 — Instantiation B settles at close, not by sweeps. [repair]**
  Rev-2 (NEW-1) proved A's sweep mechanics cannot conserve funds in B:
  per-nullifier sweeps at $C_{max}$ plus a refund-bearing close pay $D+R$
  out of a $D$ deposit, and pre-slash unattributability makes per-channel
  netting impossible. B therefore settles each channel exactly once, at
  close: payer gets $(D+R) - j\cdot C_{max}$ with both settlement caps
  $R \le j\cdot C_{max}$ and $j\cdot C_{max} \le D + R$ enforced in
  $\mathcal{R}_{close}^B$ (rev-3 R3-1, rev-4 F1) and the count certified
  plus $nf_j$ revealed per MC20 (rev-6: stale-receipt closes self-convict
  via the reveal), payee gets $j\cdot C_{max} - R = \sum c_\ell$; a
  silent payer is handled by force-close-with-forfeit after a response
  window; a channel hit by an *identity*-slash settles through the
  slash-window per-nullifier claims, and one hit by a *fund*-slash
  (failed upgrade) settles by forfeit of $D$ to the payee (rev-3 R3-2,
  scoped in rev-10/11 — the per-nullifier claims are $k$-gated,
  close-time netting cannot reach a frozen channel, and without a slash
  path the self-slash race reopens in B). Conservation is exact by
  construction. This resolves the settlement-cadence side of open
  problem 8 for B differently than for A — a genuine design consequence of
  refund privacy, worth a paragraph in the paper.
- **MC20 — Verifiable spend count at close. [repair]** Rev-5's blocking
  find: neither instantiation enforced index contiguity, so a gap-index
  close (skip index 0, spend at 1..m, close at 0) recovered the full
  deposit after consuming service — falsifying T2's floor and voiding
  MC1's self-conviction argument, in both A and B, plus A's
  pool-retention claim. Two repairs, one per instantiation, because their
  information structures differ: **A** (non-interactive, no receipts)
  closes by unused-nullifier enumeration — reveal PRF-fresh nullifiers of
  claimed-unused indices with an in-circuit well-formedness proof; false
  claims are disproven by bit-match against pre-close checkpoints; payout
  $C\cdot|U|$ + residue, two-sided sweep bar (rev-7). **B** (interactive
  receipts) certifies the count in the chain — $(tag, R, n)$ with
  $\mathcal{R}_{spend}^B$ proving index $= n$, so contiguity holds by
  construction and the close settles at the certified count with the
  $nf_j$ reveal (rev-6: stale receipts self-convict) under the
  receipt-bearing dispute discipline with its upgrade sub-window (rev-7:
  receipt withholding cannot slash an honest closer — disputes publish
  the withheld receipt and the close upgrades one count per round,
  converging at the true count; $j=0$ closes need no receipt). Closed
  channels are evicted from the tree at settlement (kills post-close
  ticket replay). That the same hole demands
  two structurally different repairs is a finding about the design space
  (non-interactive spending trades away cheap closes), owed a paragraph
  in the paper.
- **MC19 — Window-claim provenance. [repair]** Post-slash, $k$ is public
  (the `Dispute` transaction reveals it), so nothing algebraic stops a
  registered gateway from minting "documented conflicts" or old-root spend
  proofs during the claims window — rev-2 (NEW-2) caught the spec citing
  T7's lemma here, which only protects members whose $k$ is secret.
  Repair: gateways checkpoint a commitment to their accepted sets on the
  ledger at any time, at least once per epoch (rev-3 R3-3: window recovery
  is gated on pre-slash checkpoints, so cadence is a recovery lever), and
  window claims verify against a pre-slash checkpoint. Rev-7/8: in B,
  checkpoint entries are *receipt-bearing* (§2 — the close-dispute must
  exhibit the full receipt tuple, not nullifier membership alone).
  Rev-6: checkpoints do triple duty — they also gate the MC20 close-dispute (a false
  unused-claim is provable only from a pre-close checkpoint, which is
  also what protects honest closers from post-hoc fabrication) and their
  currency at a close transaction conditions the payee's close
  protection, the third cadence lever. Claim seniority
  when the remainder is short: sweeps (i) before conflicts (ii), pro-rata
  within class. Honest-limits note (rev-3 R3-9): window recovery presumes
  fleet honesty — a member–gateway collusion can pre-checkpoint real
  cooperatively-produced "service" at every solvent index and exhaust the
  remainder senior to honest gateways' conflict claims; no theorem's
  adversary class includes corrupt gateways in the recovery role, and the
  paper's honest-limits section must say so.

---

## 9. Provenance

Where each load-bearing protocol detail comes from. "Egress post" is the
reputation-gated egress post (`docs/post/index.html` in
`dmarzzz/reputation-gated-onion-egress`); section names are its headings.
Rev-2 additions are the repair rows at the bottom.

| Detail | Source |
|---|---|
| Envelope format: root, epoch scope, nullifier, proof; anonymity set = the whole tree | Egress post, "The wire protocol" |
| The five `Redeem` admission checks (proof, root, epoch, target policy, budget) and fail-closed verdicts | Egress post, "The wire protocol" |
| Epoch pseudonym $nf_e = H(secret, epoch)$: one per epoch, counted against a budget, expiring across epochs | Egress post, "A membership proof, rate-limited with RLN" |
| Channel = escrowed deposit + state counter; spend proves current state with balance; double-spend punished not prevented; replaying a spent index leaks the secret via Shamir-line algebra; deposit slashable by anyone | Egress post, "Addendum: zk payment channels — How it would work" |
| Flat pricing for egress; refund machinery deletable whole | Egress post, Addendum ("Egress pricing is flat...") and "What it costs" |
| Batch-open at enrollment; shielded funding or the anonymity dies at the funding edge | Egress post, Addendum ("How it would work") |
| Fleet shape: spent set needs no consensus because RLN prices inconsistency; double-spend across two gateways caught at reconciliation; async window bounded by the deposit | Egress post, Addendum ("What it costs") and "Payment" |
| Open problems this spec commits on: gossip-lag bound, self-slash race, deposit-edge leak | Egress post, Addendum (final paragraph); RESEARCH.md open problems 1, 2, 3, 8 |
| RLN algebra $a = H(k,i)$, $x = H(M)$, $y = k + a x$, $nf = H(a)$; index in the role of RLN's epoch; "different $x$, same nullifier" detection; $k$ recovery; slash claimable by anyone | RESEARCH.md, "What zk payment channel actually means" item 3 and deep dive 1 (verified against the ZK API Usage Credits thread) |
| Solvency invariants $(i+1) C \le D$ (flat) and $(i+1) C_{max} \le D + R$ (refunds) | RESEARCH.md deep dives 1 and Application section; BRIEF.md instantiation list |
| Refund variant: server-signed refund tickets / encrypted running total; static $E(R)$ linkable (omarespejel), re-randomization with proof of equivalence as the patch | RESEARCH.md deep dive 1; BRIEF.md T4 calibration requirement |
| Abort/evict oracle requirement and its two attack modes (evict to shrink the set; abort mid-sequence to link) | BOLT §1.4 as quoted in RESEARCH.md deep dive 2; BRIEF.md T4 |
| Anonymity-set accounting (set = capable/completed participants, shrinking under aborts) informing the $\bot$-branch of T4 | RESEARCH.md deep dives 2, 3 |
| The seven theorem targets, their priority, and the model boundary (idealized ledger, axioms in one file, no circuit verification) | BRIEF.md, Deliverable 2 |
| Exculpability shape: forging a second point on the line requires the secret; $N-1$ collusion | RESEARCH.md open problem 5; BRIEF.md T7 |
| Priced-divergence shape: extractable value $\le f(\text{lag}, \text{rate}) < D$ | RESEARCH.md open problem 1; BRIEF.md T6; egress post Addendum |
| Self-slash race and mitigation directions (frequent claims / unclaimed-balance ceiling) informing MC4 | RESEARCH.md deep dive 1 (e), open problem 2, and Application "design imports" |
| Dual stake $D + S$ (excluded, MC8) | RESEARCH.md deep dive 1 |
| MC14 gateway-bound messages: payment-layer form of the post's "bind the proof's message field to the target" production note | Egress post, production-notes list; rev-1 gate findings (all three reviewers) |
| MC15/MC16/MC17 and the MC7 expansion: protocol/game repairs forced by rev-1 counterexamples | `research_knowledge/gates.md` (B1 gate record) |
| MC18 close-time netting for B and MC19 checkpointed window claims: repairs forced by rev-2 counterexamples (NEW-1, NEW-2), refined by rev-3 (R3-1..R3-3) | `research_knowledge/gates.md` (B1 gate record, rounds 2–3) |
| MC20 verifiable spend count at close (A enumeration + B certified count with $nf_j$ reveal, receipt-bearing disputes, upgrade sub-window, two-sided sweep bar): repairs forced by rev-5/6/7 counterexamples | `research_knowledge/gates.md` (B1 gate record, rounds 5–7) |

The construction-of-record for instantiation B is the ZK API Usage Credits
thread (Crapis & Buterin, ethresear.ch/t/24104) as summarized and verified
in RESEARCH.md; this spec cites it through RESEARCH.md deliberately, since
RESEARCH.md is the verified field report the executor contract designates as
the map.
