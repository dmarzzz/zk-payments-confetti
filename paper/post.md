# zk payment channels: a definition, and the first machine-checked unlinkability results for a credit construction

<!-- ethresear.ch long-form version of paper/paper.md (task J8a). Same
claims ledger applies. -->

**TL;DR.** "zk payment channel" — a two-party channel where the payee
learns nothing about payer identity across spends, while balance security
and double-spend resistance hold — was named by BOLT in 2016 and then the
line went dormant. No systematization, no formal definition as a distinct
object, and no machine-checked privacy proof for any channel or credit
construction existed. Meanwhile the shape keeps getting reinvented:
keyed-verification credit tokens ([ACT](https://datatracker.ietf.org/doc/draft-schlesinger-cfrg-act/),
[ARC](https://datatracker.ietf.org/doc/draft-ietf-privacypass-arc-crypto/))
and [ZK API Usage Credits](https://ethresear.ch/t/zk-api-usage-credits-llms-and-beyond/24104)
are all this object under different double-spend philosophies. We wrote
the definition down as six algorithms and seven security games, placed it
against the lineage, and formalized a flat-ticket RLN instantiation in
Lean 4. The headline: spend unlinkability is machine-checked — against a
payee holding BOLT §1.4's abort/evict powers, the advantage of
distinguishing which of two members emitted a whole epoch session is
exactly zero, to our knowledge the first machine-checked unlinkability
result for any channel or credit construction. No-overspend, both
balance-security theorems, closure liveness, the fleet priced-divergence
bound, the exculpability (framing) bound (≤ 1/|F| under a stated
random-oracle good event, with a kernel-checked query-budget composition
endpoint), the refund variant's safety and conservation — now including
the full failed-upgrade cascade and finite-fleet aggregation — zero-loss
zero-knowledge bridges for three concrete proof-bearing wire encodings
(masked-proof, interactive Sigma, lazy-ROM Fiat–Shamir), an executable
ledger refining every relational transition, a multi-recipient
portable-deposit accounting layer with a threshold-issuance reference, one-trace
end-to-end composition theorems, and a built-in calibration pair that
separates the broken and fixed refund designs are all kernel-checked too —
zero `sorry`, no axiom beyond Lean's three standard ones. Along the way, eleven
rounds of adversarial review broke ten successive revisions of our own
definition with concrete counterexamples — and the repairs are, we think,
design requirements for anyone building in this space. Repo:
[dmarzzz/zk-payments-confetti](https://github.com/dmarzzz/zk-payments-confetti).

## Why this object, why now

The [ZK API Usage Credits thread](https://ethresear.ch/t/zk-api-usage-credits-llms-and-beyond/24104)
described anonymous prepaid API credits: deposit once, spend against one
provider under a zk membership proof, double-spends detected by nullifier
reuse and punished by an RLN-style secret reveal plus slash. As a thread
comment observed, this is structurally a payment channel — deposit as
channel open, monotone spend index as channel state, provider-signed
refunds as countersigned balance updates. Which raises the question: where
is the payment-channel literature this should be leaning on?

Answer: it more or less does not exist.
[BOLT (Green & Miers, CCS 2017)](https://acmccs.github.io/papers/p473-greenA.pdf)
built anonymous channels and stated the sharpest threat model this line
has produced (§1.4: a malicious merchant can shrink the anonymity set by
inducing aborts, and link a member by aborting mid-sequence). Then:
[no Zcash deployment](https://electriccoin.co/blog/bolt-private-payment-channels/),
a successor spec ([zkChannels](https://boltlabs.tech/userfiles/media/boltlabs.tech/zkchannels-protocol-spec-v0.3.2.pdf))
that never left DRAFT, an implementation
([libzkchannels](https://github.com/boltlabs-inc/libzkchannels)) archived
in 2023. Every privacy proof in the wider channel/hub literature is
pen-and-paper, and the one flagship privacy model that got stress-tested —
A2L, S&P 2021 — was shown a year later
([Glaeser et al., CCS 2022](https://dl.acm.org/doi/10.1145/3548606.3560637))
to admit "completely insecure" instantiations that satisfy its
definitions. Wrong definitions, correctly proved: that is the failure mode
this field has actually suffered, and it is why the definitions — not the
proofs — deserve the adversarial attention.

So the contribution here is deliberately unglamorous: **a definition**,
with theorems as its defense.

## The object

A zk payment channel is a tuple
**(Setup, Open, Spend, Redeem, Close, Dispute)** over payers, payees ($N$
gateways may share one logical payee role), and an idealized ledger.
The instantiation of interest runs on RLN algebra: member secret $k$,
identity commitment $cm = H_{id}(k)$ in an on-ledger Merkle tree, and per
spend at index $i$ on message $m$:

$$a = H_a(k,i), \quad x = H_x(m), \quad y = k + a \cdot x, \quad nf = H_{nf}(a)$$

with solvency $(i{+}1) \cdot C \le D$ proven in zero knowledge. Two signals
on one index are two points on a line — anyone recovers $k$ and slashes
the deposit, no watchtower. One signal (at $x \neq 0$; more on that below)
reveals nothing. Tickets also carry the epoch pseudonym $nf_e = H_e(k,e)$,
linkable within an epoch by design — that is the rate limiter.

Seven security statements: **T1** no overspend; **T2/T3** payee/payer
balance security; **T4** spend unlinkability; **T5** closure liveness;
**T6** priced divergence (fleet); **T7** exculpability under collusion
(fleet). Three deserve comment here.

**T4, the headline game**, gives the adversary the payee role plus BOLT
§1.4's abort/evict powers: it can refuse service to a candidate payer from
any point on, and in the refund variant it can withhold receipts to drive
a candidate insolvent. A candidate evicted into insolvency makes the
challenge return ⊥ — the game charges eviction to the anonymity set, not
the scheme, which is exactly what the abort attack does in reality. The
challenge is a **session**: the adversary submits a message vector, and the
hidden candidate emits a whole *q*-spend epoch session (this is a repair the
external review forced — a single-spend challenge certifies only
first-spend-of-epoch unlinkability, and would pass a scheme leaking a
persistent tag on second-and-later spends). The game is
challenge-terminated: our first version answered oracles after the
challenge and turned out to be *unsatisfiable* — three distinguishers won
it against every scheme, sound ones included (replay the challenge via the
retry oracle; probe which candidate exhausts solvency an index early; read
the spend count off a later close). And the game carries a built-in
calibration test: instantiated on the refund variant with a static
encrypted refund total (the original design, whose linkability
[omarespejel demonstrated](https://gist.github.com/omarespejel/c3f4f2aa12b1de10467601d77d0e6232)),
a concrete distinguisher must win; instantiated on the re-randomized
repair, advantage must be negligible. A game that can't tell those two
apart is the wrong game — and this one provably can: the calibration pair
is machine-checked (advantage exactly ½ against the broken design, exactly
0 against the fix).

**T6** is what makes a fleet of mutually distrusting gateways workable
without consensus on the spend path: with end-to-end reconciliation lag
$L$, per-gateway epoch budget $b$, epoch length $T_e$, the value one
member can extract beyond its deposit entitlement is at most
$f(L) = N \cdot b \cdot (\lceil L/T_e \rceil + 1) \cdot C$, and a
double-signing member is slashed fleet-wide within $L$. Deployment
condition $f(L) < D$: the async window is priced by the deposit, not
trusted away. The theorem deliberately does not claim attacker
unprofitability or full recovery — recovery is capped by the remaining
deposit and gated on checkpoint freshness.

**T7** is why an automatic, anyone-can-submit slash is safe against the
protocol's actual adversary, the fleet's own operators: $N-1$ colluding
gateways hold at most one point per line for an honest member, and one
point determines nothing about $k$; forging evidence means computing $k$.

## What adversarial review did to the definition

This spec is revision eleven. Eleven independent review rounds each broke
the previous revision with concrete counterexamples — adversary schedules,
not opinions. The three deepest, presented as what they are: design
requirements for any construction of this shape.

**Gateway-bound messages.** With messages as bare payloads, a member
replays one bit-identical ticket at all $N$ gateways: same nullifier, same
$x$ — no conflicting pair, no evidence, no slash, ever. Excess extraction
≈ $(N{-}1) \cdot D$ against a claimed bound of order $r \cdot L \cdot C$.
The repair bakes the serving gateway's identity into the hashed message,
so cross-gateway reuse *forces* a conflict. General lesson: in any
multi-verifier nullifier scheme, replay across verifiers is value-bearing
unless the verifier identity is inside the proof's message.

**Verifiable spend counts at close.** For five revisions a payer closed by
declaring its spend count, understatement policed by collision with its
own spends. Counterexample: nothing enforces index *contiguity* — indices
are hidden — so skip index 0, spend at 1..m, close declaring 0. Collides
with nothing, undisputable, full deposit refunded after consuming the
service. Root cause: the ledger has no verifiable spend count. The repair
differs per instantiation, and the difference is a design-space finding in
its own right (next section).

**Refunds versus unilateral settlement.** Letting gateways sweep per
accepted nullifier cannot coexist with refunds: sweeps pay $C_{max}$ per
nullifier *and* the close pays out the refund total — $D + R$ out of a $D$
deposit — and pre-slash unattributability means no per-channel netting can
save it. A refund-bearing anonymous channel must settle per channel, once,
at close, with circuit-enforced caps both ways ($R \le j \cdot C_{max}$,
$j \cdot C_{max} \le D + R$). Refund privacy and per-ticket settlement are
structurally incompatible under a commingled escrow.

The full gate record — every round, every counterexample, including the
ones against the *game* definitions — is in
[`research_knowledge/gates.md`](https://github.com/dmarzzz/zk-payments-confetti/blob/main/research_knowledge/gates.md).

*A note on method, since this forum cares about it: the artifacts here
(field report, spec, Lean, this post) were produced under an
agent-assisted workflow in which humans review definitions and theorem
statements only — never proofs — and each gate round was executed by a
fresh reviewer that had not written the text under review. The definition
went through eleven such rounds (gate B1) plus three on the Lean games
(gate B3), an independent statement audit (K1), an axiom audit (K2), an
adversarial-vacuity audit (K3, in the repo), and a simulated external
cryptographer (K4). The premise: machine-checked proofs
invert the review economics (if the kernel accepts, the proofs are right),
so all scrutiny concentrates on whether the definitions say what we mean —
which is precisely where this field's one famous failure lived. One datum
stands out: the TLA+ model-checker independently found the deepest hole
(the gap-index close) by state exploration at the same time the adversarial
gate found it by definition review, and then verified the same repair — two
methods sharing no machinery converging on the same defect and the same
fix. The full record is in the repo, unlaundered.*

## Two instantiations, one asymmetry

**Flat-ticket** (the egress-fleet protocol): flat price, one inequality,
non-interactive spend, no payee-held per-payer state — a payee abort is
just denial of service. Arguably the smallest machine-checkable
unlinkability target in the literature.

**Refund-bearing** (the credits-thread protocol): payee declares actual
cost $c \le C_{max}$, refunds accrue in a certified receipt chain
$(tag, R, n)$ — channel-binding tag, refund total, certified spend count —
and solvency becomes $(i{+}1) \cdot C_{max} \le D + R$. Both refund-total
representations are modeled: B-static (present the signed ciphertext
bit-identically — broken, and the T4 game must win against it) and
B-rerand (re-randomize with an in-circuit equivalence proof — the patch,
against which T4 must hold).

The asymmetry the gap-index repair exposed: **A** spends non-interactively,
so no certified count can exist, and its close must *enumerate* — reveal
the PRF-fresh nullifiers of all claimed-unused indices, disputed by
bit-match against pre-close gateway checkpoints. **B** has interactive
receipts, so the count is certified and the close is $O(1)$ — latest
receipt plus one revealed nullifier past the count, which makes closing on
a stale receipt self-convicting. Non-interactive spending buys
abort-immunity and pays at close time; interactive receipts buy cheap
certified closes and hand the payee a live abort lever (withheld receipts
stall solvency). We have not seen this trade-off stated before.

**A third shape, from Vitalik.** A unidirectional nullifier-chain channel
([design gist via dmarzzz](https://gist.github.com/dmarzzz/ddcd1302c5f511001f8f46102874a08e))
sits at a simpler point of the same space: Alice chains nullifiers
$N_{i+1} = H(N_i, c)$; each payment reveals the parent's committed
next-nullifier plus a ZK proof that the parent is the genesis or *some*
Bob-signed state (signature verified inside the proof, so which one stays
hidden), balances hidden, $\delta$ public; close opens the closed state's
committed next-nullifier, and Bob challenges a stale close by exhibiting
the message that already revealed it — collision, forfeit. One mechanism
does duplicate detection and stale-close detection uniformly down to the
genesis-refund case. It trades away non-interactivity, epochs, rate
limiting, and the fleet, and its base form leaks $D$ and the split at the
boundaries — but its penalties are fund-forfeit only, so the
identity-slash retroactive-deanonymization limit of the RLN design simply
does not exist there, and the stack is natively post-quantum. We archive the design in-repo and machine-check its core in
`Zkpc/Chain/`: balance safety and refund liveness as Class-A invariants,
both directions of the collision mechanism (stale closes always
challengeable, honest closes never challengeable — its exculpability
needs no probabilistic argument at all), and per-request anonymity at
advantage exactly zero as an RO coupling.

## What is machine-checked, exactly

Lean 4 (`v4.30.0`, mathlib `v4.30.0`, games over
[VCV-io](https://eprint.iacr.org/2026/899.pdf) pinned at `8f5dc4f`), CI
enforcing zero `sorry`, no `axiom` outside the registry (in fact the
development declares no axioms at all — assumptions are discharged by
construction in the idealized model), no `admit`/`native_decide`. Model
boundary, stated bluntly: idealized ledger, random-oracle model, protocol
layer only. **We do not verify circuits.**

Kernel-checked today, by declaration name:

- **T1** `T1_no_overspend`; exculpability lemma `honest_never_slashed`
  (`Zkpc/Core/T1.lean`)
- **T2** `T2_upper`, `T2_collectable`, `T2_settles_exactly`
  (`Zkpc/Core/T2.lean`)
- **T3** `T3_settled_amount`, `T3_payer_balance_security`
  (`Zkpc/Core/T3.lean`)
- **T5** `T5_payer_close_liveness`, `settleClose_stable`, `tick_progress`
  (`Zkpc/Core/T5.lean`)
- **T6** `T6_priced_divergence`, `T6_slash_within_L`, `T6_accept_count`,
  with `epochs_in_window` (`Zkpc/Fleet/T6.lean`, `Zkpc/Fleet/Basic.lean`).
  Formalization surfaced two boundary facts: the count form is false at
  $C = 0$, and $T_e > 0$ is load-bearing.
- **RLN algebra** `rln_recover_k`, `rln_single_point_hiding`,
  `rln_evidence_sound`, `rln_x_zero_degenerate` (`Zkpc/Games/RLN.lean`)
- **T4 — spend unlinkability, advantage exactly 0** `T4_flat_unlinkability`
  (`Zkpc/Games/T4.lean`), over the session-form `unlinkGame`. Every
  adversary, every budget: perfect indistinguishability of a member's whole
  epoch session, against the full BOLT §1.4 abort/evict oracle. The close
  view is simulatable from `(cm, count)` alone (`flat_closeViewSimulatable`),
  so the honest residue is exactly the spend count and no more.
- **T7 — framing bound ≤ 1/|F|** `T7_frame_bound` (`Zkpc/Games/T7.lean`),
  under the RO-oblivious good-event hypothesis `hobliv`; the two must-win
  degenerate adversaries `frameWinProb_YK_eq_one` and
  `frameWinProb_aReuse_eq_one` frame at probability 1, so the game's silence
  on the sound scheme means something.
- **Calibration** (`Zkpc/Games/Calibration.lean`): the pair
  `unlinkAdvantage_staticDistinguisher_eq_half` (broken B-static at ½) and
  `unlinkAdvantage_bRerand_eq_zero` (B-rerand at 0), plus the must-catch
  battery `unlinkAdvantage_aIndexLeak`, `unlinkAdvantage_nfeReuse`,
  `unlinkAdvantage_multTagDistinguisher_eq_half` — each at ½.
- **Refund variant** (B, single-channel, `Zkpc/Refund/`):
  `T1_B_no_overspend`, `T3_B_floor`, `conservation`,
  `self_slash_race_closed`.
- **Game framework** over VCV-io: advantage bridges, challenge-terminated
  adversary type, abort/evict wrapper (`Zkpc/Games/Framework.lean`).

Stated plainly rather than around, the remaining in-model deferral:

- **T7's unconditional bound** — the quantitative query-budget composition
  endpoint is kernel-checked (structural per-channel budgets, adaptive
  first-hit and multi-target slope kernels, and a theorem turning a
  deferred-sampling certificate into the corrected
  `(q_A+q_E+q_Id+q_Nf·q_sig+q_sig²+1)/|F|` bound); the originally frozen
  pointwise certificate was then kernel-*refuted* (a two-probe adversary
  makes it unsatisfiable) and replaced by a secret-averaged socket
  composing to the same bound. Constructing that averaged certificate from
  the real handler is the one open step — scoped, not smuggled into an
  axiom. The kernel guarantees everything up to it. What remains beyond is
  deployment-grade cryptography (concrete hash/signature reductions behind
  the ideal reference layers); circuits are out of the model boundary.

Every theorem above is axiom-clean: `#print axioms` shows only Lean's
`propext`/`Quot.sound`/`Classical.choice` (audited declaration by
declaration, K2).

## Placement, compressed

Full table with per-row citations in the
[paper](https://github.com/dmarzzz/zk-payments-confetti/tree/main/paper).
The shape of it:

- **Ecash and credit tokens**
  ([Chaum](https://link.springer.com/chapter/10.1007/978-1-4757-0602-4_18)/[CFN](https://link.springer.com/chapter/10.1007/0-387-34799-2_25),
  [Compact E-Cash](https://eprint.iacr.org/2005/060),
  [Cashu](https://github.com/cashubtc/nuts/blob/main/00.md),
  [Fedimint](https://github.com/fedimint/fedimint),
  [Taler](https://www.taler.net/papers/taler2016space.pdf),
  [Privacy Pass](https://www.ietf.org/rfc/rfc9576.html),
  [ARC](https://datatracker.ietf.org/doc/draft-ietf-privacypass-arc-crypto/),
  [ACT](https://datatracker.ietf.org/doc/draft-schlesinger-cfrg-act/)):
  anonymous balance at one verifier with *online prevention* — a
  synchronous spent set someone must hold. ACT is the closest living
  relative (hidden balance, nullifiers, blind change; issuer = verifier by
  construction), but prevention means it has nothing to say about multiple
  verifiers, asynchrony, framing, or settlement — no analogue of T6 or T7.
- **The hub line**
  ([TumbleBit](https://www.ndss-symposium.org/wp-content/uploads/2017/09/ndss201701-3HeilmanPaper.pdf),
  [A2L/A2L+](https://dl.acm.org/doi/10.1145/3548606.3560637),
  [BlindHub](https://eprint.iacr.org/2022/1735),
  [Accio](https://eprint.iacr.org/2023/1326), with
  [adaptor signatures formalized 2024](https://eprint.iacr.org/2024/1809.pdf)):
  where privacy definitions got modernized and stress-tested — but it
  hides who-pays-whom from a *third party*. Our adversary is the payee
  itself, so the right ancestor is BOLT, not the tumblers.
- **BOLT/zkChannels**: the origin, the threat model (§1.4 aborts), and the
  cautionary deployment history. Revocation punishment needs
  chain-watching; a zkChannels dispute forfeits the entire balance to the
  merchant.
- **[Nym zk-nym](https://nym.com/docs/network/cryptography/zk-nym/zk-nym-overview)**:
  the closest deployed system to the fleet setting — threshold-issued
  tickets, any-gateway spend, deferred Bloom-filter reconciliation — with
  the reconciliation cadence and penalties undocumented. Those are exactly
  the parameters T6 forces into the open.
- **[PrivateX402](https://ethresear.ch/t/privatex402-privacy-preserving-payment-channels-for-multi-agent-ai-systems/24151)**:
  multi-recipient, one deposit — and no unlinkability against the
  recipient at all, which is the property that defines our object.
- **Verification landscape**: Lightning has UC
  ([Kiayias–Litos](https://eprint.iacr.org/2019/778.pdf)), Why3 fund
  safety ([2503.07200](https://arxiv.org/abs/2503.07200)), TLA+
  ([2505.15568](https://arxiv.org/abs/2505.15568)). Balance security is
  covered ground; privacy is not, in any prover.

## Honest limits

- **Recipient-bound.** One deposit, one logical payee. Not a
  multi-merchant payment system.
- **Capital lockup** per counterparty, below the
  [frequency threshold](https://pubsonline.informs.org/doi/10.1287/mnsc.2022.01664)
  channels don't pay for themselves — the reason the fleet is one logical
  payee rather than N channels.
- **Funding-graph leakage.** Open is public; without shielded funding the
  anonymity set is fiction at the deposit edge. Prescribed, not modeled.
- **Spend count at close leaks.** Both closes reveal it ($j$, or
  $\lfloor D/C \rfloor - |U|$). T4 terminates at the challenge precisely
  because of this; a member closing right after a distinctive burst
  correlates itself.
- **Within-epoch linkability is by design** — the rate limiter is a
  linker at epoch granularity. T4 claims cross-epoch and to-identity
  unlinkability only. Cross-epoch intersection attacks over stable
  memberships remain unpriced, as everywhere in this literature.
- **A slash is retroactive deanonymization — identity-slash only.** An
  identity-slash publishes $k$, from which the member's entire lifetime
  history is enumerable; the privacy is contingent on $k$ staying secret,
  and the protocol itself contains the mechanism that reveals it. No forward
  anonymity by design. A fund-slash (false-claim void, settlement bar, B
  forfeit) keeps $k$ hidden and links nothing — only the evidence-pair
  identity-slash deanonymizes. FRAME machine-checks that door; B's
  failed-upgrade exculpability is spec-level, not machine-checked.
- **The B stale-close residue.** Under receipt withholding an honest B payer
  can be forced to close on a stale receipt, linking $cm$ to one epoch
  session; the upgrade window restores funds, not privacy. The nuance: a
  payee declining to dispute gets the linkage nearly free (one forgone
  $c \le C_{max}$) — publication prices the payee's recovery, not the
  linkage.
- **Two candidates, not the population.** The $2 \to n$ hybrid goes through
  (independent secrets, no peer interaction, global $D$) but is not
  machine-checked; and the challenge-capable set is adversary-shrinkable at
  zero cost (refuse service, withhold receipts), down to one — no theorem
  resists this, the defence is operational. No theorem constrains a payee's
  right to refuse service.
- **Window recovery presumes fleet honesty.** A member–gateway collusion
  can pre-checkpoint fake "service" and crowd out honest gateways'
  post-slash claims. T7 protects members from gateways, not gateways from
  each other.
- **Close racing**: bounded exposure (acceptance rate × window), borne by
  the tardy gateway in A; pause-acceptance-during-close in B.
- **$x \neq 0$**: at digest zero the signal *is* the secret
  (`rln_x_zero_degenerate`); $H_x$ must be domain-separated away from
  zero. Found by the formalization, fed back into the spec.
- **Traffic analysis** (timing, token counts, sizes) is out of scope and
  real — per the credits thread itself, "a richer fingerprint than the
  wallet address."
- **The named open problem: multi-recipient generalization.** Portable
  deposits without linking events, or threshold issuance over a shared
  spent structure with *documented* reconciliation guarantees — the
  Nym-shaped hybrid, given the T6 treatment. Named, not solved.

## Reproduce it

```
git clone https://github.com/dmarzzz/zk-payments-confetti
cd zk-payments-confetti
lake exe cache get
lake build
```

Pinned: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`, VCV-io `8f5dc4f`.
The spec of record is `Spec.md` (rev 11); the theorem-to-file map is in the
paper's reproducibility section; the gate record with every counterexample
is `research_knowledge/gates.md`; TLA+ models (including ablation configs
that replay the replay/merge-evidence counterexamples) are in `tla/`.

Attack the definitions. That is what they are for.
