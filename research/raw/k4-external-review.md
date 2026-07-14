# K4 — External review of the security definitions (simulated outside referee)

Reviewer stance: anonymous-credentials / e-cash background, no prior contact with
this repo, reviewing **the games, not the proofs** (task K4). Object under review:
Spec.md revision 8 — T4 UNLINK, T7 FRAME, the T3 exculpability clause, MC6, MC15,
MC20, and the B-static/B-rerand calibration requirement — read against the field's
prior definitional failures (BOLT §1.4 abort attacks; TumbleBit's k-anonymity
accounting; the A2L 2021→2022 model gap; ../processed/field-report.md deep dives 2–3). Lean
docstrings of `Zkpc/Games/Unlink.lean` and `Frame.lean` were read as the encoding
of record.

Severity scale used: **definitional-hole** (the game passes a scheme users would
call broken, within the game's own claimed scope) > **missing-honest-limit**
(the guarantee is real but its deployment meaning is weaker than the headline and
the gap is not yet stated quantitatively) > **presentation** (right substance,
wrong or absent statement).

---

## Summary judgment

**REVISE.** This is the most internally battle-hardened pair of privacy games I
have reviewed — eight adversarial rounds show, and several complaints I arrived
ready to make are pre-empted (see "Where the definitions survive"). But the
UNLINK game's central repair — challenge termination — has two consequences the
spec has not fully priced: the epoch-freshness predicate restricts the theorem
to *first-spends-per-epoch* (Concern 1), and termination blinds the game to all
post-challenge state-evolution leakage, of which the acknowledged "spend count at
close" is only the mildest instance (Concern 2). Both admit concrete
passes-UNLINK-but-linkable constructions inside the stated scope. The calibration
battery is one-dimensional and B-only (Concern 5), the mechanized FRAME covers
one of three slash pathways (Concern 4), and the deployment-level anonymity
accounting the spec repeatedly promises to "the paper's honest-limits section"
needs to exist as one quantitative statement, not scattered scope notes
(Concern 3). None of this requires redesigning the protocol; it requires either
strengthening the games at two identified points or narrowing the claims to what
the games actually check — the A2L lesson is precisely that the second option,
done honestly, is respectable, and silence is not.

---

## Concern 1 — Epoch-freshness makes T4 a *first-spend-of-epoch* theorem. (definitional-hole)

**The gap.** The challenge move requires that neither candidate has emitted any
signal in the challenge epoch `e*` (`epochFresh`). So the challenge ticket is
structurally always a member's *first* spend of an epoch. The theorem therefore
quantifies over exactly one wire situation, while T4's claim text ("unlinkability
of spends to member identity and across epochs") quantifies over all spends.

**Construction (passes UNLINK, users would call it linkable).** Take
instantiation A and modify `Spend` so that the *second and subsequent* spends
within one epoch carry an extra field `tag = H'(k)` — a persistent, cross-epoch
member tag (motivation a designer might even offer: a "session continuation
token" to cheapen repeat verification within an epoch). Under the UNLINK game:
pre-challenge, the adversary sees `tag(k_0)` and `tag(k_1)` on second-spends of
both candidates — but it already knows the attribution of every pre-challenge
ticket (it directs `Ospend(u, m)` by candidate index), so this is no advantage.
The challenge ticket is by construction a first-spend-of-`e*` and never carries
the tag. Advantage stays negligible; the scheme **passes**. In deployment, every
member who ever spends twice inside one epoch — the expected common case for a
rate-limited protocol with per-epoch budget `b > 1` — is linkable across *all*
epochs, forever, by a persistent tag. This violates T4's own claim text (it is
cross-epoch linkage, not the MC6 within-epoch linkage the scope excludes: MC6
covers spends in one epoch being linkable *to each other* via `nf_e`, not a
handle that survives epoch rotation).

**Why the rev-1 anti-vacuity probe missed it.** Anti-vacuity (ii) records that
"persistent tags surface in `t*` against the pre-challenge transcript." That is
true of *unconditional* tags. Multiplicity-conditional tags never surface in
`t*` because the freshness predicate guarantees `t*` is a first-spend. The probe
tested one point of a family.

**Is MC6 honest scope or a hole?** MC6 itself is honest scope — within-epoch
linkage via `nf_e` is the deployed rate-limiting mechanism, and a game denying
it would formalize a protocol the fleet does not run. The hole is not the
exclusion; it is that the *challenge shape* inherited from the exclusion is
narrower than the *claim*.

**What would satisfy me** (either suffices):

1. **Session challenge.** Replace the single challenge message `m*` with an
   adversary-chosen vector `(m*_1, …, m*_ℓ)`; `P_b` emits an entire ℓ-spend
   session inside `e*` (all under the one `nf_e`, which is fine — both worlds
   share the session structure) and the game then terminates. This makes the
   challenge exercise the second-spend wire format, and the construction above
   is caught (the tag on `t*_2` matches one candidate's pre-challenge tags).
   The freshness predicate, capability check, and termination logic carry over
   unchanged; the Lean delta is modest (challenge move iterates `S.spend`).
2. **Narrow the claim.** State T4 as *first-spend-per-epoch unlinkability*,
   demote "across epochs" to a corollary that holds only under an additional
   syntactic hypothesis (the ticket view is a function of `(k, i, m, e)` whose
   distribution is index-within-epoch-independent — true of both real
   instantiations, checkable per instance), and carry the limitation in the
   honest-limits section.

Option 1 is strictly better and I would push for it: the point of mechanizing
the definitions is that the *game* catches broken instances, not a side
hypothesis a future instance-author must remember to check.

## Concern 2 — Challenge termination hides all close-time and post-spend leakage; "spend count" understates it. (definitional-hole)

**The gap.** The game ends at challenge delivery; no oracle answers afterwards
(`ChalAdversary`, by type). MC15 states the honest residue as: "the spend count
revealed at payer-close is a side channel this theorem does not cover." But the
terminated game is blind to far more than the count — it is blind to the *entire
content* of any close event that post-dates a spend, and to every other
bit-dependent state evolution after the challenge.

**Construction (passes UNLINK, catastrophically linkable).** Take instantiation
A and modify `Close` to publish the member's **used** nullifiers instead of (or
in addition to) the unused ones — `U' = {nf_i : i < j}`. This retroactively
links every ticket the member ever emitted to its now-public `cm`. Under the
game: a *pre-challenge* `Oclose(u)` reveals used nullifiers of a candidate whose
tickets the adversary already attributes (no advantage), and a closed candidate
fails `challengeCapable`, so no challenge follows it; a *post-challenge* close
never occurs because the game has ended. The scheme **passes UNLINK**. In
deployment every member eventually closes, so this variant's privacy is: "your
spends are unlinkable until the day you close, at which point your entire
history is published." No user would accept that as "unlinkability," and no
reading of MC15's "the count leaks" covers it. The actual scheme is fine (A
reveals only PRF-fresh unused nullifiers; B reveals one fresh `nf_j`) — but the
A2L criterion is whether the *definition* excludes broken instantiations, and
here it does not: the game cannot distinguish a close that reveals fresh values
from a close that reveals the member's history.

**What would satisfy me** (in order of preference):

1. **A machine-checked CloseView-simulatability obligation**, parallel in
   spirit to `zkBridgeObligation`: per instance, a simulator that reproduces the
   `CloseView` distribution from `(cm_u, spend count, public parameters)` alone
   — no access to the candidate's spend transcript or `k`. For real-A this is
   provable in ROM (unused nullifiers are uniform values never queried
   elsewhere); for real-B likewise (`nf_j` fresh). For the used-nullifier
   variant it is false. This converts MC15's prose ("the count, and only the
   count, leaks at close") into a theorem, which is exactly what it currently
   is not.
2. Alternatively, a second small game (close-time forward privacy): full
   attributed transcript for both candidates with equal spend counts, `P_b`
   closes, adversary guesses `b`. Weaker than (1) (equal-count conditioning
   must be justified) but still catches the construction.
3. At absolute minimum: rewrite MC15's honest residue from "the spend count is
   revealed" to "the theorem constrains **nothing** about close-event content;
   the deployed instantiations additionally satisfy [count-only leakage], which
   is argued but not machine-checked" — and record the used-nullifier variant
   in `gates.md` as a known scheme the game fails to reject.

The same blindness covers post-challenge solvency-exhaustion probing (serve
both candidates to ⊥ after the observed spend and read off which budget is one
lower). The spec knows this — it is one of rev-1's three universal
distinguishers that forced termination — but the honest-limits framing again
compresses it into "the count at close," when the deployment-facing statement
is: **the composed guarantee of a challenge-terminated game is unlinkability up
to the adversary's knowledge of each member's running spend count** (see
Concern 3).

## Concern 3 — No composed, quantitative deployment statement; the erosion accounting is scattered. (missing-honest-limit)

The BOLT/TumbleBit lesson the spec cites is not just "aborts shrink sets"; it is
that the honest paper carries the *arithmetic*. Rev-8 has all the ingredients as
scattered scope notes (MC6, MC15, T4 ⊥-branch, §5 exclusions) and no single
statement. Three items are owed:

**(a) The 2-candidate → population hybrid.** Users care about anonymity within
the live membership, not a 2-member lineup. The standard hybrid does go through
here — the reduction simulates all other members as corrupt payers run honestly
(distributionally identical to honest payers, since payers hold independent
secrets, never interact peer-to-peer, and the deposit `D` is a global constant),
losing the usual factor — but the spec neither states nor proves it, and with
`GenesisInput` adversary-supplied in B one should actually check the hybrid
respects the genesis stage. One lemma or one stated corollary; currently zero.

**(b) Anonymity after q aborts / q closes.** The ⊥-branch's accounting —
eviction "charged to the anonymity set, not the scheme" — is the field-standard
choice and I endorse it (it is TumbleBit's k = completed payments, BOLT's §1.4
made formal). But it means the delivered guarantee is *indistinguishability
within the capable set*, and the capable set is adversary-controlled at zero
protocol cost (refusal of service in A; receipt withholding in B). The paper
must say: after the adversary evicts `q` members, the set is `n − q`, down to 1,
and **nothing in T4 resists this** — the defense is operational (members notice
starvation and leave; gateways compete), not cryptographic.

**(c) The intersection/counting attack the side channels compose into.** Within
the *stated* scope (no timing, no volume, no content), the adversary still
observes, per epoch, the partition of accepted spends into `nf_e`-clusters
(MC6, by design) and, at each close, `(cm, lifetime count j)` on a public ledger
(MC15). These compose: a close at count `j` constrains which unattributed
cluster-size sequences over the member's lifetime sum to `j`; across many closes
this is a constrained assignment problem, and with realistic usage skew,
solutions go unique — full retro-attribution of epoch-clusters to identities
without touching any excluded side channel. This is TumbleBit's own cross-epoch
intersection warning transposed, and it is *inside* the model. MC6 and MC15 each
say "same epistemic status as the other"; neither notes that their **joint**
leakage is superlinear. The honest-limits section should carry a worked
epochs-to-deanonymization sketch (../processed/field-report.md open problem 9 already asks for
exactly this) or an explicit statement that count-at-close plus cluster sizes
admit intersection attacks and the mitigation is operational (epoch coarseness,
close batching/delay).

Verdict on this angle: the ⊥-branch itself degrades *gracefully and honestly* —
the design choice is right. What is missing is the quantitative paragraph, and
"the paper must carry it" promises appear in the spec three times without a
draft of the content. I would not pass the paper with the promise still an IOU.

## Concern 4 — FRAME mechanizes one of three slash pathways. (presentation / machine-checked-gap, with one hole-adjacent edge)

Rev-8's protocol has three doors to a slash:

1. **Evidence-pair slashing** (`Dispute` on two line points). Modeled by FRAME;
   the win predicate is the line-recovery algebra, ancillary checks omitted in
   the adversary's favor. This is the right game for this door, and its
   `nfAt`-superset treatment of the MC20 close reveal is exemplary.
2. **False-unused-claim slashing at A-close** (MC20: a checkpointed acceptance
   whose `nf ∈ U` voids and slashes; also the settlement-detected sweep-bar
   slash). Exculpability of the honest closer rests on: checkpoint = binding
   Merkle commitment + genuinely-unused nullifiers PRF-hidden pre-close.
   Spec-prose only (T3's "no close-dispute path slashes it either"; T5's "the
   voided branch never fires").
3. **Failed-upgrade slashing at B-close** (rev-7/8 dispute discipline: a valid
   stale-close dispute opens a sub-window; only failure to upgrade slashes).
   Exculpability rests on contiguity (gap ≤ 1), receipt-bearing checkpoint
   tuples, opening-reconstruction via opening-homomorphism, and the honest
   closer's monitoring duty. Spec-prose only.

The mechanized artifact that will be advertised as "machine-checked
exculpability" covers door 1. Doors 2 and 3 are the *newest* mechanisms in the
spec (rev-5 through rev-8), which on this project's own evidence is exactly
where holes live — every one of the last four review rounds found its blocking
issue in the close path. A reviewer at a top venue will say: your mechanized
FRAME guards the oldest, best-understood door and leaves the two doors you
redesigned last month to prose. **What would satisfy me:** either a second
mechanized game (CLOSE-FRAME: adversary controls all gateways and the ledger's
checkpoint log subject to commitment binding; wins if an honest closer's close
is voided-and-slashed — the core reduction is to Merkle-commitment binding plus
PRF freshness of unused nullifiers, both already in `Assumptions`), or an
explicit, prominent statement in the paper that close-dispute exculpability is
spec-level argument, not machine-checked, with the trust boundary drawn.

Two sub-points the definitions **survive**:

- *Framing third parties rather than the ledger.* In this design, social
  framing collapses to ledger framing: the evidence pair is publicly
  recomputable by anyone (recover `a`, `k`, check `nf` and `cm`), so a gateway
  that cannot win FRAME also cannot produce an artifact that convinces any
  rational third party. There is no "soft evidence" surface (an unopened
  claimed-duplicate carries no weight without the checkable pair). This is a
  genuine strength of detect-and-slash over revocation designs and the paper
  should *claim* it, with the one-line argument, rather than leave it implicit.
- *Refusal-of-service as de-facto eviction.* Real harm, correctly not a FRAME
  matter: no cryptographic protocol compels service, and the e-cash tradition's
  exculpability has never covered it. But no theorem in T1–T7 provides any
  service-liveness either (T5 is closure liveness only), and the UNLINK
  ⊥-branch shows the same lever eroding anonymity. One explicit sentence —
  "no theorem constrains a payee's right to refuse service; the protocol prices
  refusal at zero" — belongs in honest limits, cross-referenced from both T4
  and T7.

## Concern 5 — The calibration battery is one bit, on one instantiation. (missing calibration; presentation)

B-static vs B-rerand is a good pair — the broken variant is the historically
attested failure (omarespejel's finding), and requiring the attack as a
constructive Lean term is the right discipline. But it separates on exactly one
axis: *presented-ciphertext identity*. A game that merely checked "does the
challenge view contain a bit-identical copy of a pre-challenge-issued value"
would also separate this pair — and would be wrong in every other dimension.
Concerns 1–2 exhibit two broken schemes the pair does not represent and the game
does not catch. Also note: **instantiation A currently has no calibration point
at all** — nothing tests that UNLINK-instantiated-on-A can detect any broken
A-variant.

Proposed battery (each cheap, each a different failure dimension):

1. **A-index-leak** (must be caught): A-variant whose ticket view includes the
   spend index `i`. Distinguisher: drive the candidates to unequal pre-challenge
   spend counts, read the challenge index. Exercises the counter machinery and
   gives A its first constructive calibration term.
2. **nf_e-reuse** (must be caught): epoch pseudonym computed as `H_e(k)`
   without `e`. The challenge ticket's persistent pseudonym matches one
   candidate's pre-challenge transcript despite epoch freshness. Converts
   anti-vacuity probe (ii) from prose into a constructive term.
3. **A-degenerate-RLN for FRAME** (must be won): `y = k` (no masking) and
   `a` reused across indices — both named in T7's anti-vacuity; make them
   constructive winning FRAME adversaries, symmetric to the B-static
   discipline.
4. **Negative calibration ledger** (must be *recorded as uncaught*): the
   multiplicity-tag variant (Concern 1) and the used-nullifier-close variant
   (Concern 2), entered in `gates.md` as schemes the current game passes —
   either as the motivation for the game extensions above, or, if the team
   chooses claim-narrowing instead, as the permanent honest-limits exhibit.
   A test battery that documents its own blind spots is worth more to a
   reviewer than one that only contains wins.

## Concern 6 — Punishment is total retroactive deanonymization, and no definition or limit says so. (missing-honest-limit)

A slash publishes `k`. From `k`, every `nf_i = H_nf(H_a(k, i))` and every epoch
pseudonym `nf_e = H_e(k, e)` is enumerable — the spec *relies* on this (MC4
post-slash sweep attribution). Consequence: a slash does not cost the member
`D`; it retroactively links the member's **entire lifetime request history** —
every within-epoch cluster, every accepted ticket at every gateway — to its
public `cm`. Three things follow that the definitions do not currently surface:

- The privacy delivered by T4 is *contingent and revocable*: it lasts exactly
  as long as `k` stays secret, and the protocol itself contains the mechanism
  that publishes `k`. There is no forward anonymity by design. This is a
  legitimate engineering trade (it is what makes the slash claimable by
  anyone), but a user-facing "unlinkability" claim that omits it is over-read.
  UNLINK cannot see it (candidates are statically honest, MC10 — post-
  compromise linkage is outside every game by construction), so the *paper*
  must carry it.
- The penalty is radically disproportionate for accidental double-emission: an
  honest-but-buggy client that violates MC2 once (re-emits a different message
  at a used index — the spec itself calls this "self-slashing") loses `D` *and*
  its entire anonymity history. FRAME says nothing here — the member did
  double-sign. The honest-limits section should state the blast radius of a
  client bug, because "exculpability" will otherwise be read as "honest users
  are safe," and the guarantee is actually "*correct* users are safe."
- The weight resting on FRAME should be stated in these terms: FRAME is not
  protecting a deposit; it is the sole barrier between every member and total
  retroactive deanonymization by the fleet's own operators. That reframing
  makes the Concern-4 gap (close-path slashes not mechanized) more urgent, since
  doors 2 and 3 end in the same `k`-publication... — actually, verify and state
  whether a close-dispute slash publishes `k` or only freezes/forfeits: MC20's
  false-claim slash has no evidence pair, so `k` may stay secret there. If so,
  say so — it materially softens Concern 4's stakes for door 2, and the
  distinction ("fund slash" vs "identity slash") deserves to be explicit in §2.

## Where the definitions survive (attacks attempted and repelled)

For fairness, the angles I came in expecting to land, and why they do not:

- **Bit-dependent ⊥** — `b` sampled first, ⊥-paths contribute exactly ½;
  the rev-1 repair is correct and the Lean encoding matches. No conditioning
  bug survives.
- **Abort oracle with no teeth** — the BOLT §1.4 powers are real here: in B,
  receipt withholding concretely drives insolvency, reaches the ⊥-branch, and
  anti-vacuity (iii) obliges the proof to show nothing is gained beyond the
  branch. This is better than BOLT's own informal treatment.
- **Freshness as foreknowledge** — rev-2 NEW-5's transcript-predicate reading
  is right, and the game state (`lastSig`), not the scheme, tracks it; the
  retry/freshness interaction (bit-identical re-send carries the old pseudonym,
  does not refresh) is handled correctly.
- **Adversary-issued genesis (M2)** — in B the payee issues the genesis
  receipt, and the game correctly hands that to the adversary rather than the
  challenger; malformed genesis is absorbed as one more eviction lever. This
  is the kind of detail external reviewers usually catch missing; it is not
  missing.
- **Epoch clock under adversary control** (`tick`) — maximal-power encoding,
  faithful to §6 scheduler control.
- **FRAME's `nfAt` superset** — giving the adversary *every* index's nullifier
  rather than the actual close's `U` is the right dominance move, as is the
  unbounded spend oracle and the omission of `Dispute`'s ancillary checks. The
  game is uniformly at-least-as-strong as the deployed surface for door 1.
- **Population hybrid obstruction** — I looked for a reason the 2-candidate
  game would *not* hybridize (shared state between payers, deposit
  heterogeneity, genesis coupling) and found none in this design; the gap is
  that the corollary is unstated (Concern 3a), not that it is false.
- **A cross-epoch-linkable scheme via unconditional tags** — correctly caught
  by the pre-challenge transcript, as anti-vacuity (ii) records; I could only
  evade it by conditioning the tag on multiplicity (Concern 1) or on close
  (Concern 2), i.e., on the two boundaries the game does not cross.

## Disposition requested

Accept-with-mandatory-revisions at the definitions layer:

1. Session challenge in UNLINK **or** claim narrowed to first-spend-per-epoch
   (Concern 1) — definitional-hole.
2. CloseView-simulatability obligation **or** honest-limit rewritten from
   "count leaks" to "close content unconstrained; count-only is argued, not
   checked," plus the negative calibration entry (Concern 2) —
   definitional-hole.
3. One quantitative honest-limits section: population hybrid stated, q-abort
   erosion, cluster+count intersection sketch (Concern 3) —
   missing-honest-limit.
4. The three-door slash map in the paper, with door 1 marked mechanized and
   doors 2–3 marked spec-level (CLOSE-FRAME game optional but recommended);
   claim the social-framing equivalence; state the absence of service
   liveness (Concern 4) — presentation.
5. Calibration battery extended per Concern 5, including A-side positive
   points and the uncaught-variant ledger — presentation.
6. The retroactive-deanonymization honest-limit, and the fund-slash vs
   identity-slash distinction made explicit (Concern 6) —
   missing-honest-limit.

None of these findings falsifies a theorem as stated; Concerns 1 and 2 show the
*games* certify less than the claim text and less than a user's reading of
"unlinkability." That is precisely the A2L failure mode this review was
commissioned to hunt, caught at the definitions stage where it is cheap.
