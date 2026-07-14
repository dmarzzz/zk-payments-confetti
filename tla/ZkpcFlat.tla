---------------------------- MODULE ZkpcFlat ----------------------------
(***************************************************************************)
(* C1/C2/C3: flat-ticket instantiation A of Spec.md, single gateway        *)
(* (N = 1).  Aligned to Spec.md REVISION 9 (gate-signed at rev-8).         *)
(*                                                                         *)
(* Idealized crypto: a "signal" is the record [m, idx, pay]; nf ~ (m,idx); *)
(* x ~ pay.  Knowledge soundness = only emitted signals exist and every    *)
(* redeemable ticket satisfies the solvency conjunct (idx+1)*C <= D.       *)
(* Evidence validity = two genuinely emitted signals of the same member at *)
(* one index with different messages (no forgery, T7).                     *)
(*                                                                         *)
(* CloseMode selects the payer-close mechanics:                            *)
(*  - "mc20" (rev-9 canonical, the DEFAULT): close-by-unused-enumeration.  *)
(*    The closer submits U = revealed nullifiers of claimed-unused         *)
(*    indices (all < cap = floor(D/C), distinctness and well-formedness    *)
(*    proof-enforced -- structural here).  No close signal is emitted.     *)
(*    Window: a gateway holding a PRE-CLOSE-CHECKPOINTED acceptance whose  *)
(*    nf is in U disproves the claim -> close voided + slash; ordinary     *)
(*    Dispute evidence also voids.  Settlement: TWO-SIDED SWEEP BAR --     *)
(*    (i) any nf in U already in RedeemedNF is an on-ledger disproof ->    *)
(*    void + slash with NO evidence submitter (post-window remainder       *)
(*    stays in the pool, rev-8 F8-m4); (ii) otherwise pay                  *)
(*    C*|U| + (D - cap*C), record U, refuse all future sweeps of nf in U,  *)
(*    and EVICT cm from the tree (root rotates; in-flight tickets die).    *)
(*    In-window acceptances at indices in U are allowed (the structurally  *)
(*    un-checkpointable in-flight exposure of rev-9's honest-limits note); *)
(*    if unswept at settlement the tardy/racing gateway eats them.         *)
(*  - "rev2" (HISTORICAL, revs 1-5): close-as-final-spend at index j.      *)
(*    Kept reproducible as the C2 counterexample: PoolSolvency falls to    *)
(*    the withheld-collision close and the gap-index understatement        *)
(*    (= gate round 5's blocking finding, found here concurrently).        *)
(*  - "rev2root" (HISTORICAL probe): rev2 + root rotation at close         *)
(*    submission -- shows rotation alone does not repair the hole.         *)
(*                                                                         *)
(* Other modeling choices (research/raw/tla-findings.md):            *)
(*  - Tickets carry no epoch stamp; Redeem's check 3 collapses to          *)
(*    counting the budget against the redeem-time epoch (safety-safe       *)
(*    over-approximation).  Epochs/lag are modeled in ZkpcFleet.           *)
(*  - Check 4 (gateway binding) is trivial at N = 1; see ZkpcFleet.        *)
(*  - Check order matches rev-9: budget (5) strictly before nullifier      *)
(*    logic (6); the rate counter increments on accepts only.              *)
(*  - Honest spends use a fixed payload "p1"; Byzantine members choose     *)
(*    from two payloads (enough to double-sign).                           *)
(*  - tau and Delta are collapsed: window expiry is an explicit action;    *)
(*    the MC16 monitoring duty = "no gateway-known dispute pending" as an  *)
(*    expiry guard plus fairness on the dispute actions.  Perfect          *)
(*    checkpoint cadence: the pre-close checkpoint = the accepted set at   *)
(*    the close transaction.                                               *)
(*  - The gateway only remembers presented tickets it accepted or that     *)
(*    conflict with something already observed (state reduction; plain     *)
(*    rejects/duplicates leave no trace and can be re-presented).          *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS Members, Byz, C, D, B, MaxEpoch, CloseMode

ASSUME Byz \subseteq Members
ASSUME CloseMode \in {"mc20", "rev2", "rev2root"}

MaxIdx   == D \div C                \* cap: number of solvent spend indices
Payloads == {"p1", "p2"}
AllPays  == Payloads \cup {"CLOSE"}
TicketSp == [m : Members, idx : 0..MaxIdx, pay : AllPays]
IdxSp    == 0..(MaxIdx - 1)

VARIABLES
  status,   \* [Members -> {"init","open","closing","disputed","closed","slashed"}]
  nextIdx,  \* honest emission counter per member
  emitted,  \* set of signals that exist (emission = coming into existence)
  seen,     \* signals the gateway/ledger has observed (ss \subseteq seen)
  ss,       \* gateway spent set: accepted tuples
  redeemed, \* swept tuples on the ledger (RedeemedNF, dedup by nf)
  rate,     \* accepts per member in the current epoch (epoch pseudonym counter)
  epoch,
  pool,     \* commingled escrow pool (Int: a negative value is the bug)
  closeIdx, \* rev2 modes: close index j per member, -1 if no close submitted
  claimU,   \* mc20: claimed-unused index set per member ({} before close)
  falseCk,  \* mc20: TRUE iff a pre-close checkpoint disproves the U claim
  noBounty, \* mc20: slash was settlement-detected (no evidence submitter)
  slashRem, \* remaining deposit claimable during a slash window
  paidP,    \* per-member payer-close payout received
  paidG,    \* total settled to the gateway (sweeps + window claims)
  paidB     \* total slash bounty paid out

vars == <<status, nextIdx, emitted, seen, ss, redeemed, rate, epoch, pool,
          closeIdx, claimU, falseCk, noBounty, slashRem, paidP, paidG, paidB>>

NfEq(a, b)     == a.m = b.m /\ a.idx = b.idx
Conflict(a, b) == NfEq(a, b) /\ a.pay # b.pay
AcceptedOf(m)  == {t \in ss : t.m = m}
RedeemedOf(m)  == {t \in redeemed : t.m = m}
Swept(t)       == \E r \in redeemed : NfEq(r, t)

\* Evidence the gateway/ledger can actually hold: both signals observed.
GwEvidence(m)  == \E t1 \in seen, t2 \in seen : t1.m = m /\ Conflict(t1, t2)
\* A Byzantine member knows k and can materialize any pair it has emitted.
ByzPair(m)     == \E t1 \in emitted, t2 \in emitted : t1.m = m /\ Conflict(t1, t2)

\* Membership-tree check (Redeem check 2).  mc20 evicts cm at settlement
\* (rev-9: "closed and evicted from the tree"); rev2 rotated only on slash;
\* rev2root probes rotation at close submission.
InTree(m) ==
  CASE CloseMode = "mc20"     -> status[m] \in {"open", "closing"}
    [] CloseMode = "rev2"     -> status[m] \in {"open", "closing", "closed"}
    [] CloseMode = "rev2root" -> status[m] = "open"

\* mc20 settlement-time disproof: some claimed-unused nf already swept
\* (the U-intersect-RedeemedNF side of the two-sided sweep bar).
SweptUClaim(m) == \E r \in redeemed : r.m = m /\ r.idx \in claimU[m]

\* mc20 forward bar: after settlement the ledger refuses sweeps of recorded U.
SweepBarred(t) ==
  CloseMode = "mc20" /\ status[t.m] = "closed" /\ t.idx \in claimU[t.m]

ClosePayout(m) ==
  IF CloseMode = "mc20"
  THEN C * Cardinality(claimU[m]) + (D - MaxIdx * C)
  ELSE D - closeIdx[m] * C

Init == /\ status   = [m \in Members |-> "init"]
        /\ nextIdx  = [m \in Members |-> 0]
        /\ emitted  = {}
        /\ seen     = {}
        /\ ss       = {}
        /\ redeemed = {}
        /\ rate     = [m \in Members |-> 0]
        /\ epoch    = 1
        /\ pool     = 0
        /\ closeIdx = [m \in Members |-> -1]
        /\ claimU   = [m \in Members |-> {}]
        /\ falseCk  = [m \in Members |-> FALSE]
        /\ noBounty = [m \in Members |-> FALSE]
        /\ slashRem = [m \in Members |-> 0]
        /\ paidP    = [m \in Members |-> 0]
        /\ paidG    = 0
        /\ paidB    = 0

(***************************************************************************)
(* Ledger / protocol actions                                               *)
(***************************************************************************)

Open(m) ==
  /\ status[m] = "init"
  /\ status' = [status EXCEPT ![m] = "open"]
  /\ pool'   = pool + D
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch,
                 closeIdx, claimU, falseCk, noBounty, slashRem,
                 paidP, paidG, paidB>>

\* Honest Spend: emit at the current index, consume the index (MC2).
HonestSpend(m) ==
  /\ m \notin Byz
  /\ status[m] = "open"
  /\ (nextIdx[m] + 1) * C <= D
  /\ emitted' = emitted \cup {[m |-> m, idx |-> nextIdx[m], pay |-> "p1"]}
  /\ nextIdx' = [nextIdx EXCEPT ![m] = @ + 1]
  /\ UNCHANGED <<status, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, claimU, falseCk, noBounty, slashRem,
                 paidP, paidG, paidB>>

\* A Byzantine payer emits any signal at any index with any payload
\* (conflicting signals at one index = double-sign).  Emission needs only
\* k, not the tree; the solvency conjunct is enforced at Redeem.
ByzEmit(m, i, p) ==
  /\ m \in Byz
  /\ status[m] # "init"
  /\ LET t == [m |-> m, idx |-> i, pay |-> p] IN
       /\ t \notin emitted
       /\ emitted' = emitted \cup {t}
  /\ UNCHANGED <<status, nextIdx, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, claimU, falseCk, noBounty, slashRem,
                 paidP, paidG, paidB>>

\* Redeem: delivery of an emitted ticket is scheduled by the adversary.
\* Checks in Spec.md order: (1) proof [implicit: emitted + solvency
\* conjunct], (2) current root [InTree], (3) epoch [collapsed, header],
\* (4) gateway binding [trivial at N=1], (5) budget strictly under b,
\* (6) nullifier logic.  Accepts-only budget counting.  Note: in mc20 an
\* in-window acceptance at an index in the closer's U is deliberately
\* allowed (rev-9 in-flight exposure).
Redeem(t) ==
  /\ t \in emitted
  /\ t.pay # "CLOSE"
  /\ InTree(t.m)
  /\ (t.idx + 1) * C <= D          \* solvency conjunct of R_spend
  /\ LET fresh == ~\E s \in ss : NfEq(s, t)
         acc   == fresh /\ rate[t.m] < B
         keep  == acc \/ \E s \in seen : Conflict(s, t)
     IN /\ acc \/ (keep /\ t \notin seen)   \* prune no-op re-deliveries
        /\ seen' = seen \cup {t}
        /\ ss'   = IF acc THEN ss \cup {t} ELSE ss
        /\ rate' = IF acc THEN [rate EXCEPT ![t.m] = @ + 1] ELSE rate
  /\ UNCHANGED <<status, nextIdx, emitted, redeemed, epoch, pool,
                 closeIdx, claimU, falseCk, noBounty, slashRem,
                 paidP, paidG, paidB>>

AdvanceEpoch ==
  /\ epoch < MaxEpoch
  /\ epoch' = epoch + 1
  /\ rate'  = [m \in Members |-> 0]
  /\ UNCHANGED <<status, nextIdx, emitted, seen, ss, redeemed, pool,
                 closeIdx, claimU, falseCk, noBounty, slashRem,
                 paidP, paidG, paidB>>

(*** mc20 close: close-by-unused-enumeration (rev-9 canonical) ************)

\* The closer submits U.  The proof pins structure (distinct indices < cap,
\* correct nullifiers for its own k); the only possible lie is claiming a
\* spent index unused.  No signal is emitted.  falseCk snapshots whether
\* the gateway's pre-close checkpoint (= its accepted set now; perfect
\* cadence) disproves the claim.
SubmitCloseU(m, U) ==
  /\ CloseMode = "mc20"
  /\ status[m] = "open"
  /\ claimU'  = [claimU EXCEPT ![m] = U]
  /\ falseCk' = [falseCk EXCEPT ![m] = \E t \in ss : t.m = m /\ t.idx \in U]
  /\ status'  = [status EXCEPT ![m] = "closing"]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, noBounty, slashRem, paidP, paidG, paidB>>

HonestCloseU(m) ==
  /\ m \notin Byz
  /\ SubmitCloseU(m, {i \in IdxSp : i >= nextIdx[m]})

ByzCloseU(m, U) == m \in Byz /\ SubmitCloseU(m, U)

\* Window dispute (a): a pre-close-checkpointed acceptance whose nf is in U
\* disproves the claim -> close voided, channel slashed (bounty path).
DisputeFalseClaim(m) ==
  /\ CloseMode = "mc20"
  /\ status[m] = "closing"
  /\ falseCk[m]
  /\ status'   = [status EXCEPT ![m] = "disputed"]
  /\ slashRem' = [slashRem EXCEPT ![m] = D - C * Cardinality(RedeemedOf(m))]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, claimU, falseCk, noBounty, paidP, paidG, paidB>>

\* Settlement, clean path: the ledger first checks U against RedeemedNF
\* (two-sided bar, side i); clean -> pay C*|U| + (D - cap*C), record U
\* (SweepBarred takes over), close, evict from the tree (InTree).
SettleCloseU(m) ==
  /\ CloseMode = "mc20"
  /\ status[m] = "closing"
  /\ ~GwEvidence(m)                 \* monitoring duty: disputes go first
  /\ ~falseCk[m]
  /\ ~SweptUClaim(m)
  /\ pool'   = pool - ClosePayout(m)
  /\ paidP'  = [paidP EXCEPT ![m] = @ + ClosePayout(m)]
  /\ status' = [status EXCEPT ![m] = "closed"]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch,
                 closeIdx, claimU, falseCk, noBounty, slashRem, paidG, paidB>>

\* Settlement, disproof path: some nf in U is already in RedeemedNF (swept
\* pre-close or in-window).  On-ledger disproof, no evidence submitter:
\* close voided, slash window opens, and the post-window remainder stays
\* in the pool (noBounty; rev-8 F8-m4).
SettlementSlash(m) ==
  /\ CloseMode = "mc20"
  /\ status[m] = "closing"
  /\ ~GwEvidence(m)
  /\ ~falseCk[m]
  /\ SweptUClaim(m)
  /\ status'   = [status EXCEPT ![m] = "disputed"]
  /\ slashRem' = [slashRem EXCEPT ![m] = D - C * Cardinality(RedeemedOf(m))]
  /\ noBounty' = [noBounty EXCEPT ![m] = TRUE]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, claimU, falseCk, paidP, paidG, paidB>>

(*** rev2 / rev2root close: close-as-final-spend (HISTORICAL, revs 1-5) ***)

SubmitCloseSig(m, j) ==
  /\ CloseMode # "mc20"
  /\ status[m] = "open"
  /\ LET t == [m |-> m, idx |-> j, pay |-> "CLOSE"] IN
       /\ emitted' = emitted \cup {t}
       /\ seen'    = seen \cup {t}          \* the close signal is public
  /\ closeIdx' = [closeIdx EXCEPT ![m] = j]
  /\ status'   = [status EXCEPT ![m] = "closing"]
  /\ UNCHANGED <<nextIdx, ss, redeemed, rate, epoch, pool,
                 claimU, falseCk, noBounty, slashRem, paidP, paidG, paidB>>

HonestCloseSig(m) == m \notin Byz /\ SubmitCloseSig(m, nextIdx[m])
ByzCloseSig(m, j) == m \in Byz /\ j \in 0..MaxIdx /\ SubmitCloseSig(m, j)

ExpireCloseWindow(m) ==
  /\ CloseMode # "mc20"
  /\ status[m] = "closing"
  /\ ~GwEvidence(m)
  /\ pool'   = pool - ClosePayout(m)
  /\ paidP'  = [paidP EXCEPT ![m] = @ + ClosePayout(m)]
  /\ status' = [status EXCEPT ![m] = "closed"]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch,
                 closeIdx, claimU, falseCk, noBounty, slashRem, paidG, paidB>>

(*** Dispute / slash / sweeps (both modes) ********************************)

SlashEffects(m) ==
  /\ status'   = [status EXCEPT ![m] = "disputed"]
  /\ slashRem' = [slashRem EXCEPT ![m] = D - C * Cardinality(RedeemedOf(m))]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, claimU, falseCk, noBounty, paidP, paidG, paidB>>

GwDispute(m) ==
  /\ status[m] \in {"open", "closing"}
  /\ GwEvidence(m)
  /\ SlashEffects(m)

\* A Byzantine member can always self-slash (the T2 self-slash race).
ByzSelfDispute(m) ==
  /\ m \in Byz
  /\ status[m] \in {"open", "closing"}
  /\ ByzPair(m)
  /\ SlashEffects(m)

\* Unilateral gateway sweep: C per fresh nf out of the commingled pool.
\* mc20: sweeps of recorded-U nullifiers are refused (two-sided bar, side ii).
GwSweep(t) ==
  /\ t \in ss
  /\ status[t.m] \in {"open", "closing", "closed"}
  /\ ~Swept(t)
  /\ ~SweepBarred(t)
  /\ pool'     = pool - C
  /\ paidG'    = paidG + C
  /\ redeemed' = redeemed \cup {t}
  /\ UNCHANGED <<status, nextIdx, emitted, seen, ss, rate, epoch,
                 closeIdx, claimU, falseCk, noBounty, slashRem, paidP, paidB>>

\* Slash-window claims against the remaining deposit (MC4 (i)).
ClaimSweep(t) ==
  /\ t \in ss
  /\ status[t.m] = "disputed"
  /\ ~Swept(t)
  /\ slashRem[t.m] >= C
  /\ pool'     = pool - C
  /\ paidG'    = paidG + C
  /\ slashRem' = [slashRem EXCEPT ![t.m] = @ - C]
  /\ redeemed' = redeemed \cup {t}
  /\ UNCHANGED <<status, nextIdx, emitted, seen, ss, rate, epoch,
                 closeIdx, claimU, falseCk, noBounty, paidP, paidB>>

\* Slash-window expiry.  Ordinary slashes pay the remainder to the
\* evidence submitter as bounty; a settlement-detected slash has no
\* submitter and the remainder stays in the pool (rev-8 F8-m4).
ExpireSlashWindow(m) ==
  /\ status[m] = "disputed"
  /\ ~\E t \in ss : t.m = m /\ ~Swept(t) /\ slashRem[m] >= C
  /\ pool'     = IF noBounty[m] THEN pool ELSE pool - slashRem[m]
  /\ paidB'    = IF noBounty[m] THEN paidB ELSE paidB + slashRem[m]
  /\ slashRem' = [slashRem EXCEPT ![m] = 0]
  /\ status'   = [status EXCEPT ![m] = "slashed"]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch,
                 closeIdx, claimU, falseCk, noBounty, paidP, paidG>>

Next ==
  \/ \E m \in Members : Open(m) \/ HonestSpend(m)
                        \/ HonestCloseU(m) \/ HonestCloseSig(m)
                        \/ GwDispute(m) \/ ByzSelfDispute(m)
                        \/ DisputeFalseClaim(m)
                        \/ SettleCloseU(m) \/ SettlementSlash(m)
                        \/ ExpireCloseWindow(m) \/ ExpireSlashWindow(m)
  \/ \E m \in Byz, i \in IdxSp, p \in Payloads : ByzEmit(m, i, p)
  \/ \E m \in Byz, U \in SUBSET IdxSp : ByzCloseU(m, U)
  \/ \E m \in Byz, j \in 0..MaxIdx : ByzCloseSig(m, j)
  \/ \E t \in emitted : Redeem(t)
  \/ \E t \in ss : GwSweep(t) \/ ClaimSweep(t)
  \/ AdvanceEpoch

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* C2: safety invariants                                                   *)
(***************************************************************************)

TypeOK ==
  /\ status \in [Members -> {"init","open","closing","disputed","closed","slashed"}]
  /\ nextIdx \in [Members -> 0..MaxIdx]
  /\ emitted \subseteq TicketSp
  /\ seen \subseteq emitted
  /\ ss \subseteq seen
  /\ redeemed \subseteq ss
  /\ rate \in [Members -> 0..B]
  /\ epoch \in 1..MaxEpoch
  /\ pool \in Int
  /\ closeIdx \in [Members -> -1..MaxIdx]
  /\ claimU \in [Members -> SUBSET IdxSp]
  /\ falseCk \in [Members -> BOOLEAN]
  /\ noBounty \in [Members -> BOOLEAN]
  /\ slashRem \in [Members -> 0..D]
  /\ paidP \in [Members -> 0..D]
  /\ paidG \in Nat
  /\ paidB \in Nat

\* T1 shape at L=0, N=1: accepted value attributed to each member <= D.
NoOverspend ==
  \A m \in Members : C * Cardinality(AcceptedOf(m)) <= D

\* No two accepts with the same nf at this gateway.
NoDoubleAccept ==
  \A t1, t2 \in ss : NfEq(t1, t2) => t1 = t2

\* Exculpability shape (T3/T7 + MC20's false-claim self-conviction): a
\* slashed member really double-signed, or really emitted a spend at an
\* index it declared unused in its close.
FalseUClaim(m) ==
  \E t \in emitted : t.m = m /\ t.pay # "CLOSE" /\ t.idx \in claimU[m]

SlashOnlyOnRealDoubleSpend ==
  \A m \in Members :
    status[m] \in {"disputed", "slashed"} => ByzPair(m) \/ FalseUClaim(m)

HonestNeverSlashed ==
  \A m \in Members \ Byz : status[m] \notin {"disputed", "slashed"}

\* Rev-9 (MC16): "Pool solvency is what T1 plus the MC20 sweep bar
\* protect."  Payouts are deliberately unguarded: negative pool = the bug.
PoolSolvency == pool >= 0

RECURSIVE SumPaidP(_)
SumPaidP(S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN paidP[x] + SumPaidP(S \ {x})

\* Sanity: money is conserved (deposits in = pool + all payouts).
Conservation ==
  pool + paidG + paidB + SumPaidP(Members)
    = D * Cardinality({m \in Members : status[m] # "init"})

(***************************************************************************)
(* C3: liveness under fairness                                             *)
(***************************************************************************)

\* A single weak-fairness constraint on the disjunction of all
\* honest-infrastructure progress actions suffices: each such action
\* strictly decreases a finite settlement measure (unswept accepted
\* tickets + open windows + undisputed evidence) and never re-enables
\* itself, so no individual action can be starved by the others.
ProgressStep ==
  \/ \E m \in Members : SettleCloseU(m) \/ SettlementSlash(m)
                        \/ DisputeFalseClaim(m) \/ ExpireCloseWindow(m)
                        \/ ExpireSlashWindow(m) \/ GwDispute(m)
  \/ \E t \in ss : GwSweep(t) \/ ClaimSweep(t)

Fairness == WF_vars(ProgressStep)

LiveSpec == Init /\ [][Next]_vars /\ Fairness

\* An honest payer that closes eventually settles its floor:
\* C*|U| + (D - cap*C) = D - j*C under mc20; D - j*C under rev2.
HonestCloseSettles ==
  \A m \in Members \ Byz :
    (status[m] = "closing") ~>
      (status[m] = "closed" /\ paidP[m] = ClosePayout(m))

\* Every accepted ticket eventually settles to the gateway (sweep or
\* slash-window claim) -- or is permanently sweep-barred, which under mc20
\* is exactly the priced in-flight exposure of rev-9's honest-limits note
\* (an in-window acceptance at an index in U, unswept at settlement).
SweepSettles ==
  \A t \in [m : Members, idx : IdxSp, pay : Payloads] :
    (t \in ss) ~> (Swept(t) \/ SweepBarred(t))

=============================================================================
