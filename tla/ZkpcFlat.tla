---------------------------- MODULE ZkpcFlat ----------------------------
(***************************************************************************)
(* C1/C2/C3: flat-ticket instantiation A of Spec.md rev 2, single gateway  *)
(* (N = 1).  Idealized crypto: a "signal" is the record [m, idx, pay];     *)
(* nf ~ (m, idx); x ~ pay.  Knowledge soundness = only emitted signals     *)
(* exist and every redeemable ticket satisfies the solvency conjunct       *)
(* (idx+1)*C <= D.  Evidence validity = two genuinely emitted signals of   *)
(* the same member at one index with different messages (no forgery, T7).  *)
(*                                                                         *)
(* Modeling choices (logged in research_knowledge/tla-findings.md):        *)
(*  - Tickets carry no epoch stamp; Redeem's check 3 collapses to counting *)
(*    the rate budget against the redeem-time epoch.  Over-approximates    *)
(*    acceptance (safety-safe).  Epochs are modeled properly in ZkpcFleet. *)
(*  - Check 4 (gateway binding) is trivial at N = 1; exercised in Fleet.   *)
(*  - Honest spends use a fixed payload "p1" (message content irrelevant   *)
(*    at N = 1); Byzantine members choose from two payloads to be able to  *)
(*    double-sign.                                                         *)
(*  - tau and Delta are collapsed: window expiry is an explicit action,    *)
(*    and the honest gateway's monitoring duty (MC16) is modeled as the    *)
(*    guard "no gateway-known evidence pending" on close-window expiry     *)
(*    plus weak fairness on GwDispute.                                     *)
(*  - Repair flags (both FALSE = Spec.md rev 2 as written):                *)
(*    RepairRoot: payer-close rotates the root at submission, so           *)
(*      post-close spend proofs fail (Spec.md only rotates on slash, MC5). *)
(*    RepairUnspentNf: close-as-final-spend at index j additionally        *)
(*      publishes the nullifiers of indices >= j as "unspent"; Redeem and  *)
(*      sweeps reject them, and a pre-close acceptance at index >= j       *)
(*      convicts the closer during the window (DisputeCloseFraud).         *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS Members, Byz, C, D, B, MaxEpoch, RepairRoot, RepairUnspentNf

ASSUME Byz \subseteq Members

MaxIdx   == D \div C                    \* number of solvent spend indices
Payloads == {"p1", "p2"}
AllPays  == Payloads \cup {"CLOSE"}
TicketSp == [m : Members, idx : 0..MaxIdx, pay : AllPays]

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
  closeIdx, \* close index j per member, -1 if no close submitted
  slashRem, \* remaining deposit claimable during a slash window
  paidP,    \* per-member payer-close payout received
  paidG,    \* total settled to the gateway (sweeps + window claims)
  paidB     \* total slash bounty paid out

vars == <<status, nextIdx, emitted, seen, ss, redeemed, rate, epoch, pool,
          closeIdx, slashRem, paidP, paidG, paidB>>

NfEq(a, b)     == a.m = b.m /\ a.idx = b.idx
Conflict(a, b) == NfEq(a, b) /\ a.pay # b.pay
AcceptedOf(m)  == {t \in ss : t.m = m}
RedeemedOf(m)  == {t \in redeemed : t.m = m}
Swept(t)       == \E r \in redeemed : NfEq(r, t)

\* Evidence the gateway/ledger can actually hold: both signals observed.
GwEvidence(m)  == \E t1 \in seen, t2 \in seen : t1.m = m /\ Conflict(t1, t2)
\* A Byzantine member knows k and can materialize any pair it has emitted.
ByzPair(m)     == \E t1 \in emitted, t2 \in emitted : t1.m = m /\ Conflict(t1, t2)

\* Membership-tree check (Redeem check 2). Spec.md rotates the root only on
\* slash (MC5): a closed channel's cm literally stays in the tree.
InTree(m) == /\ status[m] \in {"open", "closing", "closed"}
             /\ (RepairRoot => status[m] = "open")

\* Under RepairUnspentNf, nullifiers at indices >= closeIdx are published
\* unspent at close: Redeem rejects them and the ledger refuses their sweep.
UnspentBlocked(t) ==
  RepairUnspentNf /\ closeIdx[t.m] >= 0 /\ t.idx >= closeIdx[t.m]

CloseFraudWitness(m) ==
  closeIdx[m] >= 0 /\ \E t \in ss : t.m = m /\ t.idx >= closeIdx[m]

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
                 closeIdx, slashRem, paidP, paidG, paidB>>

\* Honest Spend: emit at the current index, consume the index (MC2).
HonestSpend(m) ==
  /\ m \notin Byz
  /\ status[m] = "open"
  /\ (nextIdx[m] + 1) * C <= D
  /\ emitted' = emitted \cup {[m |-> m, idx |-> nextIdx[m], pay |-> "p1"]}
  /\ nextIdx' = [nextIdx EXCEPT ![m] = @ + 1]
  /\ UNCHANGED <<status, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, slashRem, paidP, paidG, paidB>>

\* A Byzantine payer emits any signal at any index with any payload
\* (conflicting signals at one index = double-sign). Emission needs only k,
\* not the tree; the solvency conjunct is enforced at Redeem (it is a proof
\* conjunct, and un-provable signals are still valid slash evidence).
ByzEmit(m, i, p) ==
  /\ m \in Byz
  /\ status[m] # "init"
  /\ LET t == [m |-> m, idx |-> i, pay |-> p] IN
       /\ t \notin emitted
       /\ emitted' = emitted \cup {t}
  /\ UNCHANGED <<status, nextIdx, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, slashRem, paidP, paidG, paidB>>

\* Redeem: delivery of an emitted ticket to the gateway is scheduled by the
\* adversary (any emitted ticket, any time, any number of times).  Checks in
\* Spec.md order: (1) proof [implicit: emitted + solvency conjunct],
\* (2) current root [InTree], (3) epoch [collapsed, see header], (4) gateway
\* binding [trivial at N=1], (5) rate budget, (6) nullifier logic.
\* Bit-identical retry lands in the duplicate branch (a no-op here).
Redeem(t) ==
  /\ t \in emitted
  /\ t.pay # "CLOSE"
  /\ InTree(t.m)
  /\ (t.idx + 1) * C <= D          \* solvency conjunct of R_spend
  /\ ~UnspentBlocked(t)
  /\ LET fresh == ~\E s \in ss : NfEq(s, t)
         acc   == fresh /\ rate[t.m] < B
     IN /\ (t \notin seen) \/ acc  \* prune pure stutter re-deliveries
        /\ seen' = seen \cup {t}
        /\ ss'   = IF acc THEN ss \cup {t} ELSE ss
        /\ rate' = IF acc THEN [rate EXCEPT ![t.m] = @ + 1] ELSE rate
  /\ UNCHANGED <<status, nextIdx, emitted, redeemed, epoch, pool,
                 closeIdx, slashRem, paidP, paidG, paidB>>

AdvanceEpoch ==
  /\ epoch < MaxEpoch
  /\ epoch' = epoch + 1
  /\ rate'  = [m \in Members |-> 0]
  /\ UNCHANGED <<status, nextIdx, emitted, seen, ss, redeemed, pool,
                 closeIdx, slashRem, paidP, paidG, paidB>>

\* Close-as-final-spend (MC1): a close signal at index j on message CLOSE,
\* public on the ledger (hence in `seen`).  Honest close uses the next
\* unused index; a Byzantine close picks any j (R_close has no solvency
\* conjunct and no way to enforce "next unused").
SubmitClose(m, j) ==
  /\ status[m] = "open"
  /\ LET t == [m |-> m, idx |-> j, pay |-> "CLOSE"] IN
       /\ emitted' = emitted \cup {t}
       /\ seen'    = seen \cup {t}
  /\ closeIdx' = [closeIdx EXCEPT ![m] = j]
  /\ status'   = [status EXCEPT ![m] = "closing"]
  /\ UNCHANGED <<nextIdx, ss, redeemed, rate, epoch, pool,
                 slashRem, paidP, paidG, paidB>>

HonestClose(m) == m \notin Byz /\ SubmitClose(m, nextIdx[m])
ByzClose(m, j) == m \in Byz /\ j \in 0..MaxIdx /\ SubmitClose(m, j)

\* Close-window expiry: automatic settlement D - j*C (Spec.md pins this as
\* automatic).  Guarded by the honest gateway's monitoring duty: it will
\* have submitted any evidence it holds before the window expires.
ExpireCloseWindow(m) ==
  /\ status[m] = "closing"
  /\ ~GwEvidence(m)
  /\ ~(RepairUnspentNf /\ CloseFraudWitness(m))
  /\ pool'   = pool - (D - closeIdx[m] * C)
  /\ paidP'  = [paidP EXCEPT ![m] = @ + (D - closeIdx[m] * C)]
  /\ status' = [status EXCEPT ![m] = "closed"]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch,
                 closeIdx, slashRem, paidG, paidB>>

\* Dispute with gateway-held evidence (permissionless; the gateway is the
\* party that actually holds pairs).  Freezes the channel, opens the MC4
\* gateway-priority window sized to the remaining deposit.
SlashEffects(m) ==
  /\ status'   = [status EXCEPT ![m] = "disputed"]
  /\ slashRem' = [slashRem EXCEPT ![m] = D - C * Cardinality(RedeemedOf(m))]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, paidP, paidG, paidB>>

GwDispute(m) ==
  /\ status[m] \in {"open", "closing"}
  /\ GwEvidence(m)
  /\ SlashEffects(m)

\* A Byzantine member can always self-slash (it knows k, so it can emit a
\* conflicting pair and submit it -- the T2 self-slash race surface).
ByzSelfDispute(m) ==
  /\ m \in Byz
  /\ status[m] \in {"open", "closing"}
  /\ ByzPair(m)
  /\ SlashEffects(m)

\* Repair only: an accepted ticket at an index the closer declared unspent
\* convicts the closer (the published-unspent nullifier collides with the
\* gateway's accepted tuple).
DisputeCloseFraud(m) ==
  /\ RepairUnspentNf
  /\ status[m] = "closing"
  /\ CloseFraudWitness(m)
  /\ SlashEffects(m)

\* Unilateral gateway sweep: C per fresh nf out of the commingled pool.
GwSweep(t) ==
  /\ t \in ss
  /\ status[t.m] \in {"open", "closing", "closed"}
  /\ ~Swept(t)
  /\ ~UnspentBlocked(t)
  /\ pool'     = pool - C
  /\ paidG'    = paidG + C
  /\ redeemed' = redeemed \cup {t}
  /\ UNCHANGED <<status, nextIdx, emitted, seen, ss, rate, epoch,
                 closeIdx, slashRem, paidP, paidB>>

\* During a slash window: gateway claims sweeps of the slashed member's
\* outstanding redeemed tuples against the remaining deposit (MC4 (i)).
\* Documented-conflict claims (MC4 (ii)) cannot arise at N = 1 (RedeemedNF
\* entries come from this gateway's own accepted tuples); they are modeled
\* in ZkpcFleet.
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
                 closeIdx, paidP, paidB>>

\* Slash-window expiry: remainder of the deposit to the evidence submitter
\* as bounty.  Guard = the monitoring duty: outstanding claims go first.
ExpireSlashWindow(m) ==
  /\ status[m] = "disputed"
  /\ ~\E t \in ss : t.m = m /\ ~Swept(t) /\ slashRem[m] >= C
  /\ pool'     = pool - slashRem[m]
  /\ paidB'    = paidB + slashRem[m]
  /\ slashRem' = [slashRem EXCEPT ![m] = 0]
  /\ status'   = [status EXCEPT ![m] = "slashed"]
  /\ UNCHANGED <<nextIdx, emitted, seen, ss, redeemed, rate, epoch, pool,
                 closeIdx, paidP, paidG>>

Next ==
  \/ \E m \in Members : Open(m) \/ HonestSpend(m) \/ HonestClose(m)
                        \/ GwDispute(m) \/ ByzSelfDispute(m)
                        \/ DisputeCloseFraud(m)
                        \/ ExpireCloseWindow(m) \/ ExpireSlashWindow(m)
  \/ \E m \in Byz, i \in 0..(MaxIdx - 1), p \in Payloads : ByzEmit(m, i, p)
  \/ \E m \in Byz, j \in 0..MaxIdx : ByzClose(m, j)
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

\* Exculpability shape (T3/T7): a slashed member really double-signed
\* (or, under RepairUnspentNf, really committed close fraud).
SlashOnlyOnRealDoubleSpend ==
  \A m \in Members :
    status[m] \in {"disputed", "slashed"} =>
      ByzPair(m) \/ (RepairUnspentNf /\ CloseFraudWitness(m))

HonestNeverSlashed ==
  \A m \in Members \ Byz : status[m] \notin {"disputed", "slashed"}

\* The pool covers everything paid out of it (MC16: "Pool solvency is
\* exactly what T1 protects").  Payouts are deliberately unguarded: a
\* negative pool is the counterexample.
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

Fairness ==
  /\ \A m \in Members : /\ WF_vars(ExpireCloseWindow(m))
                        /\ WF_vars(ExpireSlashWindow(m))
                        /\ WF_vars(GwDispute(m))
                        /\ WF_vars(DisputeCloseFraud(m))
  /\ \A t \in TicketSp : /\ WF_vars(GwSweep(t))
                         /\ WF_vars(ClaimSweep(t))

LiveSpec == Init /\ [][Next]_vars /\ Fairness

\* An honest payer that closes eventually settles D - j*C.
HonestCloseSettles ==
  \A m \in Members \ Byz :
    (status[m] = "closing") ~>
      (status[m] = "closed" /\ paidP[m] = D - closeIdx[m] * C)

\* Every accepted ticket is eventually settled to the gateway (sweep or
\* slash-window claim).
SweepSettles ==
  \A t \in TicketSp : (t \in ss) ~> Swept(t)

=============================================================================
