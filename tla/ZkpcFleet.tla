---------------------------- MODULE ZkpcFleet ----------------------------
(***************************************************************************)
(* C4: fleet extension (instantiation A), N gateways, one Byzantine member *)
(* (secret k, deposit D), explicit discrete time.  Checks the T6 shape:    *)
(*                                                                         *)
(*   ExcessBound:  C * (total accepts attributed to k)                     *)
(*                   <= floor(D/C)*C + N*B*(ceil(L/TE)+1)*C                *)
(*   ConflictSlashed (T6 clause ii): a cross-accepted conflicting pair     *)
(*                   implies a fleet-wide slash within L of the second     *)
(*                   acceptance.                                           *)
(*                                                                         *)
(* Escrow/close/pool are exercised in ZkpcFlat; this model isolates the    *)
(* divergence-and-reconciliation mechanics that only exist at N >= 2.      *)
(*                                                                         *)
(* Idealized signal algebra: a tuple is [idx, x] where x is the message    *)
(* digest.  With GwBind = TRUE (MC14) the message is gateway-bound, so     *)
(* x = the serving gateway's identity; with GwBind = FALSE (rev-1 broken   *)
(* protocol) x = "p" everywhere, so cross-gateway replay is bit-identical  *)
(* and never conflicts.  MergeEv = FALSE disables MC17 (merge-time         *)
(* evidence), reproducing the rev-1 staggered-adversary counterexample.    *)
(*                                                                         *)
(* Honest-fleet guarantees (the end-to-end L of MC11) are encoded as       *)
(* guards on Tick: a tuple accepted at t is merged everywhere by t+L, and  *)
(* once evidence is known, the slash is effective by (pair time)+L.       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS GW,        \* gateway set
          C, D, B,   \* price, deposit, per-epoch per-gateway budget b
          TE,        \* epoch length in ticks
          L,         \* end-to-end reconciliation lag in ticks
          MaxTime,
          GwBind,    \* MC14 on/off
          MergeEv    \* MC17 on/off

MaxIdx == D \div C
XVals  == IF GwBind THEN GW ELSE {"p"}
TupleSp == [idx : 0..(MaxIdx - 1), x : XVals]

VARIABLES
  now,
  acc,      \* [GW -> SUBSET TupleSp]: tuples this gateway itself ACCEPTED
  mrg,      \* [GW -> SUBSET TupleSp]: tuples received via gossip
  inflight, \* [GW -> SUBSET [tp: TupleSp, dl: Nat]]: pending merges w/ deadline
  rate,     \* [GW -> 0..B]: current-epoch accepts for k's epoch pseudonym
  slashed,  \* root rotated fleet-wide
  evKnown,  \* some honest party holds valid conflicting-signal evidence
  pairT     \* time the first conflicting pair became cross-ACCEPTED; -1 if none

vars == <<now, acc, mrg, inflight, rate, slashed, evKnown, pairT>>

XVal(g)    == IF GwBind THEN g ELSE "p"
LocalSS(g) == acc[g] \cup mrg[g]

Init == /\ now      = 0
        /\ acc      = [g \in GW |-> {}]
        /\ mrg      = [g \in GW |-> {}]
        /\ inflight = [g \in GW |-> {}]
        /\ rate     = [g \in GW |-> 0]
        /\ slashed  = FALSE
        /\ evKnown  = FALSE
        /\ pairT    = 0 - 1

\* Redeem at gateway g, index i, accept branch.  Checks: root current
\* (~slashed, MC5 fleet-wide eviction), gateway binding (x is forced to
\* XVal(g) -- a ticket naming another gateway is rejected, MC14), budget
\* strictly under b (check 5, accepts only), fresh nf locally (check 6).
Accept(g, i) ==
  /\ ~slashed
  /\ rate[g] < B
  /\ LET tp == [idx |-> i, x |-> XVal(g)] IN
       /\ ~\E s \in LocalSS(g) : s.idx = i
       /\ acc' = [acc EXCEPT ![g] = @ \cup {tp}]
       /\ inflight' = [g2 \in GW |->
                        IF g2 = g THEN inflight[g2]
                        ELSE inflight[g2] \cup {[tp |-> tp, dl |-> now + L]}]
       /\ pairT' = IF pairT < 0 /\ \E g2 \in GW \ {g} :
                        \E s \in acc[g2] : s.idx = i /\ s.x # tp.x
                   THEN now ELSE pairT
  /\ rate' = [rate EXCEPT ![g] = @ + 1]
  /\ UNCHANGED <<now, mrg, slashed, evKnown>>

\* Redeem check-6 evidence branch: presented signal conflicts with a local
\* spent-set entry (necessarily one that arrived by gossip, since x = the
\* local gateway id for locally accepted tuples).  Spec order: the budget
\* check (5) precedes nullifier logic (6), so this branch needs rate < B.
RedeemConflict(g, i) ==
  /\ ~slashed
  /\ ~evKnown
  /\ rate[g] < B
  /\ \E s \in LocalSS(g) : s.idx = i /\ s.x # XVal(g)
  /\ evKnown' = TRUE
  /\ UNCHANGED <<now, acc, mrg, inflight, rate, slashed, pairT>>

\* Gossip merge.  MC17: merging a tuple that conflicts with a local entry
\* emits Dispute evidence; with MergeEv = FALSE the merge is silent (rev-1).
Merge(g) ==
  \E e \in inflight[g] :
    /\ inflight' = [inflight EXCEPT ![g] = @ \ {e}]
    /\ mrg'      = [mrg EXCEPT ![g] = @ \cup {e.tp}]
    /\ evKnown'  = \/ evKnown
                   \/ (MergeEv /\ \E s \in LocalSS(g) :
                                     s.idx = e.tp.idx /\ s.x # e.tp.x)
    /\ UNCHANGED <<now, acc, rate, slashed, pairT>>

\* Dispute lands: root rotates fleet-wide, spend proofs fail everywhere.
Slash ==
  /\ evKnown
  /\ ~slashed
  /\ slashed' = TRUE
  /\ UNCHANGED <<now, acc, mrg, inflight, rate, evKnown, pairT>>

\* Time.  Guards encode the honest-infrastructure guarantees of MC11:
\* merges land by their deadline, and once evidence exists the slash is
\* effective by pairT + L.  Epoch rollover resets the budget counters.
Tick ==
  /\ now < MaxTime
  /\ \A g \in GW : \A e \in inflight[g] : e.dl > now
  /\ (evKnown /\ ~slashed) => ~(pairT >= 0 /\ pairT + L <= now)
  /\ now'  = now + 1
  /\ rate' = IF (now + 1) % TE = 0 THEN [g \in GW |-> 0] ELSE rate
  /\ UNCHANGED <<acc, mrg, inflight, slashed, evKnown, pairT>>

Next ==
  \/ Tick
  \/ Slash
  \/ \E g \in GW : Merge(g)
  \/ \E g \in GW, i \in 0..(MaxIdx - 1) : Accept(g, i) \/ RedeemConflict(g, i)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOK ==
  /\ now \in 0..MaxTime
  /\ acc \in [GW -> SUBSET TupleSp]
  /\ mrg \in [GW -> SUBSET TupleSp]
  /\ \A g \in GW : inflight[g] \subseteq [tp : TupleSp, dl : 0..(MaxTime + L)]
  /\ rate \in [GW -> 0..B]
  /\ slashed \in BOOLEAN
  /\ evKnown \in BOOLEAN
  /\ pairT \in (0 - 1)..MaxTime

RECURSIVE SumAcc(_)
SumAcc(S) == IF S = {} THEN 0
             ELSE LET g == CHOOSE g2 \in S : TRUE
                  IN Cardinality(acc[g]) + SumAcc(S \ {g})

NGw     == Cardinality(GW)
CeilLTE == (L + TE - 1) \div TE

\* T6 clause (i): total accepted value <= floor(D/C)*C + N*B*(ceil(L/TE)+1)*C
ExcessBound ==
  C * SumAcc(GW) <= MaxIdx * C + NGw * B * (CeilLTE + 1) * C

\* T6 clause (ii): a cross-accepted conflicting pair is slashed within L
\* of the second acceptance.
ConflictSlashed ==
  (pairT >= 0 /\ now > pairT + L) => slashed

=============================================================================
