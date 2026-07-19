------------------------------ MODULE ZkpcChainV2 ------------------------------
(***************************************************************************)
(* Spec-v2 nullifier-chain channel: the clocked settlement machine of      *)
(* `lean/Zkpc/Chain/V2/State.lean`, model-checked (ROADMAP obligation 9).  *)
(*                                                                         *)
(* Chain positions replace nullifier values: message j reveals position j; *)
(* a close exhibits the positions of Spec-v2 section 4's exhibit sets.     *)
(* Collision-freedom (injective `nul`) is exact here, so TLC checks the    *)
(* combinatorics of the challenge relation, not the hash model.            *)
(*                                                                         *)
(* Switch constants reproduce design decisions as counterexamples:        *)
(*  - VIGILANT: Bob challenges rather than sleeps (Settle requires no      *)
(*    evidence). With VIGILANT = FALSE the BobFloor invariant must fail    *)
(*    (a sleeping Bob settles a stale close) — reproducing why vigilance   *)
(*    is an explicit environment assumption, not a theorem.               *)
(*  - PARENT_REVEAL: unsigned closes exhibit their parent-reveal (A2.iii  *)
(*    as refined in Spec-v2 [R1]). With FALSE, the rollback fork settles   *)
(*    under a vigilant Bob and BobFloor must fail — reproducing gate      *)
(*    finding Q2(iii)/F-R1 rationale.                                     *)
(*  - CAP_CHECK: the in-circuit `bal <= D`. With FALSE, NoOverspend must  *)
(*    fail — reproducing PROTOCOL.md's own broken mode.                   *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS D, MAXLEN, TABS, TREQ, TAU, TMAX,
          VIGILANT, PARENT_REVEAL, CAP_CHECK

ASSUME D \in Nat /\ MAXLEN \in Nat /\ MAXLEN >= 1
ASSUME TABS \in Nat /\ TREQ \in Nat /\ TAU \in Nat /\ TMAX \in Nat
ASSUME VIGILANT \in BOOLEAN /\ PARENT_REVEAL \in BOOLEAN /\ CAP_CHECK \in BOOLEAN

NoReq == -1
NoClose == [ mode |-> "none", i |-> 0, d |-> 0, t0 |-> 0 ]

VARIABLES now, len, msgs, bals, ghostD, closeReqAt, closing,
          settled, forfeited, alicePay, bobPay

vars == << now, len, msgs, bals, ghostD, closeReqAt, closing,
           settled, forfeited, alicePay, bobPay >>

Deltas == 0..D
Positions == 0..MAXLEN

TypeOK ==
  /\ now \in 0..TMAX
  /\ len \in Positions /\ msgs \in 0..(MAXLEN+1)
  /\ bals \in [Positions -> 0..(3*D)]
  /\ ghostD \in Deltas
  /\ closeReqAt \in {NoReq} \cup 0..TMAX
  /\ closing \in [ mode : {"none","genesis","signed","ghost","fresh"},
                   i : Positions, d : Deltas, t0 : 0..TMAX ]
  /\ settled \in BOOLEAN /\ forfeited \in BOOLEAN
  /\ alicePay \in (0 - 3*D)..(3*D) /\ bobPay \in (0 - 3*D)..(3*D)

Earned == bals[len]

(* Spec-v2 section 4: proof-validity of a close object. *)
ValidClose(m, i, d) ==
  CASE m = "genesis" -> TRUE
    [] m = "signed"  -> i >= 1 /\ i <= len
    [] m = "ghost"   -> msgs = len + 1
    [] m = "fresh"   -> i <= len /\ (~CAP_CHECK \/ bals[i] + d <= D)
    [] OTHER         -> FALSE

(* The balance a close pays Bob (Spec-v2 section 6). *)
BalOf(m, i, d) ==
  CASE m = "genesis" -> 0
    [] m = "signed"  -> bals[i]
    [] m = "ghost"   -> Earned + ghostD
    [] m = "fresh"   -> bals[i] + d
    [] OTHER         -> 0

(* Exhibit sets as chain positions (Spec-v2 section 4, [R1] mode-dependent). *)
Exhibits(m, i, k) ==
  CASE m = "genesis" -> k = 1
    [] m = "signed"  -> k = i + 1
    [] m = "ghost"   -> \/ (PARENT_REVEAL /\ k = len + 1)
                        \/ k = len + 2
    [] m = "fresh"   -> \/ (PARENT_REVEAL /\ k = i + 1)
                        \/ k = i + 2
    [] OTHER         -> FALSE

(* Same-state exception (Spec-v2 section 5): message j IS the closed state. *)
SameState(j, m) ==
  \/ (m = "signed" /\ j = closing.i)
  \/ (m = "ghost"  /\ j = len + 1)

(* Challenge evidence: a held message (1..msgs), not the closed state,      *)
(* revealing an exhibited position.                                         *)
EvidenceExists ==
  /\ closing.mode /= "none"
  /\ \E j \in 1..msgs :
       /\ ~SameState(j, closing.mode)
       /\ Exhibits(closing.mode, closing.i, j)

(* The Lean safe-close characterization (`safe_iff`), transcribed.          *)
SafeClose ==
  \/ (closing.mode = "genesis" /\ msgs = 0)
  \/ (closing.mode = "signed"  /\ closing.i = len /\ msgs = len)
  \/ (closing.mode = "ghost")
  \/ (closing.mode = "fresh"   /\ closing.i = len /\ msgs = len)

Init ==
  /\ now = 0 /\ len = 0 /\ msgs = 0
  /\ bals = [ p \in Positions |-> 0 ]
  /\ ghostD = 0 /\ closeReqAt = NoReq /\ closing = NoClose
  /\ settled = FALSE /\ forfeited = FALSE /\ alicePay = 0 /\ bobPay = 0

(* Vigilance as an eager-challenge scheduling assumption: while a vigilant  *)
(* Bob holds an unchallenged valid complaint inside the window, the clock   *)
(* does not outrun him (Challenge is the only enabled action there). With   *)
(* VIGILANT = FALSE time passes freely and stale closes can settle.         *)
Tick ==
  /\ ~settled /\ now < TMAX
  /\ ~(VIGILANT /\ closing.mode /= "none" /\ now < closing.t0 + TAU
       /\ EvidenceExists)
  /\ now' = now + 1
  /\ UNCHANGED << len, msgs, bals, ghostD, closeReqAt, closing,
                  settled, forfeited, alicePay, bobPay >>

Pay(d) ==
  /\ ~settled /\ closing.mode = "none" /\ msgs = len /\ len < MAXLEN
  /\ (~CAP_CHECK \/ Earned + d <= D)
  /\ len' = len + 1 /\ msgs' = msgs + 1
  /\ bals' = [ bals EXCEPT ![len + 1] = Earned + d ]
  /\ UNCHANGED << now, ghostD, closeReqAt, closing,
                  settled, forfeited, alicePay, bobPay >>

GhostSend(d) ==
  /\ ~settled /\ closing.mode = "none" /\ msgs = len /\ len < MAXLEN
  /\ (~CAP_CHECK \/ Earned + d <= D)
  /\ msgs' = msgs + 1 /\ ghostD' = d
  /\ UNCHANGED << now, len, bals, closeReqAt, closing,
                  settled, forfeited, alicePay, bobPay >>

SignGhost ==
  /\ ~settled /\ closing.mode = "none" /\ msgs = len + 1
  /\ len' = len + 1
  /\ bals' = [ bals EXCEPT ![len + 1] = Earned + ghostD ]
  /\ UNCHANGED << now, msgs, ghostD, closeReqAt, closing,
                  settled, forfeited, alicePay, bobPay >>

RequestClose ==
  /\ ~settled /\ closing.mode = "none" /\ closeReqAt = NoReq
  /\ closeReqAt' = now
  /\ UNCHANGED << now, len, msgs, bals, ghostD, closing,
                  settled, forfeited, alicePay, bobPay >>

(* `now + TAU <= TMAX` is a finite-horizon boundary (a close opened later  *)
(* could not resolve inside the model's clock), not a protocol rule.       *)
CloseOn(m, i, d) ==
  /\ ~settled /\ closing.mode = "none"
  /\ now + TAU <= TMAX
  /\ ValidClose(m, i, d)
  /\ closing' = [ mode |-> m, i |-> i, d |-> d, t0 |-> now ]
  /\ UNCHANGED << now, len, msgs, bals, ghostD, closeReqAt,
                  settled, forfeited, alicePay, bobPay >>

Challenge ==
  /\ ~settled /\ closing.mode /= "none"
  /\ now < closing.t0 + TAU
  /\ EvidenceExists
  /\ settled' = TRUE /\ forfeited' = TRUE
  /\ alicePay' = 0 /\ bobPay' = D
  /\ UNCHANGED << now, len, msgs, bals, ghostD, closeReqAt, closing >>

Settle ==
  /\ ~settled /\ closing.mode /= "none"
  /\ now >= closing.t0 + TAU
  /\ (VIGILANT => ~EvidenceExists)
  /\ settled' = TRUE /\ forfeited' = FALSE
  /\ bobPay' = BalOf(closing.mode, closing.i, closing.d)
  /\ alicePay' = D - BalOf(closing.mode, closing.i, closing.d)
  /\ UNCHANGED << now, len, msgs, bals, ghostD, closeReqAt, closing, forfeited >>

TimeoutForfeit ==
  /\ ~settled /\ closing.mode = "none"
  /\ \/ now >= TABS
     \/ (closeReqAt /= NoReq /\ now >= closeReqAt + TREQ)
  /\ settled' = TRUE /\ forfeited' = TRUE
  /\ alicePay' = 0 /\ bobPay' = D
  /\ UNCHANGED << now, len, msgs, bals, ghostD, closeReqAt, closing >>

(* Settlement is terminal; self-loop so TLC's deadlock check passes. *)
Terminated ==
  /\ settled
  /\ UNCHANGED vars

Next ==
  \/ Terminated
  \/ Tick
  \/ \E d \in Deltas : Pay(d) \/ GhostSend(d)
  \/ SignGhost
  \/ RequestClose
  \/ \E m \in {"genesis","signed","ghost","fresh"}, i \in Positions, d \in Deltas :
       CloseOn(m, i, d)
  \/ Challenge
  \/ Settle
  \/ TimeoutForfeit

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(* Invariants *)

(* Spec-v2 section 6 / Lean `conservation`. *)
Conservation == settled => alicePay + bobPay = D

(* Lean `no_overspend` (meaningful under CAP_CHECK). *)
NoOverspend == /\ bobPay <= D
               /\ \A p \in Positions : bals[p] <= D

(* Lean `challenge_enabled_iff_unsafe`: with a close pending in-window,     *)
(* evidence exists exactly when the close is outside the safe set.          *)
EvidenceIffUnsafe ==
  (~settled /\ closing.mode /= "none" /\ now < closing.t0 + TAU)
    => (EvidenceExists <=> ~SafeClose)

(* Lean `cooperative_safe_floor` + vigilance: no unforfeited settlement     *)
(* underpays Bob. Expected to FAIL when VIGILANT = FALSE (sleeping Bob) or  *)
(* PARENT_REVEAL = FALSE (rollback fork) — those runs are the recorded      *)
(* counterexamples.                                                         *)
BobFloor == (settled /\ ~forfeited) => bobPay >= Earned

(* Forfeits always pay Bob everything. *)
ForfeitAll == (settled /\ forfeited) => (bobPay = D /\ alicePay = 0)

=============================================================================
