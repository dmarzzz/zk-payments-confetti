# zk payment channels: five questions before the spec freeze

Your design doc is recorded verbatim as `PROTOCOL.md` in
github.com/dmarzzz/zk-payments-confetti and is now the target of the Lean
formalization. The method there is that definitions freeze before any
proving starts: the doc goes through adversarial review rounds, every
blocking finding needs a concrete counterexample, and proofs are only
written against the frozen spec. Round 0 of that review surfaced five
points where the document underdetermines the object. Four of them need a
sentence; one (Q2) needs a decision. Each comes with a proposed default,
so "yes" is a complete answer. Whatever you don't care about, we'll take
the default and record it as our choice, not yours.

The five are tracked publicly as issues #10 through #14 on the repo,
without attribution.

## Q1. What exactly does Bob sign?

The doc says a payment proves it extends "a state Bob signed," but never
specifies the signed payload. If the signature does not bind the channel
id, an honestly signed state from channel 1 can be spliced in as the
parent of a payment in channel 2, and the no-overspend argument breaks
across channels (Alice opens two channels with Bob, gets one state
signed, extends it in both).

**Proposed default:** Bob signs
`H(channel_id, commit(balance), commit(N_next))`, i.e. the signature
binds the channel and the exact commitments of the state being accepted.
Recipient identity is already implied by channel_id (the recipient is
named at open).

## Q2. Is closing on an unsigned-but-proof-valid state legal? (the withheld-countersignature wedge)

This is the one real design decision. Walk the message order:

1. Alice sends the message creating state i+1. That message *reveals*
   `N_{i+1}` (the nullifier state i committed to) before Bob has signed
   anything.
2. Bob keeps the message and never countersigns.
3. Alice's latest signed state is i. Closing on state i opens its
   committed next-nullifier, which is `N_{i+1}`.
4. The challenge rule as written is "Bob challenges if he holds a message
   that revealed N." He holds one. Alice forfeits everything.

As written, every state Alice can close on has been "extended" by her own
reveal the moment she attempts the next payment, whether or not Bob ever
accepted it. A recipient who ghosts one countersignature turns the
challenge rule into a griefing weapon against an honest payer.

The natural repair may already be implicit in your design: nothing in the
doc says closing *requires* Bob's signature on the closed state. If Alice
may close on state i+1 by presenting the same flat ZK proof she sent Bob
(it proves i+1 extends a signed state or genesis, with balance ≤ D), the
wedge dissolves: she closes on i+1, opens `N_{i+2}`, no message ever
revealed `N_{i+2}`, no challenge is possible. Her worst case is paying
one δ for a request Bob ghosted, and Bob gains nothing by withholding.

**Proposed default:** closing on an unsigned state is legal; the close
verifies the same payment proof plus the commitment opening. The cost is
that the close-time verifier gets bigger (it verifies a payment proof,
not just an opening), and the safety theorems have to walk the case where
the closed state was never seen by Bob.

If instead you intend closes to be signed-states-only, we need the rule
that protects the honest payer in step 4, because "Bob holds a revealing
message" and "Bob accepted the successor" are different events and the
current rule cannot tell them apart.

## Q3. How long is Bob's challenge window?

The 90-day and 7-day timers are specified; the post-close challenge
window is not. It needs a stated duration τ and the constraint that τ
exceeds the network/censorship delay assumed of Bob's monitoring.

**Proposed default:** 7 days, matching the close-on-request timer, with
the explicit assumption that Bob (or a watchtower) observes the chain at
least once per window.

## Q4. What does Close verify about the balance commitment?

Balances live in hiding commitments, but "the contract pays out per the
balance" and "the final split is revealed onchain at close." The step
between those is unstated. Presumably: the close reveals the balance and
the commitment randomness, and the contract checks the opening against
the commitment carried by the closed state (or, under the shielded-pool
extension, verifies a proof about the committed value instead of an
opening). Whichever it is, the close relation has to be written to be
transcribable into Lean.

**Proposed default:** base protocol closes open the commitment in the
clear (the split is public in the base protocol anyway); the shielded
variant replaces the opening with a proof. Genesis-close (full refund)
opens the genesis commitment the same way, keeping your uniform rule.

## Q5. Is forfeit-everything the intended penalty in the honest-limit edges?

The only penalty is forfeiture of the entire deposit. Combined with Q2,
an honest payer could reach a challengeable position through no fault of
her own; and even with Q2 repaired, edge cases remain (crash after
sending a message, close raced against an in-flight payment). Options:
bound the honest loss structurally (the Q2 default does most of this), or
keep forfeit-all and scope the residual edges out explicitly as
documented honest limits. What we don't want is to discover the policy
mid-proof.

**Proposed default:** keep forfeit-all (it is what makes the collision
rule simple), adopt the Q2 default so honest loss is bounded by one δ,
and document the crash/race edges as honest limits with their exact cost.

---

Once these five are settled the spec freezes and the proof campaign
starts. The safety core and the collision mechanism already have seed
formalizations; per-request anonymity gets the full treatment that was
built for the previous design (adaptive adversary, session challenges,
and a calibration battery that must catch non-hiding balances, which is
your own δ-matching argument stated as a theorem).
