# zk payment channels: five questions before the spec freeze

Your design doc is recorded verbatim as `PROTOCOL.md` in
github.com/dmarzzz/zk-payments-confetti and is now the target of the Lean
formalization. The method there is that definitions freeze before any
proving starts: the doc goes through adversarial review rounds, every
blocking finding needs a concrete counterexample, and proofs are only
written against the frozen spec. Round 0 of that review surfaced five
points where the document underdetermines the object — this packet itself
went through a red-team round before being sent, which killed one
question, corrected two attacks, and added the last one. Each question
comes with a proposed default, so "yes to defaults" is a complete answer.
Whatever you don't care about, we'll take the default and record it as
our choice, not yours.

## Q1. What does Bob sign, and how does a payment prove it belongs to its channel?

The doc says a payment extends "a state Bob signed," but never specifies
the signed payload, and never says how the flat proof anchors to its own
channel's genesis and deposit. Nothing binds a signed state, or a payment
proof, to one channel.

Concrete break of payment-channel safety: Alice opens channel 1 (small
D₁) and channel 2 (large D₂), both naming Bob. She makes two tiny
payments in channel 1 (Bob signs state 2, balance 2ε, committing N₃) and
buys ~D₂ of service in channel 2. She then closes channel 2 by presenting
channel-1-state-2: Bob's signature verifies (nothing scopes it to a
channel), and Alice — who knows channel 1's chain secret c — opens N₃. No
channel-2 message ever revealed N₃, so under "Bob challenges if he holds
a message that revealed N" he cannot challenge; the collision rule is
per-chain and never fires on an imported foreign chain. The contract pays
Bob 2ε out of D₂. (Note the attack is at *close*, not at payment: trying
to extend one signed state in two channels fails, because the parent's
committed next-nullifier is a single value and Bob's dedup is necessarily
global across his inbox — he can't attribute messages to channels, which
is the point of the design.)

**Proposed default:** the signed payload and the payment proof both bind
the channel, but the binding is hidden from Bob to preserve per-request
anonymity: Bob counter-signs `H(Com(channel_id; r), Com(balance),
Com(N_next))`; the payment proof takes the channel's genesis reference
and D as private witnesses and opens `Com(channel_id; r)` to the correct
channel privately; the close-time verifier, which knows its own
channel_id, checks the same opening. Binding channel_id *in the clear*
would let Bob link every payment to the public channel record and destroy
per-request anonymity, so it has to be the hidden form. This makes Bob a
blind signer of an Alice-supplied digest — plausibly safe under the ≤ D
check plus dedup, but that becomes a theorem to state, so flagging it.

## Q2. Is closing on an unsigned-but-proof-valid state legal? (the withheld-countersignature wedge)

Walk the message order:

1. Alice sends the message creating state i+1. That message *reveals*
   `N_{i+1}` (the nullifier state i committed to) before Bob has signed
   anything.
2. Bob keeps the message and never countersigns.
3. Alice's latest signed state is i. Closing on state i opens its
   committed next-nullifier, which is `N_{i+1}`.
4. The challenge rule as written is "Bob challenges if he holds a message
   that revealed N." He holds one. Alice forfeits everything.

And the genesis case is no escape: if Bob ghosts message 1, a
genesis-close opens `N₁`, which message 1 revealed — collision again. So
under the signed-states-only reading, a recipient who withholds one
countersignature leaves an honest payer with *no* safe close at all,
which contradicts the stated liveness goal ("If Bob never signed
anything, Alice can unilaterally recover her full deposit"). This is
profitable theft, not just griefing.

The natural repair is to let Alice close on the unsigned state itself —
but the naive form of that breaks safety in two ways, so the default has
to be a bundle:

**Proposed default:** closing on an unsigned-but-proof-valid state is
legal, with all three of:

- (i) the close verifies the payment proof plus the commitment opening;
- (ii) **δ ≥ 0 is enforced inside the payment circuit.** The doc states
  only `parent_balance + δ = new_balance ≤ D`, never δ ≥ 0. With unsigned
  closes Bob never sees δ, so a δ = −15 self-extension is an
  unchallengeable full refund that pays Bob nothing.
- (iii) **the challenge fires on any nullifier the close exhibits** — the
  opened next-nullifier *and* the parent nullifier revealed inside the
  close proof — matched against any held message *other than the closed
  state itself*. Without this, Alice forks an old Bob-signed state with
  δ = 0 and a fresh next-nullifier only she knows, closes on the fork,
  and no message ever revealed the opened nullifier → no challenge. (Bob's
  countersignature + dedup was the anti-rollback mechanism; the naive
  unsigned-close removes it, so the challenge relation has to pick up the
  slack.) The same-state exception is required, or an honest tip-close on
  unsigned state i+1 re-wedges on its own `N_{i+1}`.

One operational note we'd record alongside (not a protocol change): Alice
must persist a payment message before sending it — a crash-then-stale
close forfeits, and by design the contract cannot distinguish that from
cheating.

## Q3. How long is Bob's challenge window, and does payout wait for it?

The 90-day and 7-day timers are specified; the post-close challenge
window is not. And the close paragraph as written orders "The contract
pays out per the balance" *before* "Bob challenges…", so the text
currently has no window at all rather than an unnamed one — the fix is a
duration τ plus a sequencing rule.

**Proposed default:** payout is deferred until τ = 7 days elapse
unchallenged (matching the close-on-request timer), under the assumption
that Bob observes the chain at least once per window.

## Q4. Is the balance commitment joint with the next-nullifier, and what authenticates it at close?

Parts of this are already determined by the doc, and we read them as
settled: the base close reveals the split in the clear, the shielded
variant hides it inside pool-note output commitments, and a
contract-verifiable reveal of a hidden value is by definition an opening.
What the transcription still needs:

- (a) does a state carry one joint commitment `Com(balance, N_next)` or
  two separate commitments? (Under the joint reading, "opening the
  committed-next-nullifier" at close already opens the balance and the
  question nearly answers itself.)
- (b) the commitment lives in an offchain message — what exactly does
  Alice submit at close, and what authenticates that commitment as
  belonging to the closed state (Bob's signature, or the Q2 payment
  proof)? This authenticity link is also where the Q1 splice enters.

**Proposed default:** each state commits jointly to
`Com(balance, N_next)`; base-protocol closes open it in the clear; the
shielded variant replaces the opening with a proof. Genesis-close opens
only `N₁` — genesis balance is 0 by definition, so there is no genesis
balance commitment to open.

## Q5. What makes a "message that revealed N" unforgeable?

The challenge relation is "Bob holds a message that revealed N," but the
doc never says what makes a message *genuine*. If the challenge accepts
any proof-carrying message, then after any honest close — which publishes
the opening of the closed state's next-nullifier — Bob can forge a valid
"message that revealed N": parent = the closed state, δ = 0, his own
signature (self-certifying by the doc's own argument), fresh commitments,
a valid flat proof. Then he challenges and takes everything on every
honest close, inverting the safety goal.

The likely intended defense is that the payment circuit enforces
`N_{i+1} = H(N_i, c)` in-statement, against a chain secret c bound at
open through the genesis `N₁` commitment — so a forger without c cannot
author a successor to the closed state. But the doc defines the chain
equation in prose only; the proof statement as written never includes it,
and c is never said to be bound at open. The challenge relation cannot be
transcribed into Lean until this is pinned.

**Proposed default:** the payment circuit enforces `N_{i+1} = H(N_i, c)`
with c bound at open through the genesis commitment; a message is a valid
challenge witness only if its proof verifies under that constraint.

---

Once these five are settled the spec freezes and the proof campaign
starts. The safety core and the collision mechanism already have seed
formalizations; per-request anonymity gets the full treatment that was
built for the previous design (adaptive adversary, session challenges,
and a calibration battery that must catch non-hiding balances, which is
your own δ-matching argument stated as a theorem).
