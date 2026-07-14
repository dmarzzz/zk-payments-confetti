# ZK Payment Channels

Unidirectional payment channels with **per-request anonymity** (the recipient cannot link two payments to the same sender or channel) and **payment-channel safety** (the recipient never loses money earned), in a **post-quantum** setting (STARKs + hashes; no elliptic curves, no FHE, no recursive STARKs).

## Goals

- **Per-request anonymity.** Bob must not learn that two payments came from the same Alice, nor that they belong to the same channel. He learns only "someone paid me δ for this service." Channel attribution is revealed only if someone cheats.
- **Hidden balances.** The cumulative balance is never visible to Bob. (This is what enables per-request anonymity: if Bob saw cumulative balances, he could match pairs with the per-request δ he charged and reconstruct sender chains. High-entropy δ makes this *more* reliable, not less, so the balance must be hidden.)
- **Payment-channel safety.** Bob never loses money he has earned. His worst case is receiving the entire deposit (≥ what he's owed) — strictly stronger than a classical channel.
- **Liveness for Alice.** If Bob never signed anything, Alice can unilaterally recover her full deposit.

Assume elliptic curves are broken. We use STARKs, hashes (Poseidon / Blake), and a post-quantum **signature scheme** — any scheme whose verification is cheap inside a STARK. Hash-based stateful (WOTS/XMSS), hash-based stateless (SPHINCS+), and lattice-based (Dilithium/Falcon) all work; hash-based is the natural fit because verification is pure hashes, native to STARKs.

## The protocol

Alice makes a nullifier chain `N_{i+1} = H(N_i, c)` for a secret `c`.

**Open.** Alice deposits D into a channel contract naming Bob as recipient (recipient is public). The open commits (hiding) to `N₁` — the next nullifier of the genesis state (balance 0). D and the recipient are public; the commitment to `N₁` hides it.

**Payment.** Alice sends Bob a message revealing `N_{i+1}` (the nullifier the prior state committed to), plus a flat ZK proof that it extends either (i) the onchain genesis (parent balance 0), or (ii) a state Bob signed (parent balance = that state's committed balance, with Bob's signature verified inside the proof). The proof shows `parent_balance + δ = new_balance ≤ D`, with δ public and the balances private. The message commits (hiding) to the new balance and to the next nullifier `N_{i+2}`.

Bob counter-signs. If he sees a nullifier he's already seen, he refuses to sign.

**Close.** Alice must withdraw within 90 days, or within 7 days of Bob requesting close. She withdraws by opening the committed-next-nullifier of the state she closes on (a payment, or the genesis for a full refund) — revealing some `N`. The contract pays out per the balance. **Bob challenges if he holds a message that revealed `N`** (i.e. the closed state was extended). If challenged, Alice forfeits everything to Bob. Otherwise the split stands.

In the base protocol, the final balance split is revealed onchain at close.

## How it works

**The nullifier chain** is the single mechanism doing two jobs: each `Nᵢ` is a duplicate-detection tag (Bob refuses to sign two messages revealing the same nullifier), and each state's *committed* next-nullifier is a precommitment that makes stale closes detectable.

**Stale-close detection** works by collision, not by Bob finding the latest state (which anonymity prevents). Each message reveals the nullifier its parent committed to, and commits to a fresh next nullifier. Closing a state opens its committed-next-nullifier onchain. If Alice closes a non-final state, Bob holds a message that revealed that same nullifier (the state's successor) → collision → Bob challenges → Alice forfeits. The genesis is just a state that commits to `N₁`; closing it (refund) opens `N₁`, and if message 1 was made it revealed `N₁` → collision. Uniform rule, no special case.

**Per-request anonymity** comes from: (a) each nullifier is unlinkable to the previous one without `c`; (b) balances are hiding commitments, so Bob can't match cumulative-balance deltas against the per-request δ; (c) the "extends a Bob-signed state" proof hides *which* prior state, so Bob can't link a payment to its parent. The signature-verification-inside-the-STARK is what makes (c) work without a Merkle tree of states (a signature is a self-certifying witness of acceptance; the ZK proof hides which signature).

**Safety.** Bob never loses: honest close → his exact balance; stale close → he challenges and gets everything; Alice AWOL → he gets everything; genesis-close after payments → collision → he gets everything. The `new_balance ≤ D` check in each payment proof prevents Alice from paying Bob past the deposit and then recovering it.

## Privacy properties

**Has:**
- Per-request anonymity: Bob cannot link two payments to the same sender or channel. Balances, nullifier-chain linkage, and "which prior state" are all hidden inside ZK proofs.
- Unlinkable nullifiers: consecutive `Nᵢ` are unlinkable without `c`.

**Does not have (in the base protocol):**
- **Recipient anonymity.** The recipient (Bob) is named in the onchain channel record. Anyone sees that Alice opened a channel with Bob. (This is a deliberate simplification; see Extensions.)
- **Deposit-amount privacy.** D is public at open.
- **Close-amount privacy.** The final balance split is revealed at close.
- **Open/close footprint hiding.** The onchain open and close transactions are visible; only their *contents* (recipient, amounts) are partly hidden. The existence and timing of a channel between Alice and Bob is public.

Per-request anonymity is the property the design is built around; the others are leaked at the channel boundaries (open/close) but preserved within the channel's lifetime.

## Extensions

### Shielded-pool integration

The leaks above — recipient identity, D, final split, open/close footprint — can be closed by integrating with a shielded-pool protocol (Zcash/Tornado-style). The deposit D comes *from* a shielded-pool note (so the source of funds and amount are hidden among all pool users), and the close pays *into* fresh shielded-pool notes (so the final split is hidden). This makes D and the output amounts private.

**Comparison to stacking with a separate shielded pool (no integration).** One could also just use a standalone shielded pool for deposits and withdrawals, with the channel protocol oblivious to it: Alice withdraws from the pool to a public address, opens a channel (D now public), closes (split now public), and redeposits into the pool. This hides the *ultimate* source and destination of funds among pool users, but it does **not** hide the channel boundaries: the open and close are still onchain with public D and public split, linkable to each other and to the public address that touched the pool. An observer learns "some pool user opened a channel for D with Bob and closed it with split (b_A, b_B)" — the channel's existence, amount, and split are public, even if the pool user's identity is hidden behind the pool.

**Integrated** shielded-pool support closes this boundary: the open *consumes* a pool note inside its ZK proof (D becomes a private witness, proven `≤ D` and matching the channel's deposit without being revealed), and the close *creates* pool notes as outputs (the split is hidden inside output commitments). The channel's D and final split are then hidden among all pool activity, not just the source/destination.

The cost is a larger ZK proof at open and close (pool-note membership and nullifier inside the proof) and a dependency on the pool's Merkle tree. The channel protocol's core (payments, nullifier chain, challenge) is unchanged.

### Recipient-anonymous opens

If recipient anonymity is desired (not just deposit/amount privacy), the recipient can be hidden behind a per-channel ephemeral keypair `(pk_ch, sk_ch)` committed (hiding) at open: `Com(pk_ch; r)`. Bob learns the channel is his via an offchain secret from Alice (`pk_ch`, `r`). Close reveals `pk_ch` (ephemeral, unlinkable across channels, so it reveals nothing about Bob's identity). The contract verifies Bob's counter-signatures under `pk_ch` directly. This adds the ephemeral-key machinery and an offchain handshake but otherwise leaves the protocol intact. Whether it's worth it depends on the threat model: the recipient needs a persistent network address (even an onion one) to receive channel messages anyway, so hiding the on-chain recipient may be of limited marginal value.
