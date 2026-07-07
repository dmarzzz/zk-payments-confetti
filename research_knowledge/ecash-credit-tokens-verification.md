<!-- raw agent output from the 2026-07-06 research sweep (angle: ecash-credit-tokens, verification); unedited; the verified synthesis is ../RESEARCH.md and supersedes this file where they disagree -->

# Fact-check: 5 load-bearing claims

## Claim 1: ACT (draft-schlesinger-cfrg-act) exists — Schlesinger & Katz (Google), keyed-verification BBS-style credit balance, nullifier per spend, unlinkable change — and "the CFRG draft states Cloudflare and Google are exploring it for rate-limiting AI agents"

**Verdict: CONFIRMED (core) / CORRECTED (Cloudflare-Google sub-claim)**

The draft is real, authored by Samuel Schlesinger and Jonathan Katz, both Google. Abstract: "This document specifies Anonymous Credit Tokens (ACT), a privacy-preserving authentication protocol that enables numerical credit systems without tracking individual clients." The draft confirms it is "Based on keyed-verification anonymous credentials and privately verifiable BBS-style signatures," provides "Double-spend prevention through cryptographic nullifiers," and supports "Partial spending - clients can spend a portion of their credits and receive anonymous change."

**Correction:** Neither the datatracker page nor the draft-00 full text contains any mention of Cloudflare, AI agents, or deployment exploration. "Google" appears only as the authors' affiliation. The draft says only that "Example applications include rate limiting and API credits." The report's body sentence "the CFRG draft states Cloudflare and Google are exploring it for rate-limiting AI agents" is false as attributed; the report's own "Claims I could not verify" section already half-flagged this, but the body asserts it as being in the draft, which it is not.

URLs: https://datatracker.ietf.org/doc/draft-schlesinger-cfrg-act/ , https://www.ietf.org/archive/id/draft-schlesinger-cfrg-act-00.html

## Claim 2: ZK API Usage Credits (ethresear.ch/t/24104) — Crapis & Buterin, Feb 2026; deposit D + strictly increasing ticket index + RLN slashing on index reuse + signed refund tickets + solvency proof (i+1)·C_max ≤ D + R; explicitly single-provider

**Verdict: CONFIRMED**

The post exists at the cited URL: "ZK API Usage Credits: LLMs and Beyond," authored by Davide Crapis with Vitalik Buterin as co-author, posted February 11, 2026. The mechanics match: a "strictly increasing counter: 0, 1, 2, ..." ticket index; "if the Nullifier exists with a different x (Message), the user tried to spend the same ticket on two different requests. Solve for k and SLASH"; "The Server provides a signed Refund Ticket r = {v, sig}"; and the solvency constraint "(i + 1) · C_max ≤ D + R." On provider binding: the protocol uses "the Server" (singular) throughout, describes a bilateral deposit arrangement, and "does not address cross-provider deposit portability, multi-server settlements, or interoperability mechanisms" — the report's "single-provider construction" characterization holds (it is single-provider by architecture; the post does not use the phrase "explicitly single-provider").

URL: https://ethresear.ch/t/zk-api-usage-credits-llms-and-beyond/24104

## Claim 3: Nym zk-nym — threshold-issued ticketbooks; gateways collect tickets and later present them to the Quorum; Quorum members maintain a global Bloom filter for double-spend protection

**Verdict: CONFIRMED**

From the zk-nym overview docs: "This ticket is later presented to the Quorum by the Gateway that collected it, which is used to calculate reward percentages given to Nym Network infrastructure operators." Quorum member duties include "maintaining the global Bloom Filter for double-spend protection." Ticketbook structure: "Once the Requester has received over the threshold number of PSCs they can assemble them into a 'ticketbook' of 'tickets' - spendable credentials - signed by the master key." Threshold issuance: "Members then create a PSC from their fragment of the master key generated and split amongst them at the beginning of the Quorum in the initial DKG ceremony." Note the docs frame the later-presentation step as reward accounting; the report's "deferred settlement / race window" framing remains inference (the report correctly flags this itself).

URL: https://nym.com/docs/network/cryptography/zk-nym/zk-nym-overview

## Claim 4: Cashu NUT-00 — BDHKE mechanics (B_ = Y + rG, C_ = kB_, unblind to C = kY) and online double-spend prevention via spent-secret list check of k·hash_to_curve(x) == C

**Verdict: CONFIRMED**

NUT-00 matches exactly: Alice computes "B_ = Y + rG" where "Y = hash_to_curve(x)"; Bob (mint) returns "C_ = kB_"; unblinding is "C_ - rK = kY + krG - krG = kY = C"; at redemption Bob "verifies that k*hash_to_curve(x) == C" and checks whether "x appears in the spent secrets list." One minor caveat: the NUT-00 page fetched does not itself attribute the scheme to David Wagner; the "Wagner's discrete-log variant" attribution is conventional in Cashu materials but was not present in this source. Not a correction, just an unsourced-in-primary attribution.

URL: https://github.com/cashubtc/nuts/blob/main/00.md

## Claim 5: ARC (draft-ietf-privacypass-arc-crypto) — one keyed-verification credential presentable up to N times, presentations mutually unlinkable and unlinkable to issuance

**Verdict: CONFIRMED**

The draft exists (draft-ietf-privacypass-arc-crypto-01, active in the privacypass WG), authored by Cathie Yun (Apple), Christopher A. Wood (Apple), and Armando Faz-Hernandez (Cloudflare). Abstract: "This document specifies the Anonymous Rate-Limited Credential (ARC) protocol, a specialization of keyed-verification anonymous credentials with support for rate limiting." Multi-show unlinkability: "clients can present this credential to the server up to some fixed number of times... Each presentation is pairwise unlinkable, meaning the server cannot link any two presentations to the same client credential, nor can the server link a presentation to the preceding credential issuance flow." Keyed verification confirmed: the server verifies presentations "using the server private key." The report's issuer=verifier characterization is accurate.

URL: https://datatracker.ietf.org/doc/draft-ietf-privacypass-arc-crypto/

## Corrections summary

1. **ACT / Cloudflare-Google claim:** Remove or reattribute the sentence "the CFRG draft states Cloudflare and Google are exploring it for rate-limiting AI agents." The ACT draft contains no such statement (no mention of Cloudflare, AI agents, or deployment plans; Google appears only as author affiliation). If the synthesis keeps any deployment-interest claim, it must cite a source other than the draft or drop it as unsourced.
2. **ZK API Credits "explicitly single-provider":** Soften "explicitly" to architectural fact — the post is single-provider by design (singular Server, bilateral deposit, no multi-provider discussion) but does not itself declare single-provider binding as an explicit stated limitation.
3. **Cashu / Wagner attribution (minor):** NUT-00 itself does not attribute BDHKE to David Wagner; if the synthesis repeats the Wagner attribution, cite Cashu's broader docs or the 1996 cypherpunks post rather than NUT-00.

All other checked load-bearing claims (ACT mechanics and authorship, ZK API Credits authorship/date/mechanics/solvency formula, Nym Bloom filter + ticketbook + threshold DKG, Cashu BDHKE + spent-list prevention, ARC multi-show keyed-verification unlinkability) are confirmed against primary sources. No fabricated citations found among the five checked.