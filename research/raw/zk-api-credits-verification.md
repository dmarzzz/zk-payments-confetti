<!-- raw agent output from the 2026-07-06 research sweep (angle: zk-api-credits, verification); unedited; the verified synthesis is ../../processed/field-report.md and supersedes this file where they disagree -->

# Fact-check: zk-api-credits report

## Claim 1: The main post — "ZK API Usage Credits (LLMs and beyond)" by Davide Crapis and Vitalik Buterin, Feb 11 2026, ethresear.ch/24104 — with the stated construction (a = Hash(k,i), y = k + a·x, Nullifier = Hash(a), solvency (i+1)·C_max ≤ D + R, dual D+S stake, local "Spent Tickets" DB)

**Verdict: CONFIRMED**

Fetched https://ethresear.ch/t/zk-api-usage-credits-llms-and-beyond/24104/print. Byline reads "_Davide Crapis and Vitalik Buterin_", posted February 11, 2026. Formulas match exactly: "a = Hash(k, i)", "x = Hash(M)", "y = k + a · x", "Nullifier = Hash(a)", "(i + 1) · C_max ≤ D + R". Double-spend check quote confirmed: "If the Nullifier exists with a different x (Message), the user tried to spend the same ticket on two different requests." Dual stake confirmed: "The user deposits a total sum Total = D + S. D (RLN Stake): Governed by the math of the protocol... S (Policy Stake): Governed by Server Policy. Can be slashed (burned), but _not claimed_..." with "The Server calls a `slashPolicyStake()` function on the smart contract." Also confirmed: no post in the thread discusses multiple providers sharing a deposit or nullifier set (the report's single-recipient-binding argument rests on this silence, and the silence is real).

## Claim 2: Vitalik's reply justifying refunds ("overhead would be like 100x", ">$5 budget", "~a cent" per request, "infinite-variance Levy-ish distribution")

**Verdict: CONFIRMED (one quote lightly paraphrased)**

Same URL, vbuterin reply dated March 15, 2026: "The problem is that the resource consumption of requests is extremely variable... I would estimate with no refunds my overhead would be like 100x" and "when I sent requests to GPT 5.2... I need to have a >$5 budget to cover the max possible size, but on average each request costs like a cent"; "infinite-variance Levy-ish distribution" appears verbatim. Caveat: the report's quoted fragment "I need to have a >$5 budget to make requests" is a paraphrase of "to cover the max possible size" — substance identical, wording not.

## Claim 3: sergei-tikhomirov's payment-channel framing and the self-slash race ("9 requests, then deliberately double-signs")

**Verdict: CONFIRMED**

Same URL: "Concretely, we can view the payment mechanics here as a payment channel... We want value transfer from the user to the provider proportionally to the amount of service provided, without on-chain transaction per each request. The provider must be sure that at any time it can claim on-chain the fair share of the user's deposit, proportional to services provided." Self-slash: "what if the user makes 9 request, and then deliberately double-signs and tries to slash its own deposit?" MicahZoltu's differentiator also confirmed: "A state channel would certainly be simpler, but it would still correlate requests with each other." Thread's last visible post: drstone, March 21, 2026 (matches the report's snapshot caveat).

## Claim 4: PrivateX402 (McMenamin & Grigor, Nethermind, Feb 18 2026, ethresear.ch/24151) — one deposit, N channels, privacy vs chain observers not the recipient, TEE-emulated proofs, explicit N-deposits contrast with ZK API Credits

**Verdict: CONFIRMED**

Fetched https://ethresear.ch/t/privatex402-privacy-preserving-payment-channels-for-multi-agent-ai-systems/24151. Title, authors (Conor McMenamin and Artem Grigor, both Nethermind), and Feb 18, 2026 date confirmed. Exact quote present: "the contract stores only the root and total funding — individual allocations remain private", with `Leaf = H(SessionKey, AgentAddress, MaxSpend)` and "a collateral deposit of 50% of `TotalMaxSpend`". Recipient-visibility claim confirmed: "Each `SessionKey` is a random 256-bit secret shared only between the user and the corresponding agent", payments "via EIP-191 signed cumulative receipts". TEE status confirmed: "a pluggable proof backend currently uses a mock TEE (with ZK circuits drafted but not integrated)", "TEE now, ZK later". Contrast confirmed: "With RLN, a user interacting with N independent providers generally needs N deposits/commitments. PrivateX402 covers N agents with a single deposit and keeps payments proof-free" ... "concentrating proofs at setup/settlement/claim."

## Claim 5: Nirvana (IACR ePrint 2022/872, Madhusudan/Sedaghat/Jovanovic/Preneel, 2022) and the follow-up "Reusable, Instant and Private Payment Guarantees" (ePrint 2023/583, "same group")

**Verdict: CONFIRMED for 2022/872; CORRECTED for 2023/583 author attribution**

eprint.iacr.org blocks this IP (403 + explicit crawler ban page), so verified via [DBLP](https://dblp.org/rec/journals/iacr/MadhusudanSJP22.html), [Springer](https://link.springer.com/chapter/10.1007/978-3-031-35486-1_25), and the [KU Leuven COSIC copy](https://www.esat.kuleuven.be/cosic/publications/article-3509.pdf). Nirvana is real: "Nirvana: Instant and Anonymous Payment-Guarantees," Akash Madhusudan, Mahdi Sedaghat, Philipp Jovanovic, Bart Preneel, ePrint 2022/872 (2022); abstract matches the report ("a novel randomness-reusable threshold encryption that mitigates double-spending by revealing the identities of malicious users"). The follow-up exists as ePrint 2023/583 and was published at ACISP 2023, but its author list is Akash Madhusudan, Mahdi Sedaghat, Samarth Tiwari, Kelong Cong, and Bart Preneel — Jovanovic is not on it and two new authors are. "Same group" is defensible (3 of 4 Nirvana authors carry over, same COSIC/KU Leuven nucleus) but not literally the same author set.

Sources: [ePrint 2022/872](https://eprint.iacr.org/2022/872), [DBLP MadhusudanSJP22](https://dblp.org/rec/journals/iacr/MadhusudanSJP22.html), [Springer ACISP 2023 chapter](https://link.springer.com/chapter/10.1007/978-3-031-35486-1_25), [ePrint 2023/583](https://eprint.iacr.org/2023/583)

## Corrections summary

1. **ePrint 2023/583 authors:** replace "same group" (implying the Nirvana four) with the actual author list: Madhusudan, Sedaghat, Tiwari, Cong, Preneel. Jovanovic is not an author of the follow-up. Add venue: ACISP 2023 (Springer LNCS, doi 10.1007/978-3-031-35486-1_25).
2. **Vitalik quote wording:** the fragment "I need to have a >$5 budget to make requests" should read "I need to have a >$5 budget to cover the max possible size" if quoted verbatim; the "100x" and "Levy-ish" fragments are verbatim-accurate.
3. No other corrections. The report's own hedges hold up: the HackMD spec, omarespejel gist contents, 4Mica deployment status, and the Zeko demo repo remain unverified by this pass (not among the five load-bearing claims); nothing found contradicts them.