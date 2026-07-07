<!-- raw agent output from the 2026-07-06 research sweep (angle: bolt-zkchannels, verification); unedited; the verified synthesis is ../RESEARCH.md and supersedes this file where they disagree -->

# Fact-check: bolt-zkchannels report

Verified against locally extracted text of the two primary PDFs (both fetched and text-extracted with pdftotext) plus the GitHub repo and web search. Note: eprint.iacr.org actively blocked my IP ("Your IP address has been blocked"), matching the report's own 403 disclosure; all paper quotes were checked against the CCS'17 PDF the report actually cites.

## Claim 1 — The Bolt paper exists (Green & Miers, CCS'17 / eprint 2016/701) and states the quoted privacy guarantee

**Verdict: CONFIRMED**

The CCS PDF at https://acmccs.github.io/papers/p473-greenA.pdf is titled "Bolt: Anonymous Payment Channels for Decentralized Currencies" by Matthew Green and Ian Miers, Johns Hopkins University, header "CCS'17, October 30-November 3, 2017, Dallas, TX, USA". The privacy guarantee is verbatim:

> "Upon receiving a payment from some customer, the merchant learns no information beyond the fact that a valid payment (of some known positive or negative value) has occurred on a channel that is open with them. The network learns only that a channel of some balance has been opened or closed."

The anonymized-capital caveat is also real: "These techniques ensure that multiple payments on a single channel are unlinkable to each other and — if channels are funded with anonymized capital² — anonymous." The per-payer-parameters warning is verbatim too: "If a recipient provides unique channel parameters to each potential payer... the payer receives no privacy — as the set of channels open under that set of parameters has an anonymity set of a single person." The eprint 2016/701 record exists with the same title/authors ([eprint.iacr.org/2016/701](https://eprint.iacr.org/2016/701), confirmed via [dblp](https://dblp.org/pid/129/9500.html) and search since eprint blocked direct fetch).

## Claim 2 — The abort attacks (merchant shrinks anonymity set / links a user via induced aborts)

**Verdict: CONFIRMED**

From the CCS PDF, verbatim:

> "by aborting during protocol execution, the merchant can place the customer in a state where she is unable to conduct future transactions... (1) The merchant can arbitrarily reduce the anonymity set by (even temporarily) evicting other users through induced aborts. (2) The merchant may link a user to a repeating sequence of transactions by aborting the user in the middle of the sequence."

The proposed mitigation is also as reported: "customers should scan the network for premature closures and abort the channel if the number of open channels with a merchant falls below their minimal anonymity set." URL: https://acmccs.github.io/papers/p473-greenA.pdf

## Claim 3 — Hub construction: intermediary learns neither payer nor amount; amount-hiding fails beyond one intermediary

**Verdict: CONFIRMED (with one nuance correction)**

Verbatim: "the intermediary I cannot link transactions to individual users, nor — surprisingly — can they learn the amount being paid in a given transaction. Similarly, even if I is compromised, it cannot claim any transactions passing through it." And: "channels which involve more than one intermediary cannot hide the value of a payment from all intermediaries... in any chain of channels with multiple intermediaries, at least one channel will have an intermediary party on both endpoints, and one of these parties will inevitably learn the value of the payments."

**Nuance:** the report's gloss "BOLT is a hub topology, not a Lightning-style network" overstates slightly. The paper says the advantages "do not fully generalize" and explicitly offers an extension: "We provide the full details of our construction and how to extend it to support multiple intermediaries in §4.3." Multi-hop is possible; it is the amount-hiding (and the enlarged privacy guarantee) that breaks past one intermediary, not the mechanism itself. URL: https://acmccs.github.io/papers/p473-greenA.pdf

## Claim 4 — zkChannels spec v0.3.2 (Bolt Labs, 2021-08-29): asymmetric anonymity, anonymity set = merchant's open channels, Pointcheval-Sanders, amount visible, whole-balance dispute punishment

**Verdict: CONFIRMED**

The PDF at https://boltlabs.tech/userfiles/media/boltlabs.tech/zkchannels-protocol-spec-v0.3.2.pdf is "zkChannels Private Payments Protocol [DRAFT], Bolt Labs, Inc., 2021-08-29". Verbatim:

> "the merchant is at most pseudonymous and remains identifiable across all channels; the customer is at most pseudonymous during channel establishment and closure, but has the ability to make payments anonymously as long as they have an open channel with sufficient balance. That is, the customer's anonymity set for a payment is the set of all customers with whom the given merchant has a channel open."

Also verbatim: "each successful payment results in a revocation secret that allows the merchant to track whether a given state has been spent, but the merchant learns nothing else about the payment except the amount"; "if the dispute transaction is deemed valid by the network, the merchant receives the entire channel balance"; the watchtower requirement ("both parties must be online or designate a watchtower service"); §2.2 is literally titled "Pointcheval Sanders signatures"; the arbiter framing ("In practice, we use a cryptocurrency network as the arbiter J") and the "special unlinking protocol" at establishment are all present.

## Claim 5 — libzkchannels: archived Feb 28 2023, proof-of-concept not production, ZK (BLS12-381, Zcash/Tezos) + MPC (EMP-toolkit, Bitcoin) variants, 7-9 s per malicious-mode payment

**Verdict: CONFIRMED**

From https://github.com/boltlabs-inc/libzkchannels: "This repository was archived by the owner on Feb 28, 2023. It is now read-only." README: "A Rust library implementation of libzkchannels (formerly BOLT: Blind Off-chain Lightweight Transactions)"; "The libzkchannels library is a proof of concept implementation that relies on experimental libraries and dependencies at the moment. It is not suitable for production software yet." Both variants (BLS12-381 ZK for Zcash/Tezos; garbled-circuit MPC via EMP-toolkit for Bitcoin) are described, and the performance line is: "the time to execute the MPC takes about 7-9 seconds on average on a modern workstation (not including network latency)."

**Bonus spot-check:** the TumbleBit comparison the report flags as its only verified performance number is verbatim in the CCS PDF: "at 387ms per channel payment, Tumblebit is 5 times slower than our prototype implementation of Bolt's bidirectional channels."

## Corrections summary

1. **Soften "BOLT is a hub topology, not a Lightning-style network."** The paper explicitly extends the third-party construction "to support multiple intermediaries in §4.3" and says the advantages "do not fully generalize" (not that multi-hop is impossible). Correct claim: BOLT supports multi-intermediary chains, but amount-hiding from intermediaries and the enlarged anonymity guarantee hold only for exactly one intermediary; beyond that, at least one intermediary inevitably learns payment values. The report's downstream argument (hub-only for the privacy-relevant configuration) survives intact.
2. No other corrections. All five load-bearing claims, all direct quotes checked, the paper's existence/authors/venue, the spec's existence/version/date, the repo's archive status, and the two performance figures are accurate as written. The report's own hedges (eprint 403, spec read only in part, no primary source for Zcash-review folklore, "serialized payments" being the author's inference) are honest and should be preserved in synthesis.

Sources: [Bolt CCS'17 PDF](https://acmccs.github.io/papers/p473-greenA.pdf), [eprint 2016/701](https://eprint.iacr.org/2016/701), [zkChannels spec v0.3.2](https://boltlabs.tech/userfiles/media/boltlabs.tech/zkchannels-protocol-spec-v0.3.2.pdf), [libzkchannels](https://github.com/boltlabs-inc/libzkchannels), [dblp: Ian Miers](https://dblp.org/pid/129/9500.html), [ACM DL record](https://dl.acm.org/doi/10.1145/3133956.3134093)