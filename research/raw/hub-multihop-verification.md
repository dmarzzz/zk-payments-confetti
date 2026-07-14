<!-- raw agent output from the 2026-07-06 research sweep (angle: hub-multihop, verification); unedited; the verified synthesis is ../../processed/field-report.md and supersedes this file where they disagree -->

# Fact-check: anon-multihop research report

Verification notes: eprint.iacr.org returned 403 to the fetcher and has permanently IP-banned direct fetches, so all claims were checked against non-eprint primary sources: the full NDSS TumbleBit PDF (downloaded and text-extracted), the official NDSS 2019 AMHL page, the ACM CCS'17 proceedings PDF of Bolt (acmccs.github.io), the A2L author publication page, and the ACM DOI record for Foundations of Coin Mixing (via Semantic Scholar's DOI resolver).

## Claim 1: TumbleBit's anonymity set is k = payments successfully completed in the epoch (not the clientele), requires fixed denomination, and suffers cross-epoch intersection attacks (Heilman et al., NDSS 2017)

**Verdict: CONFIRMED**

Full paper PDF verified (title/authors match: Ethan Heilman, Leen AlShenibr, Foteini Baldimtsi, Alessandra Scafuro, Sharon Goldberg).

> "Thus, if k payments successfully completed during an epoch, the anonymity set is of size k."

> "Remark: Intersection attacks. While this notion of k-anonymity is commonly used in Bitcoin tumblers ... this information can be correlated to de-anonymize users across epochs (e.g., using frequency analysis or techniques used to break k-anonymity)."

Fixed denomination confirmed ("Each payment is of denomination 1 bitcoin, and the mapping from payers to payees is a bijection"), the 327 KB per-payment figure confirmed ("Our protocol requires 327 KB"), and the compatible-interaction-multi-graph definition and payee-better-than-payer asymmetry are all present verbatim.

URL: https://www.ndss-symposium.org/wp-content/uploads/2017/09/ndss201701-3HeilmanPaper.pdf

## Claim 2: AMHL (Malavolta, Moreno-Sanchez, Schneidewind, Kate, Maffei, NDSS 2019) discovered the wormhole/fee-theft attack on Lightning-style paths and gives scriptless ECDSA locks at <100 ms / <500 B

**Verdict: CONFIRMED**

Official NDSS page confirms exact title, all five authors, NDSS 2019.

> "a new attack that applies to all major PCNs, including the Lightning Network, and allows an attacker to steal the fees from honest intermediaries in the same payment path"

> "we propose a construction based on ECDSA signatures that does not require scripts" ... "AMHL operations can be performed in less than 100 milliseconds and require less than 500 bytes of communication overhead, even in the worst case."

Note on the "Lightning developers implemented it" sub-claim the report declined to repeat: the NDSS abstract does state verbatim "After acknowledging our attack, the Lightning Network developers have implemented our ECDSA-based AMHLs into their PCN." So the claim is present in the primary source, but it is the authors' own assertion circa 2019; the report's decision not to repeat it as current deployment fact remains sound (production Lightning still uses HTLCs, with PTLC rollout ongoing).

URL: https://www.ndss-symposium.org/ndss-paper/anonymous-multi-hop-locks-for-blockchain-scalability-and-interoperability/

## Claim 3: A2L (Tairi, Moreno-Sanchez, Maffei, IEEE S&P 2021) builds hub unlinkability from adaptor signatures + randomizable puzzles, ~33x less bandwidth than TumbleBit, interoperable with script-poor chains

**Verdict: CONFIRMED**

Author publication page confirms title, authors, and venue (42nd IEEE S&P, 2021).

> "A2L requires ∼33x less bandwidth than TumleBit [sic], while retaining the computational cost (or providing 2x speedup with a preprocessing technique)"

> requires "only digital signatures and timelock functionality from the underlying scripting language," making it "backwards compatible with virtually all cryptocurrencies available today"

The abstract also confirms "a provably secure instantiation based on adaptor signatures and randomizable puzzles." The ~9.92 KB/payment figure (from slides) was not independently re-verified but is arithmetically consistent with 327 KB / 33x. The griefing-registration details are not in the abstract; the report already correctly flags those as slide-sourced only.

URL: https://erkantairi.com/publication/a2l-anonymous-atomic-locks-for-scalability-in-payment-channel-hubs/

## Claim 4: Glaeser et al. (CCS 2022) showed A2L's formal model was flawed with concrete counterexamples, defined blind conditional signatures, and repaired it as A2L+ / A2L-UC

**Verdict: CONFIRMED**

Retrieved via ACM DOI 10.1145/3548606.3560637 (Semantic Scholar record; paper exists with exactly the six claimed authors: Glaeser, Maffei, Malavolta, Moreno-Sánchez, Tairi, Thyagarajan).

> "we identify a gap in their formal model and substantiate the issue by showing two concrete counterexamples: we show how to construct two encryption schemes that satisfy their definitions but lead to a completely insecure system"

> "we develop the notion of blind conditional signatures (BCS), which acts as the cryptographic core for coin mixing services ... we propose A2L+, a modified version of the protocol by Tairi et al. ... Finally, we propose A2L-UC, another construction of BCS that achieves the stronger notion of UC-security"

Important nuance the report already handled correctly: the counterexamples are definitional (contrived instantiations satisfying A2L's definitions yet insecure), not a demonstrated coin-theft attack on the concrete A2L instantiation. Keep the report's careful phrasing.

URL: https://api.semanticscholar.org/graph/v1/paper/DOI:10.1145/3548606.3560637 (DOI: https://dl.acm.org/doi/10.1145/3548606.3560637)

## Claim 5: Bolt (Green, Miers, CCS 2017) is a zk payment channel with per-payment unlinkability against the counterparty, includes an untrusted-intermediary hub variant, and needs a Zcash-like anonymous currency

**Verdict: CONFIRMED (with one softening correction on the Zcash requirement)**

Verified against the official CCS'17 proceedings PDF (Session B5, Johns Hopkins affiliations confirmed).

> "These techniques ensure that multiple payments on a single channel are unlinkable to each other and — if channels are funded with anonymized capital — anonymous."

> "Indirect channels ... enable third party payments, where an untrusted intermediary acts as a 'bridge' allowing two otherwise unconnected parties to exchange value. Critically, the intermediary learns neither the identity of the parties nor the amount transacted."

> "we can deploy Bolt as a soft fork to existing anonymous currencies such as ZCash"

Correction (minor): the paper's footnote reads "as in ZCash [3], **or that there exists some way of anonymizing or mixing that adds sufficient anonymity to non-anonymous cryptocurrency**." So "needs Zcash-like chain" overstates slightly: Bolt needs anonymously-funded channels, achievable via a Zcash-style chain OR sufficient external mixing. Also relevant to the fleet mapping: the paper confirms the amount-hiding property holds only for single-intermediary chains ("channels which involve more than one intermediary cannot hide the value of a payment from all intermediaries").

URL: https://acmccs.github.io/papers/p473-greenA.pdf

## Corrections summary

1. **Bolt / Zcash requirement (soften):** replace "requires a currency with strong on-chain anonymity (Zcash-style)" with "requires anonymously-funded channels — via a Zcash-style anonymous currency or any mixing that adds sufficient anonymity to a non-anonymous currency" (Bolt CCS'17 paper, footnote 2).
2. **AMHL / Lightning adoption (verification-status upgrade, keep the caution):** the primary source literally states "the Lightning Network developers have implemented our ECDSA-based AMHLs into their PCN" — so if quoted, attribute it as the AMHL authors' 2019 claim; do not state it as current Lightning production reality (production is HTLC, PTLC still rolling out).
3. **Foundations of Coin Mixing / nature of the break (keep exact phrasing):** the confirmed abstract supports "gap in the formal model + two counterexample encryption schemes that satisfy the definitions but yield a completely insecure system" — not a demonstrated theft against deployed/concrete A2L. The report's existing phrasing is correct; the synthesizer must not upgrade it to "A2L was broken/coins stealable."
4. No other corrections: all venues, author lists, performance numbers (327 KB, ~33x, <100 ms, <500 B), the k-anonymity/epoch definition, fixed-denomination requirement, and intersection-attack caveat check out against primary sources. None of the five citations is fabricated.