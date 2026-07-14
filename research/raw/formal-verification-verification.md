<!-- raw agent output from the 2026-07-06 research sweep (angle: formal-verification, verification); unedited; the verified synthesis is ../../processed/field-report.md and supersedes this file where they disagree -->

# Fact-check: formal-verif report — 5 load-bearing claims

Note on method: eprint.iacr.org blocked this machine's IP outright, so eprint-hosted claims were verified via dblp, Semantic Scholar (by DOI), the University of Edinburgh publication record, and the official ACM CCS 2017 open-proceedings PDF mirror.

## Claim 1: Kiayias–Thyfronitis Litos (CSF 2020) is the first full UC formalization of Lightning, and its security guarantees are explicitly parameterized by ledger properties / participant availability

**Verdict: CONFIRMED**

University of Edinburgh publication record for the paper (authors Aggelos Kiayias and Orfeas Stefanos Thyfronitis Litos, venue 2020 IEEE 33rd Computer Security Foundations Symposium):

> "we present for the first time a full formalisation and security analysis of the lightning network in the (global) universal composition setting"

> "our treatment delineates exactly how the security guarantees of the protocol depend on the properties of the underlying ledger and the frequent availability of the protocol participants"

URL: https://www.research.ed.ac.uk/en/publications/586c0dbc-a57b-4e1f-9bab-c566ad90a499

The second quote also directly supports the report's "watchtower-style liveness assumption" framing (frequent availability of participants).

## Claim 2: arXiv 2503.07200 (Fabiański, Stefański, Thyfronitis Litos) gives the first machine-checked (Why3) proof that a simplified LN safeguards honest users' funds

**Verdict: CONFIRMED**

arXiv abstract page confirms title "A Formally Verified Lightning Network" and exactly those three authors (Grzegorz Fabiański, Rafał Stefański, Orfeas Stefanos Thyfronitis Litos):

> they "use formal verification to prove that the Lightning Network ... always safeguards the funds of honest users" ... "we build our system using the Why3 platform" ... "for the first time, we provide a machine checkable proof that they are upheld under every scenario, all in an integrated fashion."

URL: https://arxiv.org/abs/2503.07200

## Claim 3: Grundmann–Hartenstein (arXiv 2505.15568) make model checking LN feasible via two proven refinements (time abstraction + channel/multi-hop decomposition), check up to 4-hop payments with 2 concurrent payments, and conclude the current spec is secure

**Verdict: CONFIRMED**

arXiv abstract page confirms title "Model Checking the Security of the Lightning Network", authors Matthias Grundmann and Hannes Hartenstein, and each element:

> they "prove that the model of time used in the protocol can be abstracted using ideas from the research of timed automata" and "prove that it suffices to model check the protocol for single payment channels and the protocol for multi-hop payments separately"; model checking covers "payments over up to four hops and two concurrent payments," and the "results indicate that the current specification of Lightning is secure."

URL: https://arxiv.org/abs/2505.15568

## Claim 4: Foundations of Coin Mixing Services (Glaeser et al., CCS 2022) found a gap in A2L's formal model, gave two concrete counterexamples yielding a completely insecure system, defined Blind Conditional Signatures, and produced A2L+ (game-based) and A2L-UC (UC, at significant cost)

**Verdict: CONFIRMED**

dblp confirms authors (Noemi Glaeser, Matteo Maffei, Giulio Malavolta, Pedro Moreno-Sanchez, Erkan Tairi, Sri Aravinda Krishnan Thyagarajan), CCS 2022, DOI 10.1145/3548606.3560637. Semantic Scholar abstract (by DOI):

> "we identify a gap in their formal model and substantiate the issue by showing two concrete counterexamples: we show how to construct two encryption schemes that satisfy their definitions but lead to a completely insecure system."

> "we develop the notion of blind conditional signatures (BCS) ... We propose game-based security definitions for BCS and propose A2L+ ... Finally, we propose A2L-UC, another construction of BCS that achieves the stronger notion of UC-security (in the standard model), albeit with a significant increase in computation cost."

The abstract also confirms the report's framing that A2L is "Tairi et al. [IEEE S&P 2021]".

URLs: https://api.semanticscholar.org/graph/v1/paper/DOI:10.1145/3548606.3560637 , https://dblp.org/search/publ/api?q=Foundations+of+Coin+Mixing+Services (canonical: https://dl.acm.org/doi/10.1145/3548606.3560637 — 403 to fetcher but DOI/metadata confirmed via dblp)

## Claim 5: Bolt (Green–Miers, CCS 2017) makes multiple payments on a single payment channel unlinkable to each other, requiring anonymous channel funding

**Verdict: CONFIRMED**

dblp confirms Matthew Green and Ian Miers, CCS 2017, DOI 10.1145/3133956.3134093 (eprint 2016/701 is the 2016 preprint). From the official CCS 2017 proceedings PDF (p.2):

> "These techniques ensure that multiple payments on a single channel are unlinkable to each other and — if channels are funded with anonymized capital — anonymous."

> "While multiple payments on the same channel are unlinkable, to avoid linking an aborted payment to the payer's identity, our construction requires that the underlying payment channel be funded anonymously."

URL: https://acmccs.github.io/papers/p473-greenA.pdf

Nuance for the synthesizer (not a correction): the paper states the *target* of a payment is pseudonymous — "the party initiating the payment is anonymous and unlinkable between payments, while the target of the payment is pseudonymous ... the recipient knows the payment came from someone with whom they have an open channel" (p.3). The report's properties-table wording ("channel endpoints still known at open/close") already captures this; the looser phrase in Relevance point 1 ("unlinkable ... even from the recipient's own view") should be read as unlinkability-of-spends, not recipient-side anonymity of the channel itself.

## Corrections summary

No corrections required. All five load-bearing claims verified against primary or authoritative secondary sources with matching titles, authors, venues, and substantive content; none of the citations checked are fabricated.

Items the synthesizer should carry forward as caveats (already flagged in the report itself, reaffirmed here):
1. Bolt unlinkability is spend-level, vs a pseudonymous recipient; channel endpoints are known at open/close, and anonymity additionally requires anonymous funding (quote above).
2. eprint.iacr.org URLs could not be fetched directly (IP block, HTTP 403/robots ban); all eprint-hosted citations were confirmed via dblp/Semantic Scholar/proceedings mirrors instead. Links themselves are presumed live but were not directly exercised.
3. The report's own "Claims I could not verify" list (Lean 4 PCN feasibility paper, zkChannels formal artifact, "Verifying Payment Channels with TLA+" venue, LN adoption of ECDSA AMHLs) remains unverified in this pass; none of those were among the five load-bearing claims.

Sources: [research.ed.ac.uk record](https://www.research.ed.ac.uk/en/publications/586c0dbc-a57b-4e1f-9bab-c566ad90a499), [arXiv 2503.07200](https://arxiv.org/abs/2503.07200), [arXiv 2505.15568](https://arxiv.org/abs/2505.15568), [Semantic Scholar DOI:10.1145/3548606.3560637](https://api.semanticscholar.org/graph/v1/paper/DOI:10.1145/3548606.3560637), [dblp](https://dblp.org/search/publ/api?q=Foundations+of+Coin+Mixing+Services), [CCS 2017 Bolt PDF](https://acmccs.github.io/papers/p473-greenA.pdf)