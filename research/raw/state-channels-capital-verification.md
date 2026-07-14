<!-- raw agent output from the 2026-07-06 research sweep (angle: state-channels-capital, verification); unedited; the verified synthesis is ../../processed/field-report.md and supersedes this file where they disagree -->

# Fact-check: 5 load-bearing claims

## Claim 1 — Channel factories (Burchert–Decker–Wattenhofer, RSOS 2018): one shared deposit funds many subchannels, funds move between subchannels off-chain, with ~50% (3-party) and ~90% (20-user/100-channel) blockchain-space savings

**Verdict: CONFIRMED** (paper exists, authors/venue correct; original URL 403'd, verified via the PMC full-text mirror of the same DOI)

Evidence (paper text via PMC):
- Off-chain reallocation: "funds are committed to a group of other users instead of a single partner and can be moved between channels with just a few messages inside this collaborating group"
- 3-party figure: "If p = 3 entities form a second layer group to create n = 3 pairwise channels, their blockchain cost is 210, so they already save 50% of the blockchain space."
- 20/100 figure: "For a group of 20 users with 100 intra-group channels, the cost of the blockchain transactions is reduced by 90% compared to 100 regular micropayment channels opened on the blockchain." (and 96% with Schnorr aggregation, "With p = 20 parties and n = 100 channels, the cost is 8, an improvement of 96%.")

URL: https://pmc.ncbi.nlm.nih.gov/articles/PMC6124062/ (mirror of https://royalsocietypublishing.org/doi/10.1098/rsos.180089, which returns HTTP 403 to automated fetch)

## Claim 2 — Perun (Dziembowski, Eckey, Faust, Malinowski, IEEE S&P 2019): virtual payment channels where the intermediary/hub is not involved in individual payments

**Verdict: CONFIRMED** (eprint 2017/635 returned 403; verified via dblp record + Semantic Scholar's copy of the official abstract for DOI 10.1109/SP.2019.00020)

Evidence:
- dblp: "Perun: Virtual Payment Hubs over Cryptocurrencies." — Stefan Dziembowski, Lisa Eckey, Sebastian Faust, Daniel Malinowski, IEEE Symposium on Security and Privacy 2019, pp. 106–123, DOI 10.1109/SP.2019.00020. Author list and venue exactly match the report.
- Abstract: "Perun introduces a technique called 'virtual payment channels' that avoids involvement of the intermediary for each individual payment"; "we formally model and prove security of this technique in the case of one intermediary, who can be viewed as a 'payment hub' that has direct channels with several parties."

Caveat the synthesizer should keep: the report's statements about Ingrid's exact collateral amount and "financial neutrality" remain sourced to the Perun 2.0 whitepaper, not the S&P paper — the report already flags this correctly and it stays flagged.

URLs: https://dblp.org/rec/conf/sp/DziembowskiEFM19.html , https://api.semanticscholar.org/graph/v1/paper/DOI:10.1109/SP.2019.00020?fields=title,authors,venue,year,abstract

## Claim 3 — Sprites (Miller, Bentov, Bakshi, Kumaresan, McCorry, FC 2019 / arXiv 1702.05812): multi-hop collateral lockup cut from Θ(ℓΔ) to Θ(ℓ+Δ)

**Verdict: CONFIRMED** (with two pedantic notes)

Evidence:
- arXiv abstract: "In Lightning Network, a payment across a path of ℓ channels requires locking up collateral for Θ(ℓΔ) time, where Δ is the time to commit an on-chain transaction. Sprites reduces this cost to O(ℓ + Δ)." Abstract also confirms off-chain partial deposits/withdrawals ("supports partial withdrawals and deposits without channel interruption").
- dblp confirms the FC version: "Sprites and State Channels: Payment Networks that Go Faster Than Lightning," Andrew Miller, Iddo Bentov, Surya Bakshi, Ranjit Kumaresan, Patrick McCorry, Financial Cryptography 2019, pp. 508–526, DOI 10.1007/978-3-030-32101-7_30 — the report's author list is exactly right for the cited FC 2019 version.

Notes: (a) the paper writes the Sprites bound as O(ℓ+Δ), not Θ(ℓ+Δ) — the report's Θ slightly overstates; (b) the arXiv listing's author roster differs from FC's (arXiv page shows Christopher Cordi and no Bakshi), so cite FC 2019 for the author list, as the report does.

URLs: https://arxiv.org/abs/1702.05812 , https://dblp.org/search/publ/api?q=Sprites+State+Channels+Payment+Networks&format=json

## Claim 4 — Guasoni–Huberman–Shikhelman, Management Science "2023": frequency threshold for channels beating on-chain; cost ~ sqrt(payment rate) unidirectional, cube root bidirectional; collateral ~ r^(-1/2) / r^(-1/3)

**Verdict: CORRECTED** (content confirmed; bibliographic year wrong; the r-exponents remain abstract-level unverified)

Evidence (publisher abstract, verbatim): "Unidirectional channels costs grow with the square-root of payment rates, while symmetric bidirectional channels with their cubic root." Also: "(i) identifies conditions for two parties to optimally establish a channel, (ii) finds explicit formulas for channel costs, (iii) obtains the optimal collaterals and savings entailed" — supports the frequency-threshold framing.

Correction: the publisher page gives **Management Science Vol. 70, Issue 6 (2024), published online November 6, 2023**. Cite as "Management Science 70(6), 2024" not "2023, Management Science." Authors (Paolo Guasoni, Gur Huberman, Clara Shikhelman) and DOI 10.1287/mnsc.2022.01664 are correct.

Residual: the specific r^(-1/2)/r^(-1/3) interest-rate exponents for optimal collateral are not in the abstract; full text is paywalled. The report already self-flags this — keep that flag; do not state the exponents as verified.

URL: https://pubsonline.informs.org/doi/10.1287/mnsc.2022.01664

## Claim 5 — Domino attack / Donner (Aumayr, Moreno-Sanchez, Kate, Maffei, NDSS 2023): rooted virtual channels admit a griefing attack that force-closes the whole underlying path; Donner avoids it

**Verdict: CONFIRMED** (read directly from the NDSS-hosted PDF)

Evidence (paper text, page 1–2): Authors are Lukas Aumayr (TU Wien), Pedro Moreno-Sanchez (IMDEA), Aniket Kate (Purdue/Supra), Matteo Maffei (TU Wien); "Network and Distributed System Security (NDSS) Symposium 2023 … https://dx.doi.org/10.14722/ndss.2023.24370". Attack: "rooted VCs are by design prone to severe drawbacks including the Domino attack …, a new DoS/griefing style attack in which (i) a malicious intermediary of a VC or (ii) an attacker establishing a VC with itself over a number of honest PCs can close the whole path of underlying PCs and bring them on-chain." Fix: "We then present Donner, the first virtual channel construction that overcomes the shortcomings above… reduces the on-chain number of transactions for disputes from linear in the path length to a single one, which is the key to prevent Domino attacks, and reduces the storage overhead from logarithmic in the path length to constant."

Note: the report's phrase "stop the intermediary-collateral from growing with the path" is not what the abstract quantifies — the paper's stated path-length improvements are dispute transactions (linear → 1) and storage overhead (logarithmic → constant). Table I compares storage overhead per party, not collateral. Soften that sub-clause or restate it in the paper's own terms.

URL: https://www.ndss-symposium.org/wp-content/uploads/2023/02/ndss2023_f370_paper.pdf

## Corrections summary

1. **GHS citation year/venue detail:** change "2023, Management Science" to **Management Science 70(6), 2024 (online Nov 6, 2023)**. DOI and authors unchanged.
2. **GHS r-exponents:** keep the r^(-1/2)/r^(-1/3) collateral scaling flagged as unverified (abstract confirms only sqrt/cube-root cost scaling in payment rate); do not promote it to a verified claim.
3. **Sprites bound notation:** the paper claims Lightning Θ(ℓΔ) → Sprites **O(ℓ+Δ)**; replace "Θ(ℓ+Δ)" with "O(ℓ+Δ)" wherever repeated.
4. **Sprites authorship provenance:** author list (incl. Bakshi) is correct for the FC 2019 version only; the arXiv v1 listing differs (Cordi, no Bakshi). Cite FC 2019 for authors.
5. **Donner path-length benefit:** restate "stops intermediary-collateral from growing with the path" as the paper's actual claims: dispute on-chain transactions linear→single and storage overhead logarithmic→constant per party; the collateral-scaling phrasing is not verbatim supported.
6. **No fabricated citations found:** all five papers exist with the stated authors and venues; the two 403-blocked primary URLs (royalsocietypublishing.org DOI page, eprint.iacr.org/2017/635) were verified through PMC full text and dblp/IEEE-DOI metadata respectively — the URLs themselves are correct, just bot-blocked.