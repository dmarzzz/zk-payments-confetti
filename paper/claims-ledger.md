# Claims ledger (task J1)

Every claim the paper makes, mapped to its source. Built before the paper;
the paper is written against this ledger and no claim may appear in
`paper.md`/`post.md`/`paper.tex` without a row here. Source kinds:

- **R** = `RESEARCH.md` (the verified field report; section named). Where R
  cites a primary source, the primary URL is repeated here — the paper
  cites the primary, per BRIEF.md ("every claim about prior work cites the
  primary source").
- **S** = `Spec.md` revision 11 (section named). The definition section
  mirrors S; S is the trust surface.
- **G** = `research_knowledge/gates.md` (agent-simulated gate round named;
  it is not independent human sign-off).
- **L** = Lean declaration (file + name). Kernel/build evidence is scoped by
  the corresponding row and the completed K2/K5 release record; it is not
  inferred merely from source text.
- **REPO** = a literal fact about this repository (file exists, pin value,
  CI config).

Claims deliberately NOT made (over-claims the sources forbid) are listed at
the end.

---

## §1 Introduction

| # | Claim | Source |
|---|---|---|
| 1.1 | BOLT (Green & Miers) named the anonymous payment channel object (eprint 2016/701; CCS 2017) and is the historical anchor of the line | R "What zk payment channel actually means" item 1; R deep dive 2. Primary: https://acmccs.github.io/papers/p473-greenA.pdf, https://eprint.iacr.org/2016/701 |
| 1.2 | The line went dormant: BOLT never shipped on Zcash; zkChannels stayed DRAFT (spec v0.3.2, 2021); libzkchannels archived Feb 2023 as proof-of-concept | R deep dive 2 "Deployment reality: zero". Primary: https://electriccoin.co/blog/bolt-private-payment-channels/, https://boltlabs.tech/userfiles/media/boltlabs.tech/zkchannels-protocol-spec-v0.3.2.pdf, https://github.com/boltlabs-inc/libzkchannels |
| 1.3 | No machine-checked proof of payment unlinkability exists for any channel or credit construction; every privacy proof in this literature is pen-and-paper (absence claim from systematic search, not provable — stated as such) | R TLDR; R deep dive 6; R "Residual unverified claims" |
| 1.4 | ZK API Usage Credits (Crapis & Buterin, ethresear.ch, Feb 2026) is structurally a zk payment channel bound to one recipient; the channel mapping is stated in-thread (sergei-tikhomirov) | R TLDR; R deep dive 1. Primary: https://ethresear.ch/t/zk-api-usage-credits-llms-and-beyond/24104 |
| 1.5 | A2L (S&P 2021) had a definitional gap found a year later: two counterexample encryption schemes satisfy its definitions yet yield "a completely insecure system" (CCS 2022); definitional counterexamples, not a demonstrated coin theft | R deep dive 3 (with the do-not-upgrade caveat). Primary: https://dl.acm.org/doi/10.1145/3548606.3560637, https://eprint.iacr.org/2022/942.pdf |
| 1.6 | Lightning has UC (pen-and-paper), Why3 (fund safety, machine-checked), and TLA+ (model-checked) treatments — the balance-security side is covered; the privacy side is not | R deep dive 6. Primary: https://eprint.iacr.org/2019/778.pdf, https://arxiv.org/abs/2503.07200, https://arxiv.org/abs/2505.15568 |
| 1.7 | The flat-ticket RLN credit protocol is arguably the smallest machine-checkable unlinkability target in the literature (no refunds, no revocation, one inequality) | R open problem 7; BRIEF.md Deliverable 2, instantiation 1 |
| 1.8 | Application context: reputation-gated Tor onion-service egress fleet; N mutually distrusting gateways; the adversary is the payee | R header + Application section. Primary: https://reputation-gated-egress.vercel.app |
| 1.9 | The definitions, not the proofs, are the risk surface (the A2L process lesson) | R deep dive 6 "Process lesson"; BRIEF.md engineering notes |

## §2 The object (definition; mirrors Spec.md rev 11 exactly)

| # | Claim | Source |
|---|---|---|
| 2.1 | The algorithm tuple (Setup, Open, Spend, Redeem, Close, Dispute); principals payer/payee/idealized ledger | S §2; BRIEF.md Deliverable 1 item 1 |
| 2.2 | Sorts: monetary quantities and indices in ℕ; signal algebra in F_p; embedding injective for i < p | S §1 |
| 2.3 | RLN signal algebra a = H_a(k,i), x = H_x(m), y = k + a·x, nf = H_nf(a); index in the role of RLN's epoch | S §1; R deep dive 1 (verified against the credits thread). Primary: https://ethresear.ch/t/zk-api-usage-credits-llms-and-beyond/24104, https://rate-limiting-nullifier.github.io/rln-docs/rln.html |
| 2.4 | H_x maps into F_p \ {0}: at x = 0 the signal is y = k, the secret outright | S §1 (rev-6); L `Zkpc/Games/RLN.lean` `rln_x_zero_degenerate` + file GATE-NOTE; G round 5 (gate-note) |
| 2.5 | Two signals on one (k,i) with x ≠ x′ reveal a and k; one signal reveals nothing (single-signal hiding, x ≠ 0) | S §1, §5.3; L `rln_recover_a`, `rln_recover_k`, `rln_single_point_hiding` |
| 2.6 | Epoch pseudonym nf_e = H_e(k,e): linkable within an epoch by design, unlinkable across epochs | S §1; egress post "A membership proof, rate-limited with RLN" (via S §9 provenance) |
| 2.7 | Gateway-bound messages m = (G, m̂); Redeem rejects other gateways' tickets (MC14, repair) | S §1, §2, §8 MC14; G round 1 blocking finding 1 |
| 2.8 | MC14 forcing counterexample: bit-identical cross-gateway replay produces no conflict, never starts the slash clock; excess ≈ (N−1)·D; numerical witnesses N=3,b=100,T_e=1d,L=1min,D=1000C → excess 2000C vs claimed bound ~0.2C | G round 1 finding 1 (found independently by all three panel lenses) |
| 2.9 | Redeem's ordered checks (proof, current root, epoch, gateway binding, budget, nullifier logic) with verdicts accept / reject-duplicate / evidence | S §2 Redeem; egress post wire protocol (via S §9) |
| 2.10 | Merge-time evidence (MC17, repair): gateways emit evidence when merging conflicting tuples; without it a one-pair-per-index staggered adversary is never slashed | S §2, §8 MC17; G round 1 blocking finding 3 |
| 2.11 | Ledger accounting: commingled escrow pool; sweeps authenticated to the gateway roster; Dispute permissionless (MC16, repair; payer sweep-front-running otherwise breaks T2) | S §2 (MC16), §8 MC16; G round 1 major findings |
| 2.12 | Payer close in A: close-by-unused-enumeration (MC20, repair) — reveal U (PRF-fresh nullifiers of claimed-unused indices), π_close well-formedness, window disputes by bit-match against pre-close checkpoints, automatic payout C·|U| + (D − cap·C), sweep bar on refunded nullifiers, tree eviction at settlement | S §2 Close (payer, A), §8 MC20; G rounds 5–6 |
| 2.13 | MC20 forcing counterexample (gap-index understatement): indices are hidden and contiguity was unenforced; skip index 0, spend at 1..m, close at j = 0 — collides with nothing, undisputable — recover full D after consuming service; root cause: ledger has no verifiable spend count | G round 5 blocking finding; S §8 MC20 |
| 2.14 | Payer close in B: certified-count close with nf_j reveal; contiguity by construction (R_spend^B proves index = certified count n); stale-receipt closes self-convict via the reveal; settlement caps R ≤ j·C_max and j·C_max ≤ D + R | S §2 Close (payer, B), §4, §8 MC18/MC20; G rounds 3 (R3-1), 4 (F1), 6 (stale-receipt) |
| 2.15 | Payee close in A: unilateral nf-deduped sweeps at C per fresh nullifier; monitoring duty part of the honest sweep protocol | S §2 Close (payee, A); G round 1 majors (MC16) |
| 2.16 | B has no unilateral sweeps; settles once at close; force-close-with-forfeit for silent payers; slashed B channels settle through the slash window (MC18, repair) | S §2, §4, §8 MC18; G round 2 NEW-1, round 3 R3-2 |
| 2.17 | MC18 forcing counterexample: sweeps at C_max plus refund-bearing close pay D + R out of a D deposit; pre-slash unattributability blocks per-channel netting; T2-B/T3-B/pool solvency jointly unsatisfiable | G round 2 NEW-1 |
| 2.18 | Dispute: recover a and k from the evidence pair, freeze + tree eviction, gateway-priority claims window (sweeps senior to documented conflicts, pro-rata within class), remainder to submitter as bounty (MC4, repair of the self-slash race) | S §2 Dispute, §8 MC4; R deep dive 1 (d) + open problem 2 |
| 2.19 | Window claims valid only against pre-slash checkpoints; checkpoint = binding Merkle set commitment, opened with membership witnesses (MC19, repair; post-slash k is public so the fleet could otherwise mint conflicts) | S §2, §8 MC19; G round 2 NEW-2, round 3 R3-3, round 6 (binding pinned) |
| 2.20 | The seven security statements T1–T7 with quantifiers, adversary classes, violation conditions, anti-vacuity notes, in proof order T1 → exculpability lemma → T2/T3 → T5 → T6 → T4 → T7 | S §7 (each theorem block); G round 1 (proof order endorsed) |
| 2.21 | T4 UNLINK is challenge-terminated; the rev-1 game with post-challenge oracles is unsatisfiable (three universal distinguishers: retry replay, solvency-exhaustion probing, close-count reading) (MC15, repair of the game) | S §7 T4 + §8 MC15; G round 1 blocking finding 2 |
| 2.22 | T4 calibration requirement: the game must be winnable against B-static (equal-totals ciphertext bit-matching distinguisher, verified end-to-end) and must yield negligible advantage on B-rerand | S §7 T4 calibration; G rounds 1–2; BRIEF.md T4; R deep dive 1 (omarespejel finding). Primary: https://gist.github.com/omarespejel/c3f4f2aa12b1de10467601d77d0e6232 |
| 2.23 | T4's abort/evict oracle is required because of BOLT §1.4's abort attacks (evict to shrink the set; abort mid-sequence to link) | BRIEF.md T4; R deep dive 2 (§1.4 quoted). Primary: https://acmccs.github.io/papers/p473-greenA.pdf §1.4 |
| 2.24 | T6 statement: accepted value ≤ ⌊D/C⌋·C + f(L), f(L) = N·b·(⌈L/T_e⌉+1)·C; slash within L of the second conflicting acceptance; f(L) < D as deployment condition; claims neither attacker unprofitability nor universal recovery | S §7 T6; L `Zkpc/Fleet/T6.lean` `T6_priced_divergence`, `T6_slash_within_L` |
| 2.25 | T7 FRAME target: N−1 colluding gateways cannot slash an honest member; algebraic core is one-point-per-line. The machine-checked finite-query statement and its exact scope are recorded separately in row 5.10. | S §7 T7; R open problem 5; L `rln_single_point_hiding`, `rln_evidence_sound` |
| 2.26 | Adversary conventions: PPT, adaptive, rushing; static corruption; oracles are the only interface to honest parties | S §6, §8 MC10 |

## §3 Placement

Every row of the placement table sources from R's map table ("The map") and
the corresponding deep dive; primary URL per row. No row is invented.

| # | Row / claim | Source |
|---|---|---|
| 3.1 | BOLT unidirectional/bidirectional: fixed/variable payments unlinkable vs merchant; anonymity set = customers with open channels at that merchant; anonymous funding required; revocation punishment needs chain-watching; abort attacks §1.4; amounts visible | R map rows + deep dive 2. Primary: https://acmccs.github.io/papers/p473-greenA.pdf |
| 3.2 | zkChannels: BOLT over an abstract arbiter, Pointcheval–Sanders, unlinking protocol; "anonymity set … all customers with whom the given merchant has a channel open"; DRAFT status | R map + deep dive 2. Primary: https://boltlabs.tech/userfiles/media/boltlabs.tech/zkchannels-protocol-spec-v0.3.2.pdf |
| 3.3 | ACT (draft-schlesinger-cfrg-act, 2025): keyed-verification hidden-balance credit token, BBS-style; issuer = verifier by construction; online prevention via issuer nullifier DB; blind change; no escrow, no dispute game | R map + deep dive 4. Primary: https://datatracker.ietf.org/doc/draft-schlesinger-cfrg-act/ |
| 3.4 | ARC (draft-ietf-privacypass-arc-crypto, 2025): N-presentation keyed-verification credential, pairwise unlinkable and unlinkable to issuance; prevention, cap N | R map + deep dive 4. Primary: https://datatracker.ietf.org/doc/draft-ietf-privacypass-arc-crypto/ |
| 3.5 | Privacy Pass (RFC 9576/9577/9578): single-use unlinkable tokens; public verifiability does not remove the per-origin spent set | R deep dive 4. Primary: https://www.ietf.org/rfc/rfc9576.html |
| 3.6 | TumbleBit (NDSS 2017): hub k-anonymity = payments completed in an epoch; abort shrinkage; intersection attacks across epochs | R map + deep dive 3. Primary: https://www.ndss-symposium.org/wp-content/uploads/2017/09/ndss201701-3HeilmanPaper.pdf |
| 3.7 | A2L/A2L+: adaptor-signature hub unlinkability; 2021 model had the definitional gap; build A2L+ | R map + deep dive 3. Primary: https://eprint.iacr.org/2019/589.pdf, https://dl.acm.org/doi/10.1145/3548606.3560637 |
| 3.8 | BlindHub (S&P 2023): variable amounts via blind adaptor signatures (amount was a linking tag) | R map + deep dive 3. Primary: https://eprint.iacr.org/2022/1735 |
| 3.9 | Accio (CCS 2023): variable amounts without NIZKs; no pre-locking, griefing gone by construction | R map + deep dive 3. Primary: https://eprint.iacr.org/2023/1326 |
| 3.10 | Adaptor signatures got formal foundations in 2024 | BRIEF.md Deliverable 1 item 2; R sources list. Primary: https://eprint.iacr.org/2024/1809.pdf |
| 3.11 | Chaum blind signatures / Chaum–Fiat–Naor: withdraw↔spend unlinkability vs bank; CFN offline detection reveals cheater identity — the ancestor of detect-and-punish | R map + deep dive 4. Primary: https://link.springer.com/chapter/10.1007/978-1-4757-0602-4_18, https://link.springer.com/chapter/10.1007/0-387-34799-2_25 |
| 3.12 | Compact E-Cash: serial-number nullifiers, identity extraction on double-spend; BOLT's unidirectional construction is repurposed compact e-cash | R map + deep dives 2, 4. Primary: https://eprint.iacr.org/2005/060 |
| 3.13 | Cashu/Fedimint/Taler: online prevention against a mint / BFT federation / exchange; unlinkable change (Taler refresh) | R map + deep dive 4. Primary: https://github.com/cashubtc/nuts/blob/main/00.md, https://github.com/fedimint/fedimint, https://www.taler.net/papers/taler2016space.pdf |
| 3.14 | Nym zk-nym: threshold issuance (Coconut lineage), any-gateway spend, deferred Bloom-filter reconciliation; cadence/penalties undocumented | R map + deep dive 4 (with the inference caveat). Primary: https://nym.com/docs/network/cryptography/zk-nym/zk-nym-overview, https://arxiv.org/abs/1802.07344 |
| 3.15 | ZK API Usage Credits: detect-and-slash via RLN line algebra, claimable by anyone, no watchtower; refund tickets for variable cost; single-provider by architecture | R map + deep dive 1. Primary: https://ethresear.ch/t/zk-api-usage-credits-llms-and-beyond/24104 |
| 3.16 | PrivateX402: multi-recipient one-deposit channels; NO unlinkability vs recipient (session key + cumulative receipts); TEE now, zk later | R map + deep dive 1. Primary: https://ethresear.ch/t/privatex402-privacy-preserving-payment-channels-for-multi-agent-ai-systems/24151 |
| 3.17 | Nirvana/RRTE lineage: anonymous payment guarantees, double-spender identity revealed by threshold decryption — in-thread-cited prior art for detect-and-reveal economics | R deep dive 1. Primary: https://eprint.iacr.org/2022/872, https://eprint.iacr.org/2023/583 |
| 3.18 | What is genuinely new in the credits construction: RLN detect-and-slash replacing revocation punishment (no watchtower, anyone-can-claim), and refund tickets under a solvency invariant | R deep dive 1 "Novel or rediscovery?" |
| 3.19 | BOLT rejected bare posted-coin ecash only for on-chain closure succinctness (§1.3) | R deep dives 2, Application. Primary: https://acmccs.github.io/papers/p473-greenA.pdf §1.3 |
| 3.20 | Channels beat on-chain only above a payment-frequency threshold (Guasoni–Huberman–Shikhelman); the r^(−1/2)/r^(−1/3) exponents are NOT verified and are not cited | R deep dive 5 + residual-unverified list. Primary: https://pubsonline.informs.org/doi/10.1287/mnsc.2022.01664 |
| 3.21 | Kiayias–Litos UC Lightning; Why3 fund-safety (arXiv 2503.07200, "for the first time … machine checkable proof" of LN fund safety); TLA+ LN feasibility (arXiv 2505.15568) | R deep dive 6. Primary URLs as in 1.6 |
| 3.22 | SSProve / CryptHOL are the mature crypto-game frameworks; Lean's game layer is young; VCV-io + ArkLib are verifying SNARK components in Lean | R deep dive 6 + "Formal verification" summary; BRIEF.md prover choice. Primary: https://eprint.iacr.org/2021/397, https://eprint.iacr.org/2017/753.pdf, https://eprint.iacr.org/2026/899.pdf, https://lean-lang.org/use-cases/arklib/ |

## §4 The constructions

| # | Claim | Source |
|---|---|---|
| 4.1 | Instantiation A: flat price C, solvency (i+1)·C ≤ D, per-index nullifier, one-message Spend, no payee-held per-payer state; abort = denial of service only | S §3; R Application ("the collapse") |
| 4.2 | Egress requests are near-uniform cost, so the refund rationale does not apply; drop refunds and the construction collapses to membership + counter inequality + per-index RLN | R Application "The collapse that decides the question"; egress post Addendum (via S §9) |
| 4.3 | Instantiation B: per-spend declared cost c ≤ C_max, refund R = Σ(C_max − c); solvency (i+1)·C_max ≤ D + R; certified refund chain (tag, R, n) with receipts carrying encryption randomness | S §4, §8 MC7; R deep dive 1 (Vitalik's 100x overhead argument, quoted). Primary: https://ethresear.ch/t/zk-api-usage-credits-llms-and-beyond/24104 |
| 4.4 | B-static is broken (bit-identical presented ciphertext links spends; genesis anchor upgrades it to first-spend identity linkage); B-rerand is the patch (re-randomize + in-circuit equivalence proof) | S §4; G round 2 NEW-4; R deep dive 1 (omarespejel + dcrapis patch). Primary: https://gist.github.com/omarespejel/c3f4f2aa12b1de10467601d77d0e6232 |
| 4.5 | The MC20 asymmetry: A (non-interactive spends, no receipts) must close by unused-nullifier enumeration; B (interactive receipts) closes by certified count — non-interactive spending trades away cheap closes; a design-space observation | S §8 MC20 ("two structurally different repairs … a finding about the design space"); G round 5 |
| 4.6 | Close-racing exposure (B) bounded by acceptance rate × τ; in-flight acceptances at an A close structurally unprotectable, bounded by transit volume | S §2 Close (both notes, rev-6/7); G round 6 |
| 4.8 | Instantiation C (unidirectional nullifier-chain channel, per-request anonymity, fund-forfeit-only penalties, post-quantum stack): design contributed by an external collaborator, relayed through the maintainer's agent; recorded verbatim in-repo (`PROTOCOL.md`); comparison claims (no identity-slash, interactivity trade, hidden balances load-bearing for per-request anonymity) | Primary: REPO `PROTOCOL.md` (verbatim design of record); L `Zkpc/Chain/` (machine-checked, row 5.23) |
| 4.7 | Consistency with the Lean modules: A's state machine, solvency guard, nullifier freshness, slash, close, sweep are `Zkpc/Core/State.lean` + `Zkpc/Core/Flat.lean`; fleet model `Zkpc/Fleet/Basic.lean` | L (files exist and build; T1/T2/T3/T5/T6 discharge against them) |

## §5 Results

| # | Claim | Source |
|---|---|---|
| 5.1 | T1 (no overspend, flat, L = 0) machine-checked: `T1_no_overspend` in `Zkpc/Core/T1.lean` | L |
| 5.2 | Exculpability lemma (symbolic): `honest_never_slashed` in `Zkpc/Core/T1.lean`; reachability invariant `reach_inv` | L |
| 5.3 | T2 machine-checked (A, N = 1): `T2_upper`, `T2_paid_exact`, `T2_swept_accepted`, `sweepOne_enabled`, `T2_collectable`, `T2_settles_exactly` in `Zkpc/Core/T2.lean`; deltas vs Spec.md recorded in the file GATE-NOTE (Δ folded to machine time; monitoring duty as the sweepOpen side condition) | L |
| 5.4 | T3 machine-checked (A): `payer_pay_inv`, `settleClose_enabled`, `T3_settled_amount`, `T3_payer_balance_security` in `Zkpc/Core/T3.lean` (equality form, stronger than the spec's floor) | L |
| 5.5 | T5 machine-checked (payer-close half + stability + progress): `T5_payer_close_liveness`, `settleClose_stable`, `tick_progress` in `Zkpc/Core/T5.lean`; payee half lives in T2's collectability; weak-fairness reading stated in the file header | L |
| 5.6 | T6 machine-checked (fleet): `T6_priced_divergence`, `T6_accept_count`, `T6_slash_within_L`, `card_le_solvency_of_conflictFree`, `card_le_rate_window` in `Zkpc/Fleet/T6.lean`; `epochs_in_window`, `fleet_inv` in `Zkpc/Fleet/Basic.lean`; 0 < C needed for the count form (counterexample in file GATE-NOTE); 0 < T_e load-bearing | L |
| 5.7 | RLN algebra machine-checked: `rln_recover_a`, `rln_recover_k`, `rln_single_point_hiding`, `rln_x_zero_degenerate`, `rln_evidence_complete`, `rln_evidence_sound` in `Zkpc/Games/RLN.lean` | L |
| 5.8 | Game framework machine-checked: `guessGap`, `guessGap_eq`, `boolBiasAdvantage_hiddenBitExp`, `hiddenBitAdvantage_eq_half_boolDistAdvantage`, smoke theorems `hiddenBitAdvantage_const`, `hiddenBitAdvantage_eq_zero_of_distEquiv`, evict wrapper `withEvict`, challenge-terminated adversary `ChalAdversary` in `Zkpc/Games/Framework.lean`, over VCV-io | L; `research_knowledge/vcvio-gap.md` (framework choice + what VCV-io provides) |
| 5.9 | T4 spend-unlinkability PROVED: `T4_flat_unlinkability` in `Zkpc/Games/T4.lean` shows advantage exactly 0 for every UNLINK adversary at every budget, over the session-form game (`unlinkGame`/`unlinkAdvantage`/`UnlinkScheme`, `Zkpc/Games/Unlink.lean`); challenge termination structural; close view simulatable from `(cm, count)` (`flat_closeViewSimulatable`, pinning the MC15 residue) | L; G gate B3 rounds 1–3 (agent sign-off only; human gate pending); K2 (axiom-clean) |
| 5.10 | T7 framing bound PROVED at the concrete secret-averaged query bound: `T7_frame_bound` retains the ≤1/\|F\| good-event lemma; for every `A` carrying `FrameQueryBounds`, `T7_frame_query_bound_unconditional` / `T7Certificate.ofQueryBounds` give `(q_A+q_E+q_Id+q_Nf·q_sig+q_sig²+1)/\|F\|` with no residual coupling or counting hypothesis. The route is `frameGoodSliceTransfer_of_tape` + `dsBadMassLe_of_queryBounds` + `frameRealBadMassLe_of_dsCount` → `frameDeferredSamplingAvg_holds`. `FrameAsymptotic.lean` supplies two conditional negligibility lifts: one assumes the explicit query/field-size ratio is negligible; its corollary assumes a polynomial numerator bound and negligible inverse field cardinality. Neither provides a PPT/runtime classifier or deployed-primitive reduction. The stronger pointwise certificate remains REFUTED (`frameDeferredSampling_refuted`, two-probe adversary, gate round 4); the proved statement is the uniform-secret average used by `frameGame`, not a pointwise-in-secret claim. | L; G gate B3 rounds 1–5 (agent review); completed K2/K5 release record |
| 5.11 | Calibration pair + battery PROVED in `Zkpc/Games/Calibration.lean`: `unlinkAdvantage_staticDistinguisher_eq_half` (B-static loses at ½), `unlinkAdvantage_bRerand_eq_zero` (B-rerand passes at 0); battery `unlinkAdvantage_aIndexLeak`, `unlinkAdvantage_nfeReuse`, `unlinkAdvantage_multTagDistinguisher_eq_half` each at ½ | L; K2 |
| 5.12 | Refund-bearing variant (B) safety PROVED in `Zkpc/Refund/`: `T1_B_no_overspend`, `T3_B_floor`, `conservation`, `self_slash_race_closed` (`Safety.lean`); full failed-upgrade cascade PROVED (`Cascade.lean`: `cascade_upgrades_le_understatement`, `cascade_settled_upgrades_eq`, `cascade_terminal_settled`, `cascade_final_payouts`, `execCascade_progress`); finite-fleet aggregation PROVED (`Fleet.lean`: `fleet_no_overspend`, `fleet_conservation`, `fleet_payer_floor`) | S §4, §7; L; K2 |
| 5.16 | Wire ZK bridges (O1) DISCHARGED zero-loss for three proof-bearing encodings: masked-proof (`T4_maskedProof_unlinkability`, `maskedProof_zkBridge`), interactive Sigma (`T4_sigmaFlat_unlinkability`, `sigmaFlat_zkBridge` over `Zkpc/Crypto/LinearSigma.lean`: completeness, exact simulator, `special_soundness`), lazy-ROM Fiat–Shamir (`T4_fsFlat_unlinkability`, `fsFlat_zkBridge` over `Zkpc/Crypto/FSRom.lean`: `evalDist_fsProveLazy_eq_simulated`, `fsProgramCollisionBound`, `fsForkChallengeCollisionBound`) | L; K2 |
| 5.17 | B-instance obligations O2/O3(M2)/O4 DISCHARGED: `bRerand_spendBatch_none_zero`, `bIdeal_openCh_adversary_genesis`, `bIdeal_serve_issuer_receipt`, `bIdeal_serve_capable_mono`, `bIdeal_closeViewSimulatable` (`Zkpc/Games/BInstances.lean`) | L; K2 |
| 5.18 | Refund crypto reference layers PROVED at their stated narrow interfaces: exact masked-cipher rerandomization/refund-update privacy (`Zkpc/Crypto/MaskedEncryption.lean`); additive ElGamal decryption, homomorphic-addition, rerandomization, and refund-update algebra with no DDH/IND-CPA theorem (`Zkpc/Crypto/ElGamal.lean`); and fixed-pair plus deterministic one-query affine-MAC bounds, including an `n/|F|` union bound for independently keyed instances with no shared key or cross-link attacker state (`Zkpc/Crypto/ReceiptMac.lean`). `AuthenticatedFleet.lean` packages that separate independent-key bound beside fleet accounting; it is not a reduction for the Spec-B shared-key receipt chain. | L; completed K2 capture |
| 5.19 | Fleet-side recovery rule (MC19) PROVED: eligibility, seniority, remainder caps, conservation, full-recovery, fund-slash forfeit (`Zkpc/Fleet/Recovery.lean`) | L; K2 |
| 5.20 | Executable refinement PROVED: executable open/spend/redeem/close/dispute/sweeps + MC20 contract drivers + refund accept/close/force-close + fleet tick/admission/slash all refine their relational `Step`s, so executable states inherit T1–T6 and refund/fleet invariants (`Zkpc/{Core,Refund,Fleet}/Refinement.lean`) | L; K2 |
| 5.21 | Multi-recipient network layer PROVED (definitional/accounting half of the named open problem): `no_overspend`, `global_dedup`, payout partitioning, view isolation (`Zkpc/Network/State.lean`); credential adapter with `redeem_rejects_global_replay` and `credential_payment_end_to_end` (`Zkpc/Network/Credential.lean`); threshold-issuance reference with `evalDist_blindRequest_uniform`, `ticket_fork_extracts`, `recipientView_unlinkable` (`Zkpc/Network/Issuance.lean`) | L; K2 |
| 5.23 | Instantiation C machine-checked (`Zkpc/Chain/`): safety (`chain_no_overspend`, `bob_never_loses`, `honest_close_exact`, `alice_refund_liveness`, `conservation`, `no_overpay_recovery`), collision exactness both directions (`stale_close_detectable`, `honest_close_unchallengeable`, `collision_iff_stale`, `honest_close_never_slashed`), per-request anonymity advantage = 0 (`chain_two_payment_anonymity`), executable refinement; signatures idealized as transition guards, chain collision-freedom an explicit injectivity hypothesis | L; K2-style axiom audit in-files |
| 5.22 | One-trace composition PROVED: `channel_endToEnd_composition` (settlement + exact floor + T1 + T2 + exculpability simultaneously on one reachable trace) and `wire_endToEnd_composition` (T4 = 0 with the zero-loss ZK bridge) in `Zkpc/Core/Composition.lean`; `flat_endToEnd_unconditional` (synchronized Core–Fleet–Network operational guarantees + scheme-level FS T4 + T7) and `refund_endToEnd_unconditional` (synchronized Refund–Network operational guarantees + scheme-level B-rerand T4 + T7) in `Zkpc/Composition/EndToEnd.lean`. The operational fields are trace-derived; the game claims are proved separately. Their T7 field is `T7Certificate.ofQueryBounds`, the secret-averaged `(qb.total+1)/|F|` finite-query statement for `FrameQueryBounds`; it is not derived from a PPT/runtime classifier or a deployed-primitive reduction. | L; completed final-endpoint K2 capture |
| 5.13 | Model boundary: protocol layer over an idealized ledger and idealized cryptography; ROM; circuits explicitly out of scope; "anyone claiming this repo verifies SNARKs is misreading it" | S §5 (verbatim wording) |
| 5.14 | The source contains no project `axiom` declarations; `Zkpc/Assumptions.lean` is audit data, not logic. Knowledge soundness and refund-receipt EUF-CMA are model guards (EUF supports T1-B/T2-B/T3-B); ZK is discharged by exact masked/Sigma/lazy-ROM-FS simulator lemmas; the ROM surface includes domain-separated `H_a`/`H_e`/`H_nf`/`H_x`/`H_id`; rerandomization and single-signal hiding are proved reference-layer properties. The completed final-endpoint `#print axioms` capture shows only propext/Quot.sound/Classical.choice. CI is configured to reject `sorry`, project-specific axioms, `admit`, and `native_decide`. | REPO `Zkpc/Assumptions.lean`; `.github/workflows/ci.yml`; completed K2 audit |
| 5.15 | Assumption 6 (blind signatures) is declared and deliberately unused | S §5.6; `Zkpc/Assumptions.lean` |

## §6 Honest limits

| # | Claim | Source |
|---|---|---|
| 6.1 | Recipient-boundness: one deposit binds to one payee (fleet counts as one logical payee); this is the object's defining restriction, shared with ACT/ARC/Cashu | S §2 Open; R map (ACT/ARC/Cashu rows); BRIEF.md Deliverable 1 item 3 |
| 6.2 | Capital lockup per counterparty; channels don't pay for themselves below a frequency threshold | R deep dive 5 (Guasoni et al.); BRIEF.md item 3. Primary: https://pubsonline.informs.org/doi/10.1287/mnsc.2022.01664 |
| 6.3 | Funding-graph leakage at Open (public ledger event; KYC trail); shielded/Privacy-Pools-style funding as the prescribed mitigation, not modeled | S §5 out-of-scope; R deep dive 1 (a) (dbrizz), Application design imports; BOLT's anonymized-capital requirement (R deep dive 2) |
| 6.4 | Spend-count-at-close side channel: j in B, cap − |U| in A — same information; not covered by T4 | S §8 MC15, §7 T4 what-is-NOT-claimed |
| 6.5 | Within-epoch linkability by design (epoch pseudonym is the rate-limiting mechanism); T4 scopes to a fresh epoch | S §8 MC6, §7 T4 |
| 6.6 | Window recovery presumes fleet honesty: member–gateway collusion can pre-checkpoint fake "service" and crowd out honest conflict claims; no theorem's adversary class covers corrupt gateways in the recovery role | S §8 MC19 honest-limits note (rev-3 R3-9) |
| 6.7 | Close racing: B exposure ≤ acceptance rate × τ; A in-flight acceptances structurally un-checkpointable | S §2 Close notes (rev-6); G round 6 |
| 6.8 | T6 recovery is remainder-capped and checkpoint-gated (exhaust-then-burst); f(L) < D does not guarantee recovery; no unprofitability claim | S §7 T6; G round 2 NEW-3, round 3 R3-3 |
| 6.9 | Abort/evict residue: eviction-to-insolvency shrinks the challenge-capable set; the game charges it to the anonymity set, not the scheme | S §7 T4 (⊥-branch) |
| 6.10 | Traffic-analysis fingerprints (timing, token counts, content) out of scope and a real re-linking surface | S §5; R deep dive 1 (b) (WGlynn). The ~96% re-linkage figure is omarespejel's own unreviewed simulation and is flagged as such | 
| 6.11 | x ≠ 0 domain-separation requirement on H_x | L `Zkpc/Games/RLN.lean` GATE-NOTE + `rln_x_zero_degenerate`; S §1 |
| 6.12 | Multi-recipient generalization is THE named open problem (what it would require: portable deposits or threshold issuance — the Nym-shaped hybrid — without re-fragmenting the anonymity set); the definitional/accounting half is now machine-checked (row 5.21), the adaptive multi-session composition and production threshold-signature reduction are not | BRIEF.md Deliverable 1 item 3; R Application (shape (b) costs; treasury-hub fallback, open problem 10); L |
| 6.13 | Static corruption only; adaptive corruption not modeled | S §8 MC10 |
| 6.14 | Clock skew not modeled (would enlarge the T6 budget by a small constant) | S §8 MC12 |

## §7 Reproducibility

| # | Claim | Source |
|---|---|---|
| 7.1 | Repo: github.com/dmarzzz/zk-payments-confetti | REPO (git remote) |
| 7.2 | Toolchain: leanprover/lean4:v4.30.0; mathlib tag v4.30.0 (manifest rev c5ea00351c28e24afc9f0f84379aa41082b1188f); VCV-io pinned @ 8f5dc4f2923cc47e39bc6ce21f71563cf7d19193 | REPO `lean-toolchain`, `lakefile.lean`, `lake-manifest.json` |
| 7.3 | Build: `lake exe cache get && lake build` | REPO lakefile + CI workflow |
| 7.4 | CI guardrails: grep-fail on `sorry` anywhere, `axiom` outside Assumptions.lean, `admit`/`native_decide` anywhere; full `lake build` on the pinned toolchain | REPO `.github/workflows/ci.yml` |
| 7.5 | Theorem-to-file map (as in §5 rows above) | L |
| 7.6 | TLA+ models of the flat and fleet state machines, including ablation configs (`ZkpcFleetNoBind.cfg`, `ZkpcFleetNoMergeEv.cfg`) replaying the MC14/MC17 counterexamples | REPO `tla/` directory (file names literal) |
| 7.7 | Agent gate record: eleven rounds on Spec.md (rev-1 → rev-11), five rounds on the Lean games (gate B3), plus agent K1/K3/K4 exercises, every counterexample logged; this is not independent human sign-off. K2 contains the completed final T7/composition/scaling/refund capture. | G (whole file); S header; K2 audit |

## Claims deliberately NOT made

- Completion of the independent human statement/game gate. The recorded
  adversarial gate rounds were agent simulations; human sign-off remains
  pending.
- A pointwise-in-secret T7 certificate, or a theorem deriving the query bound
  from a PPT/runtime adversary interface. The pointwise socket is
  kernel-refuted. The proved finite result is the concrete uniform-secret
  average `(qb.total+1)/|F|` for adversaries carrying `FrameQueryBounds`.
  `FrameAsymptotic.lean` also proves two conditional negligibility transfers:
  one assumes the explicit query/field-size ratio is negligible; its
  corollary assumes a polynomial numerator bound and negligible inverse field
  cardinality. Neither derives its premises from a runtime classifier or a
  concrete field family.
- Deployment-grade cryptography behind the ideal reference layers: a
  concrete hash-implementation reduction for the lazy-ROM Fiat–Shamir
  layer, multi-query EUF-CMA signature/MAC reductions, a production
  threshold-signature unforgeability reduction, and the adaptive
  multi-session network game connecting the per-session issuance
  distributions to executable traces.
- "First machine-checked unlinkability result" is claimed as a
  *spend-unlinkability* result for the flat-ticket ideal model ("to our
  knowledge"); it is not claimed against circuits (out of the model
  boundary) nor as a survey-complete priority claim.
- omarespejel's ~96% re-linkage figure as fact (his own unreviewed
  simulation; R residual list).
- ACT deployment interest by Cloudflare/Google (unsourced; R residual list).
- Guasoni et al.'s r^(−1/2)/r^(−1/3) collateral exponents (unverified
  against the paywalled text; only the frequency-threshold verdict is used).
- Nym's reconciliation cadence/penalties (undocumented; "bounded race
  window" is inference and is labeled as such if mentioned).
- AMHL adoption by Lightning as current fact.
- Attacker unprofitability or universal recovery in T6 (the spec explicitly
  disclaims both).
- Any statement that the repo verifies SNARKs/circuits (S §5 forbids).
