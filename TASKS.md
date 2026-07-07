# Tasks

The full implementation tree for the research line, from repo scaffold to a paper that answers the thread. Organized by workstream; each task has an ID, a one-line definition of done, and its dependencies. Human-gate tasks are marked 🚦. Milestone mapping is in `BRIEF.md`.

Status legend: `[ ]` todo · `[~]` in progress · `[x]` done · `[?]` blocked/needs decision.

---

## A. Scaffold and infrastructure

- [ ] **A1** Repo scaffold: `lakefile.lean`, `lean-toolchain` pinned, mathlib + VCV-io as deps, `Zkpc/` source root. DoD: `lake build` succeeds on an empty library.
- [ ] **A2** CI: GitHub Actions running `lake build` on the pinned toolchain. DoD: green check on a PR.
- [ ] **A3** CI guardrails: fail the build if `sorry` appears outside nothing (zero tolerance) or if `axiom` appears outside `Zkpc/Assumptions.lean`. DoD: a PR introducing either fails CI.
- [ ] **A4** `Assumptions.lean` skeleton: one axiom per crypto primitive (proof-system knowledge soundness, zk simulation, PRF/hash, EUF-CMA signature, blind-signature unforgeability+blindness), each with a docstring naming the standard property. DoD: file compiles, every axiom documented.
- [ ] **A5** Contributor doc `PROVING.md`: the model boundary in one page, how to add a theorem, what the human gates check, the `sorry`/axiom policy. DoD: a new executor can start from it alone.

## B. Specification and definitions (the trust surface)

- [ ] **B1** `Spec.md`: all seven theorem statements (T1-T7) in precise English, each with the adversary it holds against. Sourced from the egress post's wire-protocol + application sections and RESEARCH.md's application section — formalize *this* protocol, not a reinvention. 🚦 **Human gate.** DoD: reviewer who did not write it signs off.
- [ ] **B2** The abstract object: algorithm signatures Setup, Open, Spend, Redeem, Close, Dispute as Lean types (no bodies yet). DoD: type-checks; matches `Spec.md`.
- [ ] **B3** Security games as Lean definitions: balance-security game, spend-unlinkability game (with the abort/evict oracle for the adversarial payee), exculpability game. 🚦 **Human gate — this is the A2L risk surface.** DoD: games compile and each has an English docstring a human approved.
- [ ] **B4** Threat model doc: the adversary per theorem, what the idealized ledger provides, what is explicitly out of scope (circuits, network-level timing, global passive adversary). DoD: matches the games in B3.

## C. TLA+ model (M0.5, cheap insurance before Lean)

- [ ] **C1** TLA+ spec of the protocol state machine: states, actions (open, spend, nullifier-check, reconcile, slash, close). DoD: parses in TLC.
- [ ] **C2** Safety invariants in TLA+: no-overspend, no-double-accept, slash-only-on-real-double-spend. DoD: TLC finds no violation at small scope (N≤3 gateways, small deposit).
- [ ] **C3** Liveness properties: honest party can always close. DoD: TLC checks under fairness assumptions.
- [ ] **C4** Fleet extension: model N gateways with a lagged shared spent set; check the priced-divergence bound holds at small scope. DoD: TLC confirms extractable-value < D for modeled (L, r). Feeds T6.
- [ ] **C5** Record every bug TLC finds in `research_knowledge/tla-findings.md`. DoD: findings logged before the corresponding Lean work starts (they change the state model).

## D. Lean core: state model and safety theorems

- [ ] **D1** Channel/credit state model: deposit, monotone index, nullifier set, accepted-spend ledger, as Lean structures with the transition function. DoD: compiles; TLA+ findings from C reflected.
- [ ] **D2** **T1 No-overspend**: sum of accepted spends ≤ deposit, for the flat-ticket instantiation. DoD: proved, zero `sorry`, English docstring.
- [ ] **D3** **T2 Payee balance security**: honest payee closing gets exactly the sum of redeemed spends vs arbitrary payer. DoD: proved.
- [ ] **D4** **T3 Payer balance security**: honest payer loses at most authorized spends; remainder refundable at close. DoD: proved.
- [ ] **D5** Flat-ticket instantiation module: deposit D, flat price C, solvency (i+1)·C ≤ D, per-index nullifier, slash-on-reuse, as a concrete instance of the abstract object. DoD: instance satisfies the B2 signatures; D2-D4 discharge against it.

## E. Lean game framework (the reusable contribution)

- [ ] **E1** Survey VCV-io: what it provides for oracle/adversary modeling, what it lacks for indistinguishability games. DoD: a short note in `research_knowledge/vcvio-gap.md`.
- [ ] **E2** Adversary + oracle typeclasses on top of VCV-io. DoD: compiles; an example adversary type-checks.
- [ ] **E3** Advantage / indistinguishability bookkeeping: game pairs, advantage as a real, negligibility. DoD: a trivial game has provably-zero advantage as a smoke test.
- [ ] **E4** The abort/evict oracle as a reusable game component. DoD: pluggable into the unlinkability game; documented.
- [ ] **E5** Keep it under ~1000 lines of additions; refactor if over. DoD: line count checked in CI comment or PR note.

## F. Lean headline: unlinkability (T4)

- [ ] **F1** **T4 Spend unlinkability, flat-ticket**: adversarial payee with abort oracle cannot distinguish two candidate payers' challenge spend, under zk-simulation. DoD: proved, zero `sorry`. **The first machine-checked unlinkability proof for any channel/credit construction.**
- [ ] **F2** Reduction hygiene: the proof reduces cleanly to the named `Assumptions.lean` axioms, no hidden assumptions. DoD: audited; every step cites an axiom or a prior lemma.
- [ ] **F3** Docstring + English restatement of T4 for the human gate and the paper. DoD: reviewed.

## G. Lean fleet theorems (T6, T7 — the fleet's actual security)

- [ ] **G1** Distributed spent-set model: N gateways, per-gateway nullifier views, a reconciliation relation with lag L. DoD: compiles; matches the TLA+ C4 model.
- [ ] **G2** **T6 Priced divergence**: extractable double-spend value before detection ≤ f(L, r) < D. DoD: proved; the bound is explicit and matches C4.
- [ ] **G3** **T7 Exculpability under collusion**: N−1 colluding gateways cannot forge a double-spend proof against an honest member, from RLN line algebra. DoD: proved.
- [ ] **G4** RLN algebra lemmas: two signals on the same (secret, index) reveal the secret; one signal reveals nothing. DoD: proved, reused by T7 and the slash logic.

## H. Refund-bearing variant (M5 — answers Vitalik's actual use case)

- [ ] **H1** Refund-ticket state extension: server-signed refund total R, solvency (i+1)·C_max ≤ D + R. DoD: compiles as a second instantiation of the abstract object.
- [ ] **H2** Model both refund-total representations: static encrypted E(R) and re-randomized-with-proof-of-equivalence. DoD: both compile.
- [ ] **H3** **T4 on the refund variant** + the calibration test: unlinkability game *fails* against static E(R), *passes* against re-randomized. DoD: both directions proved; the failure is a real distinguisher, not an unproven `sorry`.
- [ ] **H4** T1-T3 re-discharged on the refund variant. DoD: proved.
- [ ] **H5** Self-slash-race note: formalize or at least state the condition (member races its own slash after consuming unclaimed service) and the mitigation (frequent claims / unclaimed-balance ceiling). DoD: documented; proved if tractable, open-problem'd if not.

## I. Closure liveness (T5 — stretch)

- [ ] **I1** **T5 Closure liveness**: under the idealized ledger with timeout, honest party always settles. DoD: proved, or explicitly deferred with the reason.

## J. The paper (SoK + definition)

- [ ] **J1** Outline + claims ledger: every claim mapped to a RESEARCH.md source or a theorem ID. DoD: no orphan claims.
- [ ] **J2** Definition section: the object, algorithms, security games, prose mirroring the Lean. DoD: matches B2/B3 exactly.
- [ ] **J3** Placement section + table: vs ACT/ARC, Accio/BlindHub, adaptor-sig foundations, with BOLT as origin and threat-model source; state what each lacks. DoD: every row cites a primary source.
- [ ] **J4** The construction(s): flat-ticket and refund variant, at paper altitude. DoD: consistent with the Lean modules.
- [ ] **J5** Results section: the theorems, what's machine-checked, the T4 first, the fleet theorems, honest scope. DoD: no claim exceeds what CI proves.
- [ ] **J6** Honest-limits section: recipient-boundness, capital lockup, funding-graph leakage, multi-recipient as the named open problem. DoD: written; does not oversell.
- [ ] **J7** Reproducibility appendix: repo URL, toolchain revision, `lake build` instructions, theorem-to-file map. DoD: a reader can rebuild from it.
- [ ] **J8** Two output formats: ethresear.ch long-form post, arXiv/eprint PDF. DoD: both render.

## K. Verification, review, delivery

- [ ] **K1** Independent statement audit: a second agent (and a human) reads only `Spec.md` + the games and confirms they say what's meant, before trusting any proof. 🚦 DoD: sign-off logged.
- [ ] **K2** Axiom audit: enumerate every axiom actually used, confirm each is a standard assumption, no accidental `admit`/`native_decide` escape hatches. DoD: audit note in repo.
- [ ] **K3** Adversarial proof review: a skeptic agent tries to find a vacuous theorem (true because a hypothesis is unsatisfiable) or a definition that trivializes T4. DoD: report; anything found becomes a task.
- [ ] **K4** External review of the *definitions* (the A2L lesson): solicit one outside cryptographer to attack the games, not the proofs. DoD: feedback incorporated or rebutted in writing.
- [ ] **K5** Full clean-room rebuild from a fresh checkout on a clean machine. DoD: green.
- [ ] **K6** Delivery package for the thread: repo made shareable (visibility decision 🚦), the post, the PDF, and a two-paragraph "what got proved" note for Ken/Vitalik. DoD: sent.
- [ ] **K7** Log the experiment's outcome against README's success/failure shapes (did definitions drift? trivial theorems? did Lean hold or fall back to SSProve?). DoD: `research_knowledge/experiment-outcome.md` written — this is the autoresearch result.

---

## Critical path

B1🚦 → B2 → B3🚦 → (C in parallel) → D1 → D2 → E → F1 (**the first**) → G → H3 (**the calibration test**) → J → K.

Everything in J (paper) can draft in parallel with D–I once B is frozen; K4 (external definition review) should start as early as B3 is stable, because it is the cheapest insurance against the one failure mode this field has already suffered.

## Sequencing notes

- Nothing downstream of B is safe to trust until B1 and B3 pass their human gates. Do not let proof work race ahead of frozen definitions.
- C (TLA+) is deliberately before D–G: it is hours, not days, and it catches state-model bugs that would otherwise be discovered expensively mid-proof.
- F1 is the headline and the riskiest Lean task; if it stalls, the documented fallback is SSProve (RESEARCH.md), and J can still ship with T1-T3, T6-T7 machine-checked and T4 pen-and-paper-plus-TLA+.
- H (refunds) is what makes the paper answer the thread rather than simplify it; treat it as required, not optional, for the delivery in K6.
