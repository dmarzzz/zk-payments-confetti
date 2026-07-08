# Open proofs

This is the worklist for anyone (human or agent swarm) picking up the Lean
verification. It lists what is already proved, the general classes the
proofs fall into with a worked template for each class, and the specific
open obligations ranked by value. Everything here builds on frozen
definitions: `Spec.md` is the trust surface and was signed off after
eleven rounds of adversarial review, and the security games under
`Zkpc/Games/` are signed off too, so a contribution proves theorems
*against* those definitions rather than changing them. If a proof cannot
go through as stated, that is a finding about the definition, and it goes
to the gate record (`research_knowledge/gates.md`), not into a weakened
statement.

## Ground rules for a contribution

- Toolchain is pinned: `leanprover/lean4:v4.30.0`, mathlib v4.30.0, VCV-io
  at `8f5dc4f`. `lake exe cache get` then `lake build`. This repo's Lake is
  5.0.0 and has no `-j` flag; cap parallelism with `LEAN_NUM_THREADS=N`.
- Zero `sorry`, zero `admit`, zero `native_decide`, and no `axiom` outside
  `Zkpc/Assumptions.lean` (which itself declares none: the crypto
  assumptions are discharged by the shape of the idealized model). CI greps
  for all four on every push, including inside comments, so do not write
  the bare token words in docstrings.
- Every theorem carries an English docstring restating it and citing its
  `Spec.md` clause. The statement is the contract; make it a faithful
  transcription.
- Verify with `#print axioms <thm>`: a finished proof depends on only
  `propext`, `Classical.choice`, `Quot.sound`.

## What is already proved

All kernel-checked, axiom-clean (`research_knowledge/k2-axiom-audit.md`).

| Theorem | Lean name | File |
|---|---|---|
| T1 no-overspend | `Core.T1_no_overspend` | `Zkpc/Core/T1.lean` |
| Exculpability (honest never slashed / disputed) | `Core.honest_never_slashed`, `honest_close_undisputable`, `honest_settleVoid_never` | `Zkpc/Core/T1.lean` |
| T2 payee balance (exact settlement + collectability) | `Core.T2_paid_exact`, `T2_collectable`, `T2_settles_exactly` | `Zkpc/Core/T2.lean` |
| T3 payer balance (floor + never slashed) | `Core.T3_payer_balance_security` | `Zkpc/Core/T3.lean` |
| T5 closure liveness | `Core.T5_payer_close_liveness` | `Zkpc/Core/T5.lean` |
| T6 priced divergence (both clauses) | `Fleet.T6_priced_divergence`, `T6_slash_within_L`, `epochs_in_window` | `Zkpc/Fleet/{T6,Basic}.lean` |
| T4 spend unlinkability (advantage = 0, session form) | `Games.T4_flat_unlinkability` | `Zkpc/Games/T4.lean` |
| T7 exculpability bound (conditional, see below) | `Games.T7_frame_bound` | `Zkpc/Games/T7.lean` |
| Calibration pair (B-static loses 1/2, B-rerand passes 0) | `Games.unlinkAdvantage_staticDistinguisher_eq_half`, `unlinkAdvantage_bRerand_eq_zero` | `Zkpc/Games/Calibration.lean` |
| Battery + FRAME must-win breaks | `Games.unlinkAdvantage_{aIndexLeak,nfeReuse,multTagDistinguisher_eq_half}`, `frameWinProb_{YK,aReuse}_eq_one` | `Zkpc/Games/{Calibration,T7}.lean` |
| RLN algebra | `Games.rln_recover_k`, `rln_single_point_hiding`, `rln_evidence_sound` | `Zkpc/Games/RLN.lean` |
| Refund safety (T1-B, T3-B, conservation) | `Refund.T1_B_no_overspend`, `T3_B_floor`, `conservation`, `self_slash_race_closed` | `Zkpc/Refund/Safety.lean` |

## The five proof classes (with a template each)

Every open obligation below is one of these shapes. If you have written
proofs of one shape before, the template is the file to read first.

**Class A: safety invariant over a labelled transition system.** Define a
conjunctive invariant, prove it holds at `init`, prove each transition
preserves it, then read the target off it. Induction is on the reachability
predicate (`Reach` / `FReach`). Template: `Zkpc/Core/T1.lean` (`reach_inv`
then `T1_no_overspend`). This class covers all of T1, T2, T3, T5, the T6
counting bound, and the refund safety layer.

**Class B: game-based perfect indistinguishability by RO coupling.** Reduce
"advantage against every adversary" to a single per-challenge
distributional-equality obligation, then discharge it by observing the view
components are fresh-uniform random-oracle samples on slots unqueried in
both worlds (so swapping the two candidates is a measure-preserving
bijection on the cache). Template: `Zkpc/Games/Coupling.lean`
(`unlinkAdvantage_eq_zero_of_challenge_bitfree`) plus
`Zkpc/Games/FlatInstance.lean` (`challengeResp_flat_bitfree`) and
`Zkpc/Games/T4.lean`. This is how the headline and B-rerand were proved.

**Class C: constructive distinguisher / must-win adversary.** Build one
explicit adversary and compute its advantage exactly. The trick is reducing
the concrete run to a closed form: in this codebase `pure_bind`/`map_pure`
do not fire on raw `OracleComp` terms, so run reductions use
`rw [<def>, <spend_eq>]; rfl` and defeq `show`, not `simp`. Template:
`Zkpc/Games/Calibration.lean` (`staticDistinguisher` and
`unlinkAdvantage_staticDistinguisher_eq_half`) and `Zkpc/Games/T7.lean`
(`frameWinProb_YK_eq_one`). This is how the calibration battery and the
FRAME breaks were built.

**Class D: reduction / union-bound / identical-until-bad (game hopping).**
Bound advantage by a chain of hops whose only gap is a named bad event,
then bound the bad event. This is the hardest class and where the biggest
open work sits. Partial template: `Zkpc/Games/T7.lean` (`frame_blind_bound`
gives the `1/|F|` term). VCV-io's `IdenticalUntilBad.lean` and the SecExp
hybrid lemmas are the machinery.

**Class E: field / algebra lemma.** Direct field computation, usually
`field_simp; ring` or a `Finset` support argument. Template:
`Zkpc/Games/RLN.lean`.

## Open obligations, ranked

### 1. T7 unconditional bound (Class D, highest value, hardest)

`Zkpc/Games/T7.lean` proves the FRAME slash probability `≤ 1/|F|` **only
under the hypothesis `hobliv`** (the adversary's evidence distribution is
independent of the secret, i.e. no random-oracle query hit `k`). `Spec.md`
T7 asks for the unconditional `negl(λ)` bound. The obligation: discharge
`hobliv` by a lazy-RO identical-until-bad argument over an unbounded
interactive adversary, bounding the query terms, so `T7_frame_bound`
becomes the unconditional `(q_A + q_Id + q_E + 1) / |F|`. This is the
single most valuable open proof, the "hard 20%" the VCV-io survey
(`research_knowledge/vcvio-gap.md`) flagged. Start from `frame_blind_bound`
and VCV-io `IdenticalUntilBad`.

### 2. The ZK bridge, O1 (Class D, high value)

`Zkpc.Games.zkBridgeObligation` is stated but not discharged for a concrete
instance. Prove, for a full-ticket instance `Sfull` carrying the NIZK proof
`π`, that advantage against its game is at most advantage against the
proof-free `flatInstance` plus the scheme's zero-knowledge distinguishing
advantage (Spec.md assumption 2). This is what lets the perfect
`T4_flat_unlinkability` (proved on the π-free view) speak about the real
wire protocol. See the disposition in `Zkpc/Games/FlatInstance.lean` and
`Zkpc/Games/T4.lean`.

### 3. B-instance obligations O2 / O3 / O4 (Class B/C, medium)

For the refund instantiation: the adversary-issued-genesis discharge
(`M2` / O3), and the `closeViewSimulatable` discharge for true-count B
closes (`O4`). Both are stated obligations in the games register
(`Zkpc/Games/README-games.md`); each is a concrete-instance proof against
the frozen game.

### 4. The challenge-fires lemma (Class B, small, good first task)

K3 (`research_knowledge/k3-vacuity-review.md`) recommends adding an in-tree
lemma `challengeResp (flatInstance …) = pure (some …)` for a satisfying
configuration, so the headline's non-vacuity (the challenge actually
produces a real ticket batch) is kernel-checked rather than traced by
review. Small, self-contained, and it hardens the headline; a good way to
learn the game plumbing.

### 5. Refund cascade and fleet-side settlement (Class A, medium)

`Zkpc/Refund/` models one close-dispute round at `N = 1`. Extend it to the
full upgrade sub-window cascade (`Spec.md` §2, the receipt-withholding
repair) and to the multi-gateway fleet. Separately, the fleet-side T2
recovery clauses (identity- vs fund-slash window claims, `Spec.md` MC19)
exist as prose and an `N = 1` core; lift them to the fleet transition
system (the `Zkpc/Fleet/` machine is the place).

### 6. Multi-recipient generalisation (research, not just proof)

The named open problem: the object is single-recipient by construction.
What a multi-recipient generalisation requires is stated in the paper's
open-problems section and `RESEARCH.md`. This is a definition-design task
first, then a proof task, and it would re-open the gate.

## Where the definitions and their rationale live

- `Spec.md`: the object, the games, the seven theorems, and the modeling
  choices (MC1..MC20), each tied to a counterexample that forced it.
- `research_knowledge/gates.md`: the eleven-round review record, so you can
  see why every clause is the way it is before you try to prove around it.
- `Zkpc/Games/README-games.md`: the obligation register (O1..O4) and
  prover guidance specific to the game layer.
- `paper/`: the systematization and the theorem-to-file map at paper
  altitude.
