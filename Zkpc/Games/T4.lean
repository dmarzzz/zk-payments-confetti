import Zkpc.Games.FlatInstance

/-!
# T4-A — Spend unlinkability, the headline (tasks F1–F3; Spec.md §7 T4)

The headline theorem of the development: against the flat-ticket ideal
instantiation A (`Zkpc.Games.FlatInstance.flatInstance`), **every** UNLINK
adversary has advantage exactly `0`.

## F1 — the theorem

`T4_flat_unlinkability : unlinkAdvantage (flatInstance budget) A = 0` for
every adversary `A` and every deposit budget. Spec.md T4's advantage is
`Adv = |Pr[b' = b] − 1/2|` (`Zkpc.Games.unlinkAdvantage = guessGap`), so the
theorem is the strongest possible unlinkability statement: perfect
indistinguishability, not merely negligible advantage.

The proof route (the E1 survey's recommendation, specialised): the UNLINK
game is constructed so the hidden bit `b` is consulted *only* in the
challenge move `challengeResp … b …`; the entire pre-challenge world handler
`unlinkImpl` is one handler shared by both bits. So the full
`DistEquiv.of_step` per-query coupling of the OTP-HeapBasic template
(`.lake/packages/VCVio/Examples/OneTimePad/HeapBasic.lean`) collapses to a
single obligation — that `challengeResp` is distributionally
bit-independent at every game state — discharged here by
`challengeResp_flat_bitfree`. The crux coupling is the batch coupling
`evalDist_spendBatch_flat`: on any batch-solvent state the challenge batch
has the state-independent distribution `flatFreshBatch ms`, so `P_0`'s and
`P_1`'s challenge sessions are identically distributed. The
`b`-first-sampling repair (rev-1) makes this exact: `unlinkGame` binds `b`
before anything reads it (`unlinkGame_eq_decide_unlinkRun`), and the
uniform-bit averaging lemma `probOutput_decide_eq_uniformBool_half` then
yields `Pr[b' = b] = 1/2` on the nose. No `DistEquiv` typeclass friction
arose, so the documented fallback (per-bit `GameEquiv`/`probOutput`) was not
needed; the coupling in `Zkpc.Games.Coupling` *is* that plainer route,
already reduced to the one challenge obligation.

## F2 — reduction hygiene (assumptions discharged, axioms clean)

`#print axioms T4_flat_unlinkability` lists only Lean's own
`propext`/`Classical.choice`/`Quot.sound` — no proof escape hatches and no
declared assumptions (K2 audit clean). Which named entries of
`Zkpc.Assumptions.Named` this ideal model discharges, and how:

* **`nizkZeroKnowledge`** — the ticket `View` carries no proof object `π`
  (nor `root`, `e`); removing `π` from the view *is* the simulation
  (`Assumptions` table row 2). The residual full-ticket obligation is the
  M1 `zkBridgeObligation` between a `π`-carrying `Sfull` and this proof-free
  instance, whose disposition (π simulatable; `root`/`e`
  adversary-computable and candidate-common) is recorded on `flatInstance`
  and in `Zkpc.Games.zkBridgeObligation`.
* **`prfRomIdealization`** — every random ticket component (`nf_e`, `y`,
  `nf`) is a fresh-uniform random-oracle output, sampled directly because
  each honest `(k, index)`/`(k, epoch)` key is queried at most once (the
  index counter strictly increases; MC2 retries replay `lastTicket`).
* **`singleSignalHiding`** — `y = k + a·x` with a fresh-uniform slope and a
  nonzero digest is uniform and independent of `k`; the ideal observable is
  a fresh uniform value (`Zkpc.Games.rln_single_point_hiding` is the
  algebraic core; the `x = 0` degenerate point is excluded by the
  `H_x`-domain-separation `Zkpc.Games.RLN` prescribes).

Per-instance obligations discharged for the flat instance:
`Zkpc.Games.flat_spendBatch_none_zero` (O2 — batch totality on solvent
states), `Zkpc.Games.flat_closeViewSimulatable` (O4 — CloseView simulatable
from the spend count), and O3 trivially (`GenesisInput := PUnit`, `openCh`
never fails).

## F3 — the gate record

For the gate/paper: the flat-ticket instantiation A achieves
information-theoretically perfect spend unlinkability in the ideal ROM
model, for adversaries with the full pre-challenge abort/evict power of the
BOLT §1.4 oracle (native to the UNLINK oracle surface) and adversary-chosen
session length `q ≥ 1` (rev-9 session form). The two honest limits Spec.md
T4 states are *not* over-claimed: within-session linkage via `nf_{e^*}` is
by design (MC6; the challenge batch is one session), and the aggregate spend
count revealed at close is the MC15 side channel the theorem does not cover
(pinned to exactly `(cm, count)` by `flat_closeViewSimulatable`). The paper's
honest-limits section carries both.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [SampleableType F]

/-- **T4-A, the headline (Spec.md §7 T4, instantiation A).** For every
deposit budget and every UNLINK adversary, the flat-ticket ideal instance
has spend-unlinkability advantage `|Pr[b' = b] − 1/2|` equal to exactly `0`:
perfect indistinguishability. Discharged by the challenge-response coupling
`challengeResp_flat_bitfree` (both candidates emit the state-independent
ideal batch `flatFreshBatch`) fed to the must-pass closer
`unlinkAdvantage_eq_zero_of_challenge_bitfree`. See the module docstring for
the F2 assumptions ledger and the M1/O2/O3/O4 obligation dispositions. -/
theorem T4_flat_unlinkability (budget : ℕ)
    (A : UnlinkAdversary (flatInstance (F := F) budget)) :
    unlinkAdvantage (flatInstance (F := F) budget) A = 0 :=
  unlinkAdvantage_eq_zero_of_challenge_bitfree (flatInstance (F := F) budget) A
    (fun g ms b b' => challengeResp_flat_bitfree budget g ms b b')

end Zkpc.Games

-- F2 kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.T4_flat_unlinkability
