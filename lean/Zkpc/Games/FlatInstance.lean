import Zkpc.Games.Coupling

/-!
# The flat-ticket UNLINK instance (task F1; Spec.md §4 instantiation A, §7 T4)

The ideal-model `UnlinkScheme` for **instantiation A** — the flat RLN
payment ticket — analysed in the ROM. This is the instance the headline
theorem `Zkpc.Games.T4.T4_flat_unlinkability` runs on: every adversary has
UNLINK advantage exactly `0`.

## The π-free ideal view (M1 route, `zkBridgeObligation`)

A ticket's adversary-visible content is `View = (nf_e, x, y, nf)`
(`FlatView`): the epoch pseudonym `nf_e`, the message digest `x = H_x(m)`,
the signal value `y = k + H_a(k,i)·x`, and the per-index nullifier
`nf = H_nf(H_a(k,i))` (Spec.md §1, §3 relation `R_spend^A`). The proof `π`,
the membership `root`, and the epoch tag `e` are dropped, per the documented
`zkBridgeObligation` disposition (Spec.md §5 assumption 2, nizkZeroKnowledge;
`Zkpc.Games.zkBridgeObligation`): `π` is simulatable (removing it *is* the
simulation), while `root`/`e` are common to both candidates and
adversary-computable, so a reduction reinserts them without knowing `b`.
`nf_e` is retained (it is the epoch-linkability surface the freshness
predicate exists for).

## The ideal ROM observables (prfRomIdealization + singleSignalHiding)

Under the random-oracle idealisation of the hash family (Spec.md §5
assumption 3) each of `nf_e`, `y`, `nf` is a fresh-uniform random-oracle
output keyed on `(k, index)` / `(k, epoch)`. Because the honest emission
consumes a *fresh* index at every spend (the index counter strictly
increases; `MC2` retries replay the stored ticket via `lastTicket` rather
than re-querying), each key is queried at most once on the honest path, so
the lazy-random-oracle value is distributionally a fresh independent uniform
draw. We therefore sample `nf_e`, `y`, `nf` fresh per emission directly (the
`randomOracle` idiom collapsed to its honest-path marginal). `y` is the
ideal form of `singleSignalHiding`: with a fresh-uniform slope `a` and a
digest `x ≠ 0`, `y = k + a·x` is uniform and independent of `k`, so the
ideal observable is a fresh uniform value (`Zkpc.Games.rln_single_point_hiding`
is the algebraic core; the `x = 0` degenerate point is excluded by the
`H_x`-domain-separation the RLN file prescribes). `x = H_x(m)` is modelled as
the identity digest (`M := F`, `x := m`): `H_x` is a public deterministic map
carrying only the adversary-chosen message, identical for both candidates,
and UNLINK gives the adversary no `H_x` oracle to distinguish it from a
"real" digest — so a deterministic digest loses no adversary power while
making the two candidates' `x`-components coincide exactly.

GATE-NOTE (epoch pseudonym freshness, MC6): the flat instance samples `nf_e`
fresh *per emission* rather than sharing one `nf_{e}` across a whole epoch
session. This is the maximally-hiding ideal and it is what makes the
challenge-response coupling hold at *every* game state (see
`Zkpc.Games.unlinkAdvantage_eq_zero_of_challenge_bitfree`, which quantifies
over all states with no reachability invariant, so no state-carried epoch
pseudonym could be relied upon to be fresh). Within-session linkage via a
shared `nf_{e^*}` is "by design" (MC6) and is exactly the property the
adversary already knows about the challenge batch (it *is* one session), so
independent per-emission pseudonyms only *increase* hiding; the real
scheme's `nf_e = H_e(k,e)` is bridged to this ideal via `prfRomIdealization`
plus the challenge epoch's freshness (its pseudonym slot is unqueried
pre-challenge).

GATE-NOTE (deposit fold): instantiation A has no receipt-grown refund
(`serve` is a no-op), so the deposit bound `(j+q)·C ≤ D` of Spec.md T4 is a
*static* cap `j + q ≤ budget` with `budget = ⌊D/C⌋` the number of affordable
spends. The instance is parameterised directly by `budget`.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [SampleableType F]

/-! ## The flat ticket view and payer state -/

/-- Adversary-visible content of one flat RLN ticket (Spec.md §1, §3
`R_spend^A`): epoch pseudonym `nf_e`, message digest `x = H_x(m)`, signal
value `y = k + a·x`, per-index nullifier `nf = H_nf(a)`. The proof `π`, the
membership `root`, and the epoch tag `e` are dropped per the
`zkBridgeObligation` disposition (module docstring). -/
structure FlatView (F : Type) : Type where
  /-- epoch pseudonym `nf_e` (ideal fresh-uniform RO output) -/
  nfe : F
  /-- message digest `x = H_x(m)` (identity digest, `x := m`) -/
  x : F
  /-- signal value `y = k + a·x`, ideal form: fresh uniform (`singleSignalHiding`) -/
  y : F
  /-- per-index nullifier `nf = H_nf(a)` (ideal fresh-uniform RO output) -/
  nf : F

/-- Candidate payer state for the flat instance: the next unused spend index
and the `MC2` retry buffer (the last emitted ticket). No refund state — `A`
has no certified refund chain. -/
structure FlatPSt (F : Type) : Type where
  /-- next unused spend index (emission consumes, MC2) -/
  idx : ℕ
  /-- MC2 retry buffer: the last emitted ticket view -/
  last : Option (FlatView F)

/-- Sample a list of `n` independent fresh-uniform field elements — the ideal
form of the close's unused-nullifier enumeration `U` (Spec.md MC20: the
revealed nullifiers are PRF-fresh values). -/
def freshFList : ℕ → ProbComp (List F)
  | 0 => pure []
  | n + 1 => do
      let a ← ($ᵗ F)
      let rest ← freshFList n
      pure (a :: rest)

/-- The flat-instance spend, factored out so it unfolds cleanly. If the payer
has budget for another spend (`idx < budget`) it emits a ticket whose
components are fresh-uniform ideal RO outputs (`nf_e`, `y`, `nf`) with
`x := m` the identity digest, and advances the index; otherwise it is
insolvent and outputs `⊥` (Spec.md §2: `Spend` outputs ⊥ on insolvency). -/
def flatSpend (budget : ℕ) (st : FlatPSt F) (m : F) :
    ProbComp (Option (FlatView F × FlatPSt F)) :=
  if st.idx < budget then do
    let nfe ← ($ᵗ F)
    let y ← ($ᵗ F)
    let nf ← ($ᵗ F)
    let v : FlatView F := ⟨nfe, m, y, nf⟩
    pure (some (v, ⟨st.idx + 1, some v⟩))
  else
    pure none

/-- **The flat-ticket ideal `UnlinkScheme` (instantiation A).** `View` is the
π-free ideal ticket; every random component is a fresh-uniform RO output; the
solvency cap is the static `budget`. Discharges O3 trivially
(`GenesisInput := PUnit`, `openCh` ignores it and never fails) and A has no
`serve` effect (no refund chain). -/
def flatInstance (budget : ℕ) : UnlinkScheme where
  M := F
  View := FlatView F
  CloseView := List F
  OpenView := PUnit
  GenesisInput := PUnit
  Receipt := PUnit
  PSt := FlatPSt F
  openCh _ := pure (⟨0, none⟩, PUnit.unit)
  spend _e st m := flatSpend budget st m
  lastTicket st := st.last
  serve st _ρ := st
  close _e st := do
    let U ← freshFList (budget - st.idx)
    pure (U, st)
  capableFor q st := decide (st.idx + q ≤ budget)

/-! ## The challenge-batch coupling -/

/-- The ideal challenge-batch distribution: `|ms|` fresh-uniform tickets with
`x := m` per message. State-free by construction — this is the whole content
of the flat instance's perfect unlinkability, since the batch a candidate
emits depends only on the message vector and fresh randomness, never on which
candidate (or its history) emitted it. Structurally all-`some` (no `⊥`),
which discharges O2. -/
def flatFreshBatch : List F → ProbComp (Option (List (FlatView F)))
  | [] => pure (some [])
  | m :: ms => do
      let nfe ← ($ᵗ F)
      let y ← ($ᵗ F)
      let nf ← ($ᵗ F)
      Option.map (⟨nfe, m, y, nf⟩ :: ·) <$> flatFreshBatch ms

/-- **The batch coupling (T4 secure core).** On any state solvent for the
whole batch (`idx + |ms| ≤ budget`), the flat instance's challenge batch has
the state-independent distribution `flatFreshBatch ms`. Two candidate states
therefore produce identically distributed batches — the ideal-model
coupling. Also discharges the Mi3 branch: the batch never returns `⊥` (its
distribution is `flatFreshBatch`, structurally all-`some`; see
`flat_spendBatch_none_zero`). -/
lemma evalDist_spendBatch_flat (budget e : ℕ) :
    ∀ (ms : List F) (st : FlatPSt F), st.idx + ms.length ≤ budget →
      𝒟[spendBatch (flatInstance (F := F) budget) e st ms] = 𝒟[flatFreshBatch ms] := by
  intro ms
  induction ms with
  | nil => intro st _; rfl
  | cons m ms ih =>
    intro st hst
    have hlen : st.idx + (ms.length + 1) ≤ budget := by simpa using hst
    have hsolv : st.idx < budget := by omega
    simp only [spendBatch, flatInstance, flatSpend, flatFreshBatch, if_pos hsolv,
      bind_assoc, pure_bind]
    simp only [evalDist_bind]
    refine bind_congr fun nfe => bind_congr fun y => bind_congr fun nf => ?_
    exact evalDist_map_eq_of_evalDist_eq
      (ih ⟨st.idx + 1, some ⟨nfe, m, y, nf⟩⟩
        (by show st.idx + 1 + ms.length ≤ budget; omega)) _

/-! ## O2: batch totality on solvent states -/

/-- The ideal batch never outputs `⊥`: `none` is not in its support. -/
lemma flatFreshBatch_none_not_mem (ms : List F) :
    none ∉ support (flatFreshBatch (F := F) ms) := by
  induction ms with
  | nil => simp [flatFreshBatch]
  | cons m ms ih =>
    intro hmem
    simp only [flatFreshBatch] at hmem
    obtain ⟨nfe, -, hmem⟩ := (mem_support_bind_iff _ _ _).1 hmem
    obtain ⟨y, -, hmem⟩ := (mem_support_bind_iff _ _ _).1 hmem
    obtain ⟨nf, -, hmem⟩ := (mem_support_bind_iff _ _ _).1 hmem
    rw [support_map, Set.mem_image] at hmem
    obtain ⟨l, hl, hmap⟩ := hmem
    cases l with
    | none => exact ih hl
    | some x => simp at hmap

/-- **O2 discharge (Mi3, session form).** On a state solvent for the whole
batch, the flat instance's challenge batch is total: it returns `⊥` with
probability `0`, so `capableFor q` guarantees all `q` batch spends succeed
(Spec.md T4, `challengeResp`/`spendBatch` Mi3 obligation). -/
theorem flat_spendBatch_none_zero (budget e : ℕ) (ms : List F) (st : FlatPSt F)
    (h : st.idx + ms.length ≤ budget) :
    Pr[= none | spendBatch (flatInstance (F := F) budget) e st ms] = 0 := by
  rw [probOutput_congr rfl (evalDist_spendBatch_flat budget e ms st h),
    probOutput_eq_zero_iff]
  exact flatFreshBatch_none_not_mem ms

/-! ## Challenge-response bit-freeness -/

/-- Extract the two candidates' batch-solvency facts from a passing
`challengeCapable` check. -/
private lemma flat_capable_of_challengeCapable (budget : ℕ)
    (g : GSt (flatInstance (F := F) budget)) (q : ℕ)
    (h : challengeCapable (flatInstance (F := F) budget) g q = true) :
    (g.cand false).idx + q ≤ budget ∧ (g.cand true).idx + q ≤ budget := by
  simp only [challengeCapable, flatInstance, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2.2⟩

/-- **Challenge-response is hidden-bit-independent at every game state.** The
guard (`epochFresh`, `challengeCapable`) does not mention `b`; on the passing
branch both candidates are batch-solvent, so both batches equal
`flatFreshBatch ms` (the batch coupling), hence coincide. This is the exact
hypothesis `unlinkAdvantage_eq_zero_of_challenge_bitfree` consumes. -/
theorem challengeResp_flat_bitfree (budget : ℕ)
    (g : GSt (flatInstance (F := F) budget)) (ms : List F) (b b' : Bool) :
    𝒟[challengeResp (flatInstance (F := F) budget) g b ms] =
      𝒟[challengeResp (flatInstance (F := F) budget) g b' ms] := by
  unfold challengeResp
  split_ifs with hcond
  · have hcap : challengeCapable (flatInstance (F := F) budget) g ms.length = true := by
      simp only [Bool.and_eq_true] at hcond; exact hcond.2
    obtain ⟨hf, ht⟩ := flat_capable_of_challengeCapable budget g ms.length hcap
    rw [evalDist_spendBatch_flat budget g.epoch ms (g.cand b)
        (by cases b <;> assumption),
      evalDist_spendBatch_flat budget g.epoch ms (g.cand b')
        (by cases b' <;> assumption)]
  · rfl

/-! ## O4: CloseView simulatability -/

/-- **O4 discharge (MC15, rev-9 K4 Concern 2).** The close view — the ideal
unused-nullifier enumeration `U` — is simulatable from the spend count alone:
`|U| = budget − idx` fresh-uniform values, replayed by the simulator from the
count (`cm` and the epoch are ignored). This pins the close leak to exactly
the MC15 residue (the spend count) and excludes a close publishing *used*
nullifiers. Stated over all payer states. -/
theorem flat_closeViewSimulatable (budget : ℕ) :
    closeViewSimulatable (flatInstance (F := F) budget) PUnit
      (fun _ => PUnit.unit) (fun st => budget - st.idx) := by
  refine ⟨fun _ n _ => freshFList n, ?_⟩
  intro e st
  simp [flatInstance, map_eq_bind_pure_comp, Function.comp]

end Zkpc.Games
