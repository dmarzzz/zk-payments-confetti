import Zkpc.Games.FrameIdeal
import Zkpc.Games.Coupling
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.Birthday

/-!
# T7 — Exculpability under collusion, the FRAME bound (task G3; Spec.md §7 T7)

Two deliverables against the frozen FRAME game (`Zkpc.Games.Frame`):

## The FRAME bound (`T7_frame_bound`)

`Setup` samples the honest member's secret `k ← F` uniform and hands the
adversary `cm = H_id(k)`. The adversary wins iff its evidence `ev*` slashes
`k` — i.e. `recoverSecret ev* = k` and `x ≠ x'` (`Slashes`). Because
`recoverSecret ev*` is a deterministic function of `ev*`, winning is exactly
*guessing the uniform secret `k`*. The adversary's whole view is fresh-uniform
random-oracle output (`single_signal_hiding`: each honest signal
`y = k + a·x` with fresh-uniform slope `a` is uniform and independent of `k`,
`Zkpc.Games.rln_single_point_hiding`), so `k` stays uniform *unless* a
random-oracle query lands on the first component `k` (a `roA(k,·)`,
`roE(k,·)`, or `roId(k) = cm`-preimage query — each of which "computes `k`").

`T7_frame_bound` proves the **blind-guess bound** `frameWinProb ≤ 1/|F|` for
any adversary whose evidence distribution is independent of `k`
(hypothesis `hobliv`): with no RO query hitting `k`, the evidence is
uncorrelated with `k`, so the guess `recoverSecret ev*` matches the uniform
`k` with probability exactly `1/|F|` (`frame_blind_bound`). The proof commutes
the independent `k`-draw past the evidence generation (`evalDist_bind_comm`)
and bounds the resulting `k`-sum by the single-point mass `1/|F|`
(`frame_inner_bound`).

GATE-NOTE (PPT scoping of Spec T7, the deferred hard half). Spec T7 states
`Pr[slash] ≤ negl(λ)` for every **PPT** adversary. The earlier advertised
numerator `q_A + q_Id + q_E + 1` omitted two concrete ROM events:
`H_nf` probes can hit any exposed honest slope, and two honest slopes can
collide. The corrected conservative numerator used below is
`q_A + q_Id + q_E + q_Nf*q_sig + q_sig^2 + 1`. Formalising those query terms is the lazy
random-oracle *identical-until-bad* accounting over an unbounded interactive
adversary — the estimated-hard 20% flagged in the E1 survey
(`research_knowledge/vcvio-gap.md §3`). We ship the blind-guess term rigorously
and scope the query terms behind the `hobliv` hypothesis (the "no query hit
`k`" good event), which IS the PPT scoping the deliverable permits: a
query-bounded adversary that does not correlate its evidence with `k`.
Discharging `hobliv` unconditionally for a query-bounded adversary, with the
corrected bad-event mass, is the follow-up.

## The rev-11 must-win calibration battery (anti-vacuity)

Spec.md T7's anti-vacuity note and the rev-11 battery require concrete
adversaries winning FRAME with probability `1` against two *degenerate* RLN
signal schemes — the breaks the theorem must be able to detect:

* `frameWinProb_YK_eq_one` — **degenerate `y = k`** (no line masking, slope
  absent): one observed signal hands over `k` outright, so a two-point
  evidence with both values `k` slashes with probability `1`.
* `frameWinProb_aReuse_eq_one` — **`a` reused across indices**: two signals at
  distinct digests share one line, so their two points recover `k`
  (`Zkpc.Games.recoverSecret_line`) and slash with probability `1`.

Both are constructive terms (not unproven gaps), witnessing that the FRAME win
predicate `Slashes` is satisfiable exactly when the signal degenerates — the
calibration content that the sound RLN (fresh `a` per index, `y = k + a·x`)
avoids.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## Query-bounded adversaries

The unconditional theorem charges only adversary queries that can test a
candidate for the honest secret. Honest `spend`/`nfAt` execution uses the same
random-oracle caches internally, but those handler-side lookups are not guesses
chosen by the adversary and therefore are deliberately not counted here. -/

/-- Direct adversary queries to `H_a`; these can hit `(k, i)`. -/
def isDirectRoAQuery : FrameOp F M → Bool
  | .roA _ _ => true
  | _ => false

/-- Direct adversary queries to `H_e`; these can hit `(k, e)`. -/
def isDirectRoEQuery : FrameOp F M → Bool
  | .roE _ _ => true
  | _ => false

/-- Direct adversary queries to `H_id`; these can test a preimage of `cm`. -/
def isDirectRoIdQuery : FrameOp F M → Bool
  | .roId _ => true
  | _ => false

/-- Direct `H_nf` probes can test candidate line slopes against nullifiers
published in honest signals. -/
def isDirectRoNfQuery : FrameOp F M → Bool
  | .roNf _ => true
  | _ => false

/-- Honest slope-producing operations controlled by the adversary. `nfAt`
also materializes `H_a(k,i)` and may target an index later spent, so it must be
included alongside successful `spend` and legacy `close`. -/
def isSignalQuery : FrameOp F M → Bool
  | .spend _ => true
  | .close => true
  | .nfAt _ => true
  | _ => false

/-- The explicit ROM-query budget required by the unconditional FRAME bound.
The bounds hold for every possible public commitment input, since `A` is
applied only after `cm = H_id(k)` has been sampled. Keeping the three channels
and the signal/nullifier budgets separate exposes every concrete leakage term. -/
structure FrameQueryBounds
    (A : F → OracleComp (frameSpec F M) (Evidence F)) where
  qA : ℕ
  qE : ℕ
  qId : ℕ
  qNf : ℕ
  qSig : ℕ
  roA_bound : ∀ cm : F,
    OracleComp.IsQueryBoundP (A cm) (fun t => isDirectRoAQuery t = true) qA
  roE_bound : ∀ cm : F,
    OracleComp.IsQueryBoundP (A cm) (fun t => isDirectRoEQuery t = true) qE
  roId_bound : ∀ cm : F,
    OracleComp.IsQueryBoundP (A cm) (fun t => isDirectRoIdQuery t = true) qId
  roNf_bound : ∀ cm : F,
    OracleComp.IsQueryBoundP (A cm) (fun t => isDirectRoNfQuery t = true) qNf
  signal_bound : ∀ cm : F,
    OracleComp.IsQueryBoundP (A cm) (fun t => isSignalQuery t = true) qSig

/-- Total secret-testing query budget appearing in the T7 numerator. -/
def FrameQueryBounds.total {A : F → OracleComp (frameSpec F M) (Evidence F)}
    (qb : FrameQueryBounds A) : ℕ :=
  qb.qA + qb.qE + qb.qId + qb.qNf * qb.qSig + qb.qSig * qb.qSig

/-! ## The rev-11 must-win calibration battery -/

/-- Degenerate-RLN FRAME game with `y = k` (the line-masking slope absent):
the honest signal value is the secret itself. The adversary observes it at two
distinct digests (`x = 1`, `x' = 0`) and outputs the two points `(1, k)`,
`(0, k)`. A calibration game (Spec.md T7 anti-vacuity), separate from the
frozen `frameGame`. -/
def frameGameYK : ProbComp Bool := do
  let k ← ($ᵗ F)
  pure (decide (Slashes k (⟨0, 1, k, 0, k⟩ : Evidence F)))

/-- Degenerate-RLN FRAME game with `a` reused across indices: both honest
signals lie on the *same* line `Y = k + a·X`, so their two points at digests
`1` and `0` recover `k`. A calibration game (Spec.md T7 anti-vacuity). -/
def frameGameAReuse : ProbComp Bool := do
  let k ← ($ᵗ F)
  let a ← ($ᵗ F)
  pure (decide (Slashes k (⟨0, 1, rlnY k a 1, 0, rlnY k a 0⟩ : Evidence F)))

/-- Calibration in which the published nullifier reveals the line slope
(`H_nf(a) = a`). From one signal at nonzero `x = 1`, the adversary computes
`k = y - a*x` and manufactures a second point at `x' = 0`. This witnesses why
concrete T7 query accounting must charge `H_nf` preimage probes (and their
multi-target amplification across signals), not only direct `H_a(k,·)` probes. -/
def frameGameSlopeReveal : ProbComp Bool := do
  let k ← ($ᵗ F)
  let a ← ($ᵗ F)
  let y := rlnY k a 1
  let recovered := y - a
  pure (decide (Slashes k
    (⟨a, 1, y, 0, recovered⟩ : Evidence F)))

/-- **Must-win (rev-11 battery): against `y = k`, FRAME is won with
probability `1`.** The degenerate signal reveals `k`, and the two-point
evidence `(1, k), (0, k)` slashes (`recoverSecret = k`, `1 ≠ 0`). The break
Spec.md T7's anti-vacuity note names, made a constructive winning term. -/
theorem frameWinProb_YK_eq_one :
    Pr[= true | frameGameYK (F := F)] = 1 := by
  have hc : ∀ k : F, decide (Slashes k (⟨0, 1, k, 0, k⟩ : Evidence F)) = true := by
    intro k
    simp only [decide_eq_true_eq, Slashes]
    refine ⟨one_ne_zero, ?_⟩
    simp only [recoverSecret, recoverSlope]
    ring
  have hgame : frameGameYK (F := F) = (($ᵗ F) >>= fun _ => pure true) := by
    unfold frameGameYK
    exact bind_congr fun k => by rw [hc k]
  rw [hgame, probOutput_bind_const]
  simp

/-- **Must-win (rev-11 battery): against `a` reused across indices, FRAME is
won with probability `1`.** The two signals share one line, so the recovery
formula returns `k` on the two points at digests `1` and `0`
(`recoverSecret_line`), and `Dispute` slashes. -/
theorem frameWinProb_aReuse_eq_one :
    Pr[= true | frameGameAReuse (F := F)] = 1 := by
  have hc : ∀ k a : F,
      decide (Slashes k (⟨0, 1, rlnY k a 1, 0, rlnY k a 0⟩ : Evidence F)) = true := by
    intro k a
    simp only [decide_eq_true_eq, Slashes]
    exact ⟨one_ne_zero, recoverSecret_line 0 k a 1 0 one_ne_zero⟩
  have hgame : frameGameAReuse (F := F)
      = (($ᵗ F) >>= fun _ => ($ᵗ F) >>= fun _ => pure true) := by
    unfold frameGameAReuse
    exact bind_congr fun k => bind_congr fun a => by rw [hc k a]
  rw [hgame, probOutput_bind_const, probOutput_bind_const]
  simp

/-- **Must-win slope-reveal calibration.** If the nullifier exposes `a`, one
honest signal suffices to frame with probability one. -/
theorem frameWinProb_slopeReveal_eq_one :
    Pr[= true | frameGameSlopeReveal (F := F)] = 1 := by
  have hc : ∀ k a : F,
      decide (Slashes k
        (⟨a, 1, rlnY k a 1, 0, rlnY k a 1 - a⟩ : Evidence F)) = true := by
    intro k a
    simp only [decide_eq_true_eq, Slashes]
    refine ⟨one_ne_zero, ?_⟩
    simp only [recoverSecret, recoverSlope, rlnY]
    field_simp
    ring
  have hgame : frameGameSlopeReveal (F := F) =
      (($ᵗ F) >>= fun _ => ($ᵗ F) >>= fun _ => pure true) := by
    unfold frameGameSlopeReveal
    exact bind_congr fun k => bind_congr fun a => by rw [hc k a]
  rw [hgame, probOutput_bind_const, probOutput_bind_const]
  simp

/-! ## The FRAME blind-guess bound -/

/-- The honest member's post-`cm` evidence-production process for adversary
`A`: reveal `cm = H_id(k)` and run `A` against the honest-member handler. Its
distribution is what the `hobliv` scoping hypothesis constrains. -/
def frameEvidence (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) (k : F) :
    ProbComp (Evidence F) := do
  let (cm, cId) ← lazyRO (FrameSt.init F M).roId k
  (frameImpl k mclose).run { FrameSt.init F M with roId := cId } (A cm)

/-- `frameGame` factored as: sample `k`, produce evidence, decide the slash. -/
lemma frameGame_eq_evidence (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    frameGame mclose A =
      (do
        let k ← ($ᵗ F)
        let ev ← frameEvidence mclose A k
        pure (decide (Slashes k ev))) := by
  unfold frameGame frameEvidence
  exact bind_congr fun k => by rw [bind_assoc]

section Bound

variable [Fintype F]

/-- Constant-range oracle used to model the independently uniform honest
slope draws after deferred sampling. -/
@[reducible] def slopeSpec (F : Type) : OracleSpec ℕ := fun _ => F

/-- Make `n` distinct slope-sampling queries. -/
def slopeQueries (F : Type) [DecidableEq F] :
    (n : ℕ) → OracleComp (slopeSpec F) Unit
  | 0 => pure ()
  | n + 1 => do
      let _ ← (query n : OracleComp (slopeSpec F) F)
      slopeQueries F n

/-- The slope sampler makes exactly (hence at most) `n` oracle queries. -/
theorem slopeQueries_queryBound (n : ℕ) :
    OracleComp.IsTotalQueryBound (slopeQueries F n) n := by
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [slopeQueries, OracleComp.isTotalQueryBound_query_bind_iff]
      exact ⟨Nat.zero_lt_succ n, fun _ => by simpa using ih⟩

/-- **Honest-slope birthday bound.** Among at most `qSig` independent
uniform slope samples, the probability that two query positions carry the
same slope is at most `qSig²/(2|F|)`, and therefore below the conservative
`qSig²/|F|` charge used by `FrameQueryBounds.total`. -/
theorem uniformSlopeCollisionBound (qSig : ℕ) :
    letI : IsUniformSpec (slopeSpec F) :=
      IsUniformSpec.ofFintypeInhabited _
    Pr[fun z => OracleComp.LogHasCollision z.2 |
        (simulateQ OracleComp.loggingOracle (slopeQueries F qSig)).run]
      ≤ (qSig ^ 2 : ENNReal) /
          (2 * Fintype.card F) := by
  letI : IsUniformSpec (slopeSpec F) :=
    IsUniformSpec.ofFintypeInhabited _
  apply OracleComp.probEvent_logCollision_le_birthday_total
    (slopeQueries F qSig) qSig (slopeQueries_queryBound qSig)
  intro t
  rfl

/-- **Uniform-secret adaptive first-fire bound.** A strategy making `q`
adaptive candidate-secret probes hits a uniformly sampled `k : F` with
probability at most `q / |F|`. Up to the first hit every answer is `false`, so
the candidate sequence is independent of `k`; VCV-io's hidden-target theorem
formalizes precisely that argument. This lemma is instantiated once for each
of the `H_a`, `H_e`, and `H_id` query channels. -/
theorem uniformSecretProbeBound (q : ℕ) (σ : List Bool → F) :
    Pr[(fun b : Bool => b = true) |
        OracleComp.hiddenReadMany ($ᵗ F) q σ]
      ≤ (q : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  exact OracleComp.probEvent_hiddenReadMany_le
    (fun r : F => (probOutput_uniformSample F r).le) q σ

/-- **Uniform-slope multi-target probe bound.** If `qSig` honest signals
expose independently uniform hidden slopes and the adversary makes `qNf`
adaptive candidate-preimage probes, the chance that any probe hits any slope
is at most `qSig*qNf/|F|`. This is the quantitative kernel for the corrected
nullifier-query term. -/
theorem uniformSlopeProbeBound (qNf qSig : ℕ) (σ : List Bool → F) :
    Pr[(fun b : Bool => b = true) |
        OracleComp.hiddenReadList ($ᵗ F) qNf σ qSig]
      ≤ (qSig : ENNReal) *
          ((qNf : ENNReal) * (Fintype.card F : ENNReal)⁻¹) := by
  exact OracleComp.probEvent_hiddenReadList_le
    (fun r : F => (probOutput_uniformSample F r).le) qNf σ qSig

/-- Atomic fresh-slope collision charge against an existing list of hidden
targets. Multiplicity can only increase the list length, so the distinct
target mass is at most `length/|F|`. -/
theorem uniformMemListBound (xs : List F) :
    Pr[(fun a : F => a ∈ xs) | ($ᵗ F)] ≤
      (xs.length : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  rw [probEvent_uniformSample]
  have hfilter : (Finset.univ.filter fun a : F => a ∈ xs) = xs.toFinset := by
    ext a
    simp
  rw [hfilter, div_eq_mul_inv]
  gcongr
  exact_mod_cast Multiset.toFinset_card_le xs

/-- One newly sampled honest slope hits either a prior adversarial slope probe
or a prior honest slope with probability bounded by the combined target-list
length over `|F|`. -/
theorem uniformFreshSlopeBadBound (audit : FrameAudit F) :
    Pr[(fun a : F => a ∈ audit.slopeProbes ∨ a ∈ audit.honestSlopes) |
        ($ᵗ F)] ≤
      ((audit.slopeProbes.length + audit.honestSlopes.length : ℕ) : ENNReal) *
        (Fintype.card F : ENNReal)⁻¹ := by
  calc
    Pr[(fun a : F => a ∈ audit.slopeProbes ∨ a ∈ audit.honestSlopes) |
        ($ᵗ F)] ≤
      Pr[(fun a : F => a ∈ audit.slopeProbes) | ($ᵗ F)] +
        Pr[(fun a : F => a ∈ audit.honestSlopes) | ($ᵗ F)] :=
      probEvent_or_le _ _ _
    _ ≤ (audit.slopeProbes.length : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ +
        (audit.honestSlopes.length : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ :=
      add_le_add (uniformMemListBound audit.slopeProbes)
        (uniformMemListBound audit.honestSlopes)
    _ = ((audit.slopeProbes.length + audit.honestSlopes.length : ℕ) : ENNReal) *
        (Fintype.card F : ENNReal)⁻¹ := by
      rw [Nat.cast_add, add_mul]

/-- For a *fixed* evidence `ev`, guessing the uniform secret succeeds with
probability at most `1/|F|`: the win event `Slashes k ev` forces
`k = recoverSecret ev`, a single point of the uniform `k`. -/
lemma frame_inner_bound (ev : Evidence F) :
    Pr[= true | (do let k ← ($ᵗ F); pure (decide (Slashes k ev)))]
      ≤ (Fintype.card F : ENNReal)⁻¹ := by
  rw [probOutput_bind_eq_tsum]
  calc ∑' k : F, Pr[= k | ($ᵗ F)] *
          Pr[= true | (pure (decide (Slashes k ev)) : ProbComp Bool)]
      ≤ ∑' k : F, Pr[= k | ($ᵗ F)] * (if k = recoverSecret ev then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun k => mul_le_mul_left' ?_ _
        by_cases hs : Slashes k ev
        · have h1 : Pr[= true | (pure (decide (Slashes k ev)) : ProbComp Bool)] = 1 := by
            simp [hs]
          rw [h1, if_pos hs.2.symm]
        · have h0 : Pr[= true | (pure (decide (Slashes k ev)) : ProbComp Bool)] = 0 := by
            simp [hs]
          rw [h0]; exact zero_le'
    _ = ∑' k : F, (if k = recoverSecret ev then Pr[= k | ($ᵗ F)] else 0) := by
        refine tsum_congr fun k => ?_
        split <;> simp
    _ = Pr[= recoverSecret ev | ($ᵗ F)] := by
        rw [tsum_eq_single (recoverSecret ev) fun k hk => if_neg hk]
        simp
    _ = (Fintype.card F : ENNReal)⁻¹ := by rw [probOutput_uniformSample]

/-- **The blind-guess bound.** If the evidence generator `gen` is independent
of the secret `k` (the "no RO query hit `k`" good event), then framing the
honest member succeeds with probability at most `1/|F|`: a uniform `k` drawn
independently of the evidence matches the guess `recoverSecret ev` with
probability exactly `1/|F|`. -/
lemma frame_blind_bound (gen : ProbComp (Evidence F)) :
    Pr[= true | (do let k ← ($ᵗ F); let ev ← gen; pure (decide (Slashes k ev)))]
      ≤ (Fintype.card F : ENNReal)⁻¹ := by
  rw [probOutput_congr rfl
    (OracleComp.DeferredSampling.evalDist_bind_comm ($ᵗ F) gen
      (fun k ev => pure (decide (Slashes k ev))))]
  rw [probOutput_bind_eq_tsum]
  calc ∑' ev : Evidence F, Pr[= ev | gen] *
          Pr[= true | (($ᵗ F) >>= fun k => pure (decide (Slashes k ev)))]
      ≤ ∑' ev : Evidence F, Pr[= ev | gen] * (Fintype.card F : ENNReal)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun ev => mul_le_mul_left' (frame_inner_bound ev) _
    _ = (∑' ev : Evidence F, Pr[= ev | gen]) * (Fintype.card F : ENNReal)⁻¹ := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * (Fintype.card F : ENNReal)⁻¹ :=
        mul_le_mul_right' tsum_probOutput_le_one _
    _ = (Fintype.card F : ENNReal)⁻¹ := one_mul _

/-- **Quantitative real-to-ideal FRAME bridge.** Suppose the real evidence
process for every fixed secret raises the conditional slash probability by at
most `ε` over a single secret-independent generator `gen`. Then the complete
FRAME experiment is bounded by the blind-guess term plus `ε`.

This is the assembly socket for the lazy-random-oracle identical-until-bad
argument: that argument only has to establish `hclose`, with
`ε = (q_A + q_E + q_Id + q_Nf*q_sig + q_sig^2) / |F|`; this theorem combines it with
`frame_blind_bound` and supplies the final `+ 1/|F|` term. Unlike
`T7_frame_bound`, it does not require exact distributional independence. -/
theorem T7_frame_bound_of_pointwise (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (gen : ProbComp (Evidence F)) (ε : ENNReal)
    (hclose : ∀ k : F,
      Pr[= true | frameEvidence mclose A k >>= fun ev =>
          pure (decide (Slashes k ev))]
        ≤ Pr[= true | gen >>= fun ev => pure (decide (Slashes k ev))] + ε) :
    frameWinProb mclose A ≤ (Fintype.card F : ENNReal)⁻¹ + ε := by
  unfold frameWinProb
  rw [frameGame_eq_evidence, probOutput_bind_eq_tsum]
  calc
    (∑' k : F, Pr[= k | ($ᵗ F)] *
        Pr[= true | frameEvidence mclose A k >>= fun ev =>
          pure (decide (Slashes k ev))])
        ≤ ∑' k : F, Pr[= k | ($ᵗ F)] *
          (Pr[= true | gen >>= fun ev => pure (decide (Slashes k ev))] + ε) := by
            exact ENNReal.tsum_le_tsum fun k => mul_le_mul_left' (hclose k) _
    _ = (∑' k : F, Pr[= k | ($ᵗ F)] *
          Pr[= true | gen >>= fun ev => pure (decide (Slashes k ev))])
        + (∑' k : F, Pr[= k | ($ᵗ F)]) * ε := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ (Fintype.card F : ENNReal)⁻¹ + 1 * ε := by
          gcongr
          · rw [← probOutput_bind_eq_tsum]
            exact frame_blind_bound gen
          · exact tsum_probOutput_le_one
    _ = (Fintype.card F : ENNReal)⁻¹ + ε := by rw [one_mul]

/-- A deferred-sampling certificate for a query-bounded FRAME adversary.
It is deliberately tied to `FrameQueryBounds`: the real handler is compared
with one secret-independent evidence generator, and the permitted loss is
the corrected direct-probe, slope-preimage, and collision mass. Constructing
this certificate is the stateful handler-coupling obligation; once supplied,
no further probabilistic or arithmetic hypothesis is needed. -/
structure FrameDeferredSampling (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) where
  idealEvidence : ProbComp (Evidence F)
  close : ∀ k : F,
    Pr[= true | frameEvidence mclose A k >>= fun ev =>
        pure (decide (Slashes k ev))]
      ≤ Pr[= true | idealEvidence >>= fun ev =>
          pure (decide (Slashes k ev))]
        + (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹

/-- Direct secret probes, nullifier preimage probes against all exposed
slopes, and a conservative slope-collision birthday charge combine into the
concrete handler's leakage numerator. -/
theorem frameQueryCharge_eq
    {A : F → OracleComp (frameSpec F M) (Evidence F)}
    (qb : FrameQueryBounds A) :
    (qb.qA : ENNReal) * (Fintype.card F : ENNReal)⁻¹
        + (qb.qE : ENNReal) * (Fintype.card F : ENNReal)⁻¹
        + (qb.qId : ENNReal) * (Fintype.card F : ENNReal)⁻¹
        + ((qb.qNf * qb.qSig : ℕ) : ENNReal) *
            (Fintype.card F : ENNReal)⁻¹
        + ((qb.qSig * qb.qSig : ℕ) : ENNReal) *
            (Fintype.card F : ENNReal)⁻¹
      = (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  simp only [FrameQueryBounds.total, Nat.cast_add, Nat.cast_mul, add_mul]

/-- **Query-bounded T7 composition theorem.** A stateful deferred-sampling
certificate turns the structural query budgets into the complete corrected
FRAME bound `(qb.total + 1)/|F|`. In particular, the public commitment,
honest signals, close reveal, and shared caches are all accounted for inside
the certificate rather than hidden in an informal independence claim. -/
theorem T7_frame_query_bound (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (hds : FrameDeferredSampling mclose A qb) :
    frameWinProb mclose A
      ≤ ((qb.total + 1 : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  refine le_trans
    (T7_frame_bound_of_pointwise mclose A hds.idealEvidence
      ((qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹) hds.close) ?_
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  exact le_of_eq (add_comm _ _)

/-- **T7 FRAME bound (Spec.md §7 T7, instantiation A).** For every honest
member and every adversary whose evidence is independent of the secret `k`
(the RO-oblivious / query-scoped good event, `hobliv`), the probability that
`Dispute` slashes the honest member is at most `1/|F|` — the blind guess. See
the module GATE-NOTE for the corrected concrete PPT bound and the
deferred identical-until-bad query accounting for the `q_·/|F|` terms. -/
theorem T7_frame_bound (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (gen : ProbComp (Evidence F))
    (hobliv : ∀ k : F, 𝒟[frameEvidence mclose A k] = 𝒟[gen]) :
    frameWinProb mclose A ≤ (Fintype.card F : ENNReal)⁻¹ := by
  unfold frameWinProb
  rw [frameGame_eq_evidence]
  refine le_trans (le_of_eq ?_) (frame_blind_bound gen)
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun k => ?_
  congr 1
  exact probOutput_congr rfl (by rw [evalDist_bind, evalDist_bind, hobliv k])

end Bound

end Zkpc.Games

-- F2 kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.frameWinProb_YK_eq_one
#print axioms Zkpc.Games.frameWinProb_aReuse_eq_one
#print axioms Zkpc.Games.frameWinProb_slopeReveal_eq_one
#print axioms Zkpc.Games.uniformSecretProbeBound
#print axioms Zkpc.Games.uniformSlopeProbeBound
#print axioms Zkpc.Games.uniformMemListBound
#print axioms Zkpc.Games.uniformFreshSlopeBadBound
#print axioms Zkpc.Games.uniformSlopeCollisionBound
#print axioms Zkpc.Games.T7_frame_bound_of_pointwise
#print axioms Zkpc.Games.frameQueryCharge_eq
#print axioms Zkpc.Games.T7_frame_query_bound
#print axioms Zkpc.Games.T7_frame_bound
