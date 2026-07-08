import Zkpc.Games.Frame
import Zkpc.Games.Coupling
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

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
`Pr[slash] ≤ negl(λ)` for every **PPT** adversary; the full explicit bound is
`(q_A + q_Id + q_E + 1)/|F_p|` — the `+1` is the blind guess proved here, and
each `q_·/|F_p|` is the union-bound mass of the corresponding RO channel's
queries landing on the hidden `k`. Formalising those query terms is the lazy
random-oracle *identical-until-bad* accounting over an unbounded interactive
adversary — the estimated-hard 20% flagged in the E1 survey
(`research_knowledge/vcvio-gap.md §3`). We ship the blind-guess term rigorously
and scope the query terms behind the `hobliv` hypothesis (the "no query hit
`k`" good event), which IS the PPT scoping the deliverable permits: a
query-bounded adversary that does not correlate its evidence with `k`.
Discharging `hobliv` unconditionally for a `q`-query-bounded adversary, with
the residual `(q_A+q_Id+q_E)/|F|` bad-event mass, is the follow-up.

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

/-- **T7 FRAME bound (Spec.md §7 T7, instantiation A).** For every honest
member and every adversary whose evidence is independent of the secret `k`
(the RO-oblivious / query-scoped good event, `hobliv`), the probability that
`Dispute` slashes the honest member is at most `1/|F|` — the blind guess. See
the module GATE-NOTE for the full PPT bound `(q_A+q_Id+q_E+1)/|F_p|` and the
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
#print axioms Zkpc.Games.T7_frame_bound
