import Zkpc.Games.T7

/-!
# T7 deferred-sampling certificates: refutation and the corrected socket

Two results about the composition endpoint of `Zkpc/Games/T7.lean`
(Spec.md §7 T7).

## Refutation of the pointwise certificate (`frameDeferredSampling_refuted`)

`FrameDeferredSampling mclose A qb` demands a *single* secret-independent
evidence generator whose conditional slash probability dominates the real
one **pointwise in the secret `k`**, up to `qb.total/|F|`. This is too
strong to be satisfiable. The two-probe adversary `twoProbe c₁ c₂`
(budget `qId = 2`, all other budgets `0`) queries `H_id` at the two
constants `c₁ ≠ c₂` and outputs slashing evidence for whichever preimage
matched the delivered commitment `cm`:

* at `k = c₁` it wins with probability exactly `1`;
* at `k = c₂` it wins with probability at least `1 − 1/|F|` (only a
  spurious first-probe collision spoils it).

But the events `Slashes c₁ ev` and `Slashes c₂ ev` are disjoint (the
`Dispute` recomputation recovers a single secret), so one fixed
`idealEvidence` cannot carry mass `≥ 1 − 2/|F|` on both slices once
`2 − 5/|F| > 1`, i.e. once `|F| > 5`. Hence no certificate exists for this
query-bounded adversary. This is a finding about the *statement* of the
frozen certificate, not about Spec.md T7 itself: the final bound
`(qb.total + 1)/|F|` only needs the `k`-averaged comparison, which the
counterexample does not contradict (the adversary hits a given `k` for at
most `2` of the `|F|` equally likely secrets).

## The corrected averaged socket (`FrameDeferredSamplingAvg`)

`FrameDeferredSamplingAvg` states the same real-versus-ideal comparison
*averaged over the uniform secret* — exactly the quantity the FRAME
experiment produces and exactly what the lazy-ROM identical-until-bad
argument yields (the bad-event mass `Pr_k[transcript hits k]` is small on
average even though it is `1` at adversarially chosen points).
`T7_frame_query_bound_avg` composes such a certificate into the complete
corrected FRAME bound `(qb.total + 1)/|F|`, and
`FrameDeferredSampling.toAvg` shows the averaged form is implied by the
(unsatisfiable) pointwise form, so no strength that the composition
endpoint actually uses has been lost.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## Lazy-oracle branch reductions -/

omit [Field F] [DecidableEq F] in
/-- On a cache hit, `lazyRO` is the pure return of the cached value. -/
theorem lazyRO_eq_of_some {α : Type} [DecidableEq α]
    {cache : α → Option F} {q : α} {v : F} (h : cache q = some v) :
    lazyRO cache q = pure (v, cache) := by
  unfold lazyRO
  rw [h]

omit [Field F] [DecidableEq F] in
/-- On a cache miss, `lazyRO` samples fresh-uniform and caches the sample. -/
theorem lazyRO_eq_of_none {α : Type} [DecidableEq α]
    {cache : α → Option F} {q : α} (h : cache q = none) :
    lazyRO cache q =
      (($ᵗ F) >>= fun v => pure (v, Function.update cache q (some v))) := by
  unfold lazyRO
  rw [h]

/-! ## The two-probe adversary -/

/-- Candidate evidence whose `Dispute` recomputation recovers exactly `c`:
two points `(1, c)` and `(0, c)` on the horizontal line `Y = c`. -/
def probeEvidence (c : F) : Evidence F := ⟨0, 1, c, 0, c⟩

/-- Fallback evidence with coincident abscissae; it never slashes anyone. -/
def junkEvidence (F : Type) [Field F] : Evidence F := ⟨0, 0, 0, 0, 0⟩

omit [DecidableEq F] [SampleableType F] in
/-- The probe evidence slashes exactly the targeted secret (Spec.md §2
`Dispute` recomputation on the two points `(1, c)`, `(0, c)`). -/
theorem slashes_probeEvidence_iff (k c : F) :
    Slashes k (probeEvidence c) ↔ c = k := by
  unfold Slashes probeEvidence recoverSecret recoverSlope
  simp

omit [DecidableEq F] [SampleableType F] in
/-- The fallback evidence never slashes: its two abscissae coincide. -/
theorem not_slashes_junkEvidence (k : F) : ¬ Slashes k (junkEvidence F) := by
  rintro ⟨h, -⟩
  exact h rfl

/-- The two-probe FRAME adversary: query `H_id` at the constants `c₁` and
`c₂` and output slashing evidence for whichever preimage candidate matched
the delivered commitment (Spec.md §7 T7, rev-9 `roId` channel). It makes
exactly two `roId` queries and nothing else. -/
def twoProbe (c₁ c₂ : F) :
    F → OracleComp (frameSpec F M) (Evidence F) := fun cm => do
  let v₁ ← query (spec := frameSpec F M) (FrameOp.roId c₁)
  let v₂ ← query (spec := frameSpec F M) (FrameOp.roId c₂)
  pure (if v₁ = cm then probeEvidence c₁
    else if v₂ = cm then probeEvidence c₂ else junkEvidence F)

/-- Structural query-budget certificate for the two-probe adversary:
two `H_id` probes, no other charged operations. -/
def twoProbeQueryBounds (c₁ c₂ : F) :
    FrameQueryBounds (M := M) (twoProbe c₁ c₂) where
  qA := 0
  qE := 0
  qId := 2
  qNf := 0
  qSig := 0
  roA_bound := fun _ => by
    simp [twoProbe, isQueryBoundP_query_bind_iff, isDirectRoAQuery]
  roE_bound := fun _ => by
    simp [twoProbe, isQueryBoundP_query_bind_iff, isDirectRoEQuery]
  roId_bound := fun _ => by
    simp [twoProbe, isQueryBoundP_query_bind_iff, isDirectRoIdQuery]
  roNf_bound := fun _ => by
    simp [twoProbe, isQueryBoundP_query_bind_iff, isDirectRoNfQuery]
  signal_bound := fun _ => by
    simp [twoProbe, isQueryBoundP_query_bind_iff, isSignalQuery]

omit [SampleableType F] [DecidableEq M] in
/-- The corrected leakage numerator of the two-probe adversary is `2`. -/
theorem twoProbeQueryBounds_total (c₁ c₂ : F) :
    (twoProbeQueryBounds (M := M) c₁ c₂).total = 2 := rfl

/-! ## Exact real-world runs of the two-probe adversary -/

/-- Real run of the two-probe adversary at secret `k = c₁`: the first probe
is a cache hit on the programmed commitment, so the adversary always emits
the evidence targeting `c₁` (the second probe samples an unused fresh
value). -/
theorem frameEvidence_twoProbe_first (mclose : M) (c₁ c₂ : F)
    (hne : c₁ ≠ c₂) :
    frameEvidence mclose (twoProbe c₁ c₂) c₁ =
      (($ᵗ F) >>= fun _ => ($ᵗ F) >>= fun _ => pure (probeEvidence c₁)) := by
  unfold frameEvidence
  rw [lazyRO_eq_of_none (rfl : (FrameSt.init F M).roId c₁ = none), bind_assoc]
  refine bind_congr fun cm => ?_
  rw [pure_bind]
  unfold twoProbe QueryImpl.Stateful.run frameImpl
  have h₁ : (Function.update (FrameSt.init F M).roId c₁ (some cm)) c₁ = some cm :=
    Function.update_self _ _ _
  have h₂ : (Function.update (FrameSt.init F M).roId c₁ (some cm)) c₂ = none :=
    Function.update_of_ne (Ne.symm hne) _ _
  simp [StateT.run_mk, lazyRO_eq_of_some h₁, lazyRO_eq_of_none h₂]

/-- Real run of the two-probe adversary at secret `k = c₂`: the first probe
samples fresh, the second probe is a cache hit on the programmed
commitment, so the adversary emits the evidence targeting `c₂` unless the
first fresh sample spuriously collided with the commitment. -/
theorem frameEvidence_twoProbe_second (mclose : M) (c₁ c₂ : F)
    (hne : c₁ ≠ c₂) :
    frameEvidence mclose (twoProbe c₁ c₂) c₂ =
      (($ᵗ F) >>= fun cm => ($ᵗ F) >>= fun v₁ =>
        pure (if v₁ = cm then probeEvidence c₁ else probeEvidence c₂)) := by
  unfold frameEvidence
  rw [lazyRO_eq_of_none (rfl : (FrameSt.init F M).roId c₂ = none), bind_assoc]
  refine bind_congr fun cm => ?_
  rw [pure_bind]
  unfold twoProbe QueryImpl.Stateful.run frameImpl
  have h₁ : (Function.update (FrameSt.init F M).roId c₂ (some cm)) c₁ = none :=
    Function.update_of_ne hne _ _
  simp [StateT.run_mk, lazyRO_eq_of_none h₁]
  refine bind_congr fun v₁ => ?_
  have h₂ : (Function.update
      (Function.update (FrameSt.init F M).roId c₂ (some cm)) c₁ (some v₁)) c₂
      = some cm := by
    rw [Function.update_of_ne (Ne.symm hne), Function.update_self]
  simp [lazyRO_eq_of_some h₂]
  rfl


section Refutation

variable [Fintype F]

omit [Fintype F] in
/-- At secret `c₁` the two-probe adversary slashes with probability `1`. -/
theorem twoProbe_win_first (mclose : M) (c₁ c₂ : F) (hne : c₁ ≠ c₂) :
    Pr[= true | frameEvidence mclose (twoProbe c₁ c₂) c₁ >>= fun ev =>
        pure (decide (Slashes c₁ ev))] = 1 := by
  rw [frameEvidence_twoProbe_first mclose c₁ c₂ hne]
  have hdec : decide (Slashes c₁ (probeEvidence c₁)) = true := by
    simp [slashes_probeEvidence_iff]
  simp only [bind_assoc, pure_bind, hdec]
  rw [probOutput_bind_const, probOutput_bind_const]
  simp

/-- At secret `c₂` the two-probe adversary slashes with probability at
least `1 − 1/|F|`: it fails only when the first fresh probe answer
collides with the independent uniform commitment. -/
theorem twoProbe_win_second (mclose : M) (c₁ c₂ : F) (hne : c₁ ≠ c₂) :
    1 ≤ Pr[= true | frameEvidence mclose (twoProbe c₁ c₂) c₂ >>= fun ev =>
        pure (decide (Slashes c₂ ev))]
      + (Fintype.card F : ENNReal)⁻¹ := by
  rw [frameEvidence_twoProbe_second mclose c₁ c₂ hne]
  have hdec : ∀ v₁ cm : F,
      decide (Slashes c₂ (if v₁ = cm then probeEvidence c₁ else probeEvidence c₂))
        = !(decide (v₁ = cm)) := by
    intro v₁ cm
    by_cases h : v₁ = cm
    · simp [h, slashes_probeEvidence_iff, hne]
    · simp [h, slashes_probeEvidence_iff]
  simp only [bind_assoc, pure_bind, hdec]
  set comp : ProbComp Bool :=
    (($ᵗ F) >>= fun cm => ($ᵗ F) >>= fun v₁ => pure (!(decide (v₁ = cm))))
    with hcomp
  have hfail : Pr[⊥ | comp] = 0 := by
    simp [hcomp]
  have hfalse : Pr[= false | comp] ≤ (Fintype.card F : ENNReal)⁻¹ := by
    rw [hcomp, probOutput_bind_eq_tsum]
    calc ∑' cm : F, Pr[= cm | ($ᵗ F)] *
            Pr[= false | ($ᵗ F) >>= fun v₁ =>
              (pure (!(decide (v₁ = cm))) : ProbComp Bool)]
        ≤ ∑' cm : F, Pr[= cm | ($ᵗ F)] * (Fintype.card F : ENNReal)⁻¹ := by
          refine ENNReal.tsum_le_tsum fun cm => mul_le_mul_left' ?_ _
          rw [probOutput_bind_eq_tsum]
          calc ∑' v₁ : F, Pr[= v₁ | ($ᵗ F)] *
                  Pr[= false | (pure (!(decide (v₁ = cm))) : ProbComp Bool)]
              ≤ ∑' v₁ : F, Pr[= v₁ | ($ᵗ F)] * (if v₁ = cm then 1 else 0) := by
                refine ENNReal.tsum_le_tsum fun v₁ => mul_le_mul_left' ?_ _
                by_cases h : v₁ = cm <;> simp [h]
            _ = ∑' v₁ : F, (if v₁ = cm then Pr[= v₁ | ($ᵗ F)] else 0) := by
                refine tsum_congr fun v₁ => ?_
                split <;> simp
            _ = Pr[= cm | ($ᵗ F)] := by
                rw [tsum_eq_single cm fun v₁ hv => if_neg hv]
                simp
            _ = (Fintype.card F : ENNReal)⁻¹ := probOutput_uniformSample F cm
      _ = (∑' cm : F, Pr[= cm | ($ᵗ F)]) * (Fintype.card F : ENNReal)⁻¹ := by
          rw [ENNReal.tsum_mul_right]
      _ ≤ 1 * (Fintype.card F : ENNReal)⁻¹ :=
          mul_le_mul_right' tsum_probOutput_le_one _
      _ = (Fintype.card F : ENNReal)⁻¹ := one_mul _
  have htotal : Pr[= true | comp] + Pr[= false | comp] = 1 := by
    rw [probOutput_true_add_false, hfail, tsub_zero]
  calc (1 : ENNReal) = Pr[= true | comp] + Pr[= false | comp] := htotal.symm
    _ ≤ Pr[= true | comp] + (Fintype.card F : ENNReal)⁻¹ :=
        add_le_add le_rfl hfalse

omit [SampleableType F] [Fintype F] in
/-- A single evidence distribution cannot slash two distinct secrets at
once: the two conditional slash events are disjoint, so their masses sum
to at most one. -/
theorem idealEvidence_disjoint_slices (D : ProbComp (Evidence F))
    (c₁ c₂ : F) (hne : c₁ ≠ c₂) :
    Pr[= true | D >>= fun ev => pure (decide (Slashes c₁ ev))]
      + Pr[= true | D >>= fun ev => pure (decide (Slashes c₂ ev))] ≤ 1 := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  calc ∑' ev : Evidence F,
        (Pr[= ev | D] * Pr[= true | (pure (decide (Slashes c₁ ev)) : ProbComp Bool)]
          + Pr[= ev | D] * Pr[= true | (pure (decide (Slashes c₂ ev)) : ProbComp Bool)])
      ≤ ∑' ev : Evidence F, Pr[= ev | D] := by
        refine ENNReal.tsum_le_tsum fun ev => ?_
        rw [← mul_add]
        refine mul_le_of_le_one_right' ?_
        by_cases h₁ : Slashes c₁ ev
        · have h₂ : ¬ Slashes c₂ ev := fun h₂ =>
            hne (h₁.2.symm.trans h₂.2)
          simp [h₁, h₂]
        · by_cases h₂ : Slashes c₂ ev <;> simp [h₁, h₂]
    _ ≤ 1 := tsum_probOutput_le_one

/-- **The pointwise deferred-sampling certificate is unsatisfiable**
(finding about the statement of `FrameDeferredSampling`, Spec.md §7 T7
composition layer). Over any field with more than five elements, the
two-probe adversary admits no certificate: its real slash probabilities at
the two probed secrets are `1` and `≥ 1 − 1/|F|`, while any single
secret-independent generator can grant total mass at most `1` to the two
disjoint slash slices, forcing `2 − 5/|F| ≤ 1`. The `k`-averaged
comparison (`FrameDeferredSamplingAvg`) is the corrected socket. -/
theorem frameDeferredSampling_refuted (mclose : M) (c₁ c₂ : F)
    (hne : c₁ ≠ c₂) (hcard : 5 < Fintype.card F) :
    ¬ Nonempty (FrameDeferredSampling mclose (twoProbe c₁ c₂)
      (twoProbeQueryBounds c₁ c₂)) := by
  rintro ⟨hds⟩
  set κ : ENNReal := (Fintype.card F : ENNReal)⁻¹ with hκ
  set D := hds.idealEvidence with hD
  have htot : ((twoProbeQueryBounds (M := M) c₁ c₂).total : ENNReal) = 2 := by
    rw [twoProbeQueryBounds_total]
    norm_num
  have h₁ : (1 : ENNReal) ≤
      Pr[= true | D >>= fun ev => pure (decide (Slashes c₁ ev))] + 2 * κ := by
    refine le_trans (le_of_eq (twoProbe_win_first mclose c₁ c₂ hne).symm) ?_
    refine le_trans (hds.close c₁) ?_
    rw [htot]
  have h₂ : (1 : ENNReal) ≤
      Pr[= true | D >>= fun ev => pure (decide (Slashes c₂ ev))] + 2 * κ + κ := by
    refine le_trans (twoProbe_win_second mclose c₁ c₂ hne) ?_
    refine add_le_add ?_ le_rfl
    refine le_trans (hds.close c₂) ?_
    rw [htot]
  -- Sum the two constraints against the disjoint-slice mass bound.
  have hsum := idealEvidence_disjoint_slices D c₁ c₂ hne
  have hbig : (2 : ENNReal) ≤ 1 + (2 * κ + (2 * κ + κ)) := by
    calc (2 : ENNReal) = 1 + 1 := by norm_num
      _ ≤ (Pr[= true | D >>= fun ev => pure (decide (Slashes c₁ ev))] + 2 * κ)
          + (Pr[= true | D >>= fun ev => pure (decide (Slashes c₂ ev))]
            + 2 * κ + κ) := add_le_add h₁ h₂
      _ = (Pr[= true | D >>= fun ev => pure (decide (Slashes c₁ ev))]
          + Pr[= true | D >>= fun ev => pure (decide (Slashes c₂ ev))])
          + (2 * κ + (2 * κ + κ)) := by ring
      _ ≤ 1 + (2 * κ + (2 * κ + κ)) := add_le_add hsum le_rfl
  have hfive : (1 : ENNReal) ≤ 5 * κ := by
    have h2 : (2 : ENNReal) = 1 + 1 := by norm_num
    have hκ5 : 2 * κ + (2 * κ + κ) = 5 * κ := by ring
    rw [hκ5] at hbig
    rw [h2] at hbig
    exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp hbig
  -- Multiply through by `|F|` to contradict `5 < |F|`.
  have hcard0 : (Fintype.card F : ENNReal) ≠ 0 := by
    have : 0 < Fintype.card F := lt_trans (by norm_num) hcard
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hcardtop : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hle : (Fintype.card F : ENNReal) ≤ 5 := by
    calc (Fintype.card F : ENNReal) = (Fintype.card F : ENNReal) * 1 := (mul_one _).symm
      _ ≤ (Fintype.card F : ENNReal) * (5 * κ) := mul_le_mul_left' hfive _
      _ = 5 * ((Fintype.card F : ENNReal) * κ) := by ring
      _ = 5 := by
          rw [hκ, ENNReal.mul_inv_cancel hcard0 hcardtop, mul_one]
  have : Fintype.card F ≤ 5 := by exact_mod_cast hle
  omega

end Refutation

/-! ## The corrected averaged deferred-sampling socket -/

section Averaged

variable [Fintype F]

/-- **Corrected deferred-sampling certificate** (Spec.md §7 T7): the real
FRAME evidence process is compared with one secret-independent generator
*averaged over the uniform secret*, with permitted loss the corrected
direct-probe, slope-preimage, and collision mass. Unlike the pointwise
`FrameDeferredSampling` — refuted by `frameDeferredSampling_refuted` — the
averaged comparison is exactly what the FRAME experiment produces and what
the lazy-ROM identical-until-bad argument yields: an adversary can force
its transcript to hit *specific* secrets with probability `1`, but only
`qb.total` of the `|F|` equally likely secrets in total. -/
structure FrameDeferredSamplingAvg (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) where
  idealEvidence : ProbComp (Evidence F)
  close_avg :
    Pr[= true | (do
        let k ← ($ᵗ F)
        let ev ← frameEvidence mclose A k
        pure (decide (Slashes k ev)))]
      ≤ Pr[= true | (do
          let k ← ($ᵗ F)
          let ev ← idealEvidence
          pure (decide (Slashes k ev)))]
        + (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹

/-- The refuted pointwise certificate implies the averaged one, so the
corrected socket asks for strictly less than the original while still
supplying everything `T7_frame_query_bound` used. -/
def FrameDeferredSampling.toAvg {mclose : M}
    {A : F → OracleComp (frameSpec F M) (Evidence F)}
    {qb : FrameQueryBounds A}
    (hds : FrameDeferredSampling mclose A qb) :
    FrameDeferredSamplingAvg mclose A qb where
  idealEvidence := hds.idealEvidence
  close_avg := by
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    calc ∑' k : F, Pr[= k | ($ᵗ F)] *
            Pr[= true | frameEvidence mclose A k >>= fun ev =>
              pure (decide (Slashes k ev))]
        ≤ ∑' k : F, Pr[= k | ($ᵗ F)] *
            (Pr[= true | hds.idealEvidence >>= fun ev =>
              pure (decide (Slashes k ev))]
              + (qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹) := by
          exact ENNReal.tsum_le_tsum fun k => mul_le_mul_left' (hds.close k) _
      _ = (∑' k : F, Pr[= k | ($ᵗ F)] *
            Pr[= true | hds.idealEvidence >>= fun ev =>
              pure (decide (Slashes k ev))])
          + (∑' k : F, Pr[= k | ($ᵗ F)]) *
            ((qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹) := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ ≤ (∑' k : F, Pr[= k | ($ᵗ F)] *
            Pr[= true | hds.idealEvidence >>= fun ev =>
              pure (decide (Slashes k ev))])
          + 1 * ((qb.total : ENNReal) * (Fintype.card F : ENNReal)⁻¹) := by
          gcongr
          exact tsum_probOutput_le_one
      _ = _ := by rw [one_mul]

/-- **Corrected query-bounded T7 composition theorem** (Spec.md §7 T7).
An averaged deferred-sampling certificate turns the structural query
budgets into the complete corrected FRAME bound `(qb.total + 1)/|F|`: the
averaged real/ideal comparison supplies the `qb.total/|F|` leakage term
and the blind-guess bound against the secret-independent generator
supplies the final `1/|F|`. -/
theorem T7_frame_query_bound_avg (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (hds : FrameDeferredSamplingAvg mclose A qb) :
    frameWinProb mclose A
      ≤ ((qb.total + 1 : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  unfold frameWinProb
  rw [frameGame_eq_evidence]
  refine le_trans hds.close_avg ?_
  refine le_trans (add_le_add (frame_blind_bound hds.idealEvidence) le_rfl) ?_
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  exact le_of_eq (add_comm _ _)

end Averaged

end Zkpc.Games

-- F2 kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.slashes_probeEvidence_iff
#print axioms Zkpc.Games.not_slashes_junkEvidence
#print axioms Zkpc.Games.twoProbeQueryBounds_total
#print axioms Zkpc.Games.frameEvidence_twoProbe_first
#print axioms Zkpc.Games.frameEvidence_twoProbe_second
#print axioms Zkpc.Games.twoProbe_win_first
#print axioms Zkpc.Games.twoProbe_win_second
#print axioms Zkpc.Games.idealEvidence_disjoint_slices
#print axioms Zkpc.Games.frameDeferredSampling_refuted
#print axioms Zkpc.Games.T7_frame_query_bound_avg
