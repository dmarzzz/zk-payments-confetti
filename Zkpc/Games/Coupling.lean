import Zkpc.Games.Unlink

/-!
# UNLINK coupling infrastructure (task H3 support; Spec.md §7 T4)

Generic lemmas for computing `unlinkAdvantage` of concrete instances:

* `unlinkRun` — the UNLINK game with the hidden bit factored out: the whole
  b-independent prefix (genesis stage, batch open, pre-challenge phase),
  the challenge move at a given bit, and the adversary's guess as output.
  `unlinkGame_eq_decide_unlinkRun` re-expresses `unlinkGame` as the
  canonical guess-the-bit shape `b ← $ᵗ Bool; b' ← unlinkRun S A b;
  pure (decide (b = b'))`, which is what the VCV-io hidden-bit lemmas
  (`probOutput_bind_uniformBool`, `probOutput_decide_eq_uniformBool_half`)
  consume.
* `unlinkAdvantage_eq_zero_of_challenge_bitfree` — **the flat-instance
  coupling technique**: if an instance's challenge response is
  distributionally independent of the hidden bit *at every game state*
  (`𝒟[challengeResp S g b ms] = 𝒟[challengeResp S g b' ms]`), then every
  adversary's advantage is exactly `0`. This is sound because `unlinkGame`
  samples `b` first (rev-1 repair) and nothing before the challenge ever
  reads it, so the whole transcript factors as (b-independent prefix) ×
  (challenge); the per-state coupling then makes the guess independent of
  `b`. The T4 must-pass proofs (B-rerand here; instantiation A in the
  F-phase T4 workstream) discharge exactly the per-state hypothesis.
* `unlinkAdvantage_eq_half_of_run_determined` — the must-lose closer: if a
  concrete adversary's run deterministically recovers the bit
  (`unlinkRun S A b ≡ pure b` in distribution), its advantage is exactly
  `1/2`, the maximum. The calibration distinguishers (B-static and the
  rev-11 battery) are proved through this.

GATE-NOTE (encoding): `unlinkRun` is definitionally the body of
`unlinkGame` with the final win-indicator comparison stripped; the proof
of `unlinkGame_eq_decide_unlinkRun` is pure monad-law reassociation, no
probabilistic content. `b == b'` is replaced by `decide (b = b')`
(`Bool.beq_eq_decide_eq`-style, proved by cases) to match the VCV-io
lemma shapes.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

/-- The UNLINK game body at a fixed challenge bit `b`, returning the
adversary's guess: genesis stage, batch open, pre-challenge interactive
phase, challenge move for `b`, pure guess. `unlinkGame S A` is exactly
`b ← $ᵗ Bool` followed by this and the win-indicator comparison
(`unlinkGame_eq_decide_unlinkRun`). -/
def unlinkRun (S : UnlinkScheme) (A : UnlinkAdversary S) (b : Bool) :
    ProbComp Bool := do
  let ((g₀, g₁), a₀) ← A.phase0
  let (p₀, v₀) ← S.openCh g₀
  let (p₁, v₁) ← S.openCh g₁
  let ((mstars, aux), g) ←
    (unlinkImpl S).runState (GSt.init S p₀ p₁) (A.main.phase1 (a₀, v₀, v₁))
  let resp ← challengeResp S g b mstars
  pure (A.main.guess aux resp)

private lemma beq_eq_decide_eq (b b' : Bool) :
    (b == b') = decide (b = b') := by cases b <;> cases b' <;> rfl

/-- `unlinkGame` in canonical guess-the-bit shape: sample the bit, run the
b-parameterized body, compare. Monad-law reassociation only. -/
lemma unlinkGame_eq_decide_unlinkRun (S : UnlinkScheme)
    (A : UnlinkAdversary S) :
    unlinkGame S A = do
      let b ← ($ᵗ Bool)
      let b' ← unlinkRun S A b
      pure (decide (b = b')) := by
  unfold unlinkGame unlinkRun
  refine bind_congr fun b => ?_
  simp only [bind_assoc]
  refine bind_congr fun x => ?_
  obtain ⟨⟨g₀, g₁⟩, a₀⟩ := x
  refine bind_congr fun y => ?_
  obtain ⟨p₀, v₀⟩ := y
  refine bind_congr fun z => ?_
  obtain ⟨p₁, v₁⟩ := z
  refine bind_congr fun w => ?_
  obtain ⟨⟨mstars, aux⟩, g⟩ := w
  refine bind_congr fun resp => ?_
  simp [beq_eq_decide_eq]

/-- **The flat-instance coupling technique.** If the challenge response
distribution is independent of the hidden bit at every reachable (indeed,
every) game state, then the whole run's output distribution is
b-independent. -/
lemma evalDist_unlinkRun_eq_of_challenge_bitfree (S : UnlinkScheme)
    (A : UnlinkAdversary S)
    (h : ∀ (g : GSt S) (ms : List S.M) (b b' : Bool),
      𝒟[challengeResp S g b ms] = 𝒟[challengeResp S g b' ms])
    (b b' : Bool) :
    𝒟[unlinkRun S A b] = 𝒟[unlinkRun S A b'] := by
  unfold unlinkRun
  simp only [evalDist_bind]
  refine bind_congr fun x => ?_
  obtain ⟨⟨g₀, g₁⟩, a₀⟩ := x
  simp only [evalDist_bind]
  refine bind_congr fun y => ?_
  obtain ⟨p₀, v₀⟩ := y
  simp only [evalDist_bind]
  refine bind_congr fun z => ?_
  obtain ⟨p₁, v₁⟩ := z
  simp only [evalDist_bind]
  refine bind_congr fun w => ?_
  obtain ⟨⟨mstars, aux⟩, g⟩ := w
  simp only [evalDist_bind]
  rw [h g mstars b b']

/-- **Must-pass closer (T4 secure direction).** An instance whose challenge
response is distributionally bit-independent at every game state yields
advantage exactly `0` for *every* adversary. -/
theorem unlinkAdvantage_eq_zero_of_challenge_bitfree (S : UnlinkScheme)
    (A : UnlinkAdversary S)
    (h : ∀ (g : GSt S) (ms : List S.M) (b b' : Bool),
      𝒟[challengeResp S g b ms] = 𝒟[challengeResp S g b' ms]) :
    unlinkAdvantage S A = 0 := by
  have hhalf : Pr[= true | unlinkGame S A] = 1 / 2 := by
    rw [unlinkGame_eq_decide_unlinkRun]
    exact probOutput_decide_eq_uniformBool_half (unlinkRun S A)
      (evalDist_unlinkRun_eq_of_challenge_bitfree S A h true false)
  unfold unlinkAdvantage guessGap
  rw [hhalf]
  norm_num

/-- **Must-lose closer (calibration direction).** A concrete adversary
whose run deterministically recovers the hidden bit — `unlinkRun S A b`
outputs `b` with probability `1` for both bits — has advantage exactly
`1/2`, the information-theoretic maximum. The calibration distinguishers
are all proved through this (their runs are deterministic, so the
probability-1 hypotheses reduce by `simp`). -/
theorem unlinkAdvantage_eq_half_of_run_determined (S : UnlinkScheme)
    (A : UnlinkAdversary S)
    (htrue : Pr[= true | unlinkRun S A true] = 1)
    (hfalse : Pr[= false | unlinkRun S A false] = 1) :
    unlinkAdvantage S A = 1 / 2 := by
  have hone : Pr[= true | unlinkGame S A] = 1 := by
    rw [unlinkGame_eq_decide_unlinkRun, probOutput_bind_uniformBool]
    have ht : Pr[= true | unlinkRun S A true >>= fun b' =>
        (pure (decide (true = b')) : ProbComp Bool)] = 1 := by
      rw [show (fun b' => (pure (decide (true = b')) : ProbComp Bool)) =
          fun b' => pure b' from funext fun b' => by cases b' <;> simp]
      simpa using htrue
    have hf : Pr[= true | unlinkRun S A false >>= fun b' =>
        (pure (decide (false = b')) : ProbComp Bool)] = 1 := by
      rw [show (fun b' => (pure (decide (false = b')) : ProbComp Bool)) =
          fun b' => pure (!b') from funext fun b' => by cases b' <;> simp]
      have : Pr[= true | (! ·) <$> unlinkRun S A false] = 1 := by
        rw [probOutput_not_map]; exact hfalse
      simpa [map_eq_bind_pure_comp, Function.comp] using this
    rw [ht, hf]
    norm_num
  unfold unlinkAdvantage guessGap
  rw [hone]
  norm_num

/-- **Advantage from win probability, general form** — for the battery's
inexact winners (harvest-and-match distinguishers whose loss is exactly
the pseudonym-collision mass): if the game wins with probability `p`,
the advantage is `|p.toReal − 1/2|`. Trivial unfolding, stated for
reuse. -/
lemma unlinkAdvantage_eq_of_probOutput (S : UnlinkScheme)
    (A : UnlinkAdversary S) {p : ℝ≥0∞}
    (h : Pr[= true | unlinkGame S A] = p) :
    unlinkAdvantage S A = |p.toReal - 1 / 2| := by
  unfold unlinkAdvantage guessGap
  rw [h]

end Zkpc.Games
