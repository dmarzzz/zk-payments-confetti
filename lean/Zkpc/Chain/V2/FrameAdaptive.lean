import Zkpc.Chain.V2.Frame
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps

/-!
# Non-frameability, stage 2: the adaptive shared-oracle bound (obligation 3)

`Zkpc/Chain/V2/Frame.lean` bounded a *static* framing adversary (a fixed
probe list). This module upgrades to the **adaptive** adversary the T7
campaign required: Bob chooses each chain-secret probe from the history of
previous hit/miss replies, and does so against the *fixed* honest chain
secret `c` committed at open. That is exactly VCV-io's hidden-target
adaptive read game (`OracleComp.hiddenReadMany`): the secret is drawn once
and hidden until the first hit, so the adaptive strategy's read points are
fixed by the all-miss history and the firing probability is the union
bound `q · (1/|C|)` (`probEvent_hiddenReadMany_le`).

This is the analogue for the chain of what `fsProgramCollisionBound`
(`Zkpc/Crypto/FSRom.lean`) did for the Fiat–Shamir programmed slot, reused
verbatim: same hidden-target lemma, chain secret in place of the programmed
challenge. Combined with the fresh-uniform target of the honest close
(`Zkpc/Chain/V2/CollisionBound.lean`'s lazy-RO model), an adaptive `q`-probe
framer's total advantage is at most `q/|C| + 1/|N|` — the stage-1 bound of
`Frame.lean`, now with the probe list replaced by a genuine adaptive
strategy.

Scope note (carried from `FSRom.lean`): like the stage-1 kernel and the FS
programming loss, this is a standalone hidden-target bound. Fusing it with
the payment/close oracle semantics into one adaptive experiment with a
common programmable oracle — the last mile the rev-11 T7 stack reached only
via the `FrameDeferred*`/`FrameComplete` deferred-sampling apparatus — is
the residual, tracked in `ROADMAP.md` as the deferred-sampling port and not
claimed here.
-/

open OracleComp
open scoped ENNReal

namespace Zkpc.Chain.V2

variable {C : Type} [DecidableEq C] [Fintype C] [Nonempty C] [SampleableType C]

/-- **Adaptive chain-secret probing** (Spec-v2 §7 non-frameability, the
adaptive core of stage 2): the honest chain secret `c ← C` is drawn once at
open; an adaptive `q`-probe strategy `σ` (each probe chosen from the
hit/miss history of the parent-reveal hash queries) recovers it — the
`c ∈ probes` disjunct of `Frame.lean`, now genuinely adaptive — with
probability at most `q/|C|`. Direct instance of
`OracleComp.probEvent_hiddenReadMany_le` at the uniform secret. -/
theorem adaptive_secret_probe_bound (q : ℕ) (σ : List Bool → C) :
    Pr[(fun b : Bool => b = true) | OracleComp.hiddenReadMany ($ᵗ C) q σ]
      ≤ (q : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ :=
  OracleComp.probEvent_hiddenReadMany_le
    (fun r : C => (probOutput_uniformSample C r).le) q σ

/-- **The adaptive frame bound** (Spec-v2 §7 non-frameability, stage 2):
adding the honest close's fresh-uniform framing target
(`Zkpc/Chain/V2/CollisionBound.lean`), an adaptive `q`-probe framer's total
advantage is at most `q/|C| + 1/|N|`. Here the two events are stated on
their own hidden targets (secret recovery, then the residual direct guess
at the fresh nullifier), matching the stage-1 decomposition of
`Frame.lean`'s `chainFrame_bound`; the union with the `1/|N|` fresh-target
term is the same sum. -/
theorem adaptive_frame_bound {N : Type} [DecidableEq N] [Fintype N]
    [Nonempty N] [SampleableType N] (q : ℕ) (σ : List Bool → C) (y₀ : N) :
    Pr[(fun b : Bool => b = true) | OracleComp.hiddenReadMany ($ᵗ C) q σ]
      + Pr[(· = y₀) | ($ᵗ N)]
      ≤ (q : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹
        + (Fintype.card N : ℝ≥0∞)⁻¹ := by
  refine add_le_add (adaptive_secret_probe_bound q σ) ?_
  rw [probEvent_eq_eq_probOutput]
  exact (probOutput_uniformSample N y₀).le

end Zkpc.Chain.V2

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.V2.adaptive_secret_probe_bound
#print axioms Zkpc.Chain.V2.adaptive_frame_bound
