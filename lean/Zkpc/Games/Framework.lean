import VCVio.CryptoFoundations.SecExp
import VCVio.StateSeparating.DistEquiv

/-!
# Game framework over VCV-io (tasks E2–E4)

Minimal glue between VCV-io's oracle/probability machinery and the two
`Zkpc` games (UNLINK in `Zkpc.Games.Unlink`, FRAME in `Zkpc.Games.Frame`).
Everything heavy is VCV-io's: `OracleComp`/`ProbComp` (free monad over an
`OracleSpec`), `QueryImpl.Stateful` (stateful oracle handlers, the
"world"), `evalDist`/`Pr[= x | ·]` semantics, and the advantage lemmas of
`VCVio.CryptoFoundations.SecExp` and `VCVio.StateSeparating.*`.

What this file adds, per task:

* **E2 (adversary + oracle glue).** An adversary is *just* an
  `OracleComp E α` — an arbitrary strategy tree against the oracle surface
  `E` — following the E1 survey's conclusion that no typeclass is needed.
  Two packaged shapes: `World` (a stateful handler bundled with its
  initial state, the thing a hidden bit selects between) and
  `ChalAdversary` (the challenge-terminated two-phase adversary used by
  UNLINK: an interactive phase with oracle access that ends by emitting a
  challenge, then a *pure* post-processing function to the final guess —
  post-challenge oracle silence is structural, not policed).
* **E3 (advantage bookkeeping + smoke test).** `guessGap` is the
  `|Pr[b' = b] − 1/2|` advantage form used by Spec.md T4. The exact
  bridge lemmas to VCV-io's forms are:
  `ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half` (so
  `guessGap p = p.boolBiasAdvantage / 2`, lemma `guessGap_eq`) and
  `ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch`
  (the hidden-bit ↔ two-world decomposition, lemma
  `boolBiasAdvantage_hiddenBitExp`). The smoke theorems
  `hiddenBitAdvantage_const` and `hiddenBitAdvantage_eq_zero_of_distEquiv`
  prove a game whose two worlds coincide (literally, resp. distributionally
  via `QueryImpl.Stateful.DistEquiv`) has advantage `0`.
* **E4 (abort/evict as a reusable component).** Two pieces. (i) The
  in-band game-⊥ convention: an oracle that can refuse service has
  response type `Option _` (`botSpec`), `none` being the ⊥ the adversary
  *receives as data* — the game never fails as a computation, so the
  hidden bit's advantage stays well-defined on every path (Spec.md T4,
  rev-1 finding). This is deliberately NOT `OptionT`-failure: `probFailure`
  mass would fall outside both Boolean branches and skew `guessGap`.
  (ii) `withEvict`, a handler transformer adding an adversary-controlled
  eviction switch per target: once the adversary flips a target's switch,
  every later query routed to that target answers `none`.
-/

universe u

open OracleSpec OracleComp

namespace Zkpc.Games

/-! ## Advantage in the `|Pr[b' = b] − 1/2|` form (E3) -/

/-- The advantage of a hidden-bit game `p : ProbComp Bool` whose output is
the win indicator `b' = b`: the absolute deviation of the win probability
from the coin-guessing baseline `1/2`. This is verbatim Spec.md's
`Adv = |Pr[b' = b] − 1/2|` (T4). -/
noncomputable def guessGap (p : ProbComp Bool) : ℝ :=
  |(Pr[= true | p]).toReal - 1 / 2|

/-- **Bridge to VCV-io's bias form**: our `|Pr[win] − 1/2|` is exactly half
of `ProbComp.boolBiasAdvantage` (which is `|Pr[true] − Pr[false]|`). The
proof is VCV-io's `ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half`;
this factor-2 is the standard normalization difference and nothing else. -/
lemma guessGap_eq (p : ProbComp Bool) :
    guessGap p = p.boolBiasAdvantage / 2 := by
  unfold guessGap
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half]
  ring

/-! ## Worlds and the hidden-bit experiment builder (E2, E3) -/

variable {ι : Type} {E : OracleSpec.{0, 0} ι}

/-- A **world**: one side of a two-world experiment, given as a stateful
oracle handler (implementing the export surface `E` by probabilistic
computation over private state `St`) together with its initial state.
The hidden bit of `hiddenBitExp` selects which world the adversary talks
to. -/
structure World (E : OracleSpec.{0, 0} ι) : Type 1 where
  /-- the world's private state type -/
  St : Type
  /-- the oracle handler: answers each `E`-query in `StateT St ProbComp` -/
  impl : QueryImpl.Stateful unifSpec E St
  /-- the initial private state -/
  init : St

/-- Run an adversary (an arbitrary oracle strategy `A : OracleComp E α`)
against a world, producing the adversary's output distribution. -/
def World.play (w : World E) {α : Type} (A : OracleComp E α) : ProbComp α :=
  w.impl.runProb w.init A

/-- **The two-world hidden-bit experiment** (E2): sample `b` uniformly,
run the adversary against world `w b`, and output the win indicator
`b = b'`. The `b`-first sampling order matches Spec.md T4's repair (the
bit exists on every execution path, so the advantage is unconditional). -/
def hiddenBitExp (w : Bool → World E) (A : OracleComp E Bool) :
    ProbComp Bool := do
  let b ← ($ᵗ Bool)
  let z ← if b then (w true).play A else (w false).play A
  pure (b == z)

/-- **Hidden-bit decomposition** (the second bridge lemma): the bias of the
hidden-bit experiment equals the two-world Boolean distinguishing
advantage. This is VCV-io's
`ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch`
applied to our experiment shape. -/
theorem boolBiasAdvantage_hiddenBitExp (w : Bool → World E)
    (A : OracleComp E Bool) :
    (hiddenBitExp w A).boolBiasAdvantage =
      ((w true).play A).boolDistAdvantage ((w false).play A) :=
  ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch _ _

/-- Advantage of an adversary in a two-world hidden-bit experiment, in the
`|Pr[b' = b] − 1/2|` form. -/
noncomputable def hiddenBitAdvantage (w : Bool → World E)
    (A : OracleComp E Bool) : ℝ :=
  guessGap (hiddenBitExp w A)

/-- The hidden-bit advantage is half the two-world distinguishing
advantage — the composite of the two bridge lemmas, in the form the T4
prover will consume. -/
theorem hiddenBitAdvantage_eq_half_boolDistAdvantage (w : Bool → World E)
    (A : OracleComp E Bool) :
    hiddenBitAdvantage w A =
      ((w true).play A).boolDistAdvantage ((w false).play A) / 2 := by
  unfold hiddenBitAdvantage
  rw [guessGap_eq, boolBiasAdvantage_hiddenBitExp]

/-! ## E3 smoke tests: identical worlds ⇒ advantage 0 -/

/-- **E3 smoke test (literal form).** If the two worlds are literally the
same, every adversary's advantage is `0`. -/
theorem hiddenBitAdvantage_const (w₀ : World E) (A : OracleComp E Bool) :
    hiddenBitAdvantage (fun _ => w₀) A = 0 := by
  rw [hiddenBitAdvantage_eq_half_boolDistAdvantage]
  simp [ProbComp.boolDistAdvantage]

/-- **E3 smoke test (distributional form).** If the two worlds are
distributionally equivalent as stateful handlers
(`QueryImpl.Stateful.DistEquiv`, provable per-query via
`DistEquiv.of_step`), every adversary's advantage is `0`. This is the lemma
shape the T4 secure-variant proof will discharge. -/
theorem hiddenBitAdvantage_eq_zero_of_distEquiv {w : Bool → World E}
    (h : QueryImpl.Stateful.DistEquiv
      (w true).impl (w true).init (w false).impl (w false).init)
    (A : OracleComp E Bool) :
    hiddenBitAdvantage w A = 0 := by
  rw [hiddenBitAdvantage_eq_half_boolDistAdvantage]
  have hp : Pr[= true | (w true).play A] = Pr[= true | (w false).play A] :=
    probOutput_congr rfl (h A)
  simp [ProbComp.boolDistAdvantage, hp]

/-! ## Challenge-terminated adversaries (E2, for UNLINK) -/

/-- A **challenge-terminated adversary**: the shape Spec.md T4's repaired
game requires. `phase1` is the interactive pre-challenge phase — full
oracle access to `E`, taking public setup data `Input`, ending by emitting
the challenge `Chal` together with arbitrary retained memory `Aux` (its
whole transcript, if it wants). `guess` is *pure post-processing* of the
retained memory and the challenge response: after the challenge there is
no oracle access **by type**, which encodes "the game then ends" (MC15)
structurally rather than by a bolted-on restriction. -/
structure ChalAdversary (E : OracleSpec.{0, 0} ι) (Input Chal Resp : Type) :
    Type 1 where
  /-- adversary-chosen memory carried from phase 1 into the final guess -/
  Aux : Type
  /-- interactive phase: oracle access until the challenge is emitted -/
  phase1 : Input → OracleComp E (Chal × Aux)
  /-- pure final guess from retained memory and the challenge response
  (which is `⊥`-capable: `Resp` is typically `Option _`) -/
  guess : Aux → Resp → Bool

/-! ## The abort/evict component (E4) -/

/-- Same oracle indices as `E`, with `Option`-wrapped responses: `none` is
the in-band game-⊥ delivered *as data* to the adversary (Spec.md T4: on a
failed challenge-capability check "the adversary receives ⊥" — and still
outputs its guess). Using in-band `Option` rather than `OptionT`-failure
keeps the game a total `ProbComp`, so no probability mass escapes the
Boolean output and the advantage stays well-defined. -/
@[reducible] def botSpec (E : OracleSpec.{0, 0} ι) : OracleSpec.{0, 0} ι :=
  fun i => Option (E i)

/-- **The abort/evict oracle wrapper** (E4). Wraps a stateful handler for
`E` into a handler for `botSpec E + (T →ₒ PUnit)`:

* base queries (left) are routed through `target : ι → Option T`; if the
  query concerns an evicted target the wrapper answers `none` (service
  refused) without touching the wrapped handler's state, otherwise the
  wrapped handler answers and the response is delivered as `some _`;
* eviction queries (right) let the adversary irrevocably mark a target
  `t : T` as evicted from this point on — "refusing all service to a
  chosen candidate from any point on" (Spec.md T4, abort/evict powers).

State is the wrapped state paired with the eviction flags `T → Bool`. -/
def withEvict {T : Type} [DecidableEq T] {σ : Type}
    (target : ι → Option T) (h : QueryImpl.Stateful unifSpec E σ) :
    QueryImpl.Stateful unifSpec (botSpec E + (T →ₒ PUnit)) (σ × (T → Bool))
  | .inl i => StateT.mk fun s =>
      match target i with
      | some t =>
          if s.2 t then
            pure (none, s)
          else do
            let (r, s') ← (h i).run s.1
            pure (some r, (s', s.2))
      | none => do
          let (r, s') ← (h i).run s.1
          pure (some r, (s', s.2))
  | .inr t => StateT.mk fun s =>
      pure (PUnit.unit, (s.1, Function.update s.2 t true))

/-! ## E2 example: a concrete world and adversary type-check -/

/-- Example world for the E2 sanity check: one oracle (`PUnit →ₒ Bool`)
answering every query with a fresh fair coin, no state. -/
def coinWorld : World (PUnit →ₒ Bool) where
  St := PUnit
  impl := fun _ => StateT.mk fun s => do
    let b ← ($ᵗ Bool)
    pure (b, s)
  init := PUnit.unit

/-- E2 DoD: an example adversary type-checks and the framework's smoke
theorem applies to it — any strategy against two copies of `coinWorld`
has advantage `0`. -/
example (A : OracleComp (PUnit →ₒ Bool) Bool) :
    hiddenBitAdvantage (fun _ => coinWorld) A = 0 :=
  hiddenBitAdvantage_const coinWorld A

end Zkpc.Games
