import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# RLN line algebra (task G4; Spec.md §1 "The RLN signal", §2 `Dispute`, T7's algebraic core)

GATE-NOTE (x = 0 degenerate point): Spec.md §1 types the message digest as
`x = H_x(m) ∈ F_p` without excluding `x = 0`. At `x = 0` the signal value is
`y = k + a·0 = k` — the observation hands over the secret outright
(counterexample: any `k`, any `a`, message with `H_x(m) = 0` gives `y = k`,
so "one signal reveals nothing" is FALSE at that point). The one-point
lemma below (`rln_single_point_hiding`) is therefore stated for `x ≠ 0`,
and the degenerate case is isolated as `rln_x_zero_degenerate`. A faithful
deployment must domain-separate `H_x` into `F_p \ {0}` (or reject `x = 0`
messages); Spec.md's `single_signal_hiding` assumption (§5 item 3) should
be read as conditioned on `x ≠ 0`. This is a spec caveat, not a weakening:
the two-point recovery lemmas and `rln_evidence_sound` hold for all `x`.

The signal line of Spec.md §1: for secret `k`, per-index coefficient
`a = H_a(k, i)`, and message digest `x = H_x(m)`, the signal value is
`y = k + a·x` — a point on the line `Y = k + a·X`. This file proves, over
an arbitrary field `F` (instantiated at `F_p`), the four algebraic facts
the protocol's slash/exculpability story rests on:

* **Two points reveal the secret** (`rln_recover_a`, `rln_recover_k`):
  Spec.md §1 "anyone can compute `a = (y − y′)/(x − x′)` and
  `k = y − a·x`", and §2 `Dispute`'s recomputation. This is what makes
  double-signing slashable, and is the completeness half of the slash logic.
* **One point reveals nothing — algebraic form**
  (`rln_single_point_hiding`): for any nonzero `x`, any observed `y`, and
  ANY candidate secret `k′`, there is exactly one coefficient `a′` making
  `(x, y)` lie on `k′`'s line. So the observation `(x, y)` is consistent
  with every candidate secret via a unique coefficient and determines
  nothing about `k`. This is the information-theoretic heart of Spec.md
  §5's `single_signal_hiding` (the probabilistic statement additionally
  needs `a = H_a(k, i)` pseudorandom; that reduction is T7's, task G3 —
  this file supplies its algebraic core per the G4 contract).
* **Slash soundness** (`rln_evidence_complete`, `rln_evidence_sound`):
  `Dispute`'s recovery formula is correct on genuine double-signs, and any
  evidence pair whose recovery returns `k` genuinely lies on `k`'s line —
  the ledger's slash predicate cannot be satisfied by a pair that is not
  two points of some line through `k`.

These lemmas are reused by T7 (task G3, another workstream) and by the
`Dispute` slash logic (Spec.md §2).
-/

namespace Zkpc.Games

/- `DecidableEq F` is part of the G4 interface (F_p carries it); not every
lemma consumes it, which is fine — silence the section-variable lint. -/
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]

/-- The RLN line (Spec.md §1): the signal value at digest `x` for secret
`k` and line coefficient `a` is `y = k + a·x`. In the protocol,
`a = H_a(k, i)` and `x = H_x(m)`; here they are free field elements — the
lemmas below are pure line algebra, valid for every instantiation of the
hashes. -/
def rlnY (k a x : F) : F := k + a * x

/-- **Two points reveal the coefficient** (Spec.md §1, §2 `Dispute`).
Given two well-formed signals `y = k + a·x` and `y′ = k + a·x′` on the same
`(k, a)` (same secret, same spend index) at distinct digests `x ≠ x′`, the
public reconstruction `(y − y′)/(x − x′)` recovers exactly `a`. -/
theorem rln_recover_a {k a x x' y y' : F} (hx : x ≠ x')
    (hy : rlnY k a x = y) (hy' : rlnY k a x' = y') :
    (y - y') / (x - x') = a := by
  subst hy hy'
  have hxx : x - x' ≠ 0 := sub_ne_zero.mpr hx
  simp only [rlnY]
  field_simp
  ring

/-- **Two points reveal the secret** (Spec.md §1, §2 `Dispute`).
Given two well-formed signals on the same `(k, a)` at `x ≠ x′`, the public
reconstruction `k = y − ((y − y′)/(x − x′))·x` recovers exactly `k`. This
is the recomputation `Dispute` runs before slashing `cm = H_id(k)`. -/
theorem rln_recover_k {k a x x' y y' : F} (hx : x ≠ x')
    (hy : rlnY k a x = y) (hy' : rlnY k a x' = y') :
    y - ((y - y') / (x - x')) * x = k := by
  rw [rln_recover_a hx hy hy']
  subst hy
  simp only [rlnY]
  ring

/-- **One point reveals nothing — algebraic form** (Spec.md §5,
`single_signal_hiding`, information-theoretic core). For any nonzero
digest `x`, any observed signal value `y`, and ANY candidate secret `k′`:
there is exactly one line coefficient `a′` consistent with the observation,
namely `a′ = (y − k′)/x`. Hence the single observation `(x, y)` is
consistent with every candidate secret (each via its unique coefficient)
and determines nothing about `k` — the asymmetry against the two-point
lemmas above is the entire content of the slash mechanism (Spec.md §1).

The hypothesis `x ≠ 0` is necessary: see the file GATE-NOTE and
`rln_x_zero_degenerate` — a real deployment domain-separates `H_x` away
from `0`. The probabilistic complement (that `a = H_a(k, i)` looks random,
so the unique consistent coefficient carries no information either) is the
`single_signal_hiding` assumption discharged in the T7 game layer. -/
theorem rln_single_point_hiding (k' : F) {x : F} (hx : x ≠ 0) (y : F) :
    ∃! a', rlnY k' a' x = y := by
  refine ⟨(y - k') / x, ?_, ?_⟩
  · simp only [rlnY]
    field_simp
    ring
  · intro a ha
    simp only [rlnY] at ha
    field_simp
    rw [← ha]
    ring

/-- **The `x = 0` degenerate case** (file GATE-NOTE): at digest `x = 0`
the signal value is the secret itself, `y = k`. This is exactly why a
deployment must domain-separate `H_x` into nonzero field elements — the
one-point-hiding lemma is false at `x = 0`, and Spec.md §1's typing of
`H_x` into `F_p` leaves this case open. -/
theorem rln_x_zero_degenerate (k a : F) : rlnY k a 0 = k := by
  simp [rlnY]

/-- **Slash completeness** (Spec.md §2 `Dispute`): if two valid signals
share `(k, a)` — the same secret and the same spend index, hence the same
line — with `x ≠ x′`, then `Dispute`'s recovery formula returns exactly
`(a, k)`. Packaging of `rln_recover_a` and `rln_recover_k`: a genuine
double-sign always convicts. -/
theorem rln_evidence_complete {k a x x' y y' : F} (hx : x ≠ x')
    (hy : rlnY k a x = y) (hy' : rlnY k a x' = y') :
    (y - y') / (x - x') = a ∧ y - ((y - y') / (x - x')) * x = k :=
  ⟨rln_recover_a hx hy hy', rln_recover_k hx hy hy'⟩

/-- **Slash soundness** (Spec.md §2 `Dispute`; anti-framing direction used
by T3's exculpability clause and T7). If an adversary outputs an evidence
pair `((x, y), (x′, y′))` with `x ≠ x′` whose public recovery returns `k`
— i.e. `y − ((y − y′)/(x − x′))·x = k` — then the pair genuinely consists
of two points on `k`'s line with coefficient `a′ = (y − y′)/(x − x′)`:
`y = rlnY k a′ x` and `y′ = rlnY k a′ x′`. The ledger's slash predicate
can only ever be satisfied by an actual two-point exposure of a line
through `k`; combined with `rln_single_point_hiding` (the adversary's view
of an honest member is one point per line), forging such a pair means
computing `k`, which is what T7 excludes. -/
theorem rln_evidence_sound {k x x' y y' : F} (hx : x ≠ x')
    (hk : y - ((y - y') / (x - x')) * x = k) :
    rlnY k ((y - y') / (x - x')) x = y ∧
      rlnY k ((y - y') / (x - x')) x' = y' := by
  have hxx : x - x' ≠ 0 := sub_ne_zero.mpr hx
  subst hk
  constructor
  · simp only [rlnY]
    ring
  · simp only [rlnY]
    field_simp
    ring

end Zkpc.Games
