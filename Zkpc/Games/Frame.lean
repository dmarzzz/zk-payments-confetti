import Zkpc.Games.Framework
import Zkpc.Games.RLN
import Mathlib.Algebra.Field.Basic

/-!
# The FRAME game (task B3; Spec.md §7 T7)

Exculpability under collusion, for the concrete RLN scheme (instantiation
A) over a field `F` with ROM hashes. DEFINITIONS ONLY: the T7 theorem is
a later workstream gated on human review. Docstrings restate Spec.md T7
clause by clause; deviations are marked `GATE-NOTE:`.

## Game shape (Spec.md T7, clause by clause)

1. Challenger runs `Setup` and creates one honest member with secret
   `k ← F` uniform (`frameGame` samples `k` first), open deposit `D`.
2. The adversary controls `N − 1` gateways, arbitrarily many corrupt
   members, and the scheduler. The honest `N`-th gateway's accepted
   tuples reach the adversary through reconciliation anyway, so the
   adversary effectively reads **every** signal the honest member emits —
   encoded here by delivering every emitted signal directly as an oracle
   response. GATE-NOTE: corrupt members are not separate oracles — the
   adversary holds their secrets and has direct access to the random
   oracles (`roA`/`roX`/`roNf` queries), so it can compute any corrupt
   member's signals itself. GATE-NOTE: scheduler control is the
   adversary's free interleaving of queries.
3. Oracles: `Ospend(m)` — the honest member emits its next-index ticket
   on a gateway-bound message `m` of the adversary's choice. `Oclose`,
   under MC20 (rev-6/7), emits **no signal** in the real protocol: the
   A-close publishes `(cm, U)`, the PRF-fresh nullifiers of the unused
   indices, on the public ledger (rev-1's rationale stands: the close is
   the moment `cm` goes public and the member is most targetable, so
   FRAME must cover it). That reveal surface is covered here by the
   `nfAt i` oracle (D1): `nf(i) = H_nf(H_a(k, i))` through the shared
   caches, for ANY adversary-chosen `i` — a strict superset of any
   actual `U` (no `cap`/unused bookkeeping), uniform in shape.
   The game's `close` oracle (close-as-signal) is retained as **legacy
   surplus power**, not MC20 close semantics — see its docstring.
4. The honest member never emits two signals at the same index with
   different messages: structural here — the index counter increments at
   every emission, so each index carries at most one signal ever; and
   the MC20 close reveals are nullifier values with **no line points**
   (no `(x, y)` ever exists for an unused index).
   GATE-NOTE: the MC2 identical re-send is omitted — the signal for a
   given `(k, i, m)` is a deterministic function of the (cached) oracle
   answers, so a re-send would deliver a value the adversary already
   holds. GATE-NOTE: there is no solvency/deposit gate on `Ospend` — the
   honest member here answers unboundedly many spends, strictly *more*
   adversarial power than the deposit-bounded protocol, so a theorem over
   this game covers the deployed one.
5. The adversary outputs candidate evidence `ev* = (nf, (x, y), (x', y'))`
   and wins iff the `Dispute` recomputation slashes the honest member:
   `x ≠ x'` and the recovered secret `y − ((y − y')/(x − x'))·x` equals
   `k` (`Slashes`). GATE-NOTE: `Dispute`'s ancillary checks (that `nf`
   matches `H_nf` of the recovered slope, membership of the recovered
   `cm`) are omitted from the win predicate — omitting checks only makes
   winning easier, so the theorem over this game is the stronger one.

## Random-oracle model

The four domain-separated hashes are lazily sampled random oracles with
caches inside the game state: `H_a(·,·)` (`roA`), `H_x(·)` (`roX`),
`H_nf(·)` (`roNf`), and `H_e(·,·)` (`roE`, Mi1). The adversary gets
*direct* query access to all four (clause 2), and the honest member's
emissions draw from the **same** caches, so adversary queries and honest
signals are ROM-consistent (an adversary that guesses `k` can verify it
against observed signals). Simulation note (Mi1): the game still has no
epoch clock, so honest tickets here carry no `nf_e` — but the honest
member's epoch pseudonyms are exactly `roE (k, e)` against this shared
cache, so a T7 proof wanting epoch-faithful tickets can deliver
`nf_e = roE (k, e)` alongside each signal without changing the state
shape; conversely everything the adversary could learn from those
deliveries it can already ask `roE` for (it cannot hit `(k, ·)` without
knowing `k`, which is the same event the main argument bounds).

## Tie to `Zkpc.Games.RLN` (task G4)

The line algebra lives in `Zkpc/Games/RLN.lean`: honest signals are
emitted at `y = rlnY k a x`, the `Dispute` recomputation here
(`recoverSlope`/`recoverSecret`, stated over `Evidence`) is definitionally
`rln_recover_a`/`rln_recover_k`'s formula, and the sanity lemma
`recoverSecret_line` is derived from `rln_recover_k`. The T7 prover
additionally gets `rln_single_point_hiding` / `rln_evidence_sound` from
that file. GATE-NOTE (inherited from RLN.lean's `x = 0` caveat): `roX`
answers `0` with probability `1/|F|`, and a spend whose digest is `0`
emits `y = k` outright; the T7 statement must absorb that event in its
negligible bound (or the instantiation must domain-separate `H_x` away
from `0`, as RLN.lean prescribes).
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## Signals and lazy random oracles -/

/-- One RLN signal as the fleet sees it: `x = H_x(m)`, `y = k + a·x` with
`a = H_a(k, i)`, and `nf = H_nf(a)` (Spec.md §3, relation `R_spend^A`
clause 3). The index `i` is not part of the wire signal. -/
structure Signal (F : Type) : Type where
  x : F
  y : F
  nf : F

/-- Lazy random-oracle lookup on a function-backed cache: answer from the
cache if present, else sample fresh-uniform and cache (VCVio
`randomOracle` semantics, inlined for a single self-contained game
state). -/
def lazyRO {α : Type} [DecidableEq α] (cache : α → Option F) (q : α) :
    ProbComp (F × (α → Option F)) :=
  match cache q with
  | some v => pure (v, cache)
  | none => do
      let v ← ($ᵗ F)
      pure (v, Function.update cache q (some v))

/-- FRAME game state: the honest member's next unused index, whether it
has closed, and the four random-oracle caches (shared between the honest
member's emissions and the adversary's direct queries). -/
structure FrameSt (F M : Type) : Type where
  /-- honest member's next unused index (emission consumes, MC2) -/
  idx : ℕ
  /-- whether the honest member has closed -/
  closed : Bool
  /-- cache of `H_a : F × ℕ → F` (the per-index line slope key) -/
  roA : F × ℕ → Option F
  /-- cache of `H_x : M → F` (message digest) -/
  roX : M → Option F
  /-- cache of `H_nf : F → F` (nullifier) -/
  roNf : F → Option F
  /-- cache of `H_e : F × ℕ → F` (epoch pseudonym family, Mi1) -/
  roE : F × ℕ → Option F

/-- Initial FRAME state: index 0, unclosed, empty oracle caches. -/
def FrameSt.init (F M : Type) : FrameSt F M where
  idx := 0
  closed := false
  roA := fun _ => none
  roX := fun _ => none
  roNf := fun _ => none
  roE := fun _ => none

/-- The honest member emits its signal for message `m` at its next unused
index and advances the index: `x = H_x(m)`, `a = H_a(k, idx)`,
`y = rlnY k a x = k + a·x` (the `Zkpc.Games.RLN` line), `nf = H_nf(a)`,
all against the shared RO caches. One emission per index, ever — the
honest single-signal rule, structurally. -/
def emitSignal (k : F) (m : M) (s : FrameSt F M) :
    ProbComp (Signal F × FrameSt F M) := do
  let (x, cX) ← lazyRO s.roX m
  let (a, cA) ← lazyRO s.roA (k, s.idx)
  let (nf, cNf) ← lazyRO s.roNf a
  pure (⟨x, rlnY k a x, nf⟩,
    { s with idx := s.idx + 1, roA := cA, roX := cX, roNf := cNf })

/-! ## Oracle surface -/

/-- FRAME oracle queries: the honest-member oracles of Spec.md T7, the
MC20 close-reveal surface (`nfAt`), and direct access to the four random
oracles (the adversary holds `N − 1` gateways' keys and all corrupt
members' secrets; the hash functions are public). -/
inductive FrameOp (F M : Type) : Type
  /-- `Ospend(m)`: honest member emits its next-index signal on `m` -/
  | spend (m : M)
  /-- LEGACY SURPLUS POWER — **not** spec-faithful close semantics.
  Under MC20 (rev-6/7) the real A-close emits **no signal**: it
  publishes `(cm, U)`, PRF-fresh nullifiers with no line points (that
  reveal is covered, as a strict superset, by `nfAt`). This oracle makes
  the honest member emit one *extra signal* on `m_close` at its next
  index and stop — surplus power subsumed by one `spend m_close` query
  (plus the stop, which only removes future signals). Retained so the
  game dominates both the MC20 close and the pre-MC20
  close-as-final-spend design. -/
  | close
  /-- **The MC20 close-reveal surface (D1)**: the nullifier of the honest
  member's index `i`, `nf(i) = H_nf(H_a(k, i))`, through the shared
  caches, for ANY adversary-chosen `i`. The real close publishes exactly
  `{nf(i) : i unused, i < cap}` — a subset of what this oracle hands
  out, so the game's adversary is strictly stronger than any close
  observer (uniform in shape: no `cap`/unused bookkeeping needed). -/
  | nfAt (i : ℕ)
  /-- direct `H_a` query -/
  | roA (kq : F) (i : ℕ)
  /-- direct `H_x` query -/
  | roX (m : M)
  /-- direct `H_nf` query -/
  | roNf (aq : F)
  /-- direct `H_e` query (epoch pseudonym family; Mi1, see the module
  simulation note) -/
  | roE (kq : F) (e : ℕ)

/-- Response types: honest-member signal oracles answer
`Option (Signal F)` — `none` once the member has closed (it is honest: it
stops emitting) — and reveal/RO queries answer `F`. -/
@[reducible] def frameSpec (F M : Type) : OracleSpec (FrameOp F M)
  | .spend _ => Option (Signal F)
  | .close => Option (Signal F)
  | .nfAt _ => F
  | .roA _ _ => F
  | .roX _ => F
  | .roNf _ => F
  | .roE _ _ => F

/-- The FRAME oracle handler for honest member secret `k` and distinguished
close message `mclose`. `spend`/`close` answer `⊥` after the member has
closed (it is honest: it stops emitting); `close` is the LEGACY surplus
oracle (one extra signal on `mclose`, then stop — see `FrameOp.close`;
the MC20-faithful reveal is `nfAt`). `nfAt i` answers
`roNf (roA (k, i))` through the shared caches — it is answered even
after close (the ledger's close reveal is permanent public data). RO
queries hit the shared caches. -/
def frameImpl (k : F) (mclose : M) :
    QueryImpl.Stateful unifSpec (frameSpec F M) (FrameSt F M)
  | .spend m => StateT.mk fun s =>
      if s.closed then pure (none, s)
      else do
        let (sig, s') ← emitSignal k m s
        pure (some sig, s')
  | .close => StateT.mk fun s =>
      if s.closed then pure (none, s)
      else do
        let (sig, s') ← emitSignal k mclose s
        pure (some sig, { s' with closed := true })
  | .nfAt i => StateT.mk fun s => do
      let (a, cA) ← lazyRO s.roA (k, i)
      let (nf, cNf) ← lazyRO s.roNf a
      pure (nf, { s with roA := cA, roNf := cNf })
  | .roA kq i => StateT.mk fun s => do
      let (v, c) ← lazyRO s.roA (kq, i)
      pure (v, { s with roA := c })
  | .roX m => StateT.mk fun s => do
      let (v, c) ← lazyRO s.roX m
      pure (v, { s with roX := c })
  | .roNf aq => StateT.mk fun s => do
      let (v, c) ← lazyRO s.roNf aq
      pure (v, { s with roNf := c })
  | .roE kq e => StateT.mk fun s => do
      let (v, c) ← lazyRO s.roE (kq, e)
      pure (v, { s with roE := c })

/-! ## Dispute evidence and the recovery algebra -/

/-- Candidate dispute evidence `ev* = (nf, (x, y), (x', y'))` (Spec.md §2
`Dispute`): two claimed points on one member's per-index line. -/
structure Evidence (F : Type) : Type where
  nf : F
  x : F
  y : F
  x' : F
  y' : F

/-- `Dispute`'s recovered line slope `a := (y − y') / (x − x')` — the
formula of `Zkpc.Games.rln_recover_a`, stated over `Evidence`. -/
def recoverSlope (ev : Evidence F) : F :=
  (ev.y - ev.y') / (ev.x - ev.x')

/-- `Dispute`'s recovered member secret `k' := y − a·x` — the formula of
`Zkpc.Games.rln_recover_k`, stated over `Evidence`. -/
def recoverSecret (ev : Evidence F) : F :=
  ev.y - recoverSlope ev * ev.x

/-- The win predicate: `Dispute(pp, ev*, 𝓛)` slashes the honest member's
commitment — the two points are distinct in `x` and the recovered secret
is the honest `k`. GATE-NOTE: `Dispute`'s remaining validity checks
(nullifier consistency, membership) are omitted; fewer checks = easier
win = stronger exculpability theorem. -/
def Slashes (k : F) (ev : Evidence F) : Prop :=
  ev.x ≠ ev.x' ∧ recoverSecret ev = k

instance (k : F) (ev : Evidence F) : Decidable (Slashes k ev) := by
  unfold Slashes; infer_instance

omit [SampleableType F] in
/-- Sanity of the recovery algebra (the honest-slashing direction, which
makes FRAME non-vacuous): two genuine points on the line `Y = rlnY k a X`
at distinct abscissae recover exactly `k`. Derived from
`Zkpc.Games.rln_recover_k` (task G4). -/
theorem recoverSecret_line (nf k a x x' : F) (hx : x ≠ x') :
    recoverSecret ⟨nf, x, rlnY k a x, x', rlnY k a x'⟩ = k :=
  rln_recover_k hx rfl rfl

/-! ## The game -/

/-- **The FRAME game** (Spec.md §7 T7). In order:

1. `k ← F` uniform — the honest member's secret (`Setup` + one honest
   member; the membership tree and deposit are not needed by the win
   condition, see the module GATE-NOTEs).
2. The adversary (an arbitrary strategy
   `A : OracleComp (frameSpec F M) (Evidence F)` — it *is* the `N − 1`
   corrupt gateways, all corrupt members, and the scheduler) interacts
   with the honest member through `Ospend`/`Oclose` (legacy surplus) /
   `nfAt` (the MC20 close-reveal superset) and with the public random
   oracles directly; every honest signal is delivered to it as an oracle
   response (the `N − 1`-gateway view).
3. The adversary outputs `ev* = (nf, (x, y), (x', y'))`, and the game
   outputs whether `Dispute` slashes the honest member (`Slashes`). -/
def frameGame (mclose : M) (A : OracleComp (frameSpec F M) (Evidence F)) :
    ProbComp Bool := do
  let k ← ($ᵗ F)
  let ev ← (frameImpl k mclose).run (FrameSt.init F M) A
  pure (decide (Slashes k ev))

/-- FRAME winning probability: T7 states
`frameWinProb mclose A ≤ negl(λ)` for every adversary, under
`single_signal_hiding` (one point on a fresh-slope line leaves `k`
uniform) — a probability of a bad event, not a distinguishing bias, hence
`ℝ≥0∞`-valued `Pr[= true | ·]` rather than `guessGap`. -/
noncomputable def frameWinProb (mclose : M)
    (A : OracleComp (frameSpec F M) (Evidence F)) : ENNReal :=
  Pr[= true | frameGame mclose A]

end Zkpc.Games
