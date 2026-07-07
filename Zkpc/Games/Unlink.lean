import Zkpc.Games.Framework

/-!
# The UNLINK game (task B3; Spec.md §7 T4)

The challenge-terminated spend-unlinkability game, for an abstract scheme
interface (`UnlinkScheme`). This file is DEFINITIONS ONLY: the T4 theorem
(and its B-static/B-rerand calibration pair) is a later workstream gated
on human review of these definitions. Every definition's docstring
restates its Spec.md T4 clause; encoding deviations are marked
`GATE-NOTE:` and collected in `README-games.md`.

## Game shape (Spec.md T4, clause by clause)

1. The challenger samples the hidden bit `b ← {0,1}` **at game start**
   (`unlinkGame` binds `b` first; rev-1 repair — the advantage is
   well-defined on every path, ⊥-paths contribute exactly 1/2).
2. `Setup` runs and two honest candidate payers `P₀, P₁` are created,
   equal deposits, opened in batch: two independent draws of `S.openCh`
   before any oracle query; the public open transcripts (`OpenView`) are
   handed to the adversary as its input.
3. The adversary plays the payee (all `N` gateways, all payee keys); its
   **pre-challenge oracles** are `unlinkSpec`: `spend(u, m)`, `retry(u)`,
   `serve(u, ρ)` (its accept-and-serve response; withholding it is the
   abort lever), `close(u)`, and `tick` (epoch advance). Corrupt payers
   have no interaction surface with the candidates (Spec.md: "maximality
   at zero cost"), so they are not modeled — the adversary simulates them
   internally.
4. **Challenge and termination**: `phase1` *ends by returning* the
   challenge message `m*`. The game checks, at challenge time,
   epoch-freshness (`epochFresh`: neither candidate emitted a signal in
   the current epoch) and challenge-capability (`challengeCapable`: both
   candidates unclosed and solvent for one more spend). On failure the
   adversary receives `⊥` (`none`) — in-band data, not game failure. On
   success `P_b` emits the challenge ticket for `m*` at its next index
   and the adversary receives its view. **The game then ends**: the
   adversary's `guess` is a pure function of its retained memory and the
   challenge response — no oracle access after the challenge, by type
   (`ChalAdversary`). In particular the three world-observable components
   rev-1's gate found leaky (the retry buffer, the index counters, close
   events) are reachable only through the pre-challenge oracle surface.
5. Advantage: `|Pr[b' = b] − 1/2|` (`unlinkAdvantage := guessGap`).
-/

open OracleSpec OracleComp

namespace Zkpc.Games

/-! ## The abstract scheme interface -/

/-- What the UNLINK game needs from a payment-channel instantiation: the
adversary-visible content of the candidates' emissions and the candidate
payer state evolution. Instantiation A (flat-ticket RLN) and both B
variants (B-static / B-rerand) are intended instances; the B-static
calibration attack of Spec.md T4 lives entirely in how an instance
populates `View`.

GATE-NOTE: `Open` is folded into the challenger-side sampling `openCh`
whose public transcript is `OpenView`. For instantiation B this absorbs
the genesis receipt exchange (the payee = adversary signs `ct₀`): a
faithful B instance must place the genesis certified ciphertext and its
signature data in `OpenView` and route later receipt issuance through
`serve`. Interactive `Open` is not modeled. -/
structure UnlinkScheme : Type 1 where
  /-- gateway-bound spend messages `m` (Spec.md §1, MC14) -/
  M : Type
  /-- adversary-visible content of one spend ticket: the epoch pseudonym
  `nf_e`, the signal `(x, y, nf)`, and — for instantiation B — the
  presented certified-ciphertext form. The zk proof `π` itself is absent:
  removing it *is* the zero-knowledge simulation (`Zkpc.Assumptions` §2). -/
  View : Type
  /-- adversary-visible content of a candidate's public close event:
  reveals `cm_u` and the spend count (Spec.md T4 `Oclose`; the count side
  channel is MC15, explicitly not covered by T4). -/
  CloseView : Type
  /-- public transcript of one `Open` (candidate creation) -/
  OpenView : Type
  /-- data the adversary supplies when it accepts-and-serves a spend:
  instantiation B's refund receipt `ρ = (ct', σ_S(ct'), r', c)`; `PUnit`
  in instantiation A (accept has no payer-visible effect there). -/
  Receipt : Type
  /-- candidate payer private state: index counter, refund state (`R` and
  its certified opening in B), retry buffer -/
  PSt : Type
  /-- `Open` with deposit `D` at batch time: initial payer state plus the
  public open transcript. Both candidates draw from this one distribution,
  which encodes "equal deposits, opened in batch at the same time". -/
  openCh : ProbComp (PSt × OpenView)
  /-- `Spend` at the current epoch: emit the ticket at the candidate's
  next index (consumption at emission, MC2) and advance the state;
  `none` iff the solvency conjunct is unsatisfiable at the current index
  (Spec.md §2 — "if `Spend` outputs ⊥ on insolvency, A is told so"). -/
  spend : ℕ → PSt → M → ProbComp (Option (View × PSt))
  /-- the MC2 retry buffer: the last emitted ticket, re-sent bit-identical
  (`none` if nothing was emitted yet). Read-only. -/
  lastTicket : PSt → Option View
  /-- apply an adversary-issued receipt to the candidate's refund state
  (B: grows `R` if the receipt validates; A: no-op).
  GATE-NOTE: total — an invalid receipt must be absorbed as a no-op by
  the instance; receipt validation failure is not a game event. -/
  serve : PSt → Receipt → PSt
  /-- `Close` at the current epoch: emit the close signal at the next
  unused index (close-as-final-spend, MC1), producing the public close
  event view and the final state. -/
  close : ℕ → PSt → ProbComp (CloseView × PSt)
  /-- the solvency half of challenge-capability, on the candidate's
  current certified state: A: `(j+1)·C ≤ D`; B: `(j+1)·C_max ≤ D + R`
  against the receipts held (Spec.md T4 challenge clause). -/
  capable : PSt → Bool

/-! ## Oracle surface -/

/-- Pre-challenge oracle queries of the UNLINK game (Spec.md T4). The two
candidates are addressed as `u : Bool` (`false = P₀`, `true = P₁`).

The abort/evict powers of Spec.md T4 need no dedicated index: aborting an
interaction is the adversary *not* issuing the `serve` query for a
delivered ticket (the payee's accept/abort choice; in B this withholds
the refund receipt and can drive a candidate insolvent — the concrete
abort lever), and eviction is refusing all further service to a candidate
(never serving it again). The generic `withEvict` wrapper of
`Zkpc.Games.Framework` exists for games that need an explicit eviction
switch; UNLINK's eviction power is native to its oracle surface. -/
inductive UnlinkOp (S : UnlinkScheme) : Type
  /-- `Ospend(u, m)`: `P_u` runs `Spend` on gateway-bound `m` at its next
  index; the ticket (or insolvency-⊥) is delivered to the adversary -/
  | spend (u : Bool) (m : S.M)
  /-- `Oretry(u)`: `P_u` re-sends its last emitted ticket unchanged (MC2) -/
  | retry (u : Bool)
  /-- the adversary accepts a delivered ticket and serves: hands `P_u` its
  receipt data (B: the refund receipt; A: `PUnit`) -/
  | serve (u : Bool) (ρ : S.Receipt)
  /-- `Oclose(u)`: directs `P_u` to close; the public close event (with
  its spend count) is delivered -/
  | close (u : Bool)
  /-- advance the epoch clock.
  GATE-NOTE: epochs are an abstract adversary-advanced counter. In the
  deployed protocol epochs advance with wall-clock time under scheduler
  control; Spec.md §6 gives the adversary the scheduler, so an explicit
  epoch-advance oracle is the faithful (maximal-power) encoding. -/
  | tick

/-- Response types of the UNLINK oracles. `Option` responses are the
in-band game-⊥ of `Zkpc.Games.Framework` (`botSpec` convention): `none`
is data the adversary receives, never computation failure. -/
@[reducible] def unlinkSpec (S : UnlinkScheme) : OracleSpec (UnlinkOp S)
  | .spend _ _ => Option S.View
  | .retry _ => Option S.View
  | .serve _ _ => PUnit
  | .close _ => Option S.CloseView
  | .tick => PUnit

/-! ## Challenger state and oracle handler -/

/-- Challenger-side game state: the epoch clock, both candidates' scheme
states, close flags, and the epoch of each candidate's most recent signal
emission (for the challenge-time freshness predicate — a transcript
predicate, per rev-2 NEW-5, so the *game* tracks it, not the scheme). -/
structure GSt (S : UnlinkScheme) : Type where
  /-- current epoch `e` (starts at 0, advanced only by `tick`) -/
  epoch : ℕ
  /-- candidate payer states, indexed by `u` -/
  cand : Bool → S.PSt
  /-- whether `P_u` has closed -/
  closed : Bool → Bool
  /-- epoch of `P_u`'s most recent signal emission (`none` = never).
  Because the epoch clock is monotone, "`P_u` emitted a signal during the
  current epoch" is exactly `lastSig u = some epoch`. -/
  lastSig : Bool → Option ℕ

/-- Initial game state from the two candidates' opened states. -/
def GSt.init (S : UnlinkScheme) (p₀ p₁ : S.PSt) : GSt S where
  epoch := 0
  cand := fun u => if u then p₁ else p₀
  closed := fun _ => false
  lastSig := fun _ => none

/-- The pre-challenge oracle handler (the UNLINK "world" — the same world
for both values of the hidden bit; only the challenge depends on `b`).
Per query:

* `spend u m`: if `P_u` closed, respond `⊥` (GATE-NOTE: Spec.md leaves
  spends directed at a closed candidate implicit; a closed payer emits
  nothing, so `⊥` — the adversary closed it and knows). Otherwise run
  `S.spend`; on a ticket, record the emission epoch (freshness clock) and
  the advanced state; on insolvency-`none`, deliver `⊥` ("A is told so").
* `retry u`: deliver the retry buffer, bit-identical, with **no** state
  change and **no** freshness update. GATE-NOTE: a bit-identical re-send
  is not a new signal — it carries the original epoch's pseudonym — so it
  does not count as "emitted a signal during e*" for the challenge-time
  freshness predicate. GATE-NOTE: retry is answered even after close
  (strictly more adversary power; a closed candidate is
  challenge-incapable regardless).
* `serve u ρ`: apply the receipt to `P_u`'s refund state (no-op once
  closed). The accept/abort choice of Spec.md T4 is exactly:
  issue this query, or don't.
* `close u`: emit `P_u`'s close (once; repeated closes respond `⊥`),
  deliver the public close event, mark the candidate closed. GATE-NOTE:
  the close signal counts as a signal emission in the current epoch for
  the freshness clock (close-as-final-spend emits `s_close`); this is
  immaterial to the challenge, which a closed candidate already fails.
* `tick`: advance the epoch. -/
def unlinkImpl (S : UnlinkScheme) :
    QueryImpl.Stateful unifSpec (unlinkSpec S) (GSt S)
  | .spend u m => StateT.mk fun g =>
      if g.closed u then pure (none, g)
      else do
        match ← S.spend g.epoch (g.cand u) m with
        | some (v, st') =>
            pure (some v,
              { g with
                  cand := Function.update g.cand u st'
                  lastSig := Function.update g.lastSig u (some g.epoch) })
        | none => pure (none, g)
  | .retry u => StateT.mk fun g =>
      pure (S.lastTicket (g.cand u), g)
  | .serve u ρ => StateT.mk fun g =>
      if g.closed u then pure (PUnit.unit, g)
      else pure (PUnit.unit,
        { g with cand := Function.update g.cand u (S.serve (g.cand u) ρ) })
  | .close u => StateT.mk fun g =>
      if g.closed u then pure (none, g)
      else do
        let (cv, st') ← S.close g.epoch (g.cand u)
        pure (some cv,
          { g with
              cand := Function.update g.cand u st'
              closed := Function.update g.closed u true
              lastSig := Function.update g.lastSig u (some g.epoch) })
  | .tick => StateT.mk fun g =>
      pure (PUnit.unit, { g with epoch := g.epoch + 1 })

/-! ## Challenge-time predicates and the challenge move -/

/-- **Epoch-freshness at challenge time** (Spec.md T4, rev-2 NEW-5): a
predicate on the transcript, checked when the challenge arrives — neither
candidate has emitted any signal during the current epoch `e*`. Without
it the game is trivially winnable via the shared epoch pseudonym `nf_e`
against every scheme (Spec.md T4 anti-vacuity (ii)). -/
def epochFresh (S : UnlinkScheme) (g : GSt S) : Bool :=
  !(g.lastSig false == some g.epoch) && !(g.lastSig true == some g.epoch)

/-- **Challenge-capability** (Spec.md T4): both candidates are open,
unslashed, unclosed, and solvent for one more spend under their current
certified state. Encoded: unclosed (`closed` flag) and solvent
(`S.capable`). GATE-NOTE: "open" holds by construction (both candidates
are opened at setup and there is no eviction-from-the-tree oracle), and
"unslashed" reduces to true — no UNLINK oracle can slash an honest
candidate (producing slash evidence against an honest payer is exactly
the FRAME game, T7). A candidate the adversary evicted into insolvency
fails `capable`, shrinking the capable set — the game charges that to the
anonymity set, not the scheme (the calibrated content of the abort
attack). -/
def challengeCapable (S : UnlinkScheme) (g : GSt S) : Bool :=
  (!(g.closed false) && S.capable (g.cand false)) &&
  (!(g.closed true) && S.capable (g.cand true))

/-- The challenge move: on the checks failing, the adversary receives `⊥`
(in-band `none`). Otherwise `P_b` emits the challenge ticket for `m*` at
its next index in the current epoch, and the adversary receives exactly
the ticket view — the advanced state of `P_b` is discarded, which is the
structural form of "the game then ends" (no bit-dependent continuation
exists to observe; MC15).

GATE-NOTE: if both checks pass but the abstract `S.spend` still returns
`none`, the adversary receives `⊥`. For faithful instances this branch is
unreachable (`capable` means solvent for one more spend, and a solvent
spend succeeds); it exists because the abstract interface cannot promise
it. -/
def challengeResp (S : UnlinkScheme) (g : GSt S) (b : Bool) (mstar : S.M) :
    ProbComp (Option S.View) :=
  if epochFresh S g && challengeCapable S g then
    (Option.map Prod.fst) <$> S.spend g.epoch (g.cand b) mstar
  else
    pure none

/-! ## The game -/

/-- A UNLINK adversary: interactive pre-challenge phase from the public
open transcripts, terminated by emitting the challenge message `m*`;
then a pure guess from retained memory and the challenge response
(`⊥`-capable). See `Zkpc.Games.ChalAdversary`. -/
@[reducible] def UnlinkAdversary (S : UnlinkScheme) : Type 1 :=
  ChalAdversary (unlinkSpec S) (S.OpenView × S.OpenView) S.M (Option S.View)

/-- **The UNLINK game** (Spec.md §7 T4, challenge-terminated). In order:

1. `b ← {0,1}` — sampled first, so the advantage is well-defined on every
   path and `⊥`-paths contribute exactly 1/2 (rev-1 repair).
2. Both candidates open in batch with equal deposits (two draws of
   `S.openCh`); the adversary gets the public open transcripts.
3. The adversary's interactive phase runs against the pre-challenge
   oracles (`unlinkImpl`), ending with the challenge message `m*`.
4. The challenge move (`challengeResp`): freshness + capability checks,
   then `P_b`'s ticket view or `⊥`.
5. The game ends; the adversary's pure `guess` produces `b'`, and the
   game outputs the win indicator `b = b'`. -/
def unlinkGame (S : UnlinkScheme) (A : UnlinkAdversary S) : ProbComp Bool := do
  let b ← ($ᵗ Bool)
  let (p₀, v₀) ← S.openCh
  let (p₁, v₁) ← S.openCh
  let ((mstar, aux), g) ←
    (unlinkImpl S).runState (GSt.init S p₀ p₁) (A.phase1 (v₀, v₁))
  let resp ← challengeResp S g b mstar
  pure (b == A.guess aux resp)

/-- UNLINK advantage, exactly Spec.md T4's
`Adv = |Pr[b' = b] − 1/2|` (via `Zkpc.Games.guessGap`; the bridge to
VCV-io's bias/distinguishing forms is `guessGap_eq` and the hidden-bit
decomposition in `Zkpc.Games.Framework`). -/
noncomputable def unlinkAdvantage (S : UnlinkScheme) (A : UnlinkAdversary S) : ℝ :=
  guessGap (unlinkGame S A)

end Zkpc.Games
