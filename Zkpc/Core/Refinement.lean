import Zkpc.Core.Flat

/-!
# Flat object-to-ledger forward refinement

`Core.Flat.flatScheme` supplies executable algorithm bodies, while
`Core.State.Step` is the transition system used by the safety and liveness
proofs.  This module proves that the state-changing success paths of the
object API are exactly concrete ledger transitions.  The results remove the
previous reliance on parallel, manually compared definitions.

The payer's private counter is related to the ledger's `emittedCnt`.  Spend
first updates the private state and its corresponding ledger emission step;
Open, payer Close, and identity Dispute directly return the same ledger state
as their `Step` constructor.  Automatic close-window transitions remain
ledger-internal by design and are already the subject of T2/T3/T5.
-/

namespace Zkpc.Core.Flat

open Zkpc.Spec Zkpc.Core

variable {F Pl : Type} [Field F] [DecidableEq F] [DecidableEq Pl]

/-- Open succeeds exactly on a fresh commitment and returns the state produced
by the symbolic `openCh` transition. -/
theorem open_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (hnew : k ∉ s.opened) :
    ∃ s',
      (flatScheme F Pl).open' pp k s =
        some (((k, 0, none), s')) ∧
      Step pp.C pp.D pp.tau honest s (.openCh k) s' := by
  let s' : St F (Msg Pl) := { s with opened := insert k s.opened }
  refine ⟨s', ?_, ?_⟩
  · simp [flatScheme, hnew, s']
  · exact Step.openCh s k hnew

/-- An honest executable Spend at the ledger's current counter is simulated
by one `emitHonest` transition and advances the private counter to match the
new ledger counter. -/
theorem spend_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (last : Option (F × ℕ × Msg Pl))
    (m : Msg Pl) (hh : honest k) (hlive : s.live k)
    (hsolv : (s.emittedCnt k + 1) * pp.C ≤ pp.D) :
    ∃ s' ticket payer',
      (flatScheme F Pl).spend pp (k, s.emittedCnt k, last) m =
        some (ticket, payer') ∧
      Step pp.C pp.D pp.tau honest s (.emitHonest k m) s' ∧
      ticket = (k, s.emittedCnt k, m) ∧
      payer'.1 = k ∧ payer'.2.1 = s'.emittedCnt k := by
  let ticket : F × ℕ × Msg Pl := (k, s.emittedCnt k, m)
  let payer' : F × ℕ × Option (F × ℕ × Msg Pl) :=
    (k, s.emittedCnt k + 1, some ticket)
  let s' : St F (Msg Pl) :=
    { s with sigs := insert ticket s.sigs
             emittedCnt := Function.update s.emittedCnt k (s.emittedCnt k + 1) }
  refine ⟨s', ticket, payer', ?_, ?_, rfl, rfl, ?_⟩
  · simp [flatScheme, hsolv, ticket, payer']
  · exact Step.emitHonest s k m hh hlive hsolv
  · simp [s']

/-- The executable honest payer-close enumerates exactly the unused suffix and
returns precisely the ledger state of `Step.payerClose`. -/
theorem payerClose_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (j : ℕ)
    (last : Option (F × ℕ × Msg Pl)) (hh : honest k)
    (hlive : s.live k) (hcount : j = s.emittedCnt k) :
    ∃ s' U,
      (flatScheme F Pl).payerClose pp (k, j, last) s = some s' ∧
      Step pp.C pp.D pp.tau honest s (.payerClose k U) s' ∧
      U = (Finset.range (pp.D / pp.C)).filter (fun i => j ≤ i) := by
  let U := (Finset.range (pp.D / pp.C)).filter (fun i => j ≤ i)
  let s' : St F (Msg Pl) :=
    { s with closedAt := Function.update s.closedAt k (some (U, s.clock)) }
  refine ⟨s', U, ?_, ?_, rfl⟩
  · have hopen : k ∈ s.opened := hlive.1
    simp [flatScheme, St.live, hopen, hlive.2.1, hlive.2.2, U, s']
  · apply Step.payerClose s k U hlive
    · intro i hi
      exact (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    · intro _
      subst j
      rfl

/-- A valid executable identity dispute returns exactly the state of the
symbolic slash transition. -/
theorem dispute_refines_step (pp : Params) (honest : F → Prop)
    (s : St F (Msg Pl)) (k : F) (i : ℕ) (m m' : Msg Pl)
    (h1 : (k, i, m) ∈ s.sigs) (h2 : (k, i, m') ∈ s.sigs)
    (hne : m ≠ m') (hopen : k ∈ s.opened)
    (hns : s.slashedAt k = none) :
    ∃ s',
      (flatScheme F Pl).dispute pp (k, i, m, m') s = some s' ∧
      Step pp.C pp.D pp.tau honest s (.slash k i m m') s' := by
  let s' : St F (Msg Pl) :=
    { s with slashedAt := Function.update s.slashedAt k (some s.clock) }
  refine ⟨s', ?_, ?_⟩
  · simp [flatScheme, h1, h2, hne, hopen, hns, s']
  · exact Step.slash s k i m m' h1 h2 hne hopen hns

/-- A sequence of successful refined object calls yields ordinary concrete
reachability, so all existing T1--T5 invariants apply to the executable API
trace. -/
theorem refined_steps_reachable (pp : Params) (honest : F → Prop)
    {s : St F (Msg Pl)} (h : Reach pp.C pp.D pp.tau honest s)
    {s' : St F (Msg Pl)} {a : Act F (Msg Pl)}
    (hstep : Step pp.C pp.D pp.tau honest s a s') :
    Reach pp.C pp.D pp.tau honest s' :=
  Reach.step h hstep

end Zkpc.Core.Flat

#print axioms Zkpc.Core.Flat.open_refines_step
#print axioms Zkpc.Core.Flat.spend_refines_step
#print axioms Zkpc.Core.Flat.payerClose_refines_step
#print axioms Zkpc.Core.Flat.dispute_refines_step
#print axioms Zkpc.Core.Flat.refined_steps_reachable
