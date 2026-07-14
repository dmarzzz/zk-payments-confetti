import Zkpc.Spec.Object
import Zkpc.Core.T2

/-!
# Flat-ticket instantiation of the abstract object (task D5; Spec.md rev-7/8 §3)

`flatScheme` instantiates `Zkpc.Spec.Scheme` — the abstract algorithm
tuple of Spec.md §2 — with carriers drawn from the symbolic machine of
`Zkpc.Core.State` (instantiation A, flat price, `N = 1`). This is the
typing exercise of task D5: the bodies implement §2/§3's checks over the
symbolic identifications, and the file's content is that they type-check
against the gate-reviewed signatures of `Zkpc/Spec/Object.lean`. The
theorems D2–D4/I1 are proved over the transition system in
`Zkpc.Core.T1/T2/T3/T5`, whose guards these bodies mirror clause by
clause (each body cites its `Step` constructor).

Symbolic identifications carried over from State.lean:
* a secret *is* the channel identity (`cm ≡ k`), so the carrier of
  secrets is the signal field `F`;
* a ticket *is* its extracted witness `(k, i, m)` — knowledge soundness
  by construction (Assumptions table, row 1);
* a nullifier *is* its preimage pair `(k, i)` — collision-freeness by
  construction (row 3); a payer close's claimed-unused nullifier set `U`
  (MC20) is therefore the claimed index set itself.

GATE-NOTE (what the deterministic signature layer cannot carry, per the
D5 executor guidance — guard versions implemented, deltas listed):
1. *Check 1 (π verifies / π_close well-formed).* Proof objects do not
   exist in the model; a ticket is its witness, so verification is the
   guard "the components satisfy the relation" checked semantically.
   Nothing is weakened — forged proofs have no representation at all.
   For the MC20 close, `π_close`'s "each nf ∈ U at a distinct index
   < cap" is the well-formedness of `U` as an index Finset bounded by
   `cap` (the body constructs exactly the honest enumeration).
2. *Checks 3 and 5 (epoch currency, rate budget).* Epochs and rate
   budgets are deliberately absent from the D1 machine (State.lean
   header: they only restrict the adversary, so T1–T3/T5 without them
   are strictly stronger); `redeem` therefore has no epoch or budget
   clause. They enter with the fleet model (task G1).
3. *Check 4 (gateway binding, MC14).* `Gateway := Unit` at `N = 1`, so
   the "message names this gateway" check is trivially satisfied by
   typing; it becomes contentful in the fleet model.
4. *`LedgerSt := St F (Message Unit Pl)`.* The D1 machine is one global
   configuration folding the idealized ledger and the single gateway's
   accepted ledger together, so ledger-touching algorithms take and
   return the whole machine state. `PayeeSt` (the gateway's local spent
   set `SS_G`) is nonetheless kept as its own carrier, as §2 Redeem
   specifies.
5. *`Receipt := Unit`.* Instantiation A has no refund receipts (§3:
   "no refunds"); `redeem` always returns `none` for the receipt slot.
6. *MC20 close-dispute and the rev-8 void branch are ledger-internal.*
   `Zkpc/Spec/Object.lean` deliberately keeps these automatic window
   semantics outside the user-callable algorithm tuple and names their
   concrete realization as `Step.closeDispute`, `Step.settleClose`, and
   `Step.settleVoid`. `payerClose` opens the window; the transition system
   executes and verifies its lifecycle.
7. *`Dispute`'s claims window.* `dispute` records the slash and its time
   (opening the MC4 priority window); the window's claim mechanics are
   the `hwin`-guarded `sweep` (post-slash sweeps only inside `τ`,
   `Step.sweepOne`), and the remainder-to-submitter bounty is not
   modeled at `N = 1` (no theorem in D2–D4/I1 mentions it; it enters
   with T6/T7).
8. *`merge` (MC17)* is degenerate at `N = 1` (a gateway never merges its
   own tuples) but implemented per §2: conflicting incoming tuples
   produce evidence, fresh ones join the spent set.
9. *`noncomputable`.* The evidence branches of `redeem`/`merge` extract
   the stored conflicting signal via `Finset.toList`, which is
   noncomputable in mathlib; the definition is a model, not an
   executable, so this is inert (and introduces no assumption beyond
   Lean's built-in `Classical.choice`, permitted by the K2 audit
   baseline stated in `Zkpc/Assumptions.lean`).
-/

namespace Zkpc.Core.Flat

open Zkpc.Spec Zkpc.Core

/-- Structure equality on gateway-bound messages is decidable
componentwise (needed to run the symbolic machine's finite sets over
`Message`). -/
instance {G Pl : Type} [DecidableEq G] [DecidableEq Pl] :
    DecidableEq (Zkpc.Spec.Message G Pl) := fun a b =>
  decidable_of_iff (a.gw = b.gw ∧ a.payload = b.payload)
    (by cases a; cases b; simp)

/-- Gateway-bound message for the single-gateway instantiation
(Spec.md §1, MC14): `m = (G, m̂)` with `G := Unit` at `N = 1`. -/
abbrev Msg (Pl : Type) := Zkpc.Spec.Message Unit Pl

/-- **Flat-ticket instantiation A (Spec.md rev-7/8 §3) of the abstract
scheme (Spec.md §2).** Carriers from the symbolic machine: secrets in the
signal field `F`, tickets/spent tuples as extracted witnesses
`(k, i, m)`, evidence as a conflicting signal pair on one nullifier,
ledger state the machine state of `Zkpc.Core.St`. `Pl` is the
request-payload sort. There is no distinguished close message: under
MC20 a payer closes by unused-index enumeration, emitting no signal.
See the file GATE-NOTE for the checks the deterministic layer carries as
guards and for the MC20 entry points the gate-locked abstract tuple
lacks. -/
noncomputable def flatScheme (F : Type) [Field F] [DecidableEq F]
    (Pl : Type) [DecidableEq Pl] : Zkpc.Spec.Scheme F where
  Gateway := Unit
  Payload := Pl
  Ticket := F × ℕ × Msg Pl
  Receipt := Unit
  Evidence := F × ℕ × Msg Pl × Msg Pl
  PayerSt := F × ℕ × Option (F × ℕ × Msg Pl)
  PayeeSt := Finset (F × ℕ × Msg Pl)
  LedgerSt := St F (Msg Pl)
  SpentTuple := F × ℕ × Msg Pl
  -- `Open` (Spec.md §2): register the commitment (symbolically: the
  -- secret), escrow `D` into the pool, payer state starts at index 0
  -- with nothing emitted. Refused on duplicate commitment
  -- (`Step.openCh`'s `hnew` guard).
  open' := fun _pp k st =>
    if k ∈ st.opened then none
    else some ((k, 0, none), { st with opened := insert k st.opened })
  -- `Spend` (Spec.md §2/§3): emit the witness at the current index and
  -- advance it (consumption at emission, MC2); `⊥` iff the solvency
  -- conjunct `(i+1)·C ≤ D` is unsatisfiable (R_spend conjunct 2;
  -- `Step.emitHonest`'s `hsolv` guard). The last emitted ticket is
  -- retained for the retry rule.
  spend := fun pp stP m =>
    match stP with
    | (k, i, _) =>
      if (i + 1) * pp.C ≤ pp.D then
        some ((k, i, m), (k, i + 1, some (k, i, m)))
      else none
  -- MC2 retry: re-send the last emitted ticket bit-identically;
  -- `none` if nothing was emitted yet.
  retry := fun stP => stP.2.2
  -- `Redeem` (Spec.md §2, checks in order; GATE-NOTE 1–3 for the checks
  -- the symbolic layer absorbs): check 1+2 as the liveness and solvency
  -- guards (`Step.accept`'s `hlive`/`hsolv`), then check 6's three-way
  -- nullifier logic against `SS_G` (`hfresh`, the reject-duplicate
  -- abort-retry path, and the evidence branch feeding `Dispute`).
  redeem := fun pp _gw ss ledger t =>
    match t with
    | (k, i, m) =>
      if ledger.live k ∧ (i + 1) * pp.C ≤ pp.D then
        if (k, i, m) ∈ ss then (.rejectDuplicate, ss, none)
        else
          match (ss.filter (fun u => u.1 = k ∧ u.2.1 = i)).toList with
          | u :: _ => (.evidence (k, i, u.2.2, m), ss, none)
          | [] => (.accept, insert (k, i, m) ss, none)
      else (.reject, ss, none)
  -- Fleet reconciliation (MC17), degenerate at `N = 1` (GATE-NOTE 8):
  -- merging a tuple that conflicts on a nullifier emits merge-time
  -- evidence; a fresh tuple joins the spent set.
  merge := fun ss u =>
    match u with
    | (k, i, m) =>
      if (k, i, m) ∈ ss then (ss, none)
      else
        match (ss.filter (fun v => v.1 = k ∧ v.2.1 = i)).toList with
        | v :: _ => (insert (k, i, m) ss, some (k, i, v.2.2, m))
        | [] => (insert (k, i, m) ss, none)
  -- Payer close ("close-by-unused-enumeration", MC20 [repair]): publish
  -- the claimed-unused index set — an honest payer enumerates exactly
  -- `{i | emittedCnt ≤ i < cap}`, which is what the payer-side counter
  -- `j` constructs here — opening the window at the current time
  -- (`Step.payerClose`'s guards; settlement/void at expiry are the
  -- machine's `settleClose`/`settleVoid`, automatic per §2). No signal
  -- is emitted.
  payerClose := fun pp stP ledger =>
    match stP with
    | (k, j, _) =>
      if ledger.live k then
        some { ledger with
          closedAt := Function.update ledger.closedAt k
            (some ((Finset.range (pp.D / pp.C)).filter (fun i => j ≤ i),
              ledger.clock)) }
      else none
  -- Payee close ("sweep", MC16 + MC20 bar): pay `C` per fresh nullifier
  -- of an accepted tuple, deduped against `RedeemedNF`, post-slash only
  -- within the priority window, and never for a nullifier recorded in a
  -- settled close's claimed-unused set (`Step.sweepOne`'s four guards;
  -- `sweepOpen` from Zkpc.Core.T2, `St.sweepBarred` from State.lean).
  -- Non-sweepable tuples are skipped.
  sweep := fun pp _gw tuples ledger =>
    tuples.foldl
      (fun st u =>
        match u with
        | (k, i, _m) =>
          if u ∈ st.acc ∧ (k, i) ∉ st.swept ∧ sweepOpen pp.tau st k ∧
              ¬ st.sweepBarred k i then
            { st with swept := insert (k, i) st.swept
                      paidGw := st.paidGw + pp.C }
          else st)
      ledger
  -- `Dispute` (Spec.md §2): validate the conflicting pair — two
  -- existing signals on one `(k, i)` with different messages, the line
  -- algebra recovering `k` for an open, unslashed channel — and slash,
  -- recording the window-open time (`Step.slash`'s five guards).
  -- `none` on invalid evidence. MC20 close-dispute and rev-8 void are
  -- ledger-internal transitions, as recorded in GATE-NOTE 6.
  dispute := fun _pp ev ledger =>
    match ev with
    | (k, i, m, m') =>
      if (k, i, m) ∈ ledger.sigs ∧ (k, i, m') ∈ ledger.sigs ∧ m ≠ m' ∧
          k ∈ ledger.opened ∧ ledger.slashedAt k = none then
        some { ledger with
          slashedAt := Function.update ledger.slashedAt k (some ledger.clock) }
      else none

end Zkpc.Core.Flat
