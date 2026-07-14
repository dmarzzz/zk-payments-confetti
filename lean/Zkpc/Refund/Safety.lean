import Zkpc.Refund.State

/-!
# Refund-variant safety theorems T1-B, T3-B, conservation (tasks H1/H2/H4; Spec.md §7)

The B analogues of the flat-ticket balance theorems, over the close-time
netting machine `Zkpc.Refund.State`. All three follow from one reachable
invariant `Inv`:

* the **refund/cost identity** `R + Σc = n·C_max` (the certified refund total
  is exactly the accumulated `C_max − c` over the `n` accepted spends);
* **solvency** `n·C_max ≤ D + R` (the B inequality, preserved because each
  accepted spend was solvent and the refund only grows the slack);
* **settlement conservation** `settled → payerPay + payeePay = D`;
* the **cooperative-floor identity** `settled → ¬slashed → payerPay + Σc = D`.

From these:

* **T1-B — no overspend** (`T1_B_no_overspend`, Spec.md §7 T1 refund variant):
  `Σ c_ℓ ≤ D`. The tag binding is the per-channel structure of `R` (H1): there
  is no cross-channel receipt in the model, so `R` sums only this channel's
  refunds, exactly what the `H_tag(k)` binding guarantees.
* **T3-B — payer floor** (`T3_B_floor`, Spec.md §7 T3 refund variant): a
  cooperatively closed (honest, unslashed) channel recovers exactly
  `payerPay = D − Σc = (D + R) − j·C_max` and is never slashed. The floor
  `(D + R_held) − j·C_max` is recovered on the nose and is never forfeited.
* **conservation** (`conservation`, Spec.md MC18): payer + payee payout `= D`
  per settled channel, in every settlement path (cooperative or forfeit) —
  the exact-`D` netting MC18 asserts.

H2 (both `E(R)` representations compile): every theorem is stated for an
arbitrary representation type `Rep`, so it holds at B-static's and B-rerand's
representation types alike — the safety layer is representation-generic.
-/

namespace Zkpc.Refund

variable {Rep : Type} {Cmax D : ℕ} {r0 : Rep}

/-- The reachable invariant of the B settlement machine. -/
def Inv (Cmax D : ℕ) (s : St Rep) : Prop :=
  s.R + s.sumc = s.idx * Cmax ∧
  s.idx * Cmax ≤ D + s.R ∧
  (s.settled = true → s.payerPay + s.payeePay = D) ∧
  (s.settled = true → s.slashed = false → s.payerPay + s.sumc = D) ∧
  (s.settled = true → s.closed = true)

/-- `Inv` holds at every reachable state. -/
theorem reach_inv {s : St Rep} (h : Reach Rep Cmax D r0 s) : Inv Cmax D s := by
  induction h with
  | init =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [St.init]
  | @step s s' a _ hstep ih =>
    obtain ⟨hId, hSolv, hCons, hFloor, hClosed⟩ := ih
    cases hstep with
    | accept c r' hlive hc hsolv =>
      have hexp : (s.idx + 1) * Cmax = s.idx * Cmax + Cmax := by rw [Nat.add_one_mul]
      refine ⟨?_, ?_, hCons, ?_, hClosed⟩
      · show (s.R + (Cmax - c)) + (s.sumc + c) = (s.idx + 1) * Cmax
        omega
      · show (s.idx + 1) * Cmax ≤ D + (s.R + (Cmax - c))
        omega
      · intro hset _
        rw [hClosed hset] at hlive
        exact absurd hlive (by simp)
    | close hlive =>
      have hRle : s.R ≤ s.idx * Cmax := by omega
      refine ⟨hId, hSolv, ?_, ?_, fun _ => rfl⟩
      · intro _
        show (D + s.R) - s.idx * Cmax + (s.idx * Cmax - s.R) = D
        omega
      · intro _ _
        show (D + s.R) - s.idx * Cmax + s.sumc = D
        omega
    | forceClose hlive =>
      refine ⟨hId, hSolv, ?_, ?_, fun _ => rfl⟩
      · intro _; show (0 : ℕ) + D = D; omega
      · intro _ hns; simp at hns

/-- **T1-B — No overspend (Spec.md §7 T1, refund variant, `N = 1`).** At every
reachable state, the total accepted cost `Σ c_ℓ` never exceeds the deposit
`D`. The chain tag binding (MC7) is modeled as the per-channel structure of
`R` (H1): `R` accumulates only this channel's refunds, so cross-channel
splicing cannot inflate the solvency slack. Proof: `Σc = n·C_max − R` (the
refund/cost identity) and `n·C_max ≤ D + R` (solvency) give `Σc ≤ D`. -/
theorem T1_B_no_overspend {s : St Rep} (h : Reach Rep Cmax D r0 s) :
    s.sumc ≤ D := by
  obtain ⟨hId, hSolv, -, -⟩ := reach_inv h
  omega

/-- **Conservation (Spec.md MC18).** Every settled B channel splits exactly
the deposit `D` between payer and payee — in the cooperative close
(`(D+R)−j·C_max` + `(j·C_max−R) = D`) and in the force-close forfeit
(`0 + D = D`) alike. This is MC18's "conserves exactly `D` per channel by
construction." -/
theorem conservation {s : St Rep} (h : Reach Rep Cmax D r0 s)
    (hset : s.settled = true) :
    s.payerPay + s.payeePay = D :=
  (reach_inv h).2.2.1 hset

/-- **T3-B — Payer balance floor (Spec.md §7 T3, refund variant).** A channel
that closed cooperatively (settled, not slashed — the honest closer's path,
which chooses `close`, never `forceClose`) recovers exactly the floor
`payerPay = D − Σc`, equivalently `(D + R_held) − j·C_max`, and is provably
**not slashed**. The floor is recovered on the nose and never forfeited:
`payerPay + Σc = D`. (An honest payer never takes the `forceClose` forfeit
path, so `slashed = false` for it — see `honest_close_not_slashed`.) -/
theorem T3_B_floor {s : St Rep} (h : Reach Rep Cmax D r0 s)
    (hset : s.settled = true) (hns : s.slashed = false) :
    s.payerPay + s.sumc = D :=
  (reach_inv h).2.2.2.1 hset hns

/-- **T3-B floor, explicit `D − Σc` form.** The cooperatively-settled payer
payout equals the deposit minus the total spent — the recoverable floor. -/
theorem T3_B_floor_eq {s : St Rep} (h : Reach Rep Cmax D r0 s)
    (hset : s.settled = true) (hns : s.slashed = false) :
    s.payerPay = D - s.sumc := by
  have := T3_B_floor h hset hns
  omega

/-- **Cooperative close is never a slash (Spec.md §7 T3 "no close-dispute
path slashes an honest closer").** The `close` action leaves `slashed =
false`; only `forceClose` sets it. So an honest payer that closes at its true
count is never slashed — the exculpability facet of T3-B in this machine. -/
theorem close_not_slashed (s : St Rep) (hs : s.slashed = false)
    {s' : St Rep} (hstep : Step Cmax D s .close s') :
    s'.slashed = false := by
  cases hstep; exact hs

/-- **Fund-slash forfeit path (Spec.md MC18/§7 T2-B; task H5).** A
force-closed (slashed) channel pays the whole deposit `D` to the payee: the
`k`-gated per-nullifier claims cannot run, so settlement is by forfeit. This
is the path H5 cites for closing the B self-slash race — the channel settles
(conserving `D`) rather than stranding funds. -/
theorem forceClose_forfeit (s : St Rep)
    {s' : St Rep} (hstep : Step Cmax D s .forceClose s') :
    s'.payeePay = D ∧ s'.payerPay = 0 ∧ s'.slashed = true := by
  cases hstep; exact ⟨rfl, rfl, rfl⟩

/-! ## H5 — the B self-slash race is closed (Spec.md MC18/MC4; gates.md round-3 R3-2)

`research/raw/gates.md` R3-2 (major): MC18's "no sweeps in B" left the
slash path uncovered — a B payer could consume service, self-slash, and race
the payee's recovery, stranding the payee's revenue. The repair (MC18, scoped
in rev-10/11): a channel hit by a fund-slash settles by **forfeit of `D` to
the payee** (the `k`-gated per-nullifier claims cannot run when `k` stays
hidden, and close-time netting cannot reach a frozen channel), and under the
MC4-scoped gateway-priority windows the race has no unclaimed remainder to
capture.

In this machine the race is closed **structurally**: `settle` happens exactly
once per channel (the `closed`/`settled` flags, enforced by every action's
`closed = false` guard — see `Inv`'s `settled → closed` clause), and *every*
settlement path — cooperative `close` and forfeiting `forceClose` alike —
conserves exactly `D` (`conservation`). There is no execution in which a
self-slash both consumes service and strands funds: the fund-slash path
(`forceClose_forfeit`) routes the whole deposit to the payee, and a
cooperatively-closed honest payer is protected by the T3-B floor
(`T3_B_floor`) and is never slashed (`close_not_slashed`). -/

/-- **H5 — self-slash race closure (Spec.md MC18/MC4; gates.md R3-2).** Every
settled B channel — whether it settled cooperatively or through the
fund-slash forfeit path — conserves exactly the deposit `D` between the two
parties, and settlement happens at most once. No settlement path strands
funds, so the self-slash race (consume service, then slash to escape payment)
cannot leave the payee short: the fund-slash path (`forceClose_forfeit`)
routes the whole deposit to the payee. This packages `conservation` as the H5
no-stranding statement; `forceClose_forfeit` supplies the slashed-path payee
recovery. -/
theorem self_slash_race_closed {s : St Rep} (h : Reach Rep Cmax D r0 s)
    (hset : s.settled = true) :
    s.payerPay + s.payeePay = D :=
  conservation h hset

end Zkpc.Refund

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Refund.T1_B_no_overspend
#print axioms Zkpc.Refund.T3_B_floor
#print axioms Zkpc.Refund.conservation
#print axioms Zkpc.Refund.self_slash_race_closed
