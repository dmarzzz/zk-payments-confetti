import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Distributed spent-set model: the N-gateway fleet machine (task G1; Spec.md §2 Redeem, §3 fleet, §7 T6 setting)

The discrete-time transition system over which T6 (`Zkpc.Fleet.T6`) is
stated: `N` honest gateways (`Fin N`), each enforcing `Redeem`'s admission
checks against its own local view, with reconciliation lag `L` entering as
the `FleetFair` trace hypothesis rather than as transition-relation magic.

## Modeling choices (each traceable to Spec.md; reviewer checklist)

- **One member.** T6 is a per-member statement (Spec.md §7 T6, Adversary:
  "One corrupted member … coalitions: the bound applies per-member and sums
  linearly, each deposit separately"). The machine is therefore specialized
  to the single corrupted member's tickets: the acceptance log, spent sets,
  and rate counters all concern that one secret `k`. Other members' traffic
  only consumes other budgets and other deposits; omitting it is sound and
  matches the spec's linear-summation clause.
- **Symbolic tickets.** As in `Zkpc.Core.State`: an accepted ticket *is*
  its extracted witness (knowledge soundness, Spec.md §5 assumption 1), so
  an accept is characterized by `(time, gateway, index, message)`. Forged
  proofs do not exist in the model; the nullifier `nf = H_nf(H_a(k, i))`
  *is* the index `i` (collision-freeness absorbed, §5 assumption 3).
- **Gateway-bound messages (MC14).** A message is a pair
  `m : Fin N × P` — the gateway it names, and the request payload. The
  `accept` guard `hbind : m.1 = g` is `Redeem` check 4. Consequence
  (Spec.md §1 MC14): serving one index at two gateways forces different
  messages, hence a *conflicting* pair — the divergence T6 prices. A
  bit-identical cross-gateway replay is impossible by construction, which
  is exactly the repair whose absence falsifies T6 (rev-1 counterexample).
- **Per-gateway spent sets and rate counters are derived views** of the
  acceptance log (`FSt.spentAt`, `rateCount`), not separate state — the log
  with timestamps is the primary object T6 counts. `Redeem`'s check-6
  freshness is the guard `hfresh` (index unseen *at this gateway*; the same
  index CAN be accepted at two different gateways — that is the lag-window
  divergence); check 5's budget is the guard `hrate`, counting **accepts
  only** (Spec.md §2: rejects and duplicates consume no budget), keyed by
  the epoch `clock / Te` of the member's epoch pseudonym — one pseudonym
  per epoch, the same at every gateway (MC3), so the per-gateway counter is
  per `(gateway, epoch)`.
- **Slash timing reads MC11's end-to-end `L` (Spec.md §1).** `L` folds
  gossip, evidence inclusion, and fleet-wide slash effect into one
  parameter, so the model has a single `slash` event whose time *is* the
  moment of fleet-wide effectiveness: `accept` requires `slashed = none`,
  i.e. a slash at time `ts` blocks accepts everywhere from `ts` on, with no
  further propagation delay (that delay is already inside `L`, which
  separates the second conflicting acceptance from `ts`).
- **`slash` is enabled only on real evidence** (`hconf`: a conflicting
  pair exists among accepted tickets — same index, different messages; the
  merge-time evidence of MC17 makes such a pair sufficient, and the RLN
  algebra of `Zkpc.Games.RLN` makes the ledger's recomputation sound).
  That the slash *happens*, and within `L`, is an honest-infrastructure
  guarantee (Spec.md §5 idealized ledger + §1 MC11 + §2 MC17: gateways
  reconcile, emit merge-time evidence, and the ledger includes it), NOT a
  power of the adversary's — so it enters T6 as the trace hypothesis
  `FleetFair`, never as a constraint the adversary could violate. Spec.md
  §6: `Δ` and `L` "are guarantees of the *model*, i.e., of honest
  infrastructure, not of the adversary".
- **`FleetFair` is deadline-aware**: it demands a slash only once a
  conflicting pair's `t₂ + L` deadline has passed (`… + L ≤ clock`). This
  is the faithful invariant form of "slashed within `L` of the second
  acceptance": it holds at *every* moment of an honestly reconciled
  execution, including mid-window states where the slash is not yet due —
  so T6 bounds every reachable point of a fair execution, not only
  post-slash states.

The key arithmetic fact behind T6's `⌈L/T_e⌉ + 1` factor — a window of
length `L` meets at most `⌈L/T_e⌉ + 1` epochs — is `epochs_in_window`
below, proved separately from the machine.
-/

namespace Zkpc.Fleet

open Finset

/-! ## Ceiling division and the epoch-window lemma -/

/-- Ceiling division on ℕ: `ceilDiv a t = ⌈a / t⌉` for `t > 0` (Spec.md §7
T6 writes `⌈L / T_e⌉`). Characterized by `le_mul_ceilDiv` (it is enough)
and `mul_ceilDiv_lt` (it is not more than one epoch too much). -/
def ceilDiv (a t : ℕ) : ℕ := (a + t - 1) / t

/-- `ceilDiv` sanity, upper direction: `a ≤ t · ⌈a/t⌉` — `⌈a/t⌉` epochs of
length `t` cover a window of length `a`. -/
theorem le_mul_ceilDiv {t : ℕ} (ht : 0 < t) (a : ℕ) : a ≤ t * ceilDiv a t := by
  have h := Nat.div_add_mod (a + t - 1) t
  have hm : (a + t - 1) % t < t := Nat.mod_lt _ ht
  unfold ceilDiv
  omega

/-- `ceilDiv` sanity, lower direction: `t · ⌈a/t⌉ < a + t` — the cover
overshoots by strictly less than one epoch, so `ceilDiv` is the exact
ceiling, not an over-approximation. -/
theorem mul_ceilDiv_lt {t : ℕ} (ht : 0 < t) (a : ℕ) : t * ceilDiv a t < a + t := by
  have h := Nat.div_add_mod (a + t - 1) t
  have hm : (a + t - 1) % t < t := Nat.mod_lt _ ht
  unfold ceilDiv
  omega

/-- Epoch monotone step: the last epoch a window `[a, a + w]` touches is at
most `⌈w/t⌉` epochs after the first (`t` = epoch length `T_e > 0`). -/
theorem div_window_le {t : ℕ} (ht : 0 < t) (a w : ℕ) :
    (a + w) / t ≤ a / t + ceilDiv w t :=
  calc (a + w) / t ≤ (a + t * ceilDiv w t) / t :=
        Nat.div_le_div_right (by have := le_mul_ceilDiv ht w; omega)
    _ = a / t + ceilDiv w t := Nat.add_mul_div_left a _ ht

/-- **The epoch-window lemma** (Spec.md §7 T6, "an `L`-window can straddle
`⌈L/T_e⌉ + 1` epochs, each with fresh budgets"): a time interval
`[a, a + w]` meets at most `⌈w/t⌉ + 1` distinct epochs of length `t > 0`
(epoch of time `s` = `s / t`). This is the discrete correction rev-1 found
missing from the smooth `r·L` reading, and it is the arithmetic heart of
T6's `f(L)` factor. -/
theorem epochs_in_window {t : ℕ} (ht : 0 < t) (a w : ℕ) :
    (Finset.Icc (a / t) ((a + w) / t)).card ≤ ceilDiv w t + 1 := by
  rw [Nat.card_Icc]
  have := div_window_le ht a w
  omega

/-! ## The machine -/

variable {N : ℕ} {P : Type}

/-- One accepted spend of the corrupted member (Spec.md §2 `Redeem`,
accept branch, symbolic form): the acceptance time, the serving gateway,
the spend index (≡ nullifier, §5 assumption 3), and the gateway-bound
message `(named gateway, payload)` (MC14). The accepted-spend ledger T6
quantifies over is a `Finset` of these. -/
structure Ev (N : ℕ) (P : Type) where
  /-- machine time of the acceptance -/
  time : ℕ
  /-- the gateway that accepted (serving gateway) -/
  gw : Fin N
  /-- spend index (symbolically: the nullifier `H_nf(H_a(k, i))`) -/
  idx : ℕ
  /-- the gateway-bound message `m = (G, payload)` (Spec.md §1, MC14) -/
  msg : Fin N × P
deriving DecidableEq

/-- A conflicting pair (Spec.md §2 `Redeem` evidence branch / MC17 merge):
same index (same nullifier), different messages — two distinct points on
the member's RLN line for that index, i.e. valid `Dispute` evidence
(`Zkpc.Games.RLN.rln_evidence_complete`). By MC14 gateway-binding, any
cross-gateway reuse of an index is automatically conflicting. -/
def Conflict (e₁ e₂ : Ev N P) : Prop :=
  e₁.idx = e₂.idx ∧ e₁.msg ≠ e₂.msg

instance [DecidableEq P] (e₁ e₂ : Ev N P) : Decidable (Conflict e₁ e₂) := by
  unfold Conflict; infer_instance

/-- Fleet machine state for the one corrupted member (see file docstring):
global clock, acceptance log with timestamps (primary object; per-gateway
spent sets and rate counters are derived views), and the slash flag with
its fleet-wide-effectiveness time (MC11 reading). -/
structure FSt (N : ℕ) (P : Type) where
  /-- global machine clock -/
  clock : ℕ
  /-- acceptance log: every accept of this member, fleet-wide -/
  log : Finset (Ev N P)
  /-- time at which the member's slash became effective fleet-wide, if any -/
  slashed : Option ℕ

namespace FSt

/-- Gateway `g`'s local spent set for this member (Spec.md §2, `SS_G`
restricted to the member's nullifiers), as a derived view of the log. -/
def spentAt (s : FSt N P) (g : Fin N) : Finset ℕ :=
  (s.log.filter fun e => e.gw = g).image Ev.idx

/-- Total accepted value at flat price `C` (Spec.md §7 T6: "total value of
accepted tickets attributed to `k`"; each accept is worth `C`, §3). -/
def acceptedValue (s : FSt N P) (C : ℕ) : ℕ :=
  C * s.log.card

end FSt

/-- Gateway `g`'s rate counter for the member's epoch pseudonym at epoch
`ep` (Spec.md §2 check 5 / §1 `b`): the number of *accepts* of this member
at `g` during `ep` (epoch of time `t` is `t / Te`; the pseudonym `nf_e` is
one per epoch and identical at every gateway, MC3). Derived from the log —
accepts only, per the rev-1 fidelity finding. -/
def rateCount (Te : ℕ) (log : Finset (Ev N P)) (g : Fin N) (ep : ℕ) : ℕ :=
  (log.filter fun e => e.gw = g ∧ e.time / Te = ep).card

/-- Initial state: clock 0, no accepts, not slashed. -/
def finit : FSt N P := { clock := 0, log := ∅, slashed := none }

/-- The fleet step relation, parameters `C` (flat price), `D` (deposit),
`b` (per-gateway per-epoch budget), `Te` (epoch length). Three actions:

- `tick` — time passes (the adversary controls scheduling, Spec.md §6).
- `accept` — `Redeem`'s accept branch at gateway `g` (Spec.md §2), with
  every admission check as a guard: the slash-eviction check (`hslash`,
  check 2 root rotation, MC5/MC11: a slash effective at `ts` blocks
  accepts everywhere from `ts`), solvency (`hsolv`, `R_spend` conjunct 2,
  §3), gateway binding (`hbind`, check 4, MC14), nullifier freshness at
  this gateway (`hfresh`, check 6 — the same index at *another* gateway is
  not blocked: that divergence is what T6 prices), and the epoch budget
  (`hrate`, check 5, accepts strictly under `b`).
- `slash` — `Dispute` lands fleet-wide (MC11): enabled exactly when the
  accepted log contains a conflicting pair (MC17 merge-time evidence makes
  any such pair produce `Dispute` input; `Zkpc.Games.RLN` makes the
  ledger's check sound). WHEN it fires is the scheduler's choice; that it
  fires within `L` is the honest-infrastructure guarantee `FleetFair`,
  assumed at the theorem level, not here. -/
inductive FStep [DecidableEq P] (C D b Te : ℕ) : FSt N P → FSt N P → Prop
  | tick (s : FSt N P) :
      FStep C D b Te s { s with clock := s.clock + 1 }
  | accept (s : FSt N P) (g : Fin N) (i : ℕ) (m : Fin N × P)
      (hbind : m.1 = g)
      (hslash : s.slashed = none)
      (hsolv : (i + 1) * C ≤ D)
      (hfresh : ∀ e ∈ s.log, e.gw = g → e.idx ≠ i)
      (hrate : rateCount Te s.log g (s.clock / Te) < b) :
      FStep C D b Te s { s with log := insert ⟨s.clock, g, i, m⟩ s.log }
  | slash (s : FSt N P)
      (hconf : ∃ e₁ ∈ s.log, ∃ e₂ ∈ s.log, Conflict e₁ e₂)
      (hns : s.slashed = none) :
      FStep C D b Te s { s with slashed := some s.clock }

/-- Reachability from `finit` under the fleet step relation. A `FReach`
derivation *is* an execution trace; `s.log` at the reached state is the
complete accepted-spend ledger of the execution (each `accept` inserts
exactly one fresh event — `FStep.log_growth` — and nothing is ever
removed). -/
inductive FReach [DecidableEq P] (C D b Te : ℕ) : FSt N P → Prop
  | init : FReach C D b Te finit
  | step {s s' : FSt N P} :
      FReach C D b Te s → FStep C D b Te s s' → FReach C D b Te s'

/-- **The honest-fleet reconciliation guarantee** (Spec.md §1 MC11
end-to-end `L`, §2 MC17 merge-time evidence, §5 idealized ledger; §6: a
model guarantee, not an adversary power): every conflicting accepted pair
whose deadline `t₂ + L` has passed (`t₂` = time of the later acceptance)
has been answered by a fleet-wide-effective slash at some `ts ≤ t₂ + L`.

Deadline-aware form (file docstring): nothing is demanded of conflicts
younger than `L`, so this predicate holds at *every* state of an honestly
reconciled execution — it is the trace hypothesis under which T6 is
stated, and `T6_slash_within_L` is its restatement as T6's clause (ii). -/
def FleetFair (L : ℕ) (s : FSt N P) : Prop :=
  ∀ e₁ ∈ s.log, ∀ e₂ ∈ s.log, Conflict e₁ e₂ →
    max e₁.time e₂.time + L ≤ s.clock →
    ∃ ts, s.slashed = some ts ∧ ts ≤ max e₁.time e₂.time + L

section Invariants

variable [DecidableEq P]

/-- Safety invariants of the fleet machine, established at every reachable
state by `fleet_inv` (task G1's model facts; each field cites its Spec.md
source). -/
structure Inv (C D b Te : ℕ) (s : FSt N P) : Prop where
  /-- acceptance times never exceed the clock -/
  time_le_clock : ∀ e ∈ s.log, e.time ≤ s.clock
  /-- no acceptance postdates the (fleet-wide effective) slash — the MC5
  eviction: post-slash spend proofs fail everywhere -/
  time_le_slash : ∀ e ∈ s.log, ∀ ts, s.slashed = some ts → e.time ≤ ts
  /-- accepted messages name their serving gateway (MC14, check 4) -/
  gw_bound : ∀ e ∈ s.log, e.msg.1 = e.gw
  /-- every accepted index satisfies solvency (§3 `R_spend` conjunct 2) -/
  solvent : ∀ e ∈ s.log, (e.idx + 1) * C ≤ D
  /-- per-gateway nullifier freshness (check 6): one accept per index per
  gateway — cross-gateway reuse is possible and is the priced divergence -/
  idx_uniq : ∀ e₁ ∈ s.log, ∀ e₂ ∈ s.log, e₁.gw = e₂.gw → e₁.idx = e₂.idx → e₁ = e₂
  /-- every rate counter respects the budget (check 5): at most `b`
  accepts per gateway per epoch of the member's pseudonym -/
  rate_le : ∀ g ep, rateCount Te s.log g ep ≤ b
  /-- slash soundness: the member was slashed only on real evidence — a
  conflicting accepted pair exists (Spec.md §2 `Dispute`; no framing, per
  the `Zkpc.Games.RLN` algebra and T7) -/
  slash_sound : ∀ ts, s.slashed = some ts →
    ∃ e₁ ∈ s.log, ∃ e₂ ∈ s.log, Conflict e₁ e₂

/-- Each step either leaves the log unchanged or inserts exactly one fresh
event (the `accept` action). Hence along any trace, `s.log.card` is
exactly the number of `accept` actions taken — "total accepts over the
entire execution", the quantity T6 bounds. -/
theorem FStep.log_growth {C D b Te : ℕ} {s s' : FSt N P}
    (h : FStep C D b Te s s') :
    s'.log = s.log ∨ ∃ e, e ∉ s.log ∧ s'.log = insert e s.log := by
  cases h with
  | tick => exact Or.inl rfl
  | accept g i m hbind hslash hsolv hfresh hrate =>
    exact Or.inr ⟨⟨_, g, i, m⟩, fun hmem => hfresh _ hmem rfl rfl, rfl⟩
  | slash hconf hns => exact Or.inl rfl

/-- The invariants hold at every reachable state. -/
theorem fleet_inv {C D b Te : ℕ} {s : FSt N P}
    (h : FReach C D b Te s) : Inv C D b Te s := by
  induction h with
  | init =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [finit, rateCount]
  | @step s s' hprev hstep ih =>
    obtain ⟨hTc, hTs, hGb, hSo, hUq, hRt, hSs⟩ := ih
    cases hstep with
    | tick =>
      exact ⟨fun e he => Nat.le_succ_of_le (hTc e he),
        hTs, hGb, hSo, hUq, hRt, hSs⟩
    | accept g i m hbind hslash hsolv hfresh hrate =>
      have hnotmem : (⟨s.clock, g, i, m⟩ : Ev N P) ∉ s.log :=
        fun hmem => hfresh _ hmem rfl rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- time_le_clock
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact Nat.le_refl _
        · exact hTc e he'
      · -- time_le_slash: still unslashed
        intro e he ts hts
        rw [hslash] at hts
        exact absurd hts (by simp)
      · -- gw_bound
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact hbind
        · exact hGb e he'
      · -- solvent
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact hsolv
        · exact hSo e he'
      · -- idx_uniq
        intro e₁ h₁ e₂ h₂ hgw hidx
        rcases Finset.mem_insert.mp h₁ with rfl | h₁' <;>
          rcases Finset.mem_insert.mp h₂ with rfl | h₂'
        · rfl
        · exact absurd hidx.symm (hfresh e₂ h₂' hgw.symm)
        · exact absurd hidx (hfresh e₁ h₁' hgw)
        · exact hUq e₁ h₁' e₂ h₂' hgw hidx
      · -- rate_le
        intro g' ep'
        show rateCount Te (insert ⟨s.clock, g, i, m⟩ s.log) g' ep' ≤ b
        by_cases hp : g = g' ∧ s.clock / Te = ep'
        · obtain ⟨rfl, rfl⟩ := hp
          unfold rateCount at hrate ⊢
          rw [Finset.filter_insert, if_pos (by simp),
            Finset.card_insert_of_notMem
              (fun hm => hnotmem (Finset.mem_filter.mp hm).1)]
          omega
        · unfold rateCount
          rw [Finset.filter_insert, if_neg (by simpa using hp)]
          exact hRt g' ep'
      · -- slash_sound: still unslashed
        intro ts hts
        rw [hslash] at hts
        exact absurd hts (by simp)
    | slash hconf hns =>
      refine ⟨hTc, ?_, hGb, hSo, hUq, hRt, ?_⟩
      · -- time_le_slash: the slash time is the current clock
        intro e he ts hts
        have : ts = s.clock := by
          simpa using hts.symm
        exact this ▸ hTc e he
      · -- slash_sound
        intro ts _
        exact hconf

end Invariants

end Zkpc.Fleet
