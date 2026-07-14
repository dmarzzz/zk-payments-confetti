import Zkpc.Refund.Safety

/-!
# Refund close-upgrade cascade

This module formalizes the receipt-withholding repair of Spec.md §2/MC18.
A stale close starts at a claimed certified count `j`; every dispute may
publish exactly the next withheld receipt and upgrade the claim by one.  Once
the claim reaches the channel's true certified count `n`, the close settles.

The transition system proves the two scheduler-independent facts needed by
T2-B: no upgrade can overshoot `n`, and a terminal execution cannot strand an
active close.  It also proves the sharp accounting statement: a close that
started at `j` settles after exactly `n - j` upgrade sub-windows.
-/

namespace Zkpc.Refund

/-- Public state of one refund close cascade. -/
structure CascadeSt where
  /-- count currently certified by the close window -/
  claim : ℕ
  /-- number of successful receipt upgrades so far -/
  upgrades : ℕ
  /-- whether the close is still awaiting another upgrade or settlement -/
  active : Bool

/-- Initial stale-close window at advertised count `j`. -/
def CascadeSt.init (j : ℕ) : CascadeSt := ⟨j, 0, true⟩

/-- One contract-controlled cascade transition for true certified count `n`.
An upgrade consumes the next receipt; settlement is enabled exactly at `n`. -/
inductive CascadeStep (n : ℕ) : CascadeSt → CascadeSt → Prop
  | upgrade (s : CascadeSt)
      (hactive : s.active = true) (hstale : s.claim < n) :
      CascadeStep n s ⟨s.claim + 1, s.upgrades + 1, s.active⟩
  | settle (s : CascadeSt)
      (hactive : s.active = true) (hcurrent : s.claim = n) :
      CascadeStep n s { s with active := false }

/-- Reachability of a cascade beginning with claim `j`. -/
inductive CascadeReach (n j : ℕ) : CascadeSt → Prop
  | init : CascadeReach n j (CascadeSt.init j)
  | step {s s' : CascadeSt} :
      CascadeReach n j s → CascadeStep n s s' → CascadeReach n j s'

/-- Deterministic contract driver: upgrade a stale active claim, settle a
current active claim, and reject inactive or impossible overshooting states. -/
def execCascade (n : ℕ) (s : CascadeSt) : Option CascadeSt :=
  if s.active = true then
    if s.claim < n then some ⟨s.claim + 1, s.upgrades + 1, s.active⟩
    else if s.claim = n then some { s with active := false }
    else none
  else none

/-- Executable stale-claim advancement is exactly `CascadeStep.upgrade`. -/
theorem execCascade_upgrade (n : ℕ) (s : CascadeSt)
    (hactive : s.active = true) (hstale : s.claim < n) :
    ∃ s', execCascade n s = some s' ∧ CascadeStep n s s' := by
  refine ⟨⟨s.claim + 1, s.upgrades + 1, s.active⟩, ?_,
    CascadeStep.upgrade s hactive hstale⟩
  simp [execCascade, hactive, hstale]

/-- Executable current-claim settlement is exactly `CascadeStep.settle`. -/
theorem execCascade_settle (n : ℕ) (s : CascadeSt)
    (hactive : s.active = true) (hcurrent : s.claim = n) :
    ∃ s', execCascade n s = some s' ∧ CascadeStep n s s' := by
  refine ⟨{ s with active := false }, ?_, CascadeStep.settle s hactive hcurrent⟩
  simp [execCascade, hactive, hcurrent]

/-- The central cascade invariant: the public claim is the initial claim plus
the number of upgrades, never exceeds the true count, and an inactive window
has reached the true count. -/
def CascadeInv (n j : ℕ) (s : CascadeSt) : Prop :=
  s.claim = j + s.upgrades ∧ s.claim ≤ n ∧
    (s.active = false → s.claim = n)

/-- Every reachable cascade state satisfies the accounting invariant. -/
theorem cascadeReach_inv {n j : ℕ} (hjn : j ≤ n) {s : CascadeSt}
    (h : CascadeReach n j s) : CascadeInv n j s := by
  induction h with
  | init => simp [CascadeInv, CascadeSt.init, hjn]
  | @step s s' _ hstep ih =>
    obtain ⟨hcount, hle, hdone⟩ := ih
    cases hstep with
    | upgrade hactive hstale =>
      refine ⟨?_, Nat.succ_le_of_lt hstale, ?_⟩
      · show s.claim + 1 = j + (s.upgrades + 1)
        omega
      · intro hinactive
        simp only at hinactive
        exact absurd hinactive (by simpa using hactive)
    | settle hactive hcurrent =>
      exact ⟨hcount, hle, fun _ => hcurrent⟩

/-- Every reachable active cascade has an executable next contract action. -/
theorem execCascade_progress {n j : ℕ} (hjn : j ≤ n)
    {s : CascadeSt} (hreach : CascadeReach n j s) (hactive : s.active = true) :
    ∃ s', execCascade n s = some s' ∧ CascadeStep n s s' := by
  have hle := (cascadeReach_inv hjn hreach).2.1
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact execCascade_upgrade n s hactive hlt
  · exact execCascade_settle n s hactive heq

/-- A close can undergo at most its initial count understatement many
upgrades. -/
theorem cascade_upgrades_le_understatement {n j : ℕ} (hjn : j ≤ n)
    {s : CascadeSt} (h : CascadeReach n j s) :
    s.upgrades ≤ n - j := by
  obtain ⟨hcount, hle, -⟩ := cascadeReach_inv hjn h
  omega

/-- Once the cascade settles, its claim is exactly the certified count. -/
theorem cascade_settled_at_true_count {n j : ℕ} (hjn : j ≤ n)
    {s : CascadeSt} (h : CascadeReach n j s)
    (hsettled : s.active = false) : s.claim = n :=
  (cascadeReach_inv hjn h).2.2 hsettled

/-- Sharp round count: settlement after an initial claim `j` uses exactly
`n-j` receipt-upgrade sub-windows. -/
theorem cascade_settled_upgrades_eq {n j : ℕ} (hjn : j ≤ n)
    {s : CascadeSt} (h : CascadeReach n j s)
    (hsettled : s.active = false) : s.upgrades = n - j := by
  obtain ⟨hcount, -, hdone⟩ := cascadeReach_inv hjn h
  have hclaim := hdone hsettled
  omega

/-- A state is terminal when no contract transition is enabled. -/
def CascadeTerminal (n : ℕ) (s : CascadeSt) : Prop :=
  ¬ ∃ s', CascadeStep n s s'

/-- Scheduler-independent progress: a reachable terminal cascade is settled;
it cannot remain active at either a stale or current count. -/
theorem cascade_terminal_settled {n j : ℕ} (hjn : j ≤ n)
    {s : CascadeSt} (h : CascadeReach n j s)
    (hterminal : CascadeTerminal n s) : s.active = false := by
  by_contra hnot
  have hactive : s.active = true := by
    cases hs : s.active <;> simp_all
  have hle := (cascadeReach_inv hjn h).2.1
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hterminal ⟨⟨s.claim + 1, s.upgrades + 1, s.active⟩,
      CascadeStep.upgrade s hactive hlt⟩
  · exact hterminal ⟨{ s with active := false },
      CascadeStep.settle s hactive heq⟩

/-- The fully upgraded window settles to the same close-time netting formula
used by the refund machine.  This connects the cascade count endpoint to the
existing cooperative settlement arithmetic. -/
theorem cascade_final_payouts (Cmax D R n : ℕ)
    (hR : R ≤ n * Cmax) (hsolv : n * Cmax ≤ D + R) :
    ((D + R) - n * Cmax) + (n * Cmax - R) = D := by
  omega

end Zkpc.Refund

#print axioms Zkpc.Refund.cascadeReach_inv
#print axioms Zkpc.Refund.execCascade_upgrade
#print axioms Zkpc.Refund.execCascade_settle
#print axioms Zkpc.Refund.execCascade_progress
#print axioms Zkpc.Refund.cascade_upgrades_le_understatement
#print axioms Zkpc.Refund.cascade_settled_upgrades_eq
#print axioms Zkpc.Refund.cascade_terminal_settled
#print axioms Zkpc.Refund.cascade_final_payouts
