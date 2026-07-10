import Zkpc.Network.Refinement

/-!
# Adversarial transaction scheduling and rejection refinement

`Network.execTrace` stops at the first rejected action.  A deployed mempool
does not: adversaries may reorder transactions, invalid calls fail, and later
transactions continue.  This module gives that total scheduler semantics.
Every successful action takes its proved symbolic step; every rejected action
is a state-preserving stutter.  Hence any finite adversarial ordering remains
reachable and inherits global deduplication and no-overspend.
-/

namespace Zkpc.Network

variable {Recipient Nf Payload : Type}
variable [DecidableEq Recipient] [DecidableEq Nf] [DecidableEq Payload]

/-- Outcome of one submitted transaction. -/
inductive TxOutcome
  | applied
  | rejected
  deriving DecidableEq, Repr

/-- Total transaction execution: failed guards reject without changing state. -/
def execTransaction (s : St Recipient Nf Payload)
    (a : Act Recipient Nf Payload) : TxOutcome × St Recipient Nf Payload :=
  match execStep s a with
  | some s' => (.applied, s')
  | none => (.rejected, s)

/-- Execute an adversarially ordered batch, retaining every success/failure
outcome for audit. -/
def execScheduled : St Recipient Nf Payload →
    List (Act Recipient Nf Payload) →
      List TxOutcome × St Recipient Nf Payload
  | s, [] => ([], s)
  | s, a :: actions =>
      let (outcome, s') := execTransaction s a
      let (outcomes, t) := execScheduled s' actions
      (outcome :: outcomes, t)

/-- One total transaction preserves reachability: applied calls refine to a
symbolic step, while rejected calls stutter. -/
theorem execTransaction_reachable {D : ℕ}
    {s : St Recipient Nf Payload} (hreach : Reach D s)
    (a : Act Recipient Nf Payload) :
    Reach D (execTransaction s a).2 := by
  unfold execTransaction
  cases h : execStep s a with
  | none => exact hreach
  | some s' => exact Reach.step hreach (execStep_sound h)

/-- Every finite adversarial schedule preserves symbolic reachability. -/
theorem execScheduled_reachable {D : ℕ}
    {s : St Recipient Nf Payload} (hreach : Reach D s) :
    ∀ actions, Reach D (execScheduled s actions).2 := by
  intro actions
  induction actions generalizing s with
  | nil => exact hreach
  | cons a actions ih =>
      simp only [execScheduled]
      cases htx : execTransaction s a with
      | mk outcome s' =>
          simp only
          apply ih
          have hs' := execTransaction_reachable hreach a
          simpa [htx] using hs'

/-- **Scheduler safety.** Reordering, replaying, and mixing invalid and valid
transactions cannot exceed the shared deposit or duplicate a global
nullifier in the accepted set. -/
theorem execScheduled_safety (D : ℕ)
    (actions : List (Act Recipient Nf Payload)) :
    let terminal := (execScheduled (init D) actions).2
    terminal.totalPaid ≤ D ∧ NfUnique terminal.accepted := by
  intro terminal
  have hreach : Reach D terminal := execScheduled_reachable Reach.init actions
  exact ⟨no_overspend hreach, global_dedup hreach⟩

/-- Outcome logging is complete: exactly one outcome is recorded per submitted
transaction, including rejected transactions. -/
theorem execScheduled_outcomes_length
    (s : St Recipient Nf Payload) : ∀ actions,
    (execScheduled s actions).1.length = actions.length := by
  intro actions
  induction actions generalizing s with
  | nil => rfl
  | cons a actions ih =>
      simp only [execScheduled]
      cases execTransaction s a with
      | mk outcome s' =>
          simp only [List.length_cons]
          rw [ih s']

end Zkpc.Network

#print axioms Zkpc.Network.execTransaction_reachable
#print axioms Zkpc.Network.execScheduled_reachable
#print axioms Zkpc.Network.execScheduled_safety
#print axioms Zkpc.Network.execScheduled_outcomes_length
