import Zkpc.Network.Credential

/-!
# Executable multi-recipient ledger refinement

`Network.State` proves refinement for individual admission and settlement
calls.  This module supplies the complete action dispatcher and an executable
list scheduler, then proves that every successful finite execution is a
symbolic network trace.  Consequently global nullifier deduplication and the
shared-deposit bound apply directly to executable multi-recipient runs.
-/

namespace Zkpc.Network

variable {Recipient Nf Payload : Type}
variable [DecidableEq Recipient] [DecidableEq Nf] [DecidableEq Payload]

/-- Execute any portable-network ledger action. -/
def execStep (s : St Recipient Nf Payload) :
    Act Recipient Nf Payload → Option (St Recipient Nf Payload)
  | .tick => some { s with clock := s.clock + 1 }
  | .accept ev => execAccept s ev
  | .settle ev => execSettle s ev

/-- Every successful executable network action is a symbolic transition. -/
theorem execStep_sound {s s' : St Recipient Nf Payload}
    {a : Act Recipient Nf Payload} (h : execStep s a = some s') :
    Step s a s' := by
  cases a with
  | tick =>
      simp only [execStep, Option.some.injEq] at h
      exact h ▸ Step.tick s
  | accept ev =>
      simp only [execStep, execAccept] at h
      split at h <;> rename_i guard
      · exact Option.some.inj h ▸ Step.accept s ev guard
      · contradiction
  | settle ev =>
      simp only [execStep, execSettle] at h
      split at h <;> rename_i guard
      · rcases guard with ⟨haccepted, hunpaid, hbudget⟩
        exact Option.some.inj h ▸ Step.settle s ev haccepted hunpaid hbudget
      · contradiction

/-- The dispatcher executes every relational network transition. -/
theorem execStep_complete {s s' : St Recipient Nf Payload}
    {a : Act Recipient Nf Payload} (h : Step s a s') :
    execStep s a = some s' := by
  cases h with
  | tick => rfl
  | accept ev fresh =>
      have fresh' : ∀ old ∈ s.accepted, ¬ old.nf = ev.nf := by
        intro old hold heq
        exact fresh old hold heq
      rw [execStep, execAccept, if_pos fresh']
  | settle ev accepted unpaid budget =>
      simp [execStep, execSettle, accepted, unpaid, budget]

/-- Execute a finite adversarially scheduled list of network actions,
stopping at the first rejected action. -/
def execTrace : St Recipient Nf Payload →
    List (Act Recipient Nf Payload) → Option (St Recipient Nf Payload)
  | s, [] => some s
  | s, a :: actions => execStep s a >>= fun s' => execTrace s' actions

/-- Successful executable traces preserve symbolic reachability. -/
theorem execTrace_reachable {D : ℕ} {s t : St Recipient Nf Payload}
    (hreach : Reach D s) : ∀ {actions}, execTrace s actions = some t → Reach D t := by
  intro actions
  induction actions generalizing s with
  | nil =>
      simp only [execTrace, Option.some.injEq]
      intro h
      exact h ▸ hreach
  | cons a actions ih =>
      simp only [execTrace, Option.bind_eq_bind]
      cases hstep : execStep s a with
      | none => simp
      | some s' =>
          simp only [Option.bind_some]
          intro htail
          exact ih (Reach.step hreach (execStep_sound hstep)) htail

/-- Executable multi-recipient runs inherit both headline ledger invariants. -/
theorem execTrace_safety {D : ℕ} {actions : List (Act Recipient Nf Payload)}
    {t : St Recipient Nf Payload}
    (hexec : execTrace (init D) actions = some t) :
    t.totalPaid ≤ D ∧ NfUnique t.accepted := by
  have hreach : Reach D t := execTrace_reachable Reach.init hexec
  exact ⟨no_overspend hreach, global_dedup hreach⟩

end Zkpc.Network

#print axioms Zkpc.Network.execStep_sound
#print axioms Zkpc.Network.execStep_complete
#print axioms Zkpc.Network.execTrace_reachable
#print axioms Zkpc.Network.execTrace_safety
