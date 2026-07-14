import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Portable-deposit multi-recipient payment network

This is the network generalization absent from the original recipient-bound
object. One deposit funds payments to any registered recipient. Nullifiers
are deduplicated globally, so moving a ticket between recipients cannot create
additional value; settlement is recipient-directed and charged against the
single shared deposit.

The model deliberately separates the portable accounting object from a
particular credential system. A Coconut/zk-nym-style threshold ticketbook or a
portable NIZK membership proof can instantiate `Event`; the safety proof only
needs globally unique nullifiers and the explicit value bound.
-/

namespace Zkpc.Network

open scoped BigOperators

variable {Recipient Nf Payload : Type}
variable [DecidableEq Recipient] [DecidableEq Nf] [DecidableEq Payload]

/-- One recipient-bound network payment. The nullifier is global even though
the payload and settlement destination are recipient-specific. -/
structure Event (Recipient Nf Payload : Type) where
  recipient : Recipient
  nf : Nf
  value : ℕ
  payload : Payload
deriving DecidableEq

/-- Shared-deposit network state. Accepted events remain as the audit log;
`settled` records the paid subset and `totalPaid` is executable accounting. -/
structure St (Recipient Nf Payload : Type) where
  clock : ℕ
  deposit : ℕ
  accepted : Finset (Event Recipient Nf Payload)
  settled : Finset (Event Recipient Nf Payload)
  totalPaid : ℕ

/-- Open one portable deposit, initially usable at every recipient. -/
def init (D : ℕ) : St Recipient Nf Payload :=
  ⟨0, D, ∅, ∅, 0⟩

/-- Global nullifier uniqueness, stronger than per-recipient replay defense. -/
def NfUnique (xs : Finset (Event Recipient Nf Payload)) : Prop :=
  ∀ e₁ ∈ xs, ∀ e₂ ∈ xs, e₁.nf = e₂.nf → e₁ = e₂

/-- Sum of values in an event set. -/
def valueSum (xs : Finset (Event Recipient Nf Payload)) : ℕ :=
  ∑ e ∈ xs, e.value

/-- Network actions: time, recipient admission, and ledger settlement. -/
inductive Act (Recipient Nf Payload : Type)
  | tick
  | accept (ev : Event Recipient Nf Payload)
  | settle (ev : Event Recipient Nf Payload)

/-- Network transition relation. Admission uses fleet-wide nullifier
freshness. Settlement pays an accepted event at most once and never exceeds
the portable deposit. -/
inductive Step : St Recipient Nf Payload → Act Recipient Nf Payload →
    St Recipient Nf Payload → Prop
  | tick (s) :
      Step s .tick { s with clock := s.clock + 1 }
  | accept (s) (ev : Event Recipient Nf Payload)
      (hfresh : ∀ old ∈ s.accepted, old.nf ≠ ev.nf) :
      Step s (.accept ev) { s with accepted := insert ev s.accepted }
  | settle (s) (ev : Event Recipient Nf Payload)
      (haccepted : ev ∈ s.accepted) (hunpaid : ev ∉ s.settled)
      (hbudget : s.totalPaid + ev.value ≤ s.deposit) :
      Step s (.settle ev)
        { s with settled := insert ev s.settled
                 totalPaid := s.totalPaid + ev.value }

/-- Reachability from a single portable deposit. -/
inductive Reach (D : ℕ) : St Recipient Nf Payload → Prop
  | init : Reach D (init D)
  | step {s s' a} : Reach D s → Step s a s' → Reach D s'

/-- Inductive network safety invariant. -/
structure Inv (D : ℕ) (s : St Recipient Nf Payload) : Prop where
  deposit_eq : s.deposit = D
  settled_sub : s.settled ⊆ s.accepted
  paid_eq : s.totalPaid = valueSum s.settled
  paid_le : s.totalPaid ≤ s.deposit
  nf_unique : NfUnique s.accepted

/-- Every reachable multi-recipient state satisfies conservation, global
deduplication, and the portable-deposit bound. -/
theorem reach_inv {D : ℕ} {s : St Recipient Nf Payload} (h : Reach D s) :
    Inv D s := by
  induction h with
  | init =>
      refine ⟨rfl, by simp [init], by simp [init, valueSum], by simp [init], ?_⟩
      simp [NfUnique, init]
  | step hreach hstep ih =>
      cases hstep with
      | tick =>
          exact ⟨ih.deposit_eq, ih.settled_sub, ih.paid_eq,
            ih.paid_le, ih.nf_unique⟩
      | accept ev hfresh =>
          refine ⟨ih.deposit_eq, ?_, ih.paid_eq, ih.paid_le, ?_⟩
          · intro e he
            exact Finset.mem_insert_of_mem (ih.settled_sub he)
          · intro e₁ he₁ e₂ he₂ hnf
            rcases Finset.mem_insert.mp he₁ with h₁ | h₁
            · subst e₁
              rcases Finset.mem_insert.mp he₂ with h₂ | h₂
              · exact h₂.symm
              · exact False.elim ((hfresh e₂ h₂) hnf.symm)
            · rcases Finset.mem_insert.mp he₂ with h₂ | h₂
              · subst e₂
                exact False.elim ((hfresh e₁ h₁) hnf)
              · exact ih.nf_unique e₁ h₁ e₂ h₂ hnf
      | settle ev haccepted hunpaid hbudget =>
          refine ⟨ih.deposit_eq, ?_, ?_, hbudget, ih.nf_unique⟩
          · intro e he
            rcases Finset.mem_insert.mp he with rfl | he
            · exact haccepted
            · exact ih.settled_sub he
          · simpa [valueSum, Finset.sum_insert hunpaid, ih.paid_eq,
              Nat.add_comm]

/-- Network-wide no-overspend for one deposit shared by arbitrarily many
recipients. -/
theorem no_overspend {D : ℕ} {s : St Recipient Nf Payload} (h : Reach D s) :
    s.totalPaid ≤ D := by
  have hi := reach_inv h
  simpa [hi.deposit_eq] using hi.paid_le

/-- All settled events were admitted and no two admitted events share a
nullifier, even when they name different recipients. -/
theorem global_dedup {D : ℕ} {s : St Recipient Nf Payload} (h : Reach D s) :
    NfUnique s.accepted :=
  (reach_inv h).nf_unique

/-- A recipient's local accepted-event view. -/
def acceptedView (r : Recipient) (s : St Recipient Nf Payload) :=
  s.accepted.filter (fun ev => ev.recipient = r)

/-- A recipient's local settled-event view. -/
def settledView (r : Recipient) (s : St Recipient Nf Payload) :=
  s.settled.filter (fun ev => ev.recipient = r)

/-- Value paid to one recipient, derived from its isolated settled view. -/
def paidTo (r : Recipient) (s : St Recipient Nf Payload) : ℕ :=
  valueSum (settledView r s)

/-- Traffic admitted for another recipient is invisible in this recipient's
accepted view. This is the deterministic information-flow boundary on which
the cryptographic unlinkability game is layered. -/
theorem acceptedView_insert_other (r : Recipient)
    (ev : Event Recipient Nf Payload) (s : St Recipient Nf Payload)
    (hne : ev.recipient ≠ r) :
    acceptedView r { s with accepted := insert ev s.accepted } = acceptedView r s := by
  unfold acceptedView
  rw [Finset.filter_insert]
  simp [acceptedView, hne]

/-- Settlement for another recipient neither changes this recipient's view
nor its derived payout. -/
theorem settledView_insert_other (r : Recipient)
    (ev : Event Recipient Nf Payload) (s : St Recipient Nf Payload)
    (hne : ev.recipient ≠ r) :
    settledView r { s with settled := insert ev s.settled } = settledView r s := by
  unfold settledView
  rw [Finset.filter_insert]
  simp [settledView, hne]

theorem paidTo_insert_other (r : Recipient)
    (ev : Event Recipient Nf Payload) (s : St Recipient Nf Payload)
    (hne : ev.recipient ≠ r) :
    paidTo r { s with settled := insert ev s.settled } = paidTo r s := by
  rw [paidTo, paidTo, settledView_insert_other r ev s hne]

/-! ## Executable operations and refinement -/

/-- Execute global-nullifier admission. -/
def execAccept (s : St Recipient Nf Payload) (ev : Event Recipient Nf Payload) :
    Option (St Recipient Nf Payload) :=
  if ∀ old ∈ s.accepted, old.nf ≠ ev.nf then
    some { s with accepted := insert ev s.accepted }
  else none

/-- Execute recipient-directed settlement against the portable balance. -/
def execSettle (s : St Recipient Nf Payload) (ev : Event Recipient Nf Payload) :
    Option (St Recipient Nf Payload) :=
  if ev ∈ s.accepted ∧ ev ∉ s.settled ∧
      s.totalPaid + ev.value ≤ s.deposit then
    some { s with settled := insert ev s.settled
                  totalPaid := s.totalPaid + ev.value }
  else none

/-- Executable admission is exactly the relational network step. -/
theorem execAccept_refines (s : St Recipient Nf Payload)
    (ev : Event Recipient Nf Payload)
    (hfresh : ∀ old ∈ s.accepted, old.nf ≠ ev.nf) :
    ∃ s', execAccept s ev = some s' ∧ Step s (.accept ev) s' := by
  refine ⟨{ s with accepted := insert ev s.accepted }, ?_, Step.accept s ev hfresh⟩
  have hfresh' : ∀ old ∈ s.accepted, ¬ old.nf = ev.nf := by
    intro old hold heq
    exact hfresh old hold heq
  rw [execAccept, if_pos hfresh']

/-- Portability: admission has no recipient-specific escrow partition. Any
recipient can receive the next globally fresh event from the same deposit. -/
theorem portable_accept_enabled (s : St Recipient Nf Payload)
    (ev : Event Recipient Nf Payload)
    (hfresh : ∀ old ∈ s.accepted, old.nf ≠ ev.nf) :
    execAccept s ev ≠ none := by
  obtain ⟨s', hs', _⟩ := execAccept_refines s ev hfresh
  rw [hs']
  simp

/-- Executable settlement is exactly the relational network step. -/
theorem execSettle_refines (s : St Recipient Nf Payload)
    (ev : Event Recipient Nf Payload) (haccepted : ev ∈ s.accepted)
    (hunpaid : ev ∉ s.settled)
    (hbudget : s.totalPaid + ev.value ≤ s.deposit) :
    ∃ s', execSettle s ev = some s' ∧ Step s (.settle ev) s' := by
  refine ⟨{ s with settled := insert ev s.settled
                     , totalPaid := s.totalPaid + ev.value }, ?_,
    Step.settle s ev haccepted hunpaid hbudget⟩
  simp [execSettle, haccepted, hunpaid, hbudget]

end Zkpc.Network

#print axioms Zkpc.Network.reach_inv
#print axioms Zkpc.Network.no_overspend
#print axioms Zkpc.Network.global_dedup
#print axioms Zkpc.Network.acceptedView_insert_other
#print axioms Zkpc.Network.settledView_insert_other
#print axioms Zkpc.Network.paidTo_insert_other
#print axioms Zkpc.Network.execAccept_refines
#print axioms Zkpc.Network.portable_accept_enabled
#print axioms Zkpc.Network.execSettle_refines
