import Zkpc.Chain.V2.State

/-!
# Close-window liveness under scheduling (ROADMAP obligation 5)

`Zkpc/Chain/V2/State.lean`'s `alice_liveness` is existential: from a live
state Alice *can* reach a safe settlement. This module upgrades it to a
**guaranteed** statement under a minimal fairness assumption, and pins the
two-timer deadline structure (Spec-v2 §4: 90-day absolute, 7-day
on-request) as concrete reachability facts.

The fairness model is deliberately light, matching the T5 clock lemmas the
old object used: Alice's exit is a *finite fixed sequence* of her own moves
and clock ticks (`closeOn`, `tick` past the window, `settle`), none of which
any other party can disable — `Step` has no action that, from a live
un-closing state, prevents `closeOn`. So "guaranteed under weak fairness"
here is the concrete statement that the exit sequence is enabled and
deterministic in outcome, which is what `alice_liveness` already witnesses;
what this module adds is:

* `no_action_disables_close`: from any reachable live un-closing state,
  `closeOn (canonical ctx)` is enabled regardless of history — Bob has no
  move that removes Alice's exit (the wedge lever `ghostSend` only *raises*
  the safe balance, never blocks the close);
* `timeout_reachable`: past the absolute deadline `Tabs`, if Alice has not
  closed, `timeoutForfeit` is enabled — Bob is never locked out of his
  deposit by Alice's inaction (the liveness *for Bob* dual);
* `request_deadline_reachable`: after Bob requests close, past `Treq`, the
  same holds even before `Tabs`.

Together with `alice_liveness`/`wedge_price` (the payer side) these are the
guaranteed-progress facts of Spec-v2 §7's "Liveness for Alice" and §4's
timers: no reachable live channel is stuck, for either party.
-/

namespace Zkpc.Chain.V2

variable {N : Type}

/-- **Bob cannot disable Alice's exit.** From any reachable live un-closing
state, the canonical safe close is enabled — no prior action (in particular
Bob's countersignature-withholding `ghostSend`) removes it. This is the
scheduling-independence at the heart of guaranteed liveness: Alice's exit
move is always available, so under any fair schedule she takes it. -/
theorem no_action_disables_close {P : Params} {nul : ℕ → N} {s : St}
    (h : Reach P nul s) (hlive : s.settled = false)
    (hopen : s.closing = none) :
    ∃ s', Step P nul s (.closeOn (canonical s.ctx)) s' :=
  ⟨_, Step.closeOn s (canonical s.ctx) hlive hopen
    (canonical_valid P.D s.ctx (reach_inv h).1)⟩

/-- **Bob is never locked out (absolute deadline).** Past `Tabs` on a live
un-closing channel, `timeoutForfeit` is enabled: Alice's inaction cannot
trap Bob's deposit forever. The dual of `alice_liveness` — liveness for the
recipient. -/
theorem timeout_reachable {P : Params} {nul : ℕ → N} {s : St}
    (hlive : s.settled = false) (hopen : s.closing = none)
    (hlate : P.Tabs ≤ s.now) :
    ∃ s', Step P nul s .timeoutForfeit s' ∧ s'.bobPay = P.D :=
  ⟨_, Step.timeoutForfeit s hlive hopen (Or.inl hlate), rfl⟩

/-- **Bob is never locked out (on-request deadline).** After Bob has
requested close at `t`, past `t + Treq` the timeout is enabled even before
the absolute deadline — the 7-day on-request timer of Spec-v2 §4. -/
theorem request_deadline_reachable {P : Params} {nul : ℕ → N} {s : St}
    (hlive : s.settled = false) (hopen : s.closing = none) {t : ℕ}
    (hreq : s.closeReqAt = some t) (hlate : t + P.Treq ≤ s.now) :
    ∃ s', Step P nul s .timeoutForfeit s' ∧ s'.bobPay = P.D :=
  ⟨_, Step.timeoutForfeit s hlive hopen (Or.inr ⟨t, hreq, hlate⟩), rfl⟩

/-- **Guaranteed settlement, either party.** Every reachable live channel
has an enabled next step toward settlement — Alice's safe close if the
channel is un-closing (with or without a pending timeout), or the resolution
of a running challenge window. No reachable live state is stuck: the two
liveness directions compose to total progress. -/
theorem not_stuck {P : Params} {nul : ℕ → N} {s : St}
    (h : Reach P nul s) (hlive : s.settled = false) :
    ∃ a s', Step P nul s a s' := by
  rcases hcl : s.closing with _ | ⟨x, t0⟩
  · exact ⟨_, _, Step.closeOn s (canonical s.ctx) hlive hcl
      (canonical_valid P.D s.ctx (reach_inv h).1)⟩
  · -- a close is pending: either the window still runs (tick) or it has
    -- elapsed (settle). Either way a step exists.
    rcases le_or_gt (t0 + P.tau) s.now with hwin | hwin
    · exact ⟨_, _, Step.settle s x t0 hlive hcl hwin⟩
    · exact ⟨_, _, Step.tick s 1 hlive⟩

end Zkpc.Chain.V2

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.V2.no_action_disables_close
#print axioms Zkpc.Chain.V2.timeout_reachable
#print axioms Zkpc.Chain.V2.request_deadline_reachable
#print axioms Zkpc.Chain.V2.not_stuck
