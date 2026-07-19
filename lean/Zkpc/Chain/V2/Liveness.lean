import Zkpc.Chain.V2.State

/-!
# Close-window enabledness and deadlock-freedom (ROADMAP obligation 5, partial)

`Zkpc/Chain/V2/State.lean`'s `alice_liveness` is existential: from a live
state Alice *can* reach a safe settlement. This module adds the two
progress facts that a weak-fairness liveness argument rests on —
**enabledness persistence** and **deadlock-freedom** — and pins the
two-timer deadline structure (Spec-v2 §4: 90-day absolute, 7-day
on-request) as concrete reachability facts.

**Scope (disclosed, per the review).** This module does **not** formalize
fairness: there is no temporal operator, no schedule, no fair-run
predicate, and `not_stuck` witnesses only that *some* step is enabled (for a
pending in-window close that witness is `tick`, which does not itself force
`settle`). The step "enabled + fair schedule ⇒ eventual settlement" is the
standard weak-fairness closure and is argued in prose only; obligation 5's
guaranteed-under-scheduling statement is therefore **not** discharged here —
its temporal wrapper (a fair-schedule predicate + eventual-settlement
theorem) remains open. What is proved:

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

/-- **Deadlock-freedom.** Every reachable live channel has *some* enabled
step: Alice's safe close if the channel is un-closing, `settle` once a
pending close's window has elapsed, or `tick` while it still runs. This is
progress-possible, **not** progress-guaranteed — an infinite `tick`-only run
past a pending close settles nothing; forcing `settle` needs the fairness
wrapper (see the module header). What it rules out is a genuinely stuck
state (no enabled action at all), which never arises. -/
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
