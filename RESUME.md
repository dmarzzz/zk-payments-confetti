# RESUME

The pause this file was written for is over. This file is now a redirect,
but delivery verification for the current PR is still in progress.

- **What got built and proved:** `DELIVERY.md` (two-paragraph summary,
  package manifest, and current clean-room-rebuild status).
- **Proof inventory and research extensions:** `OPEN-PROOFS.md` (implemented
  theorem chains with Lean names, the five reusable proof classes, the
  extensions not claimed by this release, and the remaining release gates).
- **Why every definition is the way it is:** `research_knowledge/gates.md`
  (the eleven-round adversarial review record).
- **The result of the experiment:**
  `research_knowledge/experiment-outcome.md`.

The T7 source endpoint is `T7_frame_query_bound_unconditional`: for an
adversary carrying `FrameQueryBounds`, it states the secret-averaged bound
`(qb.total + 1)/|F|` without residual coupling or counting hypotheses. It
is the finite counterpart to, not a proof of, the literal PPT/negligibility
clause in `Spec.md`. The scaling wrapper still assumes per-parameter query
and field-growth/negligibility premises. Do not treat earlier
clean-room output as evidence for the current PR head; follow the pending K5
instructions in `DELIVERY.md`, then record the exact verified commit. The
repository is already public; invitations, posting, and other outbound
delivery remain operator-gated (`DELIVERY.md`, K6).

The eleven B1 rounds, five B3 rounds, K1, and K4 recorded in
`research_knowledge/gates.md` were independent-agent or simulated-external
reviews. They do not satisfy the non-author human acceptance required by
`BRIEF.md`; human B1/B3/K1 sign-off remains pending.
