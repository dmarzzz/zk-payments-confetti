# RESUME

The pause this file was written for is over. This file is now a redirect.
Lean source validation for the current PR is complete at checkpoint
`abb878f`; final PDF regeneration/visual QA and the required human review
remain in progress.

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
clause in `Spec.md`. The two scaling theorems are conditional: one assumes
negligibility of the explicit query/field-size ratio, and its corollary uses
an explicit polynomial numerator bound plus negligible inverse field size.
Neither defines PPT or derives those premises from PPT.

For the source checkpoint, a fresh checkout restored 8,283 cached files and
completed all 3,595 root build jobs on Lean 4.30.0. The exact T7,
composition, scaling, and refund-reference axiom capture used only Lean's
standard axioms; the source scans and diff hygiene checks were clean. This is
evidence for `abb878f`, not a self-referential SHA for the later release
commit. The rebuilt 12-page PDF passed page-by-page visual QA; the exact
release SHA is recorded in the PR and issues after the commit exists. The
repository is already public; invitations, posting, and other
outbound delivery remain operator-gated (`DELIVERY.md`, K6).

The eleven B1 rounds, five B3 rounds, K1, and K4 recorded in
`research_knowledge/gates.md` were independent-agent or simulated-external
reviews. They do not satisfy the non-author human acceptance required by
`BRIEF.md`; human B1/B3/K1 sign-off and a real outside K4 review remain
pending.
