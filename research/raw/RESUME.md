# RESUME

Re-baselined 2026-07-14. `PROTOCOL.md` (the post-quantum nullifier-chain
channel, an external contribution recorded verbatim) is the design of
record; `Spec.md` rev-11 and its theorems are historical results about the
superseded object. PR #2 (lalalune) is merged; attribution hygiene and the
doc re-baseline are applied on top.

Pick up in this order:

1. **Spec-v2 gate rounds** on findings G1–G5 (`ROADMAP.md` Phase 0;
   `gates.md`, gate series v2). G2, the
   withheld-countersignature wedge, is the critical-path item and is
   genuine protocol design.
2. **Attestation build** of merged `main` on a machine with resources: a
   fresh-clone full root build to clear the debt on the 11 post-`e2de071`
   commits (`ROADMAP.md`, "Attestation debt"). Not a laptop job.
3. **The ranked worklist** in `ROADMAP.md` Phase 1+ (safety core on
   the new machine first; then de-idealized collision soundness; then
   non-frameability; then the full-strength anonymity port).

In parallel, doc work that needs no builds: the paper restructure
(re-scope A/B as historical, present the nullifier-chain protocol as the
superseding design, surface the C-material disclosure debts listed in
`../paper/paper.md`'s status banner) and the PDF rebuild from the de-named
source.
