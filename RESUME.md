# RESUME — pause checkpoint 2026-07-07 (machine-load pause)

Paused mid-proof-phase at dmarz's request (laptop overload from parallel
Lean builds). **Last fully green, gate-signed commit: `2648b7b`**; the
`[wip]` commit after it holds unfinished H-phase and TLA+ partials that
may not build. Branch `formalization`, PR #1 (CI green through `2648b7b`).

## Operating rule adopted just before the pause

**ONE heavy agent at a time** (a heavy agent = anything running `lake
build` or TLC). Reviewers/audits are light. Consider `lake build -j4` and
TLC `-workers 2` to keep the machine usable.

## Where everything stands

Done and gate-signed: scaffold + CI (A), definitions through **11 B1 gate
rounds + 3 B3 rounds, final sign-off on Spec.md rev-11** (B), Lean core on
final MC20 semantics — T1, T2, T3, T5, exculpability facets, flat instance
(D, I), fleet T6 + RLN algebra (most of G), game framework + session-form
UNLINK + FRAME definitions (E). K1 + K4 audits done. TLA+ main run done
(incl. the TLC↔gate convergence on the gap-index hole — headline datum);
its rev-9 alignment pass was mid-flight when stopped. Paper drafted
(paper/, 12pp PDF builds) with 5 TODO-STATUS markers awaiting proofs.

## Resume queue (sequential, one heavy at a time)

1. **F — T4-A + T7 proofs** (the headline; was just launched when paused,
   no work lost). Relaunch one agent with the F prompt: flat UnlinkScheme
   instance (ROM views, π-free per zkBridgeObligation), T4 advantage = 0
   via DistEquiv/coupling (OTP HeapBasic template), T7 query-bounded
   (q+1)/|F| bound + the two must-win degenerate-RLN adversaries. Rules:
   definitions frozen (B3-signed), zero sorry, unprovable = GATE-NOTE not
   weakening.
2. **H — refund variant + calibration battery** (agent was mid-flight;
   partials in Zkpc/Games/{BInstances,Coupling}.lean — resume or restart
   against them). Deliverables in priority order: B-static/B-rerand
   instances + constructive static distinguisher (advantage 1/2) +
   rerand advantage 0; must-catch battery (index-leak, nf_e-reuse,
   multiplicity-tag q=2); Zkpc/Refund/ symbolic layer (T1-B, T3-B,
   conservation); H5 note.
3. **TLA+ rev-9 alignment** (small: make repaired config default, add
   settlement-time U∩RedeemedNF check, findings-file convergence note;
   partials already on disk).
4. **K-phase**: K2 axiom audit (quick), K3 adversarial vacuity review,
   O4-a..d doc minors + gates.md bookkeeping, K5 clean-room rebuild
   (fresh checkout, one lake build), K6 delivery package (visibility
   decision stays with dmarz), K7 experiment-outcome log (rich material:
   11 gate rounds, TLC convergence, definition-drift catches).
5. **Paper final pass**: update TODO-STATUS markers to actual proof
   outcomes; rev-9/10/11 definition details (session form, upgrade
   sub-window, slash taxonomy); K4 honest-limits additions (composed
   statement, retroactive-k-linkage, stale-close residue + its
   free-linkage nuance, fleet-honesty presumption); TLC convergence
   paragraph in post.md.

## Key files

Spec.md (rev-11, FROZEN) · research_knowledge/gates.md (full gate record)
· research_knowledge/{k1-statement-audit,k4-external-review,tla-findings,
vcvio-gap}.md · Zkpc/ (all green at 2648b7b) · paper/ · TASKS.md (the
original tree; A/B/C-mostly/D/E/G-mostly/I/J-draft done).
