# T7 FRAME stack — adversarial statement-level audit (2026-07-10)

Auditor: independent adversarial verifier (read-only on `.lean`; all builds
performed in a detached git worktree with an isolated cloned build
directory, so sibling agents' in-flight edits could not contaminate
results). Audited commits: HEAD `acba6cf` ("Export composition and count
reindexing lemmas") and the discharge commit `ecdbcec` ("Discharge FRAME
query-bound certificate"), branch `codex/end-to-end-zk-payments`.
Freeze baseline: `28b7f80`. The live tree had
`Zkpc/Games/FrameDSCountInduction.lean` mid-edit throughout the audit.

---

## **FINDING F1 — the advertised unconditional T7 closure is NOT kernel-checked in any committed state**

**`Zkpc/Games/FrameDSCountInduction.lean` fails to compile at both the
discharge commit `ecdbcec` and HEAD `acba6cf`. Therefore
`Zkpc.Games.dsBadMassLe_of_queryBounds` (the stage-2 counting discharge)
and its dependent `Zkpc.Composition.T7Certificate.ofQueryBounds` (the
"unconditional bound from `FrameQueryBounds` alone") have never been
verified by the Lean kernel in committed history. The T7 endpoint remains
CONDITIONAL on the named residual `DSBadMassLe`.**

Failing statements, from clean rebuilds in the isolated worktree:

- At `ecdbcec` (6 errors, all inside the new seeded-shadow lane):
  - `FrameDSCountInduction.lean:791:18` and `793:14` — unsolved goals in
    the `query_bind.spend` case of `dsFrameImpl_seeded_bad_le`;
  - `805:18` and `846:18` — `rewrite` failed (pattern not found), same
    induction;
  - `1025:4` — type mismatch on the
    `DeferredSampling.evalDist_bind_comm` step **inside
    `dsBadMassLe_of_queryBounds` itself**;
  - `1029:6` — `rewrite` failed, same theorem.
- At `acba6cf` (24 errors): all of the above plus 18 new errors from
  `evalDist_rlnY_uniform` and neighbors (lines 777–784) written with the
  wrong notation glyph `𝓓[...]` (U+1D4D3) instead of the project's
  `evalDist` notation `𝒟[...]` (U+1D49F) — `Unknown identifier 𝓓`.
- Because the module fails, `Zkpc/Composition/EndToEnd.lean` (which
  imports it since `ecdbcec`) cannot be elaborated at either commit;
  `T7Certificate.ofQueryBounds` is dead code from the kernel's point of
  view.
- Additionally, at the earlier snapshot `271beae`,
  `Zkpc.Games.FrameGoodSliceTapeInduction` failed to build — so the
  good-slice discharge landed in `5d72f7a` was also committed unverified
  at first (it does verify now; see F2/item 5).

Why this slipped through: CI (`.github/workflows/ci.yml`) runs
`lake build` only on pushes to `main` and on PRs; this working branch gets
no build check, and the grep guardrails (which do pass) cannot detect
non-compiling proofs. Broken proof code has been committed at least twice
on this branch (`ecdbcec`, `acba6cf`).

**Action required:** repair `FrameDSCountInduction.lean` (the live tree is
visibly mid-repair — the wrong glyphs are already gone there), rebuild,
and only then claim the unconditional closure. Until then the honest
status line is: *T7 = conditional on `DSBadMassLe` only* (see F2).

## FINDING F2 — what IS kernel-verified (all axiom-clean)

Fresh source rebuilds at `ecdbcec`/`acba6cf` kernel-checked the following,
each printing exactly `[propext, Classical.choice, Quot.sound]` (in-file
`#print axioms` output captured from the build logs):

- Frozen layer: `T7_frame_bound`, `T7_frame_query_bound`,
  `T7_frame_query_bound_avg`, `frameDeferredSampling_refuted`,
  `frameWinProb_YK/aReuse/slopeReveal_eq_one`, `twoProbe_win_first/second`.
- Master factorization + assemblies: `frame_real_le_ghost_plus_bad`,
  `T7_frame_query_bound_of_transfers`,
  `T7_frame_query_bound_of_realGhostTransfers`,
  `T7_frame_query_bound_of_goodSlice_and_realBad`,
  `T7_frame_query_bound_of_goodSlice_stepCoupling_count`,
  `T7_frame_query_bound_of_goodSlice_and_dsCount`.
- Discharged residuals: `ghostSlopeBadBounds_holds` (ghost slope socket),
  `realDSStepCoupling_holds` (route-B stage 1),
  **`frameGoodSliceTransfer_of_tape`** (the general good-slice transfer,
  `FrameGoodSliceTapeInduction.lean:647`) — this one is real: it builds
  from source at both `ecdbcec` and `acba6cf` and is axiom-clean.

Net verified reduction: for every adversary `A` with budget certificate
`qb`, `frameWinProb mclose A ≤ (qb.total + 1)/|F|` **given only**
`DSBadMassLe mclose A qb` (via `T7_frame_query_bound_of_goodSlice_and_dsCount`
+ `frameGoodSliceTransfer_of_tape`). `DSBadMassLe` is the sole open gap.

---

## Item-by-item verdicts

### 1. Frozen-definition drift — PASS

`git diff 28b7f80 acba6cf -- Zkpc/Games/Frame.lean Zkpc/Games/T7.lean` is
empty across all ~90 intervening commits: `frameGame`, `frameWinProb`,
`Slashes`, `frameSpec`, `frameImpl`, `emitSignal`, `Evidence`,
`recoverSecret`, `FrameQueryBounds(.total)`, `FrameDeferredSampling`, and
`T7_frame_query_bound` are **byte-identical** to the freeze.
`FrameDeferredSamplingAvg` / `T7_frame_query_bound_avg`
(`FrameDeferred.lean`) were created in `3df0169` and never touched since.

### 2. Non-vacuity of `FrameQueryBounds` — PASS

- Nontrivial in-tree certificate: `twoProbeQueryBounds` for
  `twoProbe c₁ c₂` (qId = 2, total = 2), an adversary with proven real
  attack power (`twoProbe_win_first` = 1).
- `IsQueryBoundP` (VCVio `QueryBound.lean:227`) is a per-path roll bound
  on the free monad: each `p`-query requires positive remaining budget and
  decrements it, recursively along **every** answer branch; an adversary
  making n `p`-queries on any branch cannot certify a budget < n, and the
  `∀ cm` quantifier covers every adaptive continuation. Not trivially
  satisfiable.
- Smuggling attempts rejected: `A : F → OracleComp (frameSpec F M) _` is
  the only interaction surface (no composed oracles; the handler's
  `unifSpec` coins are handler-side); handler-internal RO lookups are
  uncharged by documented design, but every operation exposing honest
  material (`spend`, `close`, `nfAt`) is charged to `qSig` — including
  post-close no-op spends (conservative direction). `nfAt` is correctly
  classified as a signal (it materializes `H_a(k,i)`).

### 3. Hidden hypotheses in the assembly chain — PASS

Enumerated every hypothesis and instance argument of
`T7_frame_query_bound_of_goodSlice_and_dsCount`, `_of_transfers`,
`_of_realGhostTransfers`, `_of_goodSlice_and_realBad`: only
`[Field F] [DecidableEq F] [SampleableType F] [DecidableEq M] [Fintype F]`
plus `mclose A qb` plus the named residual `Prop`s in the *same*
`(mclose, A, qb)`. No `[Inhabited _]`/`[Nonempty _]` anywhere in the
chain. All `Decidable` instances (`Slashes`, `FrameLeakBad`,
`GhostLeakBad`, `DSShadowLeaf.bad`) come from `infer_instance` off
`DecidableEq F` — no assumption hidden in decidability. Nothing
adversary-dependent is universally quantified in a weakening position.

### 4. The k-averaged socket consumes what `frameGame` produces — PASS

Re-derived by hand: `frameGame_eq_evidence` is pure `bind_assoc`, and the
resulting `k ← $ᵗF; ev ← frameEvidence mclose A k; pure (decide (Slashes k ev))`
is **literally** the LHS of `FrameDeferredSamplingAvg.close_avg` (same
uniform `$ᵗ F`, same `frameEvidence`, same `Slashes` decide).
`auditedFrameRun`'s programmed initial state is definitionally the
`lazyRO`-on-empty-cache path of `frameEvidence`
(`fst_map_auditedFrameRun`). The `+1/|F|` bookkeeping in
`T7_frame_query_bound_avg` is exact.

### 5. Newly landed general transfers — statements PASS; verification split

- `frameGoodSliceTransfer_of_tape` concludes **exactly** the named
  residual `FrameGoodSliceTransfer mclose A` of `FrameFactor.lean` — same
  generator, same win∧¬bad predicate, same deferred-secret ghost RHS; no
  strengthened hypotheses (ambient instances + `[Fintype F]` only, no
  condition on `A`), no weakened conclusion, no swapped `k`/`A`/`mclose`
  quantifiers (proved pointwise-in-`k` and averaged by
  `frameGoodSliceTransfer_of_pointwise`, the sound direction).
  **Kernel-verified** (F2).
- `DSBadMassLe` (`FrameRealBadTransfer.lean:279`) is consumed by
  `frameRealBadMassLe_of_dsCount` / `_of_goodSlice_and_dsCount` with the
  identical `(mclose, A, qb)` statement — exact match.
  `dsBadMassLe_of_queryBounds` *states* exactly `DSBadMassLe mclose A qb`
  with no hypotheses beyond `qb`, but **does not compile** (F1).
- Tape/shadow constructions do not restrict the adversary: `DSFrameSt`'s
  slope tape is total (`ℕ → Option F`, no finite-support assumption);
  `dsFrameImpl` handles every `FrameOp` constructor; shadow/pending
  invariants (`dsShadowInvStrong_init`, `RoXCacheNonzero`) are
  initial-state facts, not conditions on `A`; `A` keeps the exact type
  `frameGame` quantifies over.

### 6. Axiom audit — PASS for everything that builds

Method: scratch import file (outside the repo) + full source rebuild of
the stack in the isolated worktree, cross-checked against the in-file
`#print axioms` lines emitted by the fresh builds. Every theorem in F2
prints exactly `[propext, Classical.choice, Quot.sound]` (a few substrate
lemmas print strict subsets). No foreign axiom anywhere.
`dsBadMassLe_of_queryBounds` and `T7Certificate.ofQueryBounds` could not
be axiom-audited — they do not elaborate (F1).

### 7. CI greps — PASS

All three CI greps clean at `acba6cf`: `sorry` — clean; `axiom` outside
`Zkpc/Assumptions.lean` — clean; `admit|native_decide` — clean. (But see
F1: the greps pass while the build is red; CI's `lake build` job does not
run on this branch.)

### 8. `T7Certificate.ofQueryBounds` — statement PASS, verification FAIL

Statement (`Zkpc/Composition/EndToEnd.lean`, identical at `ecdbcec` and
`acba6cf`): `(mclose)(A)(qb : FrameQueryBounds A) : T7Certificate mclose A qb`
where `T7Certificate ... := frameWinProb mclose A ≤ (qb.total + 1)/|F|`.
Hypotheses beyond `qb`: none — only the ambient typeclass instances needed
to state the game. If its dependency compiled, this would be the
unconditional Spec.md §7 T7 endpoint (any PPT adversary carries a
polynomial `qb`, giving `negl`). It does not currently compile (F1); its
sibling `T7Certificate.ofAveraged` (from any `FrameDeferredSamplingAvg`)
is verified.

---

## Observations (recorded, not flaws)

1. `Slashes` omits `Dispute`'s ancillary checks (nullifier match,
   membership) — enlarges the win set, sound direction, documented
   GATE-NOTE in `Frame.lean`.
2. Handler-internal RO reads are uncharged by documented design; the
   `IsQueryBoundP` certificates correctly charge only adversary-issued
   queries.
3. `qSig` charges post-close no-op `spend`/`close` queries — conservative.
4. The pointwise `FrameDeferredSampling` remains in-tree but refuted
   (`frameDeferredSampling_refuted`, |F| > 5); its consumer
   `T7_frame_query_bound` is sound but conditionally vacuous for
   adversaries like `twoProbe`. The averaged socket is the live one.
5. `nonzeroDigest` folds raw sample `0` onto `1` (digest value `1` has
   mass `2/|F|`); `x`-collisions play no role in `Slashes` or the leakage
   events.
6. `OPEN-PROOFS.md` and `ROADMAP-STATUS.md` were updated at
   `56d5c3f`/`acba6cf` to claim the closure; per F1 those claims are ahead
   of the kernel and should be re-reconciled after the repair.
