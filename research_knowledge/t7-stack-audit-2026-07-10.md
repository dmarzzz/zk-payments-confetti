# T7 FRAME stack — adversarial statement-level audit (2026-07-10)

Auditor: independent adversarial verifier (read-only on `.lean`).
Audited commit: `acba6cf` ("Export composition and count reindexing lemmas"),
branch `codex/end-to-end-zk-payments`, checked in a detached worktree of that
commit (the live tree had one file mid-edit, `Zkpc/Games/FrameDSCountInduction.lean`;
everything below refers to the committed state at `acba6cf`).
Freeze baseline: `28b7f80`.

## Verdict summary

**No soundness flaw found at the statement level.** All eight audit items
pass. The T7 endpoint is now **unconditional given only a
`FrameQueryBounds` certificate**: `Zkpc.Composition.T7Certificate.ofQueryBounds`
proves `frameWinProb mclose A ≤ (qb.total + 1)/|F|` for every adversary
`A`, every close message `mclose`, and every query-budget certificate
`qb`, with kernel axioms exactly `propext`, `Classical.choice`,
`Quot.sound`. Observations (not flaws) are listed at the end.

---

## 1. Frozen-definition drift — PASS

Method: `git diff 28b7f80 acba6cf -- Zkpc/Games/Frame.lean Zkpc/Games/T7.lean`
across all 90 intervening commits.

- `Frame.lean` and `T7.lean` are **byte-identical** to the freeze — hence
  `frameGame`, `frameWinProb`, `Slashes`, `frameSpec`, `frameImpl`,
  `emitSignal`, `Evidence`, `recoverSecret`, `FrameQueryBounds`,
  `FrameQueryBounds.total`, `FrameDeferredSampling`, and
  `T7_frame_query_bound` are unchanged (not merely statement-stable).
- `FrameDeferredSamplingAvg` / `T7_frame_query_bound_avg` live in
  `Zkpc/Games/FrameDeferred.lean`, created in `3df0169` and **never touched
  since** (`git log 3df0169..acba6cf -- FrameDeferred.lean` is empty).

## 2. Non-vacuity of `FrameQueryBounds` — PASS

- In-tree nontrivial certificate: `twoProbeQueryBounds`
  (`FrameDeferred.lean`) for the two-probe adversary `twoProbe c₁ c₂`
  (qId = 2, total = 2), whose real win mass at probed secrets is proven
  `1` and `≥ 1 − 1/|F|` (`twoProbe_win_first/second`) — so budgeted
  adversaries with real attacking power exist and are certified.
- `IsQueryBoundP` (VCVio `QueryBound.lean:227`) is a per-path roll bound on
  the free-monad computation: at every `p`-query the remaining budget must
  be positive and is decremented, recursively along **every** answer
  branch. It is not trivially satisfiable — an adversary making n
  `p`-queries on some branch cannot certify a budget < n, and `A` is
  quantified *before* the commitment (`∀ cm`), so the budget covers every
  adaptive continuation.
- Smuggling attempts considered and rejected:
  - There is no composed-oracle channel: `A : F → OracleComp (frameSpec F M) _`
    is the only interaction surface, and `simulateQ` routes every query
    through the audited/handler classifiers. `frameImpl`'s internal
    `unifSpec` coin oracle is handler-side and not adversary-accessible.
  - Handler-internal RO lookups (inside `spend`/`nfAt`) are deliberately
    uncharged, but the information they expose to the adversary flows only
    through the returned signal/nullifier, and every such operation is
    charged to `qSig` via `isSignalQuery` (`spend`, `close`, `nfAt` all
    `true`) — including post-close no-op spends (conservative, sound
    direction).
  - `nfAt` is charged as a signal even though it returns only a nullifier —
    correct, since it materializes `H_a(k,i)` (documented in `T7.lean`).

## 3. Hidden hypotheses in the assembly chain — PASS

Enumerated every hypothesis/instance of the endpoints:

- `T7_frame_query_bound_of_transfers` / `_of_realGhostTransfers`
  (`FrameAssembly.lean`): `[Field F] [DecidableEq F] [SampleableType F]
  [DecidableEq M] [Fintype F]` + `mclose A qb` + named residuals
  (`FrameGoodSliceTransfer`, `FrameBadMassTransfer`, `GhostSlopeBadBounds`;
  the last discharged by `ghostSlopeBadBounds_holds`).
- `T7_frame_query_bound_of_goodSlice_and_dsCount`
  (`FrameRealBadStep.lean`): same instances + `hgood :
  FrameGoodSliceTransfer mclose A` + `hcount : DSBadMassLe mclose A qb`.
- No `[Inhabited _]` or `[Nonempty _]` anywhere in the chain. All
  `Decidable` instances (`Slashes`, `FrameLeakBad`, `GhostLeakBad`,
  `DSShadowLeaf.bad`) are derived by `infer_instance` from
  `DecidableEq F` — no assumption hidden in decidability.
- Quantifier discipline: nothing adversary-dependent is universally
  quantified inside a hypothesis in a way that weakens the conclusion; the
  residuals are `Prop`s in the *same* `(mclose, A, qb)` as the conclusion.
  `RealDSStepCoupling` was `∀ k` (correct direction — an obligation, not a
  weakening) and is discharged (`realDSStepCoupling_holds`).

## 4. The k-averaged socket consumes what `frameGame` produces — PASS

Re-derived by hand: `frameGame mclose A = k ← $ᵗF; (cm,cId) ←
lazyRO roId k; ev ← (frameImpl k mclose).run {init with roId := cId} (A cm);
pure (decide (Slashes k ev))`. `frameEvidence` is exactly the post-`k`
suffix, and `frameGame_eq_evidence` (pure `bind_assoc`) rewrites the game
to `k ← $ᵗF; ev ← frameEvidence mclose A k; decide (Slashes k ev)` —
which is **literally** the LHS of `FrameDeferredSamplingAvg.close_avg`
(same uniform `$ᵗ F`, same `frameEvidence`, same `decide (Slashes k ev)`).
`T7_frame_query_bound_avg` applies `frameGame_eq_evidence`, then
`close_avg`, then `frame_blind_bound` on the ideal generator; the `+1/|F|`
bookkeeping (`Nat.cast_add`) is exact. Also checked
`auditedFrameRun`'s initial state (`Function.update roId k (some cm)` after
`cm ← $ᵗF`) is definitionally the `lazyRO`-on-empty-cache path of
`frameEvidence` (`fst_map_auditedFrameRun` proves the erasure exactly).

## 5. Newly landed general transfers + final discharges — PASS

- `frameGoodSliceTransfer_of_tape` (`FrameGoodSliceTapeInduction.lean`)
  concludes **exactly** the named residual `FrameGoodSliceTransfer mclose A`
  of `FrameFactor.lean` — same generator (`auditedFrameJoint`), same
  win∧¬bad predicate, same deferred-secret ghost RHS; no strengthened
  hypotheses (only the ambient instances + `[Fintype F]`, no condition on
  `A`), no weakened conclusion, no swapped `k`/`A`/`mclose` quantifiers
  (it is proved pointwise-in-`k` via `FramePointwiseGoodSlice` and averaged
  by `frameGoodSliceTransfer_of_pointwise`, the sound direction).
- `dsBadMassLe_of_queryBounds` (`FrameDSCountInduction.lean:1067` at
  `acba6cf`) concludes **exactly** `DSBadMassLe mclose A qb` as defined in
  `FrameRealBadTransfer.lean:279` — same `dsFrameJoint`, same
  `FrameLeakBad`, same `qb.total/|F|` budget; hypotheses are only the five
  `IsQueryBoundP` fields of `qb` itself (consumed per-`cm`, matching
  `∀ cm` in the certificate).
- Tape/shadow constructions do not restrict the adversary: `DSFrameSt`'s
  slope tape is total (`ℕ → Option F`, no finite-support assumption);
  `dsFrameImpl` handles every `FrameOp` constructor; the shadow-state
  invariant (`dsShadowInvStrong_init`) and `RoXCacheNonzero`/pending
  validity are *initial-state* facts, not conditions on `A`; `A` remains an
  arbitrary `OracleComp (frameSpec F M) (Evidence F)` (the same type
  `frameGame` quantifies over — finiteness of each computation path is
  intrinsic to `OracleComp`, identical on both sides).
- Route A's remaining `FrameBadMassTransfer` is still open, but route B
  (good-slice + `DSBadMassLe`) is fully discharged, and route A is now
  redundant for the endpoint. The `FrameTransfer.lean` module header's
  warning that `FrameBadMassTransfer` is second-order delicate is a
  statement-level *caution*, consistent with routing around it.

## 6. Axiom audit — PASS

Method: scratch file (outside the repo) importing
`Zkpc.Composition.EndToEnd`, `Zkpc.Games.FrameAssembly`,
`Zkpc.Games.FrameTransfer`; modules **rebuilt from source at `acba6cf`**
in the isolated worktree (so oleans match audited sources), then
`lake env lean` on the scratch file. Every endpoint printed exactly
`[propext, Classical.choice, Quot.sound]`:

`T7_frame_bound`, `T7_frame_query_bound`, `T7_frame_query_bound_avg`,
`T7_frame_query_bound_of_transfers`,
`T7_frame_query_bound_of_realGhostTransfers`,
`T7_frame_query_bound_of_goodSlice_and_realBad`,
`T7_frame_query_bound_of_goodSlice_and_dsCount`,
`frameGoodSliceTransfer_of_tape`, `framePointwiseGoodSlice_of_tape`,
`realDSStepCoupling_holds`, `dsBadMassLe_of_queryBounds`,
`ghostSlopeBadBounds_holds`, `frameDeferredSampling_refuted`,
`frame_real_le_ghost_plus_bad`, `T7Certificate.ofQueryBounds`,
`T7Certificate.ofAveraged`, `twoProbe_win_first`,
`frameWinProb_YK_eq_one`, `frameWinProb_aReuse_eq_one`.

## 7. CI greps — PASS

All three CI greps run at `acba6cf`: `sorry` — clean; `axiom` outside
`Zkpc/Assumptions.lean` — clean; `admit|native_decide` — clean.

## 8. `T7Certificate.ofQueryBounds` gives the unconditional bound — PASS

Statement (`Zkpc/Composition/EndToEnd.lean`):

```
theorem T7Certificate.ofQueryBounds (mclose : GameMessage)
    (A : F → OracleComp (Games.frameSpec F GameMessage) (Games.Evidence F))
    (qb : Games.FrameQueryBounds A) : T7Certificate mclose A qb
```

where `T7Certificate ... := frameWinProb mclose A ≤ (qb.total + 1)/|F|`.
Hypotheses beyond `qb`: **none** — only the ambient typeclass instances
(`Field F`, `DecidableEq F`, `SampleableType F`, `Fintype F`,
`DecidableEq GameMessage`), all necessary to state the game and the bound.
It composes `frameGoodSliceTransfer_of_tape` + `dsBadMassLe_of_queryBounds`
through the frozen `T7_frame_query_bound_of_goodSlice_and_dsCount`.
`#print axioms` = `propext, Classical.choice, Quot.sound` (see item 6).
Spec.md §7 T7's `negl(λ)` claim for PPT adversaries is therefore fully
covered: any polynomially query-bounded adversary carries a polynomial
`qb`, giving `(poly + 1)/|F|`.

---

## Observations (recorded, not flaws)

1. **`Slashes` omits `Dispute`'s ancillary checks** (nullifier match,
   membership). Omission enlarges the adversary's win set, so the proved
   bound covers the deployed predicate — sound direction, documented as a
   GATE-NOTE in `Frame.lean`.
2. **Handler-internal RO reads are uncharged by design** (documented in
   `T7.lean` §Query-bounded adversaries). This is not a hypothesis of the
   theorem — the proof is machine-checked against `frameGame` — but anyone
   instantiating the bound should compute `qb` from the adversary's *own*
   queries only, which the `IsQueryBoundP` certificates enforce.
3. **`qSig` charges post-close no-op `spend`/`close` queries** (the
   classifier is per-op, not per-emitted-signal). This only makes the
   budget, hence the numerator, larger — conservative.
4. **The pointwise `FrameDeferredSampling` remains in-tree but refuted**
   (`frameDeferredSampling_refuted`, |F| > 5). Its consumer
   `T7_frame_query_bound` is sound but conditionally vacuous for
   adversaries like `twoProbe`; the averaged socket is the live one. No
   action needed — the refutation is itself kernel-checked and the frozen
   theorem was not weakened.
5. **`nonzeroDigest` folds the raw sample `0` onto `1`**, giving `H_x`
   digest value `1` probability `2/|F|`. `x`-collisions play no role in
   `Slashes` or the leakage events, so this does not affect the audited
   statements.
6. `OPEN-PROOFS.md` §1 lags the closure (it still describes the good-slice
   and bad-mass residuals as open); `56d5c3f` reconciled other docs.
   Cosmetic staleness only.

## Method note

Live tree had `Zkpc/Games/FrameDSCountInduction.lean` mid-edit throughout
the audit; all verification (greps, builds, axiom prints, statement reads
of the discharged lanes) was performed in a detached git worktree pinned
to `acba6cf` with its own cloned build directory, so sibling agents'
in-flight edits could not contaminate the results.
