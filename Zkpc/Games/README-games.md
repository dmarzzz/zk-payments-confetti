# Zkpc.Games — game layer status

Two sections: the current 2026-07-10 batch (T4 discharged, T7 substrate), then
the rev-9 record kept verbatim as history. The game *definitions* (rev-9 forms
of `Framework.lean`, `Unlink.lean`, `Frame.lean`) are unchanged; everything
below the definitions is new proof mass.

## 2026-07-10 batch — T4 discharged; T7 reduced to two named Props

**Build**: `lake build` over the whole `Zkpc` tree kernel-checks the game
layer; the `Zkpc.Games` modules are now `Framework`, `Unlink`, `Frame`, `RLN`,
`Calibration`, `Coupling`, `T4`, `T4Fires`, `T7`, `FlatInstance`,
`SigmaInstance`, `BInstances`, `FullTicketInstance`, and the T7 Frame stack
(`FrameAudit`, `FrameIdeal`, `FrameDeferred`, `FrameCoupling`, `FrameGhost`,
`FrameGhostBounds`, `FrameGhostCoupling`, `FrameGhostCoverage`, `FrameBadMass`,
`FrameFactor`, `FrameAssembly`, `FrameTransfer`) — green, zero
`sorry`/`axiom`/`admit`/`native_decide`; open sub-goals are explicit named
`Prop` hypotheses (house convention), never axioms; `#print axioms` on the
endpoint theorems shows only `propext`/`Classical.choice`/`Quot.sound`.

### T4 (B3) — discharged

- `T4.lean`: `T4_flat_unlinkability` — every `UnlinkAdversary` has advantage
  exactly `0` against the proof-free `flatInstance`.
- `FlatInstance.lean`: the π-free ideal view; discharges O2 batch totality
  (`flat_spendBatch_none_zero`) and O4 (`flat_closeViewSimulatable`); the
  bit-free core is `challengeResp_flat_bitfree`.
- `SigmaInstance.lean`: Sigma-protocol and Fiat–Shamir wires —
  `sigmaFlatInstance` / `fsFlatInstance` with `T4_sigmaFlat_unlinkability`,
  `T4_fsFlat_unlinkability` and the zero-loss ZK bridges `sigmaFlat_zkBridge`,
  `fsFlat_zkBridge`; the FS wire is consumed end-to-end in
  `Zkpc/Core/Composition.lean`.
- `FullTicketInstance.lean`: proof-bearing reference instances closing M1/O1
  at the ideal-proof hop — `fullFlatInstance` (`T4_fullFlat_unlinkability`,
  `fullFlat_zkBridge`) and `maskedProofInstance`
  (`T4_maskedProof_unlinkability`, `maskedProof_zkBridge`); a concrete NIZK
  must later match this reference and pay its own `εZK`.
- `T4Fires.lean`: non-vacuity of the challenge — `challengeResp_flat_fires`
  (a concrete real batch is reachable for every `budget ≥ 1`) and
  `challengeResp_flat_never_bot` (the challenge never answers ⊥ there),
  discharged from the O2 batch-totality lemmas.

With that, the rev-9 obligations register is settled for the reference
instances: O1/M1 (`zkBridgeObligation`), O2/Mi3 (batch), O3 (B-instances),
and O4 (`closeViewSimulatable`) all have in-tree discharges.

### T7 (FRAME) — the Frame stack, file by file

- `Frame.lean` — game definition, unchanged from rev-9 (5 lazy RO caches,
  `cm := roId(k)` delivered at game start, win = `Slashes k ev`).
- `T7.lean` — composition endpoints: `T7_frame_bound_of_pointwise` /
  `T7_frame_query_bound` (pointwise socket) and the conditional
  `T7_frame_bound`; the pointwise socket is kept for the record but is now
  known to be unsatisfiable as frozen (next item).
- `FrameDeferred.lean` — **pointwise certificate refuted**:
  `frameDeferredSampling_refuted` (two-probe `roId` adversary; any single
  secret-independent generator dominating pointwise in `k` forces `|F| ≤ 5`;
  gates.md Round 4, 2026-07-09). The corrected **k-averaged** socket
  `FrameDeferredSamplingAvg` and its endpoint `T7_frame_query_bound_avg`
  (same `(qb.total + 1)/|F|` bound) replace it.
- `FrameAudit.lean` — write-only audit ornament on the real handler;
  `auditedFrameImpl_run_project` is the exact computation-level erasure.
- `FrameIdeal.lean` — secret-independent ideal handler `idealFrameImpl`,
  the coupling relation `FrameCoupled` / `idealizeFrame`, per-oracle coupling
  steps, and the initial-state honest-spend step.
- `FrameCoupling.lean` — general-state coupling bricks: `HiddenSlopeInj`,
  `RoNfCovered`, and the `nfAt`-channel steps at arbitrary audit-complete
  states.
- `FrameGhost.lean` — ghost handler `ghostFrameImpl`: ideal handler plus a
  fully `k`-free ghost audit (`GhostAudit`, bad event `GhostLeakBad`), with
  exact erasure back to the ideal handler (`ghostFrameImpl_run_erase`) and
  the deferred-secret run `ghostFrameRun`.
- `FrameGhostBounds.lean` — deferred-secret budget arithmetic:
  `ghostFrameRun_secret_probe_bound` and the assembled
  `ghostFrameRun_leak_bad_bound` from the `GhostSlopeBadBounds` socket.
- `FrameGhostCoupling.lean` — the real/ghost run invariant
  `RealGhostCoupled`; crucially `frameLeakBad_iff_ghostLeakBad`, so the two
  bad flags coincide under the coupling (one monotone flag, no second loss).
- `FrameGhostCoverage.lean` — `GhostRoNfCovered`: every populated public
  ghost `roNf` key was explicitly probed (`ghostFrameImpl_run_roNfCovered`),
  the ghost-side source of `RoNfCovered`.
- `FrameBadMass.lean` — the ghost bad mass closed **unconditionally**:
  `ghostSlopeBadBounds_holds` supplies the slope-tape fields
  (via `materializeSlopeTape`), and `ghostFrameRun_leakBad_prob_le` gives
  `E_k[GhostLeakBad] ≤ qb.total/|F|` with no remaining hypothesis.
- `FrameFactor.lean` — the **master factorization**
  `frame_real_le_ghost_plus_bad`: k-averaged real slash probability ≤
  deferred-secret ghost win mass + deferred-secret ghost bad mass, from the
  two named transfer residuals `FrameGoodSliceTransfer` /
  `FrameBadMassTransfer`. Also the atomic deferred-secret couplings:
  `evalDist_uniform_add_pad` (the secret-consumption pad),
  `initial_spend_deferredSecret_ghost_eq` (fresh-slope form), and
  `initial_nfAt_spend_deferredSecret_ghost_eq` (the `nfAt`-then-`spend`
  crux — the eager-read obstruction closed in atomic form). Load-bearing
  observation recorded in this file: `OracleComp` here is a plain free monad
  with no failure leaf, so adversary runs are total and bad-at-end coincides
  with bad-ever-fired on both sides.
- `FrameAssembly.lean` — route A stitching:
  `frameDeferredSamplingAvg_of_transfers` builds the k-averaged certificate
  from `FrameGoodSliceTransfer` + `FrameBadMassTransfer` +
  `GhostSlopeBadBounds`, and `T7_frame_query_bound_of_transfers` derives the
  full corrected bound (the `GhostSlopeBadBounds` input is now discharged by
  `FrameBadMass`).
- `FrameTransfer.lean` — route B and a statement-level warning: route A's
  `FrameBadMassTransfer` is recorded **not per-transcript dominated** (a
  fixed two-signal transcript gives real mass `3/|F|` vs ghost mass
  `3/|F| − 2/|F|²`, so any proof needs exact second-order cancellation and
  may fail). The safer first-order target is the direct real-side bound
  `FrameRealBadMassLe`; `frameDeferredSamplingAvg_of_goodSlice_and_realBad`
  and `T7_frame_query_bound_of_goodSlice_and_realBad` assemble the endpoint
  from `FrameGoodSliceTransfer` + `FrameRealBadMassLe`. The fixed-transcript
  root kernel (`DeferredLine`, `frameRealRootCandidates`,
  `probEvent_uniform_mem_frameRealRootCandidates_le`) machine-checks the
  stage-2 counting.
- `FrameGoodSlice.lean` (in flight, not yet in tree) — the lane discharging
  `FrameGoodSliceTransfer`; do not create or edit it outside that lane.

### What actually remains for T7

Exactly **two open Props**, both claimed and in progress (lane claims and the
working two-stage architecture live in `OPEN-PROOFS.md` §1):

1. `FrameGoodSliceTransfer` (`FrameFactor.lean`) — the off-bad run-level
   real/ghost win-mass coupling (orchestrator lane, `FrameGoodSlice.lean`).
2. `FrameRealBadMassLe` (`FrameTransfer.lean`) — the direct real-side bound
   `Pr[FrameLeakBad] ≤ qb.total/|F|` over the audited joint experiment
   (route-B lane).

Either route closes the unconditional Spec.md §7 T7 endpoint through the
already-kernel-checked assemblies; route B is the recommended one. Nothing
else — no probability algebra, game rearrangement, or ghost-side mass —
stands between those two Props and `T7_frame_query_bound_avg` firing
unconditionally.

---

## Historical record — rev-9 (E2–E4, B3; pre-T4/T7 discharge)

Everything below is the rev-9 status as written at the time (B3 round 2
signed off). It predates the T4 instance suite and the whole T7 Frame
substrate above; the game definitions it describes are still the current
ones, but its "what the prover will need" section is superseded by the
2026-07-10 batch.

**Build (rev-9)**: `lake build +Zkpc.Games.Framework +Zkpc.Games.Unlink +Zkpc.Games.Frame` — green, zero `sorry`/`axiom`/`admit`/`native_decide`; `#print axioms` on every proved theorem shows only `propext`/`Classical.choice`/`Quot.sound`.

### What compiles (rev-9)

- `Framework.lean` (E2–E4, unchanged since round 1): `guessGap` (= Spec.md's `|Pr[b'=b] − 1/2|`; bridges: `guessGap_eq` via `ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half`, `boolBiasAdvantage_hiddenBitExp` via `ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch`); `World`, `hiddenBitExp`, `hiddenBitAdvantage`; E3 smoke theorems (proved): `hiddenBitAdvantage_const`, `hiddenBitAdvantage_eq_zero_of_distEquiv`; `ChalAdversary`; E4: `botSpec` + `withEvict`.
- `Unlink.lean` (B3/T4, **session form rev-9**): `UnlinkScheme` (`GenesisInput`, `openCh : GenesisInput → …`, `capableFor : ℕ → PSt → Bool`), `UnlinkOp`/`unlinkSpec`, `GSt`, `unlinkImpl`, `epochFresh`, `challengeCapable … q`, `spendBatch`, `challengeResp` (vector challenge), `UnlinkAdversary` (`phase0` genesis stage + `main : ChalAdversary … (List S.M) (Option (List S.View))`), `unlinkGame`, `unlinkAdvantage`, `zkBridgeObligation` (M1), **`closeViewSimulatable` (O4, new stated Prop)**.
- `Frame.lean` (B3/T7): `Signal`, `lazyRO`, `FrameSt` (**5 RO caches**, incl. `roId`), `emitSignal` (`y = rlnY k a x`), `FrameOp`/`frameSpec` (`spend`/`close`-legacy/`nfAt`/`roA`/`roX`/`roNf`/`roE`/**`roId`**), `frameImpl`, `Evidence`, `recoverSlope`/`recoverSecret`, `Slashes`, `recoverSecret_line` (proved via `rln_recover_k`), `frameGame` (**adversary receives `cm` at game start**), `frameWinProb`. Tied to `RLN.lean` (G4).

### Rev-9 batch (B3 round 3 verified exactly these)

1. **Session challenge (K4 Concern 1)**: the challenge is now a vector `m*₁..m*_q : List S.M`, `q ≥ 1` adversary-chosen. Freshness unchanged; capability is `capableFor q` on both candidates (A: `(j+q)·C ≤ D`; B: `(j+q)·C_max ≤ D + R`); on success `spendBatch` emits `P_b`'s next `q` tickets **atomically at `e*`** (no oracle interleaving ⇒ shared `nf_{e*}` structurally); response `Option (List S.View)`. Verified cores preserved: `b`-first sampling, ⊥ decided by both-candidate checks (`b`-independent), structural termination (`ChalAdversary` pure guess). GATE-NOTE: empty vector answered ⊥ (spec types `q ≥ 1`); Mi3 obligation extended: `capableFor q ⇒` all `q` batch spends succeed.
2. **O4 (K4 Concern 2)**: `closeViewSimulatable (S) (Cm) (cm : PSt → Cm) (count : PSt → ℕ) : Prop` — ∃ simulator with `𝒟[close output] = 𝒟[sim (cm st) (count st) e]` for all states (an instance may weaken to game-reachable states, recorded at its gate entry). The instance supplies the `cm`/`count` summary since the abstract interface does not expose them. Cross-referenced from `CloseView`'s docstring. Rationale (MC15): the game ends at the challenge, so close content is outside its view; the obligation pins the close leak to exactly `(cm, count)` — MC15's residue — and excludes e.g. a close publishing *used* nullifiers.
3. **FRAME cm exposure (K1 finding D1)**: fifth lazy RO `roId` (`H_id`); `frameGame` materializes `cm := roId(k)` through the shared cache and passes it as the adversary's input (`A : F → OracleComp …`); direct `roId` queries let the adversary test preimages — same `q/|F|` ROM mass as the `roA` channel (docstrings on `FrameOp.roId` and the game).

### Oracle surfaces

- **UNLINK**: phase 0 (no oracles): genesis inputs. Pre-challenge: `spend (u m) : Option View` · `retry u : Option View` · `serve (u ρ) : PUnit` · `close u : Option CloseView` · `tick : PUnit`. Challenge: `!empty && fresh && capableFor q`, response `Option (List View)` (⊥ in-band), then pure `guess` only.
- **FRAME**: input `cm : F`; `spend m : Option (Signal F)` · `close : Option (Signal F)` (legacy surplus) · `nfAt i : F` · `roA (k i) : F` · `roX m : F` · `roNf a : F` · `roE (k e) : F` · `roId k : F`. Shared caches (ROM-consistent, incl. the game-start `cm`). Win = `Slashes k ev`.

### GATE-NOTE / GATE-OBLIGATION register (rev-9; obligations since discharged — see the 2026-07-10 batch)

**Obligations (per-instance proof debts):** (O1/M1) discharge `zkBridgeObligation` full-ticket → proof-free with the instance's `εZK`; (O2/Mi3, session form) `capableFor q ⇒` the whole `q`-batch succeeds (or bound the branch); (O3) B instances formalize adversary-issued genesis/receipt absorption (at the issuer abstraction every supplied handle is well formed); **(O4)** discharge `closeViewSimulatable` — close output simulatable from `(cm, spend count)` alone. O2/O3/O4 are discharged for B-rerand/`bIdeal` in `BInstances.lean`.

**UNLINK notes:** session challenge is atomic at `e*` (shared `nf_{e*}` structural); empty challenge vector ⇒ ⊥ (`q ≥ 1` per spec, `b`-independent); epochs = adversary `tick` counter (§6 scheduler); retry ≠ new signal (no freshness update) and answered post-close; close's `lastSig` update = conservative no-op (MC20: no close signal); capability's "open ∧ unslashed" vacuous here (Mi2: no circularity — excul lemma precedes T4); `Open` folded to `openCh(GenesisInput)`+`OpenView`; spend-at-closed ⇒ ⊥; corrupt payers unmodeled (zero-cost maximality).

**FRAME notes:** adversary holds `cm` from game start (rev-9/K1-D1; `roId` preimage confirmation = `q/|F|` mass, same as `roA` channel); no solvency gate on `Ospend` (more power); win predicate omits nf-consistency/membership (more power); corrupt members via direct RO access; N−1 view = all oracle outputs; MC2 re-send omitted (deterministic replay); `close` = legacy surplus, `nfAt` = MC20 reveal superset; no epoch clock — `roE` present with simulation note; `roX` enforces Spec.md's nonzero digest codomain through `nonzeroDigest`, so the degenerate `x = 0, y = k` signal is unreachable.

### What the T4/T7 prover will need (rev-9 forecast — superseded)

Kept as written for the record; the T4 half is done (see the 2026-07-10
batch) and the T7 half's ROM sketch turned into the audited/ghost coupling
stack above, with the pointwise deferred-sampling shape it implicitly
assumed later refuted.

- T4: instantiate `UnlinkScheme` per variant (A, B-static, B-rerand) twice each (full-ticket + proof-free), discharge `zkBridgeObligation` and `closeViewSimulatable`; bound the proof-free game via `hiddenBitAdvantage_eq_zero_of_distEquiv`/`DistEquiv.of_step` (HeapBasic template) or `ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage` (shared-prefix bridge); the session form means the two-world coupling must cover the whole `q`-batch (extend the per-query case split over `spendBatch` by induction on the vector); the B-static calibration attack must be a constructive `UnlinkAdversary` term (it survives the session form — `q = 1` remains available to it).
- T7: `rln_single_point_hiding` + `rln_evidence_sound` (RLN.lean) + ROM argument: the view fixes ≤ 1 point per line unless the adversary queries `roA`/`roE`/`roId` at `k` (= computes `k`; the `cm` input adds only the `roId` confirmation channel, same mass); `nfAt`/`roNf` values are line-point-free; `x = 0` is excluded by the handler and RO collisions go to the negligible mass.
