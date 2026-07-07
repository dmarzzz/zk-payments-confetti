# Zkpc.Games — game layer status (E2–E4, B3; post-gate REVISE round, Spec.md rev-7)

**Build**: `lake build +Zkpc.Games.Framework +Zkpc.Games.Unlink +Zkpc.Games.Frame` — green, zero `sorry`/`axiom`/`admit`/`native_decide`; `#print axioms` on every proved theorem shows only `propext`/`Classical.choice`/`Quot.sound`.

## What compiles

- `Framework.lean` (E2–E4, unchanged this round): `guessGap` (= Spec.md's `|Pr[b'=b] − 1/2|`; bridges: `guessGap_eq` via `ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half`, `boolBiasAdvantage_hiddenBitExp` via `ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch`); `World`, `hiddenBitExp`, `hiddenBitAdvantage`; E3 smoke theorems (proved): `hiddenBitAdvantage_const`, `hiddenBitAdvantage_eq_zero_of_distEquiv`; `ChalAdversary`; E4: `botSpec` + `withEvict`.
- `Unlink.lean` (B3/T4): `UnlinkScheme` (now with `GenesisInput`, `openCh : GenesisInput → …` — M2), `UnlinkOp`/`unlinkSpec`, `GSt`, `unlinkImpl`, `epochFresh`, `challengeCapable`, `challengeResp`, `UnlinkAdversary` (now a structure: `phase0` genesis stage + `main : ChalAdversary` — M2), `unlinkGame`, `unlinkAdvantage`, **`zkBridgeObligation` (M1, new stated Prop)**.
- `Frame.lean` (B3/T7): `Signal`, `lazyRO`, `FrameSt` (now 4 RO caches), `emitSignal` (`y = rlnY k a x`), `FrameOp`/`frameSpec` (now with `nfAt` — D1 — and `roE` — Mi1), `frameImpl`, `Evidence`, `recoverSlope`/`recoverSecret`, `Slashes`, `recoverSecret_line` (proved via `rln_recover_k`), `frameGame`, `frameWinProb`. Tied to `RLN.lean` (G4).

## Gate fixes applied (rev-7 aware)

- **M1**: `zkBridgeObligation (Sfull Sfree : UnlinkScheme) (εZK : ℝ) : Prop` — every full-ticket adversary is matched by a proof-free-game adversary up to `εZK` (assumption 2, NIZK-ZK). Docstring states the `root`/`e` disposition (common to both candidates, adversary-computable — `root` shared, `e` = the adversary's own `tick` count — hence droppable; `nf_e` NOT droppable). Cross-referenced from the module docstring and `UnlinkScheme.View` (marked GATE-OBLIGATION, impossible to miss).
- **M2**: interface extension taken. `UnlinkScheme.GenesisInput` (`PUnit` in A), `openCh : GenesisInput → ProbComp (PSt × OpenView)` (total; malformed genesis absorbed as a never-capable state — one more abort lever, charged to the anonymity set); `UnlinkAdversary` gains `phase0 : ProbComp ((GenesisInput × GenesisInput) × Aux0)` whose memory threads into `main.phase1`. `b` is still sampled before phase 0.
- **D1**: `FrameOp.nfAt i` answers `roNf(roA(k, i))` through the shared caches for adversary-chosen `i` — a strict superset of any MC20 close reveal `U`, uniform in shape; answered even post-close. Legacy `close` retained with corrected docstring: LEGACY SURPLUS POWER, subsumed by one `spend m_close` query, **not** MC20 close semantics.
- **D2**: both Unlink close docstrings rewritten to MC20 (A: `(cm, U, π_close)` unused-enumeration, `CloseView` carries `cm_u` + `U`; B: `(cm, j, nf_j, π_close)`, `CloseView` carries `cm_u`, count, `nf_j`; no close signal exists). The handler's `lastSig`-at-close update re-justified as a conservative no-op: any execution where it could flip freshness has that candidate closed, hence already challenge-incapable and the challenge already ⊥. No behavior change.
- **Mi1**: fourth lazy RO `roE` (`H_e` family) + module simulation note (honest `nf_e` = `roE (k, e)` on the same cache; epoch-faithful tickets deliverable without changing state shape).
- **Mi2**: proof-order line added to `challengeCapable` (exculpability lemma precedes T4 in §7's order — no circularity in reading "unslashed" as vacuous).
- **Mi3**: capable-but-⊥ branch of `challengeResp` marked GATE-OBLIGATION: per-instance proof must show the branch dead or account for its probability.

## Oracle surfaces

- **UNLINK**: phase 0 (no oracles): genesis inputs. Pre-challenge: `spend (u m) : Option View` · `retry u : Option View` · `serve (u ρ) : PUnit` · `close u : Option CloseView` · `tick : PUnit`. Challenge: freshness && capability, response `Option View` (⊥ in-band), then pure `guess` only.
- **FRAME**: `spend m : Option (Signal F)` · `close : Option (Signal F)` (legacy surplus) · `nfAt i : F` · `roA (k i) : F` · `roX m : F` · `roNf a : F` · `roE (k e) : F`. Shared caches (ROM-consistent). Win = `Slashes k ev`.

## GATE-NOTE / GATE-OBLIGATION register

**Obligations (per-instance proof debts):** (O1/M1) discharge `zkBridgeObligation` full-ticket → proof-free with the instance's `εZK`; (O2/Mi3) prove `capable ⇒ spend succeeds` (or bound the branch); (O3) B instances: `serve` absorbs invalid receipts as no-ops; `openCh` absorbs malformed genesis as never-capable state — instances must implement exactly that.

**UNLINK notes:** epochs = adversary `tick` counter (§6 scheduler); retry ≠ new signal (no freshness update) and answered post-close; close's `lastSig` update = conservative no-op (MC20: no close signal); capability's "open ∧ unslashed" vacuous here (Mi2: no circularity — excul lemma precedes T4); `Open` folded to `openCh(GenesisInput)`+`OpenView`; spend-at-closed ⇒ ⊥; corrupt payers unmodeled (zero-cost maximality).

**FRAME notes:** no solvency gate on `Ospend` (more power); win predicate omits nf-consistency/membership (more power); corrupt members via direct RO access; N−1 view = all oracle outputs; MC2 re-send omitted (deterministic replay); `close` = legacy surplus, `nfAt` = MC20 reveal superset; no epoch clock — `roE` present, simulation note in module docstring; inherited RLN `x = 0` caveat (`roX` hits 0 w.p. `1/|F|`, `y = k` there — T7's negligible mass absorbs it).

## What the T4/T7 prover will need

- T4: instantiate `UnlinkScheme` per variant (A, B-static, B-rerand) **twice each** (full-ticket + proof-free) and discharge `zkBridgeObligation`; then bound the proof-free game via `hiddenBitAdvantage_eq_zero_of_distEquiv`/`DistEquiv.of_step` (HeapBasic template) or `ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage` (shared-prefix bridge); B-static calibration attack must be a constructive `UnlinkAdversary` term.
- T7: `rln_single_point_hiding` + `rln_evidence_sound` (RLN.lean) + ROM argument: the view fixes ≤ 1 point per line unless the adversary queries `roA`/`roE` at `(k, ·)` (= computes `k`); `nfAt`/`roNf` values are line-point-free; `x = 0` and RO collisions go to the negligible mass.
