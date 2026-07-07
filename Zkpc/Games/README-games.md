# Zkpc.Games — game layer status (E2–E4, B3)

**Build**: `lake build +Zkpc.Games.Framework +Zkpc.Games.Unlink +Zkpc.Games.Frame` — green, zero `sorry`/`axiom`/`admit`/`native_decide`; `#print axioms` on every proved theorem shows only `propext`/`Classical.choice`/`Quot.sound`.

## What compiles

- `Framework.lean` (E2–E4): `guessGap` (= Spec.md's `|Pr[b'=b] − 1/2|`; bridges: `guessGap_eq` via `ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half`, and `boolBiasAdvantage_hiddenBitExp` via `ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch`); `World`, `hiddenBitExp`, `hiddenBitAdvantage`; **E3 smoke theorems (proved)**: `hiddenBitAdvantage_const`, `hiddenBitAdvantage_eq_zero_of_distEquiv`; `ChalAdversary` (interactive phase + pure guess — post-challenge silence by type); E4: `botSpec` (in-band `Option` game-⊥) + `withEvict` (adversary-flipped per-target eviction switch).
- `Unlink.lean` (B3/T4): `UnlinkScheme` (abstract instance interface: `View`/`CloseView`/`OpenView`/`Receipt`/`PSt`, `openCh`/`spend`/`lastTicket`/`serve`/`close`/`capable`), `UnlinkOp`/`unlinkSpec`, `GSt`, `unlinkImpl`, `epochFresh`, `challengeCapable`, `challengeResp`, `unlinkGame`, `unlinkAdvantage`.
- `Frame.lean` (B3/T7): `Signal`, `lazyRO`, `FrameSt`, `emitSignal` (emits `y = rlnY k a x`), `FrameOp`/`frameSpec`, `frameImpl`, `Evidence`, `recoverSlope`/`recoverSecret`, `Slashes`, `recoverSecret_line` (proved, from `rln_recover_k`), `frameGame`, `frameWinProb`. Tied to `RLN.lean` (task G4, parallel workstream).

## Oracle surfaces

- **UNLINK** (pre-challenge only; game state = epoch clock, both `PSt`, closed flags, last-signal epochs): `spend (u m) : Option View` (⊥ = insolvent or closed) · `retry u : Option View` (MC2 buffer, no state change) · `serve (u ρ) : PUnit` (accept-and-serve; abort = withhold) · `close u : Option CloseView` (once) · `tick : PUnit` (epoch advance). Challenge: `phase1` returns `m*`; game checks `epochFresh && challengeCapable`, answers `Option View` (⊥ in-band), then only the pure `guess` runs.
- **FRAME** (state = next index, closed flag, three RO caches): `spend m : Option (Signal F)` · `close : Option (Signal F)` · `roA (k i) : F` · `roX m : F` · `roNf a : F`. Honest emissions and adversary RO queries share caches (ROM-consistent). Adversary outputs `Evidence`; win = `Slashes k ev`.

## GATE-NOTEs (deviations from Spec.md prose)

UNLINK: (1) epochs = adversary-advanced `tick` counter (scheduler is adversarial, §6); (2) `retry` does not update the freshness clock (bit-identical re-send ≠ new signal); (3) retry answered even after close (more adversary power); (4) `close` counts as a signal emission in its epoch (immaterial: closed ⇒ challenge-incapable); (5) capability's "open ∧ unslashed" reduces to true (no UNLINK oracle can slash/evict-from-tree an honest candidate; that is FRAME's power) — encoded check is unclosed ∧ `capable`; (6) `Open` folded into `openCh`+`OpenView` (B's genesis receipt exchange absorbed there); (7) `serve` total — invalid receipts are instance-side no-ops; (8) spend directed at a closed candidate answers ⊥; (9) if checks pass but abstract `spend` still ⊥s, adversary gets ⊥ (unreachable for faithful instances); (10) corrupt payers unmodeled (spec: zero-cost maximality — adversary simulates them).

FRAME: (1) no solvency/deposit gate on `Ospend` (unbounded honest spends = strictly more adversary power); (2) win predicate omits `Dispute`'s nullifier-consistency/membership checks (easier win = stronger theorem); (3) corrupt members computed by the adversary via direct RO access, not oracles; (4) N−1-gateway view = all oracle responses (honest gateway's tuples reach A via reconciliation); (5) MC2 identical re-send omitted (deterministic replay of a held value); (6) epoch pseudonym `nf_e`/epochs absent (irrelevant to line algebra; add one more `lazyRO` if gate wants it); (7) inherited from RLN.lean: `roX` hits `0` w.p. `1/|F|`, where `y = k` — the T7 bound must absorb it.

## What the T4/T7 prover will need

- T4: instantiate `UnlinkScheme` per variant (A, B-static, B-rerand); for the secure direction, express `unlinkGame` as two bit-worlds sharing a prefix and use `hiddenBitAdvantage_eq_zero_of_distEquiv` / `DistEquiv.of_step` (per-query `evalDist` case split, HeapBasic template) or `ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage` for the shared-prefix bridge; for B-static, a concrete `ChalAdversary` term matching `View`'s ciphertext presentation (the calibration attack must be a constructive term).
- T7: `rln_single_point_hiding` + `rln_evidence_sound` (RLN.lean) + a ROM argument that the adversary's view fixes at most one point per line unless it queries `roA` at `(k, ·)`, i.e. computes `k`; the `x = 0` and RO-collision events go into the negligible mass.
