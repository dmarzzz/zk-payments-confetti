# Zkpc/ — module map

`lake exe cache get && lake build` from the repo root kernel-checks
everything (or `make build`). Rules in [`CONTRIBUTING.md`](../CONTRIBUTING.md).

## New protocol (`PROTOCOL.md`) — the live target

| Module | What it proves |
|---|---|
| `Chain/State.lean` | Settlement state machine: balance safety, conservation, honest-close-exact, refund liveness (with three disclosed idealizations — see docstring). |
| `Chain/Collision.lean` | The stale-close collision mechanism, both directions (stale ⇒ challengeable, honest ⇒ unchallengeable). |
| `Chain/Anonymity.lean` | Two-payment anonymity warm-up, advantage exactly 0 (idealized: no oracle access). Not the full T4 successor. |
| `Chain/Refinement.lean` | Executable refinement of the chain machine. |

## Reusable engines (protocol-agnostic)

| Module | Role |
|---|---|
| `Games/Framework.lean` | Game/advantage definitions, hidden-bit experiments, adversary plumbing (VCV-io). |
| `Games/Coupling.lean`, `Games/FlatInstance.lean`, `Games/T4.lean`, `Games/T4Fires.lean` | The random-oracle coupling engine behind the advantage-0 unlinkability results, plus non-vacuity witnesses. |
| `Games/Calibration.lean` | Must-fail/must-pass calibration adversaries (the anti-vacuity discipline). |
| `Games/Frame*.lean` | The T7 campaign: secret-averaged deferred sampling, query charging, the finite-query bound — and the kernel-refutation of pointwise certificates (`FrameDeferred.lean`). |
| `Crypto/FSRom.lean` | Lazy programmable random oracle (hash-based, PQ-compatible). |

## Historical (superseded rev-11 object — kept compiling, no live role)

| Module | What it was |
|---|---|
| `Core/*` (T1, T2, T3, T5, Flat, State, ...) | Safety core of the old object. `Core/T1.lean` is the Class A template. |
| `Games/{Unlink,BInstances,RLN,T7}.lean` | Old unlinkability game, B-instance calibrations, RLN algebra, conditional T7. |
| `Fleet/*`, `Refund/*`, `Network/*`, `Composition/*` | Fleet bound, encrypted-refund layer, multi-recipient accounting, end-to-end compositions. |
| `Crypto/{ElGamal*,Schnorr*,ThresholdSchnorr,LinearSigma,...}.lean` | Elliptic-curve instantiations — excluded by the new protocol's post-quantum constraint. The post-`e2de071` ones are unattested (see `STATUS.md`). |
| `Spec/Object.lean`, `Assumptions.lean` | The old object tuple and the named-assumption registry (rework pending for Spec-v2). |

Full inventory with theorem names: `research/raw/proof-inventory-rev11.md`.
What to build next: `ROADMAP.md`.
