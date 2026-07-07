# PROVING.md — how to work on the Lean formalization

One page. If you are an executor (human or agent) starting from zero, this is enough.

## The model boundary

We formalize the **protocol layer** of a zk payment channel over an **idealized ledger** and **idealized cryptography**. Concretely:

- The ledger is a Lean value (a state the transition function updates), not a blockchain. Its guarantees (transactions land, timeouts fire) are part of the model, stated in `Spec.md` §threat-model.
- Cryptographic primitives never appear as real algorithms. Each one is an **axiom** in `Zkpc/Assumptions.lean` — one per primitive, with a docstring naming the standard property it encodes (proof-system knowledge soundness, zk simulation, PRF/hash collision resistance, EUF-CMA signatures, blind-signature unforgeability + blindness).
- We do **not** verify circuits, the SNARK, or any implementation. Anyone claiming otherwise about this repo is misreading it.

## The trust surface

The statements, not the proofs. If `lake build` is green with zero `sorry`, the kernel has checked the proofs; the only thing left for human judgment is whether the **definitions** (in `Zkpc/Spec/`) and **theorem docstrings** say what we meant. That is why:

- Every theorem carries a docstring restating it in English. Keep them faithful; the human gates review docstrings + `Spec.md`, nothing else.
- Changes to `Zkpc/Spec/` (algorithm signatures, security games) re-open the corresponding human gate. Do not "adjust the definition slightly" to make a proof go through without flagging it — definition drift toward provability is this experiment's named failure mode.

## Rules (CI enforces the first three)

1. **Zero `sorry`**, everywhere, at every commit that lands on main.
2. **`axiom` only in `Zkpc/Assumptions.lean`.** If a proof needs a new assumption, add it there with a docstring naming the standard property, and note it in the PR — the axiom audit (K2) enumerates these.
3. **No `admit`, no `native_decide`.**
4. Game framework additions on top of VCV-io stay under ~1000 lines total. Resist generality; this repo proves seven theorems, it does not build a library.

## How to add a theorem

1. Find its statement in `Spec.md` (T1–T7). The Lean statement must be a faithful transcription; when in doubt, transcribe more literally.
2. Put the statement in the module named in the theorem-to-file map (README appendix), with the English docstring.
3. Prove it. Prefer induction over the transition relation for safety theorems; prefer explicit bijections/simulators for indistinguishability arguments.
4. `lake build` locally; CI replays it.

## Layout

| Path | Content |
|---|---|
| `Spec.md` | English spec: the object, T1–T7, threat model. The trust surface. |
| `Zkpc/Assumptions.lean` | All axioms. Nothing else may declare one. |
| `Zkpc/Spec/` | Algorithm signatures and security games (gate-reviewed). |
| `Zkpc/Core/` | State model, transition function, flat-ticket instantiation. |
| `Zkpc/Games/` | Game framework over VCV-io (adversaries, oracles, advantage). |
| `Zkpc/Theorems/` | T1–T7, one module per theorem group. |
| `tla/` | TLA+ model (M0.5) and its TLC configs. |

## What the human gates check

- **Gate B1**: `Spec.md` theorem statements — do they say what the protocol needs?
- **Gate B3**: the security-game definitions in Lean — is the adversary strong enough (abort/evict oracle present), is winning defined right? This is where A2L failed; it gets line-by-line review.
- **Gate K1**: independent re-read of statements only, by a reviewer who wrote none of it.
