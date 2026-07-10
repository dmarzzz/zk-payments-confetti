# PROVING.md — how to work on the Lean formalization

One page. If you are an executor (human or agent) starting from zero, this is enough.

## The model boundary

We formalize the **protocol layer** of a zk payment channel over an **idealized ledger** and **idealized cryptography**. Concretely:

- The ledger is a Lean value (a state the transition function updates), not a blockchain. Its guarantees (transactions land, timeouts fire) are part of the model, stated in `Spec.md` §threat-model.
- Cryptographic primitives never appear as real algorithms. Each named assumption is registered in `Zkpc/Assumptions.lean` with a docstring naming the standard property it encodes (proof-system knowledge soundness, zk simulation, PRF/hash collision resistance, EUF-CMA signatures, blind-signature unforgeability + blindness). In the current tree every one of them is **discharged by construction** in the idealized model — knowledge soundness as transition guards, zero knowledge as proof-free or simulator-equal views, hashes as lazily sampled random oracles — so the file declares **no Lean `axiom` at all**; the registry exists so that if a future proof genuinely needs one, it has exactly one audited place to live.
- We do **not** verify circuits, the SNARK, or any implementation. Anyone claiming otherwise about this repo is misreading it.

## The trust surface

The statements, not the proofs. If `lake build` is green with zero proof
escape hatches and the axiom audit shows only the intended foundations, the
kernel has checked the proofs; the remaining judgment is whether the
**definitions** (in `Zkpc/Spec/`) and **theorem docstrings** say what we
meant. Source checkpoint `abb878f` has that technical evidence: fresh cache
restore (8,283 files), all 3,595 root jobs on Lean 4.30.0, exact endpoint
axiom capture using only standard Lean axioms, and clean source/diff scans.
That does not replace the pending human gates. The later synchronized
12-page PDF has separately completed its clean rebuild and page-by-page
visual QA. That is why:

- Every theorem carries a docstring restating it in English. Keep them faithful; the human gates review docstrings + `Spec.md`, nothing else.
- Changes to `Zkpc/Spec/` (algorithm signatures, security games) re-open the corresponding human gate. Do not "adjust the definition slightly" to make a proof go through without flagging it — definition drift toward provability is this experiment's named failure mode.

## Rules (CI enforces the first three)

1. **Zero `sorry`**, everywhere, at every commit that lands on main.
2. **`axiom` only in `Zkpc/Assumptions.lean`.** If a proof needs a new assumption, add it there with a docstring naming the standard property, and note it in the PR — the axiom audit (K2) enumerates these.
3. **No `admit`, no `native_decide`.**
4. Game framework additions on top of VCV-io stay under ~1000 lines total. Resist generality; this repo proves seven theorems, it does not build a library.

## How to add a theorem

1. Find its statement in `Spec.md` (T1–T7). The Lean statement must be a faithful transcription; when in doubt, transcribe more literally.
2. Put the statement in the module named in the theorem-to-file map (paper §7 / `OPEN-PROOFS.md`), with the English docstring.
3. Prove it. Prefer induction over the transition relation for safety theorems; prefer explicit bijections/simulators for indistinguishability arguments.
4. `lake build` locally; CI replays it.

## Layout

| Path | Content |
|---|---|
| `Spec.md` | English spec: the object, T1–T7, threat model. The trust surface. |
| `Zkpc/Assumptions.lean` | The assumption registry (currently declares no `axiom`; nothing else may declare one). |
| `Zkpc/Spec/` | Algorithm signatures (gate-reviewed). |
| `Zkpc/Core/` | State model, transitions, flat-ticket instantiation, T1/T2/T3/T5, executable refinement, composition. |
| `Zkpc/Games/` | Game framework over VCV-io, the security games, T4/T7 and the FRAME campaign. |
| `Zkpc/Fleet/`, `Zkpc/Refund/` | The fleet bound (T6, recovery) and the refund variant (safety, cascade, fleet). |
| `Zkpc/Crypto/`, `Zkpc/Network/`, `Zkpc/Chain/` | Wire-protocol reference layers, the multi-recipient network layer, and the nullifier-chain instantiation. |
| `tla/` | TLA+ model and its TLC configs. |

For T7, keep the quantifiers precise. `FrameQueryBounds A` carries the five
structural query certificates. `dsBadMassLe_of_queryBounds` and
`frameGoodSliceTransfer_of_tape` feed the secret-averaged certificate
`frameDeferredSamplingAvg_holds`, and
`T7_frame_query_bound_unconditional` proves
`frameWinProb mclose A ≤ (qb.total + 1)/|F|` with no additional coupling or
counting premise. The pointwise `FrameDeferredSampling` socket is
kernel-refuted and must not be revived. `FrameAsymptotic.lean` supplies
two conditional negligibility lifts: the first assumes negligibility of the
explicit query/field-size ratio; the second uses an explicit polynomial
numerator bound and negligible inverse field size to establish that premise.
Both assume per-parameter query certificates. Neither supplies a PPT/runtime
classifier, derives query bounds or field growth from PPT, or reduces
deployed primitives.

## What the human gates check

- **Gate B1**: `Spec.md` theorem statements — do they say what the protocol needs?
- **Gate B3**: the security-game definitions in Lean — is the adversary strong enough (abort/evict oracle present), is winning defined right? This is where A2L failed; it gets line-by-line review.
- **Gate K1**: independent re-read of statements only, by a reviewer who wrote none of it.
- **Gate K4**: a real outside cryptographer attacks the definitions. The
  recorded simulated-external agent exercise is useful evidence, but it is
  not this gate.

B1, B3, and K1 still require non-author human sign-off. The exact final
documentation/PDF SHA is recorded in the PR and issues rather than being
conflated with source checkpoint `abb878f`.
