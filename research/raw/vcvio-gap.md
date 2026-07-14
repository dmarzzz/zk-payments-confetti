# VCV-io gap analysis (task E1)

Survey of `Verified-zkEVM/VCV-io` @ `8f5dc4f2923cc47e39bc6ce21f71563cf7d19193` (local clone:
`.lake/packages/VCVio`, verified at that commit; toolchain `leanprover/lean4:v4.30.0`,
pins `mathlib v4.30.0` — same as our root). All file paths below are relative to the VCVio repo.
Note: this fork is far richer than upstream `dtumad/VCV-io`; most of the machinery below
(StateSeparating, SecExp advantage lemmas, ProgramLogic tactics) is fork-specific.

## 1. Core machinery

**Oracles.** `OracleSpec ι := ι → Type` (`VCVio/OracleComp/OracleSpec.lean`) — an index type
where each index is a query (input data lives in the index; `spec t` is the response type).
Combine specs with `+` (disjoint sum), notation `A →ₒ B` for a single oracle with domain `A`.
`OracleComp spec α` (`VCVio/OracleComp/OracleComp.lean`) is the free monad
(`PFunctor.FreeM`) over the spec. `ProbComp := OracleComp unifSpec`
(`VCVio/OracleComp/ProbComp.lean`) with sampling notation `$[0..n]`, `$ᵗ α`
(via `SampleableType`, uniformity enforced).

**Semantics.** `evalDist` / notation `𝒟[mx]` maps into `SPMF` (subprobability, `PMF (Option α)`)
via `MonadLiftT m SPMF` (`VCVio/EvalDist/Defs/Basic.lean:85-115`). Notation:
`Pr[= x | mx]` (`probOutput`), `Pr[p | mx]` (`probEvent`), `Pr[⊥ | mx]` (`probFailure`).
For `OracleComp`, the lift exists when `[IsProbabilitySpec spec]` / `[IsUniformSpec spec]`
(`VCVio/OracleComp/EvalDist.lean`) — each oracle answer is drawn from a per-index PMF,
uniform in the `IsUniformSpec` case. Support semantics via `MonadLiftT m SetM`.
Failure/abort in computations is `OptionT (OracleComp spec)` (`failure`, `guard`); `probFailure`
measures the `none` mass. Total-variation distance: `tvDist` (`VCVio/EvalDist/TVDist.lean`).

**Simulation.** `QueryImpl spec m` answers each query in a monad `m`; `simulateQ`
(`VCVio/OracleComp/SimSemantics/SimulateQ.lean`) folds a computation through it. Stateful
handlers: `QueryImpl.Stateful I E σ := QueryImpl E (StateT σ (OracleComp I))` with `run`/`run₀`
(`VCVio/OracleComp/SimSemantics/StateT/StateSeparating.lean`). Handlers compose:
`+` (append), `link`, `parSum`.

**Random oracle.** `OracleSpec.randomOracle` (`VCVio/OracleComp/QueryTracking/RandomOracle/Basic.lean`)
= lazy RO: fresh uniform sample on first query, cached in `QueryCache spec` thereafter —
exactly "fresh outputs uniform + independent, repeated queries consistent". Also
`eagerRandomOracle` (seeded, independent-per-call) in `RandomOracle/Eager.lean`,
plus `DeferredSampling`, `ProbeEps` (RO probability bounds), and `roSim` glue lemmas
(`RandomOracle/Simulation.lean`) for `unifSpec + hashSpec` games.

## 2. Security-experiment machinery (all at this commit)

`VCVio/CryptoFoundations/SecExp.lean`:
- `ProbComp.boolBiasAdvantage p = |Pr[true] - Pr[false]|` and
  `boolBiasAdvantage_eq_two_mul_abs_sub_half` — i.e. exactly `2·|Pr[guess=b] − 1/2|`.
- `ProbComp.boolDistAdvantage p q = |Pr[true|p] − Pr[true|q]|` (two-world form),
  triangle inequality, and the **hidden-bit decomposition**
  `boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch` (+ shared-prefix variant
  `boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage`): the hidden-bit game's bias
  equals the two-world distinguishing advantage. This is precisely the bridge our
  unlinkability definition needs.
- `ProbComp.guessAdvantage`, `distAdvantage`, `distAdvantage_eq_tvDist`,
  `distAdvantage_le_sum_range` (hybrid chains), `BoundedAdversary`, `structure SecExp`.

`VCVio/StateSeparating/` (SSP-style, the best fit for oracle-interactive games):
- `QueryImpl.Stateful.advantage h₀ s₀ h₁ s₁ A` (`Advantage.lean`) — Boolean distinguishing
  advantage of adversary `A : OracleComp E Bool` against two stateful handlers ("worlds").
- `DistEquiv (h₀,s₀) ≡ᵈ (h₁,s₁)` (`DistEquiv.lean`): `∀ A, 𝒟[h₀.run s₀ A] = 𝒟[h₁.run s₁ A]`.
  Constructors: `DistEquiv.of_step` (pointwise per-query `evalDist` equality of handlers ⇒
  equivalence against **every** adversary), `of_step_bij` (state-bijection coupling),
  `link_inner_congr`, `parSum_congr`. Bridge: **`DistEquiv.advantage_zero`** — equivalence
  gives advantage = 0 for all adversaries. `IndistAt … ε` (`IndistAt.lean`) for ε-bounds,
  `Hybrid.lean`, `IdenticalUntilBad.lean`.
- `GameEquiv g₁ g₂ := 𝒟[g₁] = 𝒟[g₂]` and `AdvBound` (`VCVio/ProgramLogic/NotationCore.lean:59`).

Worked examples (concrete evidence, sorry-free):
- `Examples/OneTimePad/Basic.lean` — `oneTimePad.perfectSecrecyAt` proved two ways:
  direct `probOutput` computation and relational bijection coupling (`by_equiv` / `rvcstep`
  tactics from `VCVio/ProgramLogic/Tactics/Relational.lean`).
- `Examples/OneTimePad/HeapBasic.lean` — **`realImpl_distEquiv_idealImpl`**: real-vs-ideal
  stateful handlers proved `≡ᵈ₀` via one per-(query,state) `evalDist` case-split + a
  bijection lemma, then `DistEquiv.of_step`. ~100 lines total for the whole real/ideal OTP
  story. This is a template for our secure-variant proof.
- `Examples/ElGamal/SSP.lean`, `Examples/SealedSender`, IND-CPA one-time/oracle games in
  `VCVio/CryptoFoundations/AsymmEncAlg/INDCPA/{OneTime,Oracle}.lean` (hidden-bit game shape:
  `let b ← $ᵗ Bool; …; pure (b == b')`).
- ZK: `SigmaProtocol.HVZK` / `PerfectHVZK` (`VCVio/CryptoFoundations/SigmaProtocol.lean:126-137`) —
  simulated-transcript-equals-real formulation; the "simulated zk proof" pattern is to
  parameterize by a simulator `Stmt → ProbComp Transcript` and assume/prove `𝒟`-equality.

Query tracking: `QueryLog` / `QueryCache` (`VCVio/OracleComp/QueryTracking/Structures.lean`),
`QueryImpl.withLogging` (`LoggingOracle.lean`, WriterT-based per-query logs),
`CountingOracle`, `SeededOracle`, `QueryBound` (`IsQueryBoundP` for per-oracle bounds).
Repo-wide sorry count: 11, confined to files we don't need
(`FujisakiOkamoto/*`, `GPVHashAndSign`, `FiatShamir/WithAbort/Security`, 4 example files).

## 3. What is missing for our two games (glue estimate)

- **Adversary typeclass: not needed.** An unbounded adversary is literally
  `A : OracleComp E Bool` (arbitrary strategy tree, no complexity structure), universally
  quantified. `DistEquiv` already quantifies over all `A` and all output types.
- **Two-world bookkeeping: exists** (`Stateful.advantage`, `DistEquiv.advantage_zero`,
  hidden-bit ↔ two-world bridge in SecExp). Nothing to build.
- **Abort/evict oracle: modeled, not prefab.** We add an index to our protocol `OracleSpec`
  and implement it in the world handlers (state update + response). If the *game* itself
  must abort, use `OptionT (OracleComp spec)` + `guard`; `probFailure`/SPMF semantics handle
  it. FS-with-abort files show the retry/abort idiom but are signature-specific.
- **Protocol-specific content (the real work):** channel state type, oracle spec
  (open/pay/abort-evict/challenge), the two world handlers for bit 0/1, the broken-variant
  handlers, one concrete distinguishing adversary + a finite probability computation for
  advantage > 0. Estimate: **~250–500 lines** of definitions + the per-query `evalDist`
  equality proof (secure variant) and one concrete `simp`-driven computation (broken
  variant). The generic glue VCVio already provides would have been ~1–2k lines to rebuild.
- Minor friction: heavy typeclass/universe plumbing (`IsUniformSpec`, `SampleableType`,
  `DecidableEq ι`) — budget some fight time; the examples show the working incantations.

## 4. Import surface

- The lakefile defines separate `lean_lib`s: `VCVio` (default target), `FFI`, `LatticeCrypto`,
  `HashSig`, `Examples`, `VCVioWidgets`, `ToMathlib`, `Interop`. C code (`csrc/`,
  `third_party/mlkem-native`) is compiled by `extern_lib` targets used by `FFI`/`LatticeCrypto`.
  Core `VCVio` modules do not import `FFI`/`HashSig`/`LatticeCrypto`/`Interop` (CI enforces
  Interop isolation). Importing e.g. `VCVio.CryptoFoundations.SecExp` +
  `VCVio.StateSeparating.DistEquiv` + `VCVio.OracleComp.QueryTracking.RandomOracle.Basic`
  stays inside pure-Lean deps: mathlib (cached), `PolyFun` (small), `loom2`/`Hax` are pulled
  as package deps by lake but their modules are only imported by `ProgramLogic/{Loom,Tactics}`
  and `Interop` respectively — Hax modules never build for core imports.
- Do **not** `import VCVio` (the root) — it pulls all ~200 modules incl. FiatShamir/Fischlin
  towers (long compile, still no C). Import the ~5 leaf modules we need.
- Empirical check: `lake build +VCVio.CryptoFoundations.SecExp` from our project (mathlib
  cache present) — see build-status note at the bottom of this file.

## 5. Recommendation: **(a)** — build on VCVio `OracleComp` + `evalDist`/`DistEquiv`

Justification:
1. **The hard 20% already exists and is proven.** `DistEquiv.of_step` +
   `DistEquiv.advantage_zero` reduce "advantage = 0 against every unbounded adversary with
   oracle access" to a per-query, per-state `𝒟`-equality of the two world handlers — a
   finite, local, non-interactive obligation. `Examples/OneTimePad/HeapBasic.lean` proves
   exactly this shape sorry-free in ~100 lines. On bare PMF we would have to reinvent the
   adversary-as-strategy-tree induction (`simulateQ_StateT_evalDist_congr` etc.) ourselves;
   an adversary that *interacts with oracles* (incl. abort/evict) has no natural encoding as
   a plain `PMF`-valued function of the bit without rebuilding a free monad.
2. **Advantage bookkeeping is done**: `boolBiasAdvantage` (= our `|Pr[guess=b] − 1/2|` up to
   the standard factor 2) with the hidden-bit ↔ two-world decomposition already proven.
3. **RO + simulated ZK idioms exist** (`randomOracle` caching impl; `PerfectHVZK`-style
   simulator parameterization), with support lemmas.
4. Version alignment is exact (Lean v4.30.0 / mathlib v4.30.0 on both sides), and evalDist
   ultimately *is* mathlib `PMF`/`SPMF`, so nothing is lost vs option (b) — pointwise
   `probOutput` computations for the broken-variant witness work the same way.

Caveats (honest): this fork moves fast and we're pinned to a commit — fine. The
StateSeparating layer is labeled experimental by its own docs (pilot ports), but the
lemmas we depend on are small and sorry-free. Budget 1–2 days for typeclass/universe
friction before the games take shape; the perfect-indistinguishability proof itself should
then be days, not weeks. Fallback if handler plumbing fights back: the plainer
`GameEquiv`/`ProbComp` route (still option (a) infrastructure, one `OracleComp` game per
bit, `evalDist_ext` + `probOutput` lemmas) as in `Examples/OneTimePad/Basic.lean`.

**Build status (verified 2026-07-06, from this project):**
`lake build +VCVio.CryptoFoundations.SecExp +VCVio.StateSeparating.DistEquiv`
`+VCVio.OracleComp.QueryTracking.RandomOracle.Basic +VCVio.OracleComp.QueryTracking.LoggingOracle`
completed successfully — 54 VCVio oleans + PolyFun, **zero C objects built**, a few minutes
wall-clock with the mathlib cache. The full recommended import surface compiles clean.
