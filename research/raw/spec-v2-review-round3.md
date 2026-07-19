# Spec-v2 round-3 review (2026-07-18): independent Fable-5 passes

Two independent Fable-5 reviews of the campaign: a modeling/soundness audit
of the Lean corpus (does the kernel-checked code state what it claims?) and
a strategy/sequencing pass. Findings distilled into `Spec-v2.md` §11 as
R3-1..R3-7 (applied corrections + two opened rigor items). Full text below.

---

## Review A: modeling soundness audit

All nine files read, plus spot-checks of the referenced `PayMsg`/`Anonymity.lean`, the vendored `hiddenReadMany` lemma in VCVio, and the ROADMAP residual entries. Findings below, ranked most-load-bearing first.

---

## Ranked concerns

### 1. `adaptive_frame_bound` is not a bound on any game (FrameAdaptive.lean) — GENUINE DEFECT (in statement, not proof)

The theorem proves `Pr[E1 | game1] + Pr[E2 | game2] ≤ q/|C| + 1/|N|` where game1 (`hiddenReadMany`) and game2 (`$ᵗ N`) are **two disjoint probability spaces glued by `add_le_add`**. A sum of probabilities from unrelated experiments is not the probability of anything; there is no joint experiment in which an adversary wins by "secret recovered OR fallback hits", so the docstring's "an adaptive q-probe framer's **total advantage** is at most q/|C| + 1/|N|" is not what the Lean says. Contrast stage 1 (`chainFrame_bound` in Frame.lean), which *does* define a single win predicate `ChainFrameWins` over one product sample space; stage 2 quietly loses that structure. The docstring half-discloses ("stated on their own hidden targets... the same sum"), but the theorem name and headline sentence promise the fused claim, which is exactly the residual the file says it is *not* claiming.

**Fix:** either (a) define the joint adaptive game (adaptive probes + fallback guess over `$ᵗ (C × N)`, the honest analogue of `FrameGuess`) and prove the union bound there, or (b) demote: rename to `adaptive_secret_probe_bound_plus_guess`, and state plainly that stage 2 covers only the secret-recovery disjunct adaptively; the fused adaptive frame game is entirely in the FrameDeferred residual. "Stage 2 core" is a fair label for `adaptive_secret_probe_bound` alone; it is an overclaim for `adaptive_frame_bound` as written.

### 2. Global `Function.Injective nul` is unsatisfiable at the intended instantiation (Close.lean, inherited by State.lean, Liveness.lean) — OVERCLAIM / HYPOTHESIS-SCOPE GAP

Every downstream theorem assumes `Function.Injective nul` for `nul : ℕ → N`. For the *real* nullifier space (finite hash range), no injective `ℕ → N` exists (pigeonhole), so the theorems can never be instantiated at the actual protocol type; they are non-vacuous only because `N` is left an abstract (implicitly infinite) type. The probabilistic justification (`probEvent_chain_collision_le`) covers only a finite prefix `Fin n → N`, and the bridge ("instantiating from an injective finite prefix of length m ≥ msgs + 2 is a finite matter", CollisionBound.lean docstring) is asserted, never formalized. So the hypothesis assumed is strictly stronger than the hypothesis proven to hold w.h.p.

**Fix:** the proofs only ever apply `hinj` at indices ≤ msgs + 2. Weaken to `Set.InjOn nul (Set.Iic (c.msgs + 2))` (or a per-theorem bound) and prove the one-line bridge lemma from an injective prefix. Cheap, and it closes the only path by which "kernel-checked with hypothesis H" and "H holds except with prob n²/|N|" fail to compose.

### 3. The framing adversary gets one fallback guess; Spec §7 promises `~q/|N|` (Frame.lean `chainFrame_bound`, FrameAdaptive.lean) — MODELING GAP / SPEC MISMATCH

`FrameGuess.fallback : N` is a **single** direct guess, giving the `1/|N|` term. Spec §7 states non-frameability with "bound of shape `~q/|N|`". A real challenging Bob does not get one guess: every held message from *another* channel is a free candidate collision against the exhibited nullifier (the contract will evaluate `N_m ∈ E` for each submitted challenge, and nothing in Spec §5 limits challenge attempts within the window). The kernel's "probe hits secret ⇒ conservatively award the win" is genuinely conservative (good), but the fallback side is *anti*-conservative: it silently downgrades the adversary from q' guesses to 1.

**Fix:** `fallback : List N`, bound `q_C/|C| + q_N/|N|`, matching the spec's stated shape. The counting lemma changes trivially. Alternatively, amend Spec §7 to the `q/|C| + 1/|N|` shape with an explicit single-shot justification, but I don't see one that survives multiple cross-channel held messages.

### 4. Liveness.lean claims "guaranteed under fairness" but formalizes no fairness — OVERCLAIM IN WORDING

The docstring says the module "upgrades [alice_liveness] to a **guaranteed** statement under a minimal fairness assumption". No fairness assumption appears anywhere in the Lean: there is no temporal operator, no schedule, no fair-run predicate. What is proven is (valuable) *enabledness persistence* (`no_action_disables_close`) and *deadlock freedom* (`not_stuck`). `not_stuck`'s title "Guaranteed settlement, either party" is wrong as stated: for a pending close inside the window the witness step is `tick 1`, and an infinite tick-only run settles nothing; nothing forces `settle` to fire, ever. The prose argument ("enabledness of a finite Alice-only sequence + weak fairness ⇒ guarantee") is correct informally but is exactly the part not in the kernel. ROADMAP obligation 5 ("guaranteed-liveness under fairness") should not be marked discharged by this file.

**Fix:** reword the module header and `not_stuck` docstring to "enabledness / no-deadlock facts; fairness composition is prose" or formalize a fair-schedule predicate (all-suffixes-take-enabled-Alice-moves) and prove eventual settlement. Note also `Step.tick` accepts `dt = 0`, so even "time passes" is not guaranteed by the step relation.

### 5. `signed_close_anonymity`'s "advantage exactly 0" is a property of the ideal model, and the ideal model contains the F-R2-1 repair's entire burden (CloseView.lean) — ACCEPTABLE WITH DISCLOSURE, NEEDS REWORD

Three idealizations do the work:
- **One-time-mask commitments (`r + v`)**: perfectly hiding, unconditionally. Real `Com` is hash-based and at best computationally hiding; the honest real-world statement is "advantage ≤ Adv_hiding", never 0. The "exactly 0" headline should carry the ideal-commitment qualifier wherever it is quoted (STATUS, ROADMAP, spec).
- **Proof objects outside the view**: the F-R2-1 repair moves `C_x` and `σ` *into* `π_close` as witnesses. If `π_close` is not zero-knowledge, `C_x` leaks right back out through the proof, and the repair is void. ZK of `π_close` is not even a named hypothesis; it is enforced by omission (the view type simply lacks the proof). This assumption is load-bearing for the repair and should be added to Spec §1's primitive list ("π_close is ZK") and to the module's GATE-NOTE explicitly.
- **Equal-δ / equal-split session form**: this is the *right* isolation, in my judgment. The conceded leak (Spec §8 item 3, subset-sum on splits) is precisely the split value; conditioning on equal splits removes exactly that channel and nothing else, since the only other split-dependent view components (payment δs) are public in both worlds. It does not hide a further leak. However it proves indistinguishability only on the diagonal of the split space; the simulator-form statement Spec §8 already records ("close-view simulator given cid, D, split, mode, time") is the claim a cryptographer wants, and it is strictly stronger (it implies the equal-split game and cleanly quotients out leak 3). Recommend targeting the simulator form for stage 2 rather than growing the game zoo.

Also disclosed and fine: q = 2, one payment per channel, non-adaptive. "Stage 1" is an honest label here.

### 6. `challenge_enabled_iff_unsafe` discharges the fiat *within the symbolic layer only*; the "iff" is one-sidedly conditional (State.lean) — ACCEPTABLE WITH DISCLOSURE, ONE REWORD

The discharge is real: settlement is guarded by window expiry alone, and unsafe-settlement is a reachable outcome attributed to Bob's sleep, not hidden by a guard. Two residual conditions ride along:
- **Forward direction** ("unsafe ⇒ challengeable"): assumes Bob retained every sent message (`Evidence` quantifies over all `j ≤ msgs`). Vigilance is disclosed (§9); *retention* should be named alongside it.
- **Reverse direction** ("safe ⇒ unchallengeable", `safe_close_unchallengeable`): absolute in the model, but only `q/|C| + 1/|N|`-true in reality, because forged witnesses are outside the symbolic layer. The machine and the frame kernel each hold on their own; the statement "honest closer is never slashed, except with probability ≤ ..." exists nowhere as one theorem. That composition is the same unfused residual as concern 1, and it is the single most important missing end-to-end statement of the campaign. The module docstrings disclose this correctly; STATUS/ROADMAP should present "Bob never loses" and "never slashed" as *conditional on the unfused crypto kernels*, not as done.

Separately, `Inv` is genuinely constraining, not slack: I checked each conjunct is load-bearing in a downstream theorem (caps in `no_overspend`, conservation conjunct in `conservation`, the cooperative conjunct in `cooperative_exact`), contexts are frozen during the challenge window (all of `pay`/`ghostSend`/`signGhost` require `closing = none`, so `balV s.ctx x` at settlement equals the close-time value), and the challenge/settle window guards partition on `t0 + tau` with no overlap. `alice_liveness`'s constructed run is robust, not just existential luck: at every intermediate state, `challenge` is disabled by safety, `timeoutForfeit` and `requestClose` by `closing = some`. That theorem is the strongest honest result in the campaign.

### 7. G7 is assumed, not modeled; plus an undisclosed Bob-loss channel from just-closed channels (State.lean guard `earned + δ ≤ P.D`; Spec §2/§3/GN-3) — RESIDUAL HOLE IN SPEC-COVERAGE CLAIMS

The G7 decision (Merkle anchor, `D` propagating inductively) is sound as a design repair for phantom channels, and the F-R1-1/F-R1-3 repairs look complete on their surfaces. But in the Lean, "the proof speaks about the real D" is a *transition guard*, i.e., G7's conclusion is baked in; the inductive propagation argument (genesis branch reads D under root, signed branch copies it, cid-matched membership per GN-1) exists only in prose. That's a legitimate layering, but STATUS should not count G7 as formally covered. One residual G7 hole worth surfacing to §7: with epoch roots accepting current + previous epoch, Bob accepts payments from **already-closed channels** for up to ~2 epochs (GN-3 admits this), and such payments are unsettleable, so Bob renders service for nothing. That loss is outside the single-channel machine, outside "Bob never loses", and listed nowhere in §7's safety properties. Add it as a disclosed bounded-loss item (bounded by service value per 2 epochs per channel), or shrink acceptance to current-epoch-only at close.

### 8. Calibrations: real but weaker than their billing (Frame.lean, CalibrationChain.lean) — ACCEPTABLE, MINOR REWORD/STRENGTHEN

- `chainFrame_leaky_loses` / `chainFrame_grind_loses`: these hardwire the win into the adversary (fallback := the sampled target itself; probes := all of C). They witness that both terms of the bound are attainable, i.e., the *win predicate* is not vacuously false and both terms are load-bearing. They do **not** model a leaky *scheme* (there is no scheme object whose leak the game detects). Fine, but the docstring "a scheme that leaks the committed next-nullifier is framed with probability 1" describes an interpretation, not the formal content; say "the game's win predicate awards the echo adversary probability 1, witnessing the 1/|N| term".
- `linkable_leak_detected`: genuinely valuable (distribution inequality for the unmasked scheme, exact negation of the real coupling). One gap: "so *some* adversary distinguishes" is inferred, not formalized. The natural strengthening is one lemma: adversary `A := fun p => pure (decide (linkEvent p))` has positive advantage in the actual `anonGame`. Worth doing; it converts the calibration from "distributions differ" to "the game as played catches it".

### 9. Spec §5 challenge clause 2 not updated for F-R2-1 (Spec-v2.md; Close.lean `SameState`) — WORDING/CONSISTENCY

After the repair, signed closes publish no `C_x`, so §5's "`C_m ≠ C_x`" is unevaluable for them; §5 only carves out the genesis case. The §4 [R2] note argues no exception is needed (correct: for a signed tip close nothing held reveals `N_{x+1}`; for a stale signed close the challenger's `C_m = C_{i+1} ≠ C_i` anyway), but §5's normative challenge relation should state the per-mode rule explicitly. Correspondingly, Lean's `SameState c j (.signed i) := j = i` excludes a case the real contract *cannot* check; it is inert under injectivity (`nul i ≠ nul (i+1)`), so no theorem is affected, but add a comment noting the exclusion is a modeling convenience, not a contract check, and that it is provably inert.

### 10. CollisionBound covers one chain; cross-channel absorption is a claim (CollisionBound.lean; Spec §5 [R1]) — MINOR

Spec §5 absorbs cross-channel false positives "into the collision bound", and Close.lean's GATE-NOTE repeats it, but the proven bound is a single iid draw of one chain's n links. The union-of-two-chains instance is the same birthday argument at 2n and trivially follows, but it is not stated. Also, the iid-uniform reduction assumes no adversary pre-queried Alice's slots `(N_j, c)`, which itself holds only modulo the secret-probe bound; another instance of the unfused composition. One sentence in the docstring acknowledging both would make the claim exact. The constant itself checks out: `n(n-1)/(2|N|)` is correct, tighter than the advertised `n²/|N|`, and the degenerate cases (n ≤ 1, |N| = 0) are handled rather than assumed away.

---

## On the residual labels

"Stage 1" (Frame kernel, CloseView game) and the ROADMAP's explicit tracking of the FrameDeferred fusion and the full adaptive session game are honest **except** for `adaptive_frame_bound` (concern 1), which dresses the unfused pair in fused language, and the Liveness module (concern 4), which claims obligation 5's substance while proving its enabledness skeleton. A cryptographer reading only theorem names and headline docstrings would come away believing more is proven than is; a cryptographer reading the GATE-NOTEs would not. Move the load-bearing caveats from GATE-NOTE prose into the theorem docstrings' first lines.

## Module verdicts

| Module | Verdict |
|---|---|
| Close.lean | SOUND-BUT-REWORD (injectivity hypothesis scope, concern 2; evidence algebra itself is a faithful transcription of §4–5, I verified every `ExhibitIdx`/`SameState` case against the spec) |
| State.lean | SOUND (fiat discharge is genuine; add retention to the vigilance disclosure, concern 6) |
| CollisionBound.lean | SOUND (constant correct; add the two one-sentence scope notes, concern 10) |
| Frame.lean | SOUND-BUT-REWORD (single-fallback vs spec's `~q/|N|`, concern 3; calibration billing, concern 8) |
| FrameAdaptive.lean | DEFECT (`adaptive_frame_bound` states a sum over disjoint experiments as a "total advantage"; `adaptive_secret_probe_bound` alone is sound, concern 1) |
| CloseView.lean | SOUND-BUT-REWORD (ideal-commitment qualifier on "advantage 0"; surface ZK-of-`π_close` as a named assumption, concern 5) |
| CalibrationChain.lean | SOUND (strengthen to a concrete positive-advantage adversary, concern 8) |
| Liveness.lean | SOUND-BUT-REWORD (theorems fine as enabledness facts; module framing claims fairness content that does not exist in the kernel, concern 4) |

Files audited: `/Users/clawbox/cleavelabs/zk-payments-confetti/Spec-v2.md`, `/Users/clawbox/cleavelabs/zk-payments-confetti/lean/Zkpc/Chain/V2/{Close,State,CollisionBound,Frame,FrameAdaptive,CloseView,CalibrationChain,Liveness}.lean`, with `/Users/clawbox/cleavelabs/zk-payments-confetti/lean/Zkpc/Chain/Anonymity.lean`, `/Users/clawbox/cleavelabs/zk-payments-confetti/ROADMAP.md`, and the vendored `VCVio/.../ProbeEps.lean` as cross-checks.

---

## Review B: strategy and sequencing

## Verdict: GO-WITH-FIXES

Continue autonomous proving while awaiting sign-off, but not on both tails. One tail is genuinely sign-off-independent and one is exactly the thing pending sign-off. Running both symmetrically violates the repo's own ground rule ("nothing gets proved against a moving target," ROADMAP.md line 13). And the plan under-invests in the one action that actually moves the gate: a two-decision note, not the PR.

---

### 1. Sequencing under the gate: split the work by what the two open decisions can actually touch

**What G7 and the rescope can change.** G7 changes the genesis branch of R_pay (channel-tree membership, `root` in payment public inputs). The rescope changes the anonymity theorem's top-level statement (adversary view, simulator inputs in Spec-v2 §8, mode-dependent exhibit sets). Neither touches the challenge relation. That was pinned by A5/G6, which Vitalik already accepted on 2026-07-18 as part of A1–A5.

**Sign-off-INDEPENDENT (safe to run now):**
- **The FrameDeferred fusion (tail a).** Non-frameability is stated against the challenge relation (`N_{i+1} = H(N_i, c)`, c bound at open) and the nullifier chain. Both are inside the accepted A1–A5 surface. If Vitalik rejects the channel-tree, R_pay's anchoring branch changes but the frame game does not. Waste risk: near zero.
- Collision-bound residuals 2(b–c) (binding-as-assumption, threading the probabilistic event through machine-level statements).
- Genesis-uniformity (obligation 6), dedup (obligation 7), PQ-model restatement (obligation 8), the liveness fairness wrapper. All are safety/machine-level, untouched by either decision.
- The per-endpoint `#print axioms` audit debt (STATUS.md "Residual"). Cheap, pure hygiene.
- **Definition-agnostic anonymity prep:** porting the `Unlink`/`Coupling`/`FlatInstance` scaffolding to the chain view, and the calibration battery members that survive any rescope answer. In particular the **hidden-balance necessity lemma** (formalizing PROTOCOL.md's own δ-matching argument): that argument is the *mechanism* of the subset-sum leak, so it is load-bearing under every plausible answer.

**Sign-off-DEPENDENT (hold):**
- **The full adaptive anonymity session game (tail b), top-level statement onward.** The rescope IS its definition. Concretely wasted if the answer changes: the session-game statement, the simulator-input plumbing (§8's enumerated inputs), the charged-abort-lever accounting, and every mention of `root`/epoch if G7's anchor changes form. The realistic "rejection" of the rescope is not "prove full strength anyway" (the subset-sum leak makes that false); it is "fold the shielded pool into the base protocol," which rewrites the entire close view and would strand most of a completed tail-b campaign. That asymmetry, tail a survives any answer and tail b survives none of the bad ones, is the whole sequencing argument.
- ZK-bridge/composition (obligation 10): partially G7-dependent (the bridged R_pay includes the membership branch). Scaffolding is portable, statement is not.

### 2. The two tails: frame fusion first, and yes to autonomous campaigns with one discipline added

**Order: FrameDeferred fusion first.** Three reasons beyond the gate-independence above: (i) it is the highest proof-engineering-risk item left (pointwise certificates are already *refuted* in this repo, `frameDeferredSampling_refuted`, so the secret-averaged port is the subtle one; front-load the risk); (ii) it completes the safety story (Bob can't steal, Alice can't be framed), which is what a payment-channel designer most needs to believe; (iii) FrameAdaptive.lean already has the stage-2 core, so the residual is specifically "the deferred-sampling fusion with oracle semantics," a bounded port of `FrameDeferredSamplingAvg` + `qb.total` charging from the FRAME campaign. That is exactly the shape (existing machinery, mechanical port, kernel-verified loop) where an overnight multi-agent campaign is the right vehicle.

**Do these need a human cryptographer first?** Not to *prove*, yes to *claim*. The Lean kernel is a trustworthy verification loop for the proofs; it is not a check that the statement means what you think. The method doc's standing open risk (no outside human has ever attacked the definitions) should gate two things: external "proved secure" claims, and any product commitment. It should NOT gate the frame campaign, because its definitional surface already survived the red-team gate rounds and designer acceptance. The one discipline to add: **freeze the theorem statement + English docstring first, run a Fable review on the statement (per your own spend-gate rule), then launch the overnight run against the frozen statement.** Statement drift mid-campaign is how agent swarms prove the wrong thing with zero sorries.

### 3. The collaboration: send a two-decision note, not the PR

The PR is the record; it is not the ask. The winning move in this repo's own history is the Q1–Q5 packet: each question with a proposed default so a one-word answer sufficed, and Vitalik accepted all five in one pass. Repeat it exactly:

- **Decision 1 (G7):** "Payments need an anchor to a real deposit or Alice fabricates a phantom channel and safety fails totally at close. Any per-channel public input breaks anonymity, so the anchor must be channel-tree membership in the genesis branch. Note your 'no Merkle tree' remark concerned *states*, not channels. Default: accept. One word suffices."
- **Decision 2 (rescope):** "The red team turned your own δ-matching argument against the close boundary: a clear split is subset-sum-linkable, so base-protocol anonymity is intrinsically *unlinkable-until-close*; full strength is exactly the shielded-pool extension. Default: accept the rescope + mode-dependent exhibit sets."

Two things make this note land. First, lead with **F-R2-1**: the close-view proof attempt *found and repaired a real attribution leak* (signed closes publishing `C_x`), then went through at advantage exactly 0. That is the machine demonstrating it earns its keep, and it is the kind of finding that keeps Vitalik engaged; nobody stays engaged reviewing 83 Lean modules. Second, **put the human-cryptographer gap in the note as a question, not a confession**: "the standing open risk is that no outside human cryptographer has attacked these definitions; do you want to nominate one (PSE, an academic), or attack the two anonymity definitions yourself for 30 minutes?" Asking for his judgment is more engaging than asking for his review, and it converts the project's biggest methodological weakness into a collaboration hook.

### 4. Product angle: research collaboration with optionality. Do not resource as a product line.

Honest read: Cleave is an options DEX mid-fundraise, mid-MVP-simplification. This is a PQ anonymous payment channel with no circuit implementation, no cost numbers, and a privacy claim that is agent-reviewed only. The real assets today are (a) the Vitalik association (fundraising-relevant, but only if the work stays credible, which argues for the human-review gate), (b) the reusable agent-FV capability, which IS strategically relevant to Cleave (you can point the same machinery at Cleave's own options contracts), and (c) a cheap option on the private-AI-payments thesis, which rhymes with the world-market act-two direction but is not on its critical path.

To flip it to a product line, ALL of: spec frozen and an outside human cryptographer's attack logged; a real STARK circuit with proof-time and on-chain cost per payment that beats non-private alternatives (x402-style flows) by enough that privacy is the tiebreaker; identified buyers who pay for *unlinkability* of inference payments specifically, not just cheap payments; and Cleave post-raise with spare capacity. Until then: one autonomous-campaign track plus Jiajun's collaboration hours, zero headcount, revisit at spec freeze.

---

## Ranked next actions

1. **Draft and send the two-decision note to Vitalik** (G7 + rescope, proposed defaults, one-word-answer format, F-R2-1 as the hook, human-reviewer question included). Effort: 2–3h from Spec-v2 §8/§11. Trigger: now; blocks nothing, unblocks everything.
2. **Launch the FrameDeferred fusion campaign** (obligation 3 residual). Statement freeze + docstring + Fable statement-review first, then overnight multi-agent port of the FRAME deferred-sampling stack. Effort: 1–2 overnight runs. Trigger: now; independent of both open decisions.
3. **Definition-agnostic anonymity prep**: port `Unlink`/`Coupling`/`FlatInstance` to the chain view; prove the hidden-balance necessity lemma. Do NOT state the top-level session game. Effort: 1 overnight. Trigger: now, as the parallel/second track.
4. **Batch the cheap independent debt**: collision 2(b–c), `#print axioms` per-endpoint audits, PQ restatement, dedup, genesis-uniformity. Effort: ~1 overnight total, fills idle agent capacity. Trigger: now, lowest priority of the "now" items.
5. **Full adaptive anonymity session game** (tail b proper). Effort: the biggest remaining campaign, 2–4 overnights plus human statement review before launch. Trigger: Vitalik signs G7 + the rescope. Hard-gated; do not start early.
6. **Log an outside human cryptographer attacking the definitions** (Vitalik's nominee, or PSE/academic outreach if he doesn't bite). Effort: hours of outreach, weeks elapsed. Trigger: with action 1. Standing rule until logged: no external security claims, no product commitment.
7. **One-page product-decision memo for Cleave**: defer productization; revisit trigger = spec frozen + human attack logged + per-payment cost benchmark vs non-private alternatives. Effort: 1–2h. Trigger: after action 1 ships, so the memo reflects Vitalik's response latency.

The single most likely failure mode of the current plan is symmetric treatment of the two tails: an overnight swarm completes the adaptive anonymity game against the unsigned §8 definitions, Vitalik answers "just make the shielded pool base," and the campaign is stranded. Fixes 1 and 5 above eliminate that scenario; everything else is already pointed the right way.
