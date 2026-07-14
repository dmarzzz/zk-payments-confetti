import Zkpc.Games.FlatInstance

/-!
# T4-A challenge-firing witness (Spec.md §7 T4; k3-vacuity-review.md flag 1)

The K3 adversarial-vacuity review (`research/raw/k3-vacuity-review.md`)
proves `T4_flat_unlinkability : unlinkAdvantage (flatInstance budget) A = 0` is
**non-vacuous**, but records (its §"Flagged build-checks", item 1) that the
argument rests *by analogy* on the shared, instance-generic challenge machinery
being live: the closer `unlinkAdvantage_eq_zero_of_challenge_bitfree` consumes
only bit-freeness, which would *also* hold vacuously for a hypothetical instance
whose challenge always returned `⊥`. The review therefore recommends adding, and
kernel-checking, one in-tree lemma per secure instance mirroring
`challengeResp_bStatic_init` — witnessing that the flat instance's `challengeResp`
actually **fires** on a satisfying configuration, returning a real `some [...]`
ticket batch rather than `none`/`⊥`.

This module discharges that recommendation for `flatInstance` (instantiation A).

## The witnessing configuration (Spec.md §7 T4 challenge clause, session form)

The simplest satisfying game state: both candidate payers freshly opened at
index `0` (`⟨0, none⟩`), the initial epoch `0` (so `epochFresh` holds — neither
candidate has emitted a signal in the current epoch), a solvent budget
(`budget ≥ 1`, so both candidates are `capableFor 1`), and a one-element message
vector `[m]` (`q = 1`, nonempty). On this config all three challenge guards fire
(`!mstars.isEmpty`, `epochFresh`, `challengeCapable … 1`), so the challenge takes
its emitting branch and `P_b` runs the length-`1` batch `spendBatch`.

## Which form, and why it witnesses non-vacuity

Unlike the deterministic calibration instances (B-static / the leak battery,
whose `spend` echoes a held handle, so `challengeResp … = pure (some [handle])`
is a bare equality), the flat instance's `spend` **samples fresh-uniform**
random-oracle components (`nf_e`, `y`, `nf`; `Zkpc.Games.flatSpend`), so
`challengeResp` is a genuine *distribution* over real ticket batches, not a
`pure`. We therefore witness firing at the level of the computation's `support`:

* `challengeResp_flat_fires` — a **concrete** real batch is reachable:
  `some [⟨m, m, m, m⟩] ∈ support (challengeResp (flatInstance budget) g_init b [m])`.
  This exhibits an actual non-`⊥` ticket list of length `q = 1` in the challenge
  output, so the `0` of `T4_flat_unlinkability` is a coupling of *real* batches,
  not an always-`⊥` artifact. (Any field element in each slot is reachable since
  `support ($ᵗ F) = univ`; we reuse the message `m` in every slot to name one.)
* `challengeResp_flat_never_bot` — the *strong* complement:
  `none ∉ support (challengeResp (flatInstance budget) g_init b [m])`, i.e. on
  this config the challenge **never** returns `⊥` — every execution yields a
  genuine `some`-batch. Discharged from the already-proved O2 obligation
  `flat_spendBatch_none_zero`. Together with the fact that a `ProbComp` support
  is always inhabited, this refutes "always `⊥`" outright.

Both hold for either hidden bit `b`, matching the game's `b`-independence of the
challenge guards. This closes flag 1 of k3-vacuity-review.md *by construction*
(kernel-checked) rather than by analogy to the calibration lemmas.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [SampleableType F]

/-- The flat instance's solvency cap is the static budget check (`rfl` unfold of
the `capableFor` field), matching the `bStatic_capableFor` idiom. -/
@[simp] private lemma flatInstance_capableFor (budget q : ℕ) (st : FlatPSt F) :
    (flatInstance (F := F) budget).capableFor q st = decide (st.idx + q ≤ budget) := rfl

/-- **The flat challenge fires on the opened init state.** With both candidates
fresh at index `0`, the initial epoch, a solvent budget and a nonempty singleton
message vector, all three challenge guards pass, so `challengeResp` reduces to
the candidate's real length-`1` batch `spendBatch (flatInstance budget) 0 ⟨0,none⟩ [m]`
(state-independent: both candidates share the `⟨0, none⟩` opened state). This is
the exact structural analogue of `challengeResp_bStatic_init`, adapted to the
flat instance whose spend is randomized. -/
private lemma flat_challengeResp_init_reduces (budget : ℕ) (hb : 1 ≤ budget) (m : F) (b : Bool) :
    challengeResp (flatInstance (F := F) budget)
        (GSt.init (flatInstance (F := F) budget) ⟨0, none⟩ ⟨0, none⟩) b [m]
      = spendBatch (flatInstance (F := F) budget) 0 (⟨0, none⟩ : FlatPSt F) [m] := by
  have hfresh : epochFresh (flatInstance (F := F) budget)
      (GSt.init (flatInstance (F := F) budget) ⟨0, none⟩ ⟨0, none⟩) = true := rfl
  have hcap : challengeCapable (flatInstance (F := F) budget)
      (GSt.init (flatInstance (F := F) budget) ⟨0, none⟩ ⟨0, none⟩) [m].length = true := by
    simp only [challengeCapable, GSt.init, ite_self, flatInstance_capableFor, List.length_cons,
      List.length_nil, Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hguard : (!([m].isEmpty) && epochFresh (flatInstance (F := F) budget)
      (GSt.init (flatInstance (F := F) budget) ⟨0, none⟩ ⟨0, none⟩) &&
      challengeCapable (flatInstance (F := F) budget)
        (GSt.init (flatInstance (F := F) budget) ⟨0, none⟩ ⟨0, none⟩) [m].length) = true := by
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, hfresh]
    exact hcap
  unfold challengeResp
  split
  · cases b <;> rfl
  · rename_i hc
    exact absurd hguard hc

/-- **Challenge-firing witness (k3-vacuity-review.md flag 1), concrete form.**
A real, non-`⊥` ticket batch of length `q = 1` is reachable in the flat
instance's challenge output on the satisfying init configuration: the challenge
genuinely fires and returns `some [⟨m, m, m, m⟩]` with positive probability. This
witnesses, by construction, that `T4_flat_unlinkability`'s advantage `0` couples
*real* batches rather than being an always-`⊥` artifact. Holds for either hidden
bit `b`. -/
lemma challengeResp_flat_fires (budget : ℕ) (hb : 1 ≤ budget) (m : F) (b : Bool) :
    some [(⟨m, m, m, m⟩ : (flatInstance (F := F) budget).View)] ∈
      support (challengeResp (flatInstance (F := F) budget)
        (GSt.init (flatInstance (F := F) budget) ⟨0, none⟩ ⟨0, none⟩) b [m]) := by
  rw [flat_challengeResp_init_reduces budget hb m b, spendBatch]
  refine (mem_support_bind_iff _ _ _).2
    ⟨some ((⟨m, m, m, m⟩ : FlatView F), (⟨0 + 1, some ⟨m, m, m, m⟩⟩ : FlatPSt F)), ?_, ?_⟩
  · -- the first (and only) spend of the batch fires with a concrete fresh ticket
    show some ((⟨m, m, m, m⟩ : FlatView F), (⟨0 + 1, some ⟨m, m, m, m⟩⟩ : FlatPSt F)) ∈
        support (flatSpend budget (⟨0, none⟩ : FlatPSt F) m)
    have hlt : (⟨0, none⟩ : FlatPSt F).idx < budget := by show (0 : ℕ) < budget; omega
    simp only [flatSpend, if_pos hlt]
    refine (mem_support_bind_iff _ _ _).2 ⟨m, mem_support_uniformSample F, ?_⟩
    refine (mem_support_bind_iff _ _ _).2 ⟨m, mem_support_uniformSample F, ?_⟩
    refine (mem_support_bind_iff _ _ _).2 ⟨m, mem_support_uniformSample F, ?_⟩
    simp
  · -- the tail of the batch is empty, so the assembled ticket list is `[⟨m,m,m,m⟩]`
    show some [(⟨m, m, m, m⟩ : FlatView F)] ∈
        support (Option.map ((⟨m, m, m, m⟩ : FlatView F) :: ·) <$>
          spendBatch (flatInstance (F := F) budget) 0 (⟨0 + 1, some ⟨m, m, m, m⟩⟩ : FlatPSt F) [])
    rw [spendBatch, support_map]
    exact ⟨some [], (mem_support_pure_iff _ _).mpr rfl, rfl⟩

/-- **Challenge-firing witness (k3-vacuity-review.md flag 1), strong form.** On
the satisfying init configuration the flat challenge **never** returns `⊥`:
`none` is not in the support, so every execution yields a genuine `some`-batch of
real tickets. Discharged from the already-proved O2 batch-totality obligation
`flat_spendBatch_none_zero`. Since a `ProbComp` support is always inhabited, this
refutes "the advantage `0` is an always-`⊥` artifact" outright. Holds for either
hidden bit `b`. -/
lemma challengeResp_flat_never_bot (budget : ℕ) (hb : 1 ≤ budget) (m : F) (b : Bool) :
    none ∉ support (challengeResp (flatInstance (F := F) budget)
      (GSt.init (flatInstance (F := F) budget) ⟨0, none⟩ ⟨0, none⟩) b [m]) := by
  rw [flat_challengeResp_init_reduces budget hb m b]
  exact (probOutput_eq_zero_iff _ _).1
    (flat_spendBatch_none_zero budget 0 [m] (⟨0, none⟩ : FlatPSt F)
      (by show (0 : ℕ) + 1 ≤ budget; omega))

end Zkpc.Games

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.challengeResp_flat_fires
#print axioms Zkpc.Games.challengeResp_flat_never_bot
