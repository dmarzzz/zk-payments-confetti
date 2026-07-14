import Zkpc.Games.BInstances

/-!
# The rev-11 calibration battery (task H3 + T4 battery; Spec.md §7 T4)

The paper's built-in definitional tests that the UNLINK game
(`Zkpc.Games.Unlink`) is neither too weak (a broken scheme must lose) nor
vacuously strong. Two families:

## The B-static / B-rerand calibration pair (deliverable 1, must-have)

* **B-static must-lose** — `staticDistinguisher` is a *constructive*
  `UnlinkAdversary` term with `unlinkAdvantage (bStatic …) staticDistinguisher
  = 1/2`, the information-theoretic maximum. It opens the two candidates with
  distinct certified-ciphertext handles (the adversary-payee issues them,
  M2), reads the challenge batch's presented handle, and matches it against
  its own issuance bookkeeping. A `q = 1` singleton session suffices.
* **B-rerand must-pass** — `unlinkAdvantage_bRerand_eq_zero` proves advantage
  exactly `0` for *every* adversary, by the same coupling technique the flat
  instance uses (`Zkpc.Games.challengeResp_bRerand_bitfree`).

## The must-catch battery (deliverable 2)

Three broken variants, each with a winning distinguisher at advantage `1/2`,
witnessing that the game catches the named leak:

* `aIndexLeak` + `indexLeakDistinguisher` — a variant whose ticket carries
  the spend index in the clear; the winner opens the candidates with unequal
  counts and reads the challenge index.
* `nfeReuse` + `nfeReuseDistinguisher` — a variant whose epoch pseudonym is
  reused across epochs (epoch-independent, identity-derived); the winner
  reads the challenge pseudonym and matches it to the known identity.
* `multTag` + `multTagDistinguisher` — a variant leaking a persistent
  per-secret tag **only on the second-and-later spend within an epoch
  session**; a `q = 2` session winner reads the challenge batch's second
  ticket's tag. This is the K4 construction that motivated the session form:
  a `q = 1` challenge never sees the second ticket, so it would miss the tag.

## GATE-NOTE register (encoding deltas, all deliberate)

* **GATE-NOTE (must-lose route).** `staticDistinguisher` runs its whole
  strategy through the genesis/opening handles rather than a pre-challenge
  `serve` transcript: it opens `P₀, P₁` with distinct handles `h₀ ≠ h₁` and
  the B-static spend echoes the held handle bit-identically, so the challenge
  ticket *is* the opening handle. This is exactly Spec.md §4's genesis-anchor
  break (rev-2 NEW-4: "B-static presents `ct₀` bit-identically at the first
  spend — direct first-spend-to-identity linkage … the T4 calibration
  distinguisher may use it"). It is equivalent in effect to the
  serve-transcript route (equal totals, distinct randomness) but needs no
  oracle-transcript evaluation, so `phase1` is a pure return; the adversary's
  guess is a pure function of the challenge response, as the game's
  `ChalAdversary` type already forces post-challenge. Advantage is still
  exactly `1/2`.
* **GATE-NOTE (battery routes).** Likewise every battery winner encodes the
  distinguishing asymmetry at open (unequal genesis counts / identity-derived
  leaked components) rather than by pre-challenge `Ospend`/`tick` harvesting,
  and reads the leak off the challenge response with a pure guess. Since the
  adversary controls the candidates' identities/genesis, any identity-derived
  persistent leak is known to it, and any count asymmetry is set at open;
  each winner still exercises the *challenge* surface (the leak surfaces in
  the challenge batch) and proves advantage exactly `1/2`. The `q = 1`-safety
  direction of `multTag` (that only the session form catches it) is argued in
  prose, not formalized; only the `q = 2` winner is a constructive term, as
  the battery requires.
* **GATE-NOTE (identity-derived leaks).** `nfeReuse` and `multTag` model the
  leaked component as the payer's opening handle (a stand-in for the persistent
  secret-derived value `H_e(k)` / `H_tag(k)`), epoch-independent. Modeling it
  as freshly sampled but stored-and-reused would force the winner to harvest
  it via a pre-challenge spend; the identity-derived form is a faithful
  instance of "reused / persistent" and is directly adversary-known, which is
  what lets the winner run with a pure `phase1`.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable (H : Type) [SampleableType H]

/-! ## B-rerand must-pass (deliverable 1c) -/

/-- **T4-B, B-rerand (Spec.md §7 T4, patched variant): advantage `0`.**
For every deposit/cap and every UNLINK adversary, the re-randomized
presentation has spend-unlinkability advantage `|Pr[b' = b] − 1/2|` equal to
exactly `0`. Discharged by the challenge-response coupling
`challengeResp_bRerand_bitfree` (both candidates emit the state-independent
ideal batch `bFreshBatch`) fed to the must-pass closer
`unlinkAdvantage_eq_zero_of_challenge_bitfree`. Assumption-5 (re-randomization
independence) is discharged in ideal form by the fresh-handle spend. -/
theorem unlinkAdvantage_bRerand_eq_zero (Cmax D : ℕ)
    (A : UnlinkAdversary (bRerand H Cmax D)) :
    unlinkAdvantage (bRerand H Cmax D) A = 0 :=
  unlinkAdvantage_eq_zero_of_challenge_bitfree (bRerand H Cmax D) A
    (fun g ms b b' => challengeResp_bRerand_bitfree H Cmax D g ms b b')

/-! ## B-static must-lose (deliverable 1b) -/

/-- Clean unfolding of the B-static spend on a solvent state: it echoes the
held certified handle bit-identically (the broken presentation). -/
lemma bStatic_spend_eq (Cmax D e : ℕ) (st : BPSt H) (m : PUnit)
    (h : (st.idx + 1) * Cmax ≤ D + st.R) :
    (bStatic H Cmax D).spend e st m =
      pure (some (st.ct, { st with idx := st.idx + 1, last := some st.ct })) := by
  show (bIdeal H Cmax D false).spend e st m = _
  simp only [bIdeal, if_pos h]
  rfl

@[simp] lemma bStatic_openCh (Cmax D : ℕ) (g : H) :
    (bStatic H Cmax D).openCh g = pure (⟨g, 0, 0, none⟩, PUnit.unit) := rfl

@[simp] lemma bStatic_capableFor (Cmax D q : ℕ) (st : BPSt H) :
    (bStatic H Cmax D).capableFor q st = decide ((st.idx + q) * Cmax ≤ D + st.R) := rfl

/-- The constructive B-static distinguisher (Spec.md §7 T4 calibration
requirement). It opens `P₀, P₁` with distinct certified-ciphertext handles
`h₀ ≠ h₁`, issues a `q = 1` singleton challenge, and matches the challenge
ticket's presented handle against `h₁` — since B-static echoes the held
handle bit-identically, that handle *is* `h_b`, so the match recovers `b`. -/
def staticDistinguisher [DecidableEq H] (Cmax D : ℕ) (h0 h1 : H) :
    UnlinkAdversary (bStatic H Cmax D) where
  Aux0 := PUnit
  phase0 := pure ((h0, h1), PUnit.unit)
  main :=
    { Aux := PUnit
      phase1 := fun _ => pure ([PUnit.unit], PUnit.unit)
      guess := fun _ (resp : Option (List H)) =>
        match resp with
        | some (v :: _) => decide (v = h1)
        | _ => false }

/-- The B-static challenge response on the opened init state is the singleton
batch echoing the challenged candidate's held handle (`h_b`). The guard passes
(nonempty vector; both candidates fresh and solvent for one spend). -/
lemma challengeResp_bStatic_init (Cmax D : ℕ) (h0 h1 : H) (b : Bool)
    (hCmax : Cmax ≤ D) :
    challengeResp (bStatic H Cmax D)
        (GSt.init (bStatic H Cmax D) ⟨h0, 0, 0, none⟩ ⟨h1, 0, 0, none⟩) b [PUnit.unit]
      = pure (some [if b then h1 else h0]) := by
  have hs : ((⟨h0, 0, 0, none⟩ : BPSt H).idx + 1) * Cmax
      ≤ D + (⟨h0, 0, 0, none⟩ : BPSt H).R := by simpa using hCmax
  have ht : ((⟨h1, 0, 0, none⟩ : BPSt H).idx + 1) * Cmax
      ≤ D + (⟨h1, 0, 0, none⟩ : BPSt H).R := by simpa using hCmax
  have hfresh : epochFresh (bStatic H Cmax D)
      (GSt.init (bStatic H Cmax D) ⟨h0, 0, 0, none⟩ ⟨h1, 0, 0, none⟩) = true := rfl
  have hcap : challengeCapable (bStatic H Cmax D)
      (GSt.init (bStatic H Cmax D) ⟨h0, 0, 0, none⟩ ⟨h1, 0, 0, none⟩)
      [PUnit.unit].length = true := by
    unfold challengeCapable
    simp only [GSt.init, bStatic_capableFor, List.length_cons,
      List.length_nil, Nat.zero_add, Bool.not_false, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨hs, ht⟩
  have hguard : (!([PUnit.unit].isEmpty) &&
      epochFresh (bStatic H Cmax D)
        (GSt.init (bStatic H Cmax D) ⟨h0, 0, 0, none⟩ ⟨h1, 0, 0, none⟩) &&
      challengeCapable (bStatic H Cmax D)
        (GSt.init (bStatic H Cmax D) ⟨h0, 0, 0, none⟩ ⟨h1, 0, 0, none⟩)
        [PUnit.unit].length) = true := by
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, hfresh]
    exact hcap
  unfold challengeResp
  split
  · cases b
    · show spendBatch (bStatic H Cmax D) 0 (⟨h0, 0, 0, none⟩ : BPSt H) [PUnit.unit]
        = pure (some [h0])
      rw [spendBatch, bStatic_spend_eq H Cmax D 0 ⟨h0, 0, 0, none⟩ PUnit.unit hs]; rfl
    · show spendBatch (bStatic H Cmax D) 0 (⟨h1, 0, 0, none⟩ : BPSt H) [PUnit.unit]
        = pure (some [h1])
      rw [spendBatch, bStatic_spend_eq H Cmax D 0 ⟨h1, 0, 0, none⟩ PUnit.unit ht]; rfl
  · rename_i hc
    exact absurd hguard hc

/-- **The B-static run recovers the bit deterministically.** For distinct
handles and a channel solvent for one spend, `unlinkRun` on the B-static
distinguisher outputs exactly the hidden bit `b`. -/
theorem staticDistinguisher_run [DecidableEq H] (Cmax D : ℕ) (h0 h1 : H)
    (h01 : h0 ≠ h1) (hCmax : Cmax ≤ D) (b : Bool) :
    unlinkRun (bStatic H Cmax D) (staticDistinguisher H Cmax D h0 h1) b
      = pure b := by
  -- the all-pure prefix reduces definitionally to the challenge move
  show (challengeResp (bStatic H Cmax D)
        (GSt.init (bStatic H Cmax D) ⟨h0, 0, 0, none⟩ ⟨h1, 0, 0, none⟩) b [PUnit.unit] >>=
        fun resp => pure ((staticDistinguisher H Cmax D h0 h1).main.guess PUnit.unit resp))
      = pure b
  rw [challengeResp_bStatic_init H Cmax D h0 h1 b hCmax]
  show (pure ((staticDistinguisher H Cmax D h0 h1).main.guess PUnit.unit
      (some [if b then h1 else h0])) : ProbComp Bool) = pure b
  congr 1
  cases b <;> simp [staticDistinguisher, h01]

/-- **B-static must-lose (Spec.md §7 T4 calibration requirement).** The
constructive distinguisher achieves UNLINK advantage exactly `1/2` — the
information-theoretic maximum — against the broken bit-identical variant.
Fed to the must-lose closer `unlinkAdvantage_eq_half_of_run_determined`. -/
theorem unlinkAdvantage_staticDistinguisher_eq_half [DecidableEq H]
    (Cmax D : ℕ) (h0 h1 : H) (h01 : h0 ≠ h1) (hCmax : Cmax ≤ D) :
    unlinkAdvantage (bStatic H Cmax D) (staticDistinguisher H Cmax D h0 h1) = 1 / 2 := by
  apply unlinkAdvantage_eq_half_of_run_determined
  · rw [staticDistinguisher_run H Cmax D h0 h1 h01 hCmax true]; simp
  · rw [staticDistinguisher_run H Cmax D h0 h1 h01 hCmax false]; simp

/-! ## The must-catch battery (deliverable 2)

A generic *transparent-leak* scheme `leakScheme` captures the two `q = 1`
must-catch variants: each spend's `View` exposes a value `emit e st`
computed from the payer's state, and the winner reads it off the challenge
ticket and matches it to the adversary-known value of candidate `P₁`.

* **A-index-leak** (`aIndexLeak`): `emit = st.idx` — the spend index in the
  clear. The winner opens the candidates with **unequal counts** (distinct
  genesis indices) so the challenge indices differ.
* **`nf_e`-reuse** (`nfeReuse`): `emit = st.val` — an epoch-independent,
  identity-derived pseudonym. The winner reads it and matches the identity.

The `multTag` variant (a persistent tag leaked only on the second-and-later
spend of an epoch session) is `q = 2` and lives below. -/

/-- Payer state of the transparent-leak scheme: a carried leaked value `val`
(the identity-derived component) and the spend index. -/
structure LeakPSt (V : Type) where
  /-- carried identity/leaked value -/
  val : V
  /-- next spend index -/
  idx : ℕ

/-- The generic transparent-leak `UnlinkScheme`: each spend at epoch `e`
emits `emit e st` as its `View`, advancing the index; `budget` is the static
solvency cap. The adversary sets the initial state at open (`GenesisInput =
LeakPSt V`), so unequal counts / identity-derived leaked values are set at
open. -/
def leakScheme {V : Type} (budget : ℕ) (emit : ℕ → LeakPSt V → V) : UnlinkScheme where
  M := PUnit
  View := V
  CloseView := ℕ
  OpenView := PUnit
  GenesisInput := LeakPSt V
  Receipt := PUnit
  PSt := LeakPSt V
  openCh g := pure (g, PUnit.unit)
  spend e st _m :=
    if st.idx < budget then
      pure (some (emit e st, { st with idx := st.idx + 1 }))
    else
      pure none
  lastTicket _ := none
  serve st _ρ := st
  close _e st := pure (st.idx, st)
  capableFor q st := decide (st.idx + q ≤ budget)

variable {V : Type}

@[simp] lemma leakScheme_openCh (budget : ℕ) (emit : ℕ → LeakPSt V → V) (g : LeakPSt V) :
    (leakScheme budget emit).openCh g = pure (g, PUnit.unit) := rfl

@[simp] lemma leakScheme_capableFor (budget q : ℕ) (emit : ℕ → LeakPSt V → V) (st : LeakPSt V) :
    (leakScheme budget emit).capableFor q st = decide (st.idx + q ≤ budget) := rfl

lemma leak_spend_eq (budget e : ℕ) (emit : ℕ → LeakPSt V → V) (st : LeakPSt V) (m : PUnit)
    (h : st.idx < budget) :
    (leakScheme budget emit).spend e st m =
      pure (some (emit e st, { st with idx := st.idx + 1 })) := by
  show (leakScheme budget emit).spend e st m = _
  simp only [leakScheme, if_pos h]

/-- The transparent-leak challenge response on the opened init state is the
singleton batch exposing the challenged candidate's leaked value
`emit 0 (P_b's genesis)`. -/
lemma challengeResp_leak_init (budget : ℕ) (emit : ℕ → LeakPSt V → V)
    (g0 g1 : LeakPSt V) (b : Bool)
    (h0 : g0.idx + 1 ≤ budget) (h1 : g1.idx + 1 ≤ budget) :
    challengeResp (leakScheme budget emit)
        (GSt.init (leakScheme budget emit) g0 g1) b [PUnit.unit]
      = pure (some [emit 0 (if b then g1 else g0)]) := by
  have hfresh : epochFresh (leakScheme budget emit)
      (GSt.init (leakScheme budget emit) g0 g1) = true := rfl
  have hcap : challengeCapable (leakScheme budget emit)
      (GSt.init (leakScheme budget emit) g0 g1) [PUnit.unit].length = true := by
    unfold challengeCapable
    simp only [GSt.init, leakScheme_capableFor, List.length_cons, List.length_nil,
      Nat.zero_add, Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h0, h1⟩
  have hguard : (!([PUnit.unit].isEmpty) &&
      epochFresh (leakScheme budget emit) (GSt.init (leakScheme budget emit) g0 g1) &&
      challengeCapable (leakScheme budget emit) (GSt.init (leakScheme budget emit) g0 g1)
        [PUnit.unit].length) = true := by
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, hfresh]
    exact hcap
  unfold challengeResp
  split
  · cases b
    · show spendBatch (leakScheme budget emit) 0 g0 [PUnit.unit] = pure (some [emit 0 g0])
      rw [spendBatch, leak_spend_eq budget 0 emit g0 PUnit.unit (by omega)]; rfl
    · show spendBatch (leakScheme budget emit) 0 g1 [PUnit.unit] = pure (some [emit 0 g1])
      rw [spendBatch, leak_spend_eq budget 0 emit g1 PUnit.unit (by omega)]; rfl
  · rename_i hc
    exact absurd hguard hc

/-- The generic transparent-leak distinguisher: opens `P₀, P₁` with genesis
states `g0, g1`, issues a `q = 1` challenge, and matches the challenge
ticket's exposed value against candidate `P₁`'s known value `emit 0 g1`. -/
def leakDistinguisher [DecidableEq V] (budget : ℕ) (emit : ℕ → LeakPSt V → V)
    (g0 g1 : LeakPSt V) : UnlinkAdversary (leakScheme budget emit) where
  Aux0 := PUnit
  phase0 := pure ((g0, g1), PUnit.unit)
  main :=
    { Aux := PUnit
      phase1 := fun _ => pure ([PUnit.unit], PUnit.unit)
      guess := fun _ (resp : Option (List V)) =>
        match resp with
        | some (v :: _) => decide (v = emit 0 g1)
        | _ => false }

/-- **The generic transparent-leak run recovers the bit.** If the two
candidates' exposed values differ (`emit 0 g0 ≠ emit 0 g1`) and both are
solvent for one spend, `unlinkRun` outputs the hidden bit. -/
theorem leakDistinguisher_run [DecidableEq V] (budget : ℕ) (emit : ℕ → LeakPSt V → V)
    (g0 g1 : LeakPSt V) (hne : emit 0 g0 ≠ emit 0 g1)
    (h0 : g0.idx + 1 ≤ budget) (h1 : g1.idx + 1 ≤ budget) (b : Bool) :
    unlinkRun (leakScheme budget emit) (leakDistinguisher budget emit g0 g1) b = pure b := by
  show (challengeResp (leakScheme budget emit)
        (GSt.init (leakScheme budget emit) g0 g1) b [PUnit.unit] >>=
        fun resp => pure ((leakDistinguisher budget emit g0 g1).main.guess PUnit.unit resp))
      = pure b
  rw [challengeResp_leak_init budget emit g0 g1 b h0 h1]
  show (pure ((leakDistinguisher budget emit g0 g1).main.guess PUnit.unit
      (some [emit 0 (if b then g1 else g0)])) : ProbComp Bool) = pure b
  congr 1
  cases b <;> simp [leakDistinguisher, hne]

/-- **Generic transparent-leak must-catch: advantage `1/2`.** -/
theorem unlinkAdvantage_leakDistinguisher_eq_half [DecidableEq V] (budget : ℕ)
    (emit : ℕ → LeakPSt V → V) (g0 g1 : LeakPSt V) (hne : emit 0 g0 ≠ emit 0 g1)
    (h0 : g0.idx + 1 ≤ budget) (h1 : g1.idx + 1 ≤ budget) :
    unlinkAdvantage (leakScheme budget emit) (leakDistinguisher budget emit g0 g1) = 1 / 2 := by
  apply unlinkAdvantage_eq_half_of_run_determined
  · rw [leakDistinguisher_run budget emit g0 g1 hne h0 h1 true]; simp
  · rw [leakDistinguisher_run budget emit g0 g1 hne h0 h1 false]; simp

/-! ### A-index-leak variant -/

/-- **A-index-leak variant** (Spec.md §7 T4 battery): the ticket carries the
spend index in the clear. -/
def aIndexLeak (budget : ℕ) : UnlinkScheme := leakScheme budget (fun _ st => st.idx)

/-- **A-index-leak must-catch.** Opening the candidates with unequal counts
(`P₀` at index `0`, `P₁` at index `1`) makes the challenge indices differ, so
the winner reads the challenge index and recovers the bit with advantage
`1/2`. Requires `budget ≥ 2` (both solvent for one more spend). -/
theorem unlinkAdvantage_aIndexLeak (budget : ℕ) (hb : 2 ≤ budget) :
    unlinkAdvantage (aIndexLeak budget)
      (leakDistinguisher budget (fun _ (st : LeakPSt ℕ) => st.idx) ⟨0, 0⟩ ⟨0, 1⟩) = 1 / 2 := by
  refine unlinkAdvantage_leakDistinguisher_eq_half budget (fun _ (st : LeakPSt ℕ) => st.idx)
    ⟨0, 0⟩ ⟨0, 1⟩ (by decide) ?_ ?_
  · show (0 : ℕ) + 1 ≤ budget; omega
  · show (1 : ℕ) + 1 ≤ budget; omega

/-! ### `nf_e`-reuse variant -/

/-- **`nf_e`-reuse variant** (Spec.md §7 T4 battery): the epoch pseudonym is
epoch-independent and identity-derived (`emit e st = st.val`), i.e. reused
across every epoch. -/
def nfeReuse (H : Type) (budget : ℕ) : UnlinkScheme :=
  leakScheme budget (fun _ (st : LeakPSt H) => st.val)

omit [SampleableType H] in
/-- **`nf_e`-reuse must-catch.** The pseudonym is the payer's identity handle,
constant across epochs; the winner opens the candidates with distinct handles
`h₀ ≠ h₁`, reads the challenge pseudonym, and matches — advantage `1/2`.
Because the pseudonym is epoch-independent, no earlier-epoch harvest is
needed (the challenge value equals the known genesis value). -/
theorem unlinkAdvantage_nfeReuse [DecidableEq H] (budget : ℕ) (hb : 1 ≤ budget)
    (h0 h1 : H) (h01 : h0 ≠ h1) :
    unlinkAdvantage (nfeReuse H budget)
      (leakDistinguisher budget (fun _ (st : LeakPSt H) => st.val) ⟨h0, 0⟩ ⟨h1, 0⟩) = 1 / 2 := by
  refine unlinkAdvantage_leakDistinguisher_eq_half budget (fun _ (st : LeakPSt H) => st.val)
    ⟨h0, 0⟩ ⟨h1, 0⟩ h01 ?_ ?_
  · show (0 : ℕ) + 1 ≤ budget; omega
  · show (0 : ℕ) + 1 ≤ budget; omega

/-! ### Multiplicity-tag variant (q = 2, the session-form witness)

`multTag` leaks a persistent per-secret tag (the identity handle) **only on
the second-and-later spend within an epoch session**: the first spend of an
epoch carries `none`, the second carries `some val`. A `q = 1` challenge sees
only the first ticket (tag `none`) and cannot distinguish; a `q = 2` session
challenge surfaces the tag in the second ticket, and the winner matches it.
This is the K4 construction that motivated the session form (Spec.md §7 T4,
rev-9): the `q = 2` winner below is the constructive witness that the session
challenge closes Concern 1. -/

/-- Payer state of the multiplicity-tag variant: identity `val`, spend index,
the last epoch spent in, and the per-epoch spend count. -/
structure MultPSt (H : Type) where
  /-- identity-derived tag value -/
  val : H
  /-- next spend index -/
  idx : ℕ
  /-- the epoch of the most recent spend (`none` = none yet) -/
  lastEpoch : Option ℕ
  /-- number of spends already made in `lastEpoch` -/
  epochCnt : ℕ

/-- One multiplicity-tag spend at epoch `e`: compute the ordinal of this spend
within the epoch session; emit the tag iff it is the second-or-later
(`2 ≤ newCnt`). -/
def multTagSpend {H : Type} (e : ℕ) (st : MultPSt H) : Option H × MultPSt H :=
  let newCnt := if st.lastEpoch = some e then st.epochCnt + 1 else 1
  (if 2 ≤ newCnt then some st.val else none,
    { st with idx := st.idx + 1, lastEpoch := some e, epochCnt := newCnt })

/-- **Multiplicity-tag variant** (Spec.md §7 T4 battery, rev-10 F9-m2): a
persistent per-secret tag leaked only on the second-and-later spend within an
epoch session. `View = Option H`. -/
def multTag (H : Type) (budget : ℕ) : UnlinkScheme where
  M := PUnit
  View := Option H
  CloseView := ℕ
  OpenView := PUnit
  GenesisInput := MultPSt H
  Receipt := PUnit
  PSt := MultPSt H
  openCh g := pure (g, PUnit.unit)
  spend e st _m :=
    if st.idx < budget then pure (some (multTagSpend e st)) else pure none
  lastTicket _ := none
  serve st _ρ := st
  close _e st := pure (st.idx, st)
  capableFor q st := decide (st.idx + q ≤ budget)

@[simp] lemma multTag_openCh (H : Type) (budget : ℕ) (g : MultPSt H) :
    (multTag H budget).openCh g = pure (g, PUnit.unit) := rfl

@[simp] lemma multTag_capableFor (H : Type) (budget q : ℕ) (st : MultPSt H) :
    (multTag H budget).capableFor q st = decide (st.idx + q ≤ budget) := rfl

lemma multTag_spend_eq (H : Type) (budget e : ℕ) (st : MultPSt H) (m : PUnit)
    (h : st.idx < budget) :
    (multTag H budget).spend e st m = pure (some (multTagSpend e st)) := by
  show (multTag H budget).spend e st m = _
  simp only [multTag, if_pos h]

/-- The `q = 2` challenge response on the opened init states: the batch
`[none, some (P_b's tag)]` — the first ticket carries no tag, the second
carries the identity tag (the second spend of the epoch session). -/
lemma challengeResp_multTag_init (H : Type) (budget : ℕ) (h0 h1 : H) (b : Bool)
    (hb : 2 ≤ budget) :
    challengeResp (multTag H budget)
        (GSt.init (multTag H budget) ⟨h0, 0, none, 0⟩ ⟨h1, 0, none, 0⟩) b
        [PUnit.unit, PUnit.unit]
      = pure (some [none, some (if b then h1 else h0)]) := by
  have hcap : challengeCapable (multTag H budget)
      (GSt.init (multTag H budget) ⟨h0, 0, none, 0⟩ ⟨h1, 0, none, 0⟩)
      [PUnit.unit, PUnit.unit].length = true := by
    unfold challengeCapable
    simp only [GSt.init, multTag_capableFor, List.length_cons, List.length_nil,
      Nat.zero_add, Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by show (0 : ℕ) + 2 ≤ budget; omega, by show (0 : ℕ) + 2 ≤ budget; omega⟩
  have hfresh : epochFresh (multTag H budget)
      (GSt.init (multTag H budget) ⟨h0, 0, none, 0⟩ ⟨h1, 0, none, 0⟩) = true := rfl
  have hguard : (!([PUnit.unit, PUnit.unit].isEmpty) &&
      epochFresh (multTag H budget)
        (GSt.init (multTag H budget) ⟨h0, 0, none, 0⟩ ⟨h1, 0, none, 0⟩) &&
      challengeCapable (multTag H budget)
        (GSt.init (multTag H budget) ⟨h0, 0, none, 0⟩ ⟨h1, 0, none, 0⟩)
        [PUnit.unit, PUnit.unit].length) = true := by
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, hfresh]
    exact hcap
  have hlt0 : (0 : ℕ) < budget := by omega
  have hlt1 : (1 : ℕ) < budget := by omega
  unfold challengeResp
  split
  · cases b
    · have h1s : (multTag H budget).spend 0 (⟨h0, 0, none, 0⟩ : MultPSt H) PUnit.unit
          = pure (some (none, ⟨h0, 1, some 0, 1⟩)) := by
        rw [multTag_spend_eq H budget 0 ⟨h0, 0, none, 0⟩ PUnit.unit hlt0]; rfl
      have h2s : (multTag H budget).spend 0 (⟨h0, 1, some 0, 1⟩ : MultPSt H) PUnit.unit
          = pure (some (some h0, ⟨h0, 2, some 0, 2⟩)) := by
        rw [multTag_spend_eq H budget 0 ⟨h0, 1, some 0, 1⟩ PUnit.unit hlt1]; rfl
      show spendBatch (multTag H budget) 0 (⟨h0, 0, none, 0⟩ : MultPSt H)
          [PUnit.unit, PUnit.unit] = pure (some [none, some h0])
      rw [spendBatch, h1s]
      show Option.map (none :: ·) <$>
          spendBatch (multTag H budget) 0 (⟨h0, 1, some 0, 1⟩ : MultPSt H) [PUnit.unit]
        = pure (some [none, some h0])
      rw [spendBatch, h2s]; rfl
    · have h1s : (multTag H budget).spend 0 (⟨h1, 0, none, 0⟩ : MultPSt H) PUnit.unit
          = pure (some (none, ⟨h1, 1, some 0, 1⟩)) := by
        rw [multTag_spend_eq H budget 0 ⟨h1, 0, none, 0⟩ PUnit.unit hlt0]; rfl
      have h2s : (multTag H budget).spend 0 (⟨h1, 1, some 0, 1⟩ : MultPSt H) PUnit.unit
          = pure (some (some h1, ⟨h1, 2, some 0, 2⟩)) := by
        rw [multTag_spend_eq H budget 0 ⟨h1, 1, some 0, 1⟩ PUnit.unit hlt1]; rfl
      show spendBatch (multTag H budget) 0 (⟨h1, 0, none, 0⟩ : MultPSt H)
          [PUnit.unit, PUnit.unit] = pure (some [none, some h1])
      rw [spendBatch, h1s]
      show Option.map (none :: ·) <$>
          spendBatch (multTag H budget) 0 (⟨h1, 1, some 0, 1⟩ : MultPSt H) [PUnit.unit]
        = pure (some [none, some h1])
      rw [spendBatch, h2s]; rfl
  · rename_i hc
    exact absurd hguard hc

/-- The `q = 2` multiplicity-tag distinguisher: reads the **second** ticket's
tag and matches it against `P₁`'s known identity `h₁`. -/
def multTagDistinguisher [DecidableEq H] (budget : ℕ) (h0 h1 : H) :
    UnlinkAdversary (multTag H budget) where
  Aux0 := PUnit
  phase0 := pure ((⟨h0, 0, none, 0⟩, ⟨h1, 0, none, 0⟩), PUnit.unit)
  main :=
    { Aux := PUnit
      phase1 := fun _ => pure ([PUnit.unit, PUnit.unit], PUnit.unit)
      guess := fun _ (resp : Option (List (Option H))) =>
        match resp with
        | some (_ :: some v :: _) => decide (v = h1)
        | _ => false }

omit [SampleableType H] in
/-- **The multiplicity-tag `q = 2` run recovers the bit.** -/
theorem multTagDistinguisher_run [DecidableEq H] (budget : ℕ) (h0 h1 : H)
    (h01 : h0 ≠ h1) (hb : 2 ≤ budget) (b : Bool) :
    unlinkRun (multTag H budget) (multTagDistinguisher H budget h0 h1) b = pure b := by
  show (challengeResp (multTag H budget)
        (GSt.init (multTag H budget) ⟨h0, 0, none, 0⟩ ⟨h1, 0, none, 0⟩) b
        [PUnit.unit, PUnit.unit] >>=
        fun resp => pure ((multTagDistinguisher H budget h0 h1).main.guess PUnit.unit resp))
      = pure b
  rw [challengeResp_multTag_init H budget h0 h1 b hb]
  show (pure ((multTagDistinguisher H budget h0 h1).main.guess PUnit.unit
      (some [none, some (if b then h1 else h0)])) : ProbComp Bool) = pure b
  congr 1
  cases b <;> simp [multTagDistinguisher, h01]

omit [SampleableType H] in
/-- **Multiplicity-tag must-catch (`q = 2` session winner, advantage `1/2`).**
The constructive witness that the session form catches a tag leaked only on
the second-and-later spend of an epoch (Spec.md §7 T4 rev-9/K4 Concern 1). -/
theorem unlinkAdvantage_multTagDistinguisher_eq_half [DecidableEq H]
    (budget : ℕ) (h0 h1 : H) (h01 : h0 ≠ h1) (hb : 2 ≤ budget) :
    unlinkAdvantage (multTag H budget) (multTagDistinguisher H budget h0 h1) = 1 / 2 := by
  apply unlinkAdvantage_eq_half_of_run_determined
  · rw [multTagDistinguisher_run H budget h0 h1 h01 hb true]; simp
  · rw [multTagDistinguisher_run H budget h0 h1 h01 hb false]; simp

end Zkpc.Games

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.unlinkAdvantage_bRerand_eq_zero
#print axioms Zkpc.Games.unlinkAdvantage_staticDistinguisher_eq_half
#print axioms Zkpc.Games.unlinkAdvantage_aIndexLeak
#print axioms Zkpc.Games.unlinkAdvantage_nfeReuse
#print axioms Zkpc.Games.unlinkAdvantage_multTagDistinguisher_eq_half
