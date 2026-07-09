import Zkpc.Games.Coupling

/-!
# The B-static / B-rerand calibration pair (task H3; Spec.md §4, §7 T4)

Ideal-model `UnlinkScheme` instances for the two refund-total
representations of instantiation B (Spec.md §4, MC7):

* **B-static** (`bStatic`): the payer presents, at each spend, the
  certified ciphertext **bit-identical** to the one the payee last signed.
  Ideal form: ciphertexts are opaque handles of type `H`; the
  adversary-payee *issues* handles (genesis via `GenesisInput = H`, M2;
  per-accept receipts via `Receipt = H × ℕ` through `serve`), the payer
  stores the latest signed handle in its state (`BPSt.ct`) and every spend
  view echoes it. This is Spec.md's broken original design; the
  calibration requirement makes `staticDistinguisher`
  (`Zkpc.Games.Calibration`) win against it.
* **B-rerand** (`bRerand`): the payer re-randomizes, presenting
  `ct* = Rerand(ct; r*)`. Ideal form of assumption 5 (re-randomization
  produces ciphertexts distributed independently of the input): the
  presented component is a **fresh uniform handle per spend**, sampled
  from `H`. T4 must pass: `unlinkAdvantage_bRerand_eq_zero`
  (`Zkpc.Games.Calibration`) proves advantage exactly `0` for **all**
  adversaries, via the coupling technique of `Zkpc.Games.Coupling` — the
  same OTP/HeapBasic per-query coupling the flat instance uses.

Both instances share one skeleton (`bIdeal`), differing **only** in the
presented-ciphertext component of `View` — the load-bearing difference of
Spec.md §4. Solvency is B's real inequality `(i+1)·C_max ≤ D + R`
(Spec.md §4), with `R` grown by adversary-issued receipts through `serve`
— so the eviction-to-insolvency abort lever has its teeth (T4
anti-vacuity (iii)): a candidate starved of receipts can fail
`capableFor` and shrink the capable set.

## GATE-NOTE register (encoding deltas, all deliberate)

* **GATE-NOTE (view components).** `View := H` — the pair's ticket view is
  *exactly* MC7's presented-ciphertext component. The signal `(x, y, nf)`,
  the epoch pseudonym `nf_e`, `π`, `root`, `e` are all dropped: their
  ideal forms are fresh-uniform / candidate-i.i.d. values carrying no
  bit-dependence, so (must-lose) dropping them only weakens the
  distinguisher, which still wins, and (must-pass) their re-inclusion is
  exactly the F-phase full-ticket T4-B obligation (M1
  `zkBridgeObligation`, and the game-state/scheme-state freshness
  invariant for `nf_e`), recorded here as the pair's gate entry. The pair
  therefore isolates the single definitional question Spec.md §4 poses:
  does the game separate echoed from re-randomized presentation? The
  battery's `nfeReuse` variant (`Zkpc.Games.Calibration`) covers the
  pseudonym component's own calibration content separately.
* **GATE-NOTE (contiguity).** `BPSt.idx` plays both the spend index and
  the certified count `n` (B spends are contiguous by construction,
  MC20/rev-6): the ideal chain needs no separate `n`.
* **GATE-NOTE (O3, receipts).** `serve` accepts every `(H × ℕ)` receipt:
  the adversary-payee *is* the signing oracle in this game, so "invalid
  signature" does not exist at this abstraction — O3's
  absorb-invalid-receipts obligation is discharged vacuously. Malformed
  genesis likewise: any `H` handle is a well-formed genesis ciphertext.
* **GATE-NOTE (O4, close).** `CloseView := ℕ`, the certified count `j`
  (`= idx`). `cm` is the public open identity (constant per candidate) and
  the revealed `nf_j` is a PRF-fresh value determined in distribution by
  the count — MC15's own argument — so the ideal close view is the count.
  `bIdeal_closeViewSimulatable` discharges O4 for both instances.
* **GATE-NOTE (M1).** These are calibration instances of the battery, not
  the F-phase real variants; they are proof-free *by construction* (the
  ideal model has no `π`), so `zkBridgeObligation` is out of scope here
  and owed by the F-phase full-ticket instances.
* **GATE-NOTE (messages).** `M := PUnit`: the ideal instances ignore
  message content (gateway binding is A-side machinery; B has `N = 1`).
  Dropping it loses no adversary power in this pair — views do not depend
  on `m`.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

/-- Payer state of the ideal-model B instances: the latest payee-signed
certified ciphertext handle (`ct`), the next spend index (= certified
count, contiguity by construction), the certified refund total `R`, and
the MC2 retry buffer. -/
structure BPSt (H : Type) : Type where
  /-- latest payee-signed certified ciphertext handle held by the payer -/
  ct : H
  /-- next spend index = certified count `n` (contiguous by construction) -/
  idx : ℕ
  /-- certified refund total `R` -/
  R : ℕ
  /-- MC2 retry buffer: the last emitted ticket view -/
  last : Option H

variable (H : Type) [SampleableType H]

/-- The shared ideal-model B skeleton. `rerand = false` is **B-static**
(spend echoes the held certified handle bit-identically), `rerand = true`
is **B-rerand** (spend presents a fresh uniform handle — assumption 5's
ideal form). This is the *only* difference between the two instances. -/
def bIdeal (Cmax D : ℕ) (rerand : Bool) : UnlinkScheme where
  M := PUnit
  View := H
  CloseView := ℕ
  OpenView := PUnit
  GenesisInput := H
  Receipt := H × ℕ
  PSt := BPSt H
  openCh g := pure (⟨g, 0, 0, none⟩, PUnit.unit)
  spend _e st _m :=
    if (st.idx + 1) * Cmax ≤ D + st.R then
      if rerand then do
        let h ← ($ᵗ H)
        pure (some (h, { st with idx := st.idx + 1, last := some h }))
      else
        pure (some (st.ct, { st with idx := st.idx + 1, last := some st.ct }))
    else
      pure none
  lastTicket st := st.last
  serve st ρ := { st with ct := ρ.1, R := st.R + ρ.2 }
  close _e st := pure (st.idx, st)
  capableFor q st := decide ((st.idx + q) * Cmax ≤ D + st.R)

/-- **B-static** (Spec.md §4): the broken bit-identical-presentation
variant. The T4 calibration requirement demands a winning distinguisher
against it — `Zkpc.Games.unlinkAdvantage_staticDistinguisher_eq_half`. -/
def bStatic (Cmax D : ℕ) : UnlinkScheme := bIdeal H Cmax D false

/-- **B-rerand** (Spec.md §4): the patched re-randomized-presentation
variant, ideal form. `Zkpc.Games.unlinkAdvantage_bRerand_eq_zero` proves T4
holds with advantage exactly `0`. -/
def bRerand (Cmax D : ℕ) : UnlinkScheme := bIdeal H Cmax D true

/-- **O4 discharge for both B instances** (Spec.md MC15, rev-9 K4
Concern 2): the close view (the certified count) is simulatable from the
spend count alone — the simulator ignores `cm` and the epoch and replays
the count. Stated over all payer states (no reachability weakening
needed). -/
theorem bIdeal_closeViewSimulatable (Cmax D : ℕ) (rerand : Bool) :
    closeViewSimulatable (bIdeal H Cmax D rerand) PUnit
      (fun _ => PUnit.unit) BPSt.idx :=
  ⟨fun _ c _ => pure c, fun _e _st => by simp [bIdeal]⟩

/-! ## O3/M2: adversary-issued genesis and receipt absorption -/

/-- **M2 genesis discharge.** Every handle selected by the adversary-payee is
accepted as the genesis certified ciphertext and produces the canonical live
state.  At this abstraction the adversary is the receipt issuer, so there is
no separate malformed-signature branch. -/
theorem bIdeal_openCh_adversary_genesis (Cmax D : ℕ) (rerand : Bool) (g : H) :
    (bIdeal H Cmax D rerand).openCh g =
      pure ((⟨g, 0, 0, none⟩ : BPSt H), PUnit.unit) := rfl

/-- **O3 receipt discharge.** Serving an issuer-produced receipt replaces
the certified ciphertext handle and adds precisely its certified refund to
the payer state, while preserving the index and retry buffer. -/
theorem bIdeal_serve_issuer_receipt (Cmax D : ℕ) (rerand : Bool)
    (st : BPSt H) (ct' : H) (refund : ℕ) :
    (bIdeal H Cmax D rerand).serve st (ct', refund) =
      { st with ct := ct', R := st.R + refund } := rfl

/-- Serving an issuer-produced receipt cannot make a previously capable
candidate insolvent: certified refunds only enlarge the B solvency budget.
This is the operational content of absorbing adversary-issued receipts in the
UNLINK game. -/
theorem bIdeal_serve_capable_mono (Cmax D q : ℕ) (rerand : Bool)
    (st : BPSt H) (ct' : H) (refund : ℕ)
    (hcap : (bIdeal H Cmax D rerand).capableFor q st = true) :
    (bIdeal H Cmax D rerand).capableFor q
      ((bIdeal H Cmax D rerand).serve st (ct', refund)) = true := by
  simp only [bIdeal, decide_eq_true_eq] at hcap ⊢
  omega

/-! ## The B-rerand coupling (must-pass direction) -/

/-- The state-independent ideal B-rerand challenge batch: `n` fresh uniform
handles, one per spend. This is the ideal content of assumption 5 —
re-randomization severs the presented component from the payer's certified
state, so the batch a candidate emits depends only on the batch length and
fresh randomness, never on which candidate emitted it. Mirrors
`Zkpc.Games.flatFreshBatch`. -/
def bFreshBatch (H : Type) [SampleableType H] : ℕ → ProbComp (Option (List H))
  | 0 => pure (some [])
  | n + 1 => do
      let h ← ($ᵗ H)
      Option.map (h :: ·) <$> bFreshBatch H n

/-- Clean unfolding of the B-rerand spend on a solvent state: it samples a
fresh uniform handle and emits it (re-randomization, assumption 5's ideal
form). -/
lemma bRerand_spend_eq (Cmax D e : ℕ) (st : BPSt H) (m : PUnit)
    (h : (st.idx + 1) * Cmax ≤ D + st.R) :
    (bRerand H Cmax D).spend e st m =
      (do let hd ← ($ᵗ H)
          pure (some (hd, { st with idx := st.idx + 1, last := some hd }))) := by
  show (bIdeal H Cmax D true).spend e st m = _
  simp only [bIdeal, if_pos h]
  rfl

/-- **The batch coupling (T4-B secure core).** On any state solvent for the
whole batch, the B-rerand challenge batch has the state-independent
distribution `bFreshBatch |ms|`: every spend succeeds (Mi3 discharged for
this instance) and emits a fresh uniform handle, so any two batch-solvent
states — the two candidates — produce identically distributed batches.
Mirrors `Zkpc.Games.evalDist_spendBatch_flat`. -/
lemma evalDist_spendBatch_bRerand (Cmax D e : ℕ) :
    ∀ (ms : List PUnit) (st : BPSt H),
      (st.idx + ms.length) * Cmax ≤ D + st.R →
      𝒟[spendBatch (bRerand H Cmax D) e st ms] = 𝒟[bFreshBatch H ms.length] := by
  intro ms
  induction ms with
  | nil => intro st _; rfl
  | cons m ms ih =>
    intro st hst
    have hlen : (st.idx + (ms.length + 1)) * Cmax ≤ D + st.R := by
      simpa [List.length_cons] using hst
    have hsolv : (st.idx + 1) * Cmax ≤ D + st.R := by
      have hmono : (st.idx + 1) * Cmax ≤ (st.idx + (ms.length + 1)) * Cmax := by
        gcongr; omega
      omega
    have hst' : ((st.idx + 1) + ms.length) * Cmax ≤ D + st.R := by
      have he : (st.idx + 1) + ms.length = st.idx + (ms.length + 1) := by omega
      rw [he]; exact hlen
    simp only [spendBatch, bRerand_spend_eq H Cmax D e st m hsolv, bind_assoc, pure_bind,
      bFreshBatch]
    simp only [evalDist_bind]
    refine bind_congr fun hd => ?_
    exact evalDist_map_eq_of_evalDist_eq
      (ih ⟨st.ct, st.idx + 1, st.R, some hd⟩ hst') _

/-! ## O2: batch totality on solvent states -/

/-- The ideal B-rerand batch never outputs `⊥`: `none` is not in its
support. -/
lemma bFreshBatch_none_not_mem (n : ℕ) :
    none ∉ support (bFreshBatch H n) := by
  induction n with
  | zero => simp [bFreshBatch]
  | succ n ih =>
    intro hmem
    simp only [bFreshBatch] at hmem
    obtain ⟨h, -, hmem⟩ := (mem_support_bind_iff _ _ _).1 hmem
    rw [support_map, Set.mem_image] at hmem
    obtain ⟨l, hl, hmap⟩ := hmem
    cases l with
    | none => exact ih hl
    | some x => simp at hmap

/-- **O2 discharge (Mi3, session form).** On a state solvent for the whole
batch, the B-rerand challenge batch is total: it returns `⊥` with
probability `0`, so `capableFor q` guarantees all `q` batch spends succeed
(Spec.md T4, `challengeResp`/`spendBatch` Mi3 obligation). -/
theorem bRerand_spendBatch_none_zero (Cmax D e : ℕ) (ms : List PUnit) (st : BPSt H)
    (h : (st.idx + ms.length) * Cmax ≤ D + st.R) :
    Pr[= none | spendBatch (bRerand H Cmax D) e st ms] = 0 := by
  rw [probOutput_congr rfl (evalDist_spendBatch_bRerand H Cmax D e ms st h),
    probOutput_eq_zero_iff]
  exact bFreshBatch_none_not_mem H ms.length

/-! ## Challenge-response bit-freeness -/

/-- Extract the two candidates' batch-solvency facts from a passing
`challengeCapable` check. -/
private lemma bRerand_capable_of_challengeCapable (Cmax D : ℕ)
    (g : GSt (bRerand H Cmax D)) (q : ℕ)
    (h : challengeCapable (bRerand H Cmax D) g q = true) :
    ((g.cand false).idx + q) * Cmax ≤ D + (g.cand false).R ∧
      ((g.cand true).idx + q) * Cmax ≤ D + (g.cand true).R := by
  simp only [challengeCapable, bRerand, bIdeal, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2.2⟩

/-- **Challenge-response is hidden-bit-independent at every game state**
(B-rerand). The guard does not mention `b`; on the passing branch both
candidates are batch-solvent, so both batches equal `bFreshBatch |ms|` (the
batch coupling), hence coincide. This is the hypothesis
`unlinkAdvantage_eq_zero_of_challenge_bitfree` consumes. Mirrors
`Zkpc.Games.challengeResp_flat_bitfree`. -/
theorem challengeResp_bRerand_bitfree (Cmax D : ℕ)
    (g : GSt (bRerand H Cmax D)) (ms : List PUnit) (b b' : Bool) :
    𝒟[challengeResp (bRerand H Cmax D) g b ms] =
      𝒟[challengeResp (bRerand H Cmax D) g b' ms] := by
  unfold challengeResp
  split_ifs with hcond
  · have hcap : challengeCapable (bRerand H Cmax D) g ms.length = true := by
      simp only [Bool.and_eq_true] at hcond; exact hcond.2
    obtain ⟨hf, ht⟩ := bRerand_capable_of_challengeCapable H Cmax D g ms.length hcap
    rw [evalDist_spendBatch_bRerand H Cmax D g.epoch ms (g.cand b)
        (by cases b <;> assumption),
      evalDist_spendBatch_bRerand H Cmax D g.epoch ms (g.cand b')
        (by cases b' <;> assumption)]
  · rfl

end Zkpc.Games

#print axioms Zkpc.Games.bIdeal_openCh_adversary_genesis
#print axioms Zkpc.Games.bIdeal_serve_issuer_receipt
#print axioms Zkpc.Games.bIdeal_serve_capable_mono
#print axioms Zkpc.Games.bIdeal_closeViewSimulatable
#print axioms Zkpc.Games.bRerand_spendBatch_none_zero
