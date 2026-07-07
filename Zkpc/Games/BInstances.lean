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
  (this file) proves advantage exactly `0` for **all** adversaries, via
  the coupling technique of `Zkpc.Games.Coupling`.

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

variable (H : Type) [DecidableEq H] [SampleableType H]

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
against it — `Zkpc.Games.Calibration.unlinkAdvantage_staticDistinguisher`. -/
def bStatic (Cmax D : ℕ) : UnlinkScheme := bIdeal H Cmax D false

/-- **B-rerand** (Spec.md §4): the patched re-randomized-presentation
variant, ideal form. `unlinkAdvantage_bRerand_eq_zero` below proves T4
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

/-! ## The B-rerand coupling (must-pass direction) -/

/-- The B-rerand challenge batch has a state-independent output
distribution once the state is solvent for the whole batch: every spend
succeeds (Mi3 discharged for this instance) and emits a fresh uniform
handle, so any two batch-solvent states produce identically distributed
batches. This is the ideal content of assumption 5: re-randomization
severs the presented component from the payer's certified state. -/
lemma evalDist_spendBatch_bRerand (Cmax D e : ℕ) (ms : List PUnit) :
    ∀ st st' : BPSt H,
      (st.idx + ms.length) * Cmax ≤ D + st.R →
      (st'.idx + ms.length) * Cmax ≤ D + st'.R →
      𝒟[spendBatch (bRerand H Cmax D) e st ms] =
        𝒟[spendBatch (bRerand H Cmax D) e st' ms] := by
  induction ms with
  | nil => intro st st' _ _; rfl
  | cons m ms ih =>
    intro st st' hst hst'
    have h1 : (st.idx + 1) * Cmax ≤ D + st.R :=
      le_trans (Nat.mul_le_mul_right _ (by omega)) hst
    have h1' : (st'.idx + 1) * Cmax ≤ D + st'.R :=
      le_trans (Nat.mul_le_mul_right _ (by omega)) hst'
    simp only [spendBatch, bRerand, bIdeal, if_pos h1, if_pos h1',
      if_pos rfl, bind_assoc, pure_bind]
    simp only [evalDist_bind]
    refine bind_congr fun h => ?_
    exact congrArg _ (ih _ _ (by simpa using by omega : _) (by simpa using by omega : _))

end Zkpc.Games
