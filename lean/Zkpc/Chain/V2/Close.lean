import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic

/-!
# Spec-v2 close objects and the challenge-evidence algebra

The algebra behind Spec-v2 Sections 4–5 (close modes, exhibit sets, challenge
validity), superseding the `i < len` index rule of `Zkpc/Chain/Collision.lean`
for the post-A2 protocol: closing is legal on **signed states, the genesis,
and unsigned-but-proof-valid states** (accepted default A2), and the challenge
matches a held message's revealed nullifier against the close's **exhibit
set** — the opened next-nullifier for signed/genesis closes, plus the
parent-reveal for unsigned closes (Spec-v2 [R1] mode-dependent refinement of
A2.iii) — excluding the closed state itself (the same-state exception).

## Modeling conventions

* **Chain positions.** As in `Zkpc/Chain/Collision.lean`, the nullifier chain
  `N₁ = H(cid, c)`, `N_{j+1} = H(N_j, c)` is abstracted to `nul : ℕ → N`
  (`nul j` is `N_j`), and the random-oracle content is the collision-freedom
  hypothesis `Function.Injective nul` (probability `≥ 1 - n²/|N|` over the
  first `n` links; theorems take the collision-free event as a hypothesis).
* **Knowledge soundness as object validity.** A close object exists (is
  `Valid`) iff its `π_close` relation from Spec-v2 §4 is satisfiable: signed
  closes need a countersigned index, ghost closes need a pending ghost,
  unsigned-fresh closes need a signed-or-genesis parent and the in-circuit
  value guards (`δ' ≥ 0` by type, `bal ≤ D`). Chain-equation enforcement
  (A5) is what pins every proof-valid state to a chain position, hence to
  the exhibit indices used here: a forger without `c` is outside this
  symbolic layer (Spec-v2 §7 non-frameability, a future obligation).
* **The unsigned frontier is one deep** (Spec-v2 §3: a payment proof needs a
  Bob-signed parent or the genesis, and Bob's dedup blocks re-reveals), so a
  context is `(len, msgs)` with `msgs ∈ {len, len+1}`; `msgs = len + 1`
  means one ghosted (sent, never countersigned) message with public
  increment `ghostδ` is outstanding.
* **Message identity is commitment identity** (Spec-v2 §5, `C_m ≠ C_x`).
  Closing the ghost message *itself* (`CloseObj.ghost`) reuses its
  commitment, so the ghost is same-state-excluded; any *other* unsigned
  close carries a fresh commitment (`CloseObj.unsignedFresh`) and matches no
  held message. `SameState` transcribes exactly this.

## GATE-NOTE (disclosed simplifications)

Single channel (cross-channel evidence is a hash collision, absorbed into
the collision bound — Spec-v2 §5); one ghost at a time (forced by dedup);
`δ : ℕ` so `δ ≥ 0` (A2.ii) holds by type.
-/

namespace Zkpc.Chain.V2

/-- Off-chain channel context at close time: `len` = latest countersigned
state index (0 = genesis), `msgs` = payment messages sent (`len` or
`len + 1`; the latter means one ghosted message is outstanding), `balOf i` =
balance committed in chain state `i`, `ghostδ` = the ghosted message's public
increment (meaningful only when `msgs = len + 1`). -/
structure Ctx where
  len : ℕ
  msgs : ℕ
  balOf : ℕ → ℕ
  ghostδ : ℕ

namespace Ctx

variable (c : Ctx)

/-- Bob's earned balance: the balance of the latest countersigned state. -/
def earned : ℕ := c.balOf c.len

/-- The balance the current frontier commits to Bob: `earned`, plus the
ghosted `δ` if a ghost is outstanding (Spec-v2 §7, "Liveness for Alice":
under a ghost, Alice's safe close pays the ghost's balance — the one-δ abort
price). -/
def owed : ℕ := if c.msgs = c.len + 1 then c.earned + c.ghostδ else c.earned

/-- Context well-formedness, maintained by the Spec-v2 machine
(`Zkpc/Chain/V2/State.lean`) as part of its invariant: genesis balance zero,
deposit cap on every committed balance, monotone countersigned chain, the
one-deep unsigned frontier, and the cap on the ghost's balance (its payment
proof enforced `bal ≤ D` too). -/
structure WF (D : ℕ) : Prop where
  genesis_zero : c.balOf 0 = 0
  cap : ∀ i, c.balOf i ≤ D
  mono : ∀ i j, i ≤ j → j ≤ c.len → c.balOf i ≤ c.balOf j
  msgs_lb : c.len ≤ c.msgs
  msgs_ub : c.msgs ≤ c.len + 1
  ghost_cap : c.msgs = c.len + 1 → c.earned + c.ghostδ ≤ D

theorem earned_le_owed : c.earned ≤ c.owed := by
  unfold owed
  split <;> omega

/-- **The wedge price is one δ** (Spec-v2 §7): what the frontier owes exceeds
the countersigned balance by at most the ghosted increment. -/
theorem owed_le_earned_add_ghost : c.owed ≤ c.earned + c.ghostδ := by
  unfold owed
  split <;> omega

end Ctx

/-- The close objects of Spec-v2 §4, indexed by what `π_close` proves:
* `genesis` — full-refund close (opens `N₁`, balance 0);
* `signed i` — close on countersigned state `i` (opens `N_{i+1}`);
* `ghost` — unsigned close on the outstanding ghosted message itself
  (commitment identical to the held message);
* `unsignedFresh p δ'` — unsigned close on a proof-valid state with a fresh
  commitment: parent `p` (countersigned or genesis), increment `δ'`.
  Rollback forks of old parents and tip re-extensions both live here. -/
inductive CloseObj
  | genesis
  | signed (i : ℕ)
  | ghost
  | unsignedFresh (p δ' : ℕ)

/-- Which close objects are proof-valid in context (Spec-v2 §4, the three
close relations; knowledge soundness as validity, per the module docstring). -/
def Valid (D : ℕ) (c : Ctx) : CloseObj → Prop
  | .genesis => True
  | .signed i => 1 ≤ i ∧ i ≤ c.len
  | .ghost => c.msgs = c.len + 1
  | .unsignedFresh p δ' => p ≤ c.len ∧ c.balOf p + δ' ≤ D

/-- The balance a close object's settlement pays Bob (Spec-v2 §6). -/
def balV (c : Ctx) : CloseObj → ℕ
  | .genesis => 0
  | .signed i => c.balOf i
  | .ghost => c.earned + c.ghostδ
  | .unsignedFresh p δ' => c.balOf p + δ'

/-- The exhibit set, as chain positions (Spec-v2 §4): signed/genesis closes
exhibit the opened next-nullifier only; unsigned closes also exhibit the
parent-reveal. The ghost sits at chain depth `len + 1` (parent `len`), a
fresh unsigned state at depth `p + 1` (parent `p`). -/
def ExhibitIdx (c : Ctx) : CloseObj → ℕ → Prop
  | .genesis, k => k = 1
  | .signed i, k => k = i + 1
  | .ghost, k => k = c.len + 1 ∨ k = c.len + 2
  | .unsignedFresh p _, k => k = p + 1 ∨ k = p + 2

/-- The same-state exception (Spec-v2 §5, `C_m ≠ C_x`): held message `j` is
the closed state itself only for a signed close on `j` or the ghost close on
the ghosted message (`j = len + 1`). Genesis has no message; a fresh unsigned
close's commitment matches no held message. -/
def SameState (c : Ctx) (j : ℕ) : CloseObj → Prop
  | .signed i => j = i
  | .ghost => j = c.len + 1
  | _ => False

variable {N : Type}

/-- **Challenge evidence** (Spec-v2 §5): some held message `j ∈ [1, msgs]`,
not the closed state itself, whose revealed nullifier `N_j` equals an
exhibited nullifier of the close. Messages reveal `nul j` (message `j`
reveals its parent's committed next-nullifier `N_j`, Spec-v2 §2). -/
def Evidence (nul : ℕ → N) (c : Ctx) (x : CloseObj) : Prop :=
  ∃ j k, 1 ≤ j ∧ j ≤ c.msgs ∧ ¬ SameState c j x ∧ ExhibitIdx c x k ∧
    nul j = nul k

/-- A close is safe iff it is proof-valid and admits no challenge evidence. -/
def Safe (nul : ℕ → N) (D : ℕ) (c : Ctx) (x : CloseObj) : Prop :=
  Valid D c x ∧ ¬ Evidence nul c x

/-! ## Per-mode characterization (under chain collision-freedom) -/

/-- Genesis-close evidence is exactly "some message was sent": message 1
revealed `N₁`, the nullifier the refund opens — `PROTOCOL.md`'s "uniform
rule, no special case", now with the A2 unsigned frontier included. -/
theorem evidence_genesis (nul : ℕ → N) (hinj : Function.Injective nul)
    (c : Ctx) : Evidence nul c .genesis ↔ 1 ≤ c.msgs := by
  constructor
  · rintro ⟨j, k, hj1, hj2, -, hk, hcol⟩
    simp only [ExhibitIdx] at hk
    have hjk := hinj hcol
    omega
  · intro h
    exact ⟨1, 1, le_refl _, h, by simp [SameState], rfl, rfl⟩

/-- Signed-close evidence is exactly staleness relative to *messages*: the
close on countersigned `i` opens `N_{i+1}`, revealed iff message `i + 1`
exists. Note `msgs`, not `len`: a ghosted message is evidence against the
signed tip (the wedge's forfeit-bait, Spec-v2 §7 / G2). -/
theorem evidence_signed (nul : ℕ → N) (hinj : Function.Injective nul)
    (c : Ctx) (i : ℕ) :
    Evidence nul c (.signed i) ↔ i + 1 ≤ c.msgs := by
  constructor
  · rintro ⟨j, k, hj1, hj2, -, hk, hcol⟩
    simp only [ExhibitIdx] at hk
    have hjk := hinj hcol
    omega
  · intro h
    refine ⟨i + 1, i + 1, by omega, h, ?_, rfl, rfl⟩
    simp only [SameState]
    omega

/-- The ghost close is never challengeable: its parent-reveal `N_{len+1}` is
revealed only by the ghost itself (same-state-excluded), and its opened
`N_{len+2}` by nothing (no message beyond the ghost can exist). This is the
G2 repair working: the wedged payer closes on the withheld message safely. -/
theorem ghost_no_evidence (nul : ℕ → N) (hinj : Function.Injective nul)
    (c : Ctx) (hub : c.msgs ≤ c.len + 1) : ¬ Evidence nul c .ghost := by
  rintro ⟨j, k, hj1, hj2, hns, hk, hcol⟩
  simp only [SameState] at hns
  simp only [ExhibitIdx] at hk
  have hjk := hinj hcol
  rcases hk with hk | hk <;> omega

/-- Fresh-commitment unsigned closes are challengeable exactly when their
parent edge was already messaged (`p + 1 ≤ msgs`): the parent-reveal clause
catches every rollback fork — of an old parent *and* of the tip when a ghost
is outstanding (Alice cannot roll back a ghosted payment; abort price is the
δ, not a rollback). The only safe fresh unsigned close is a tip extension
with no ghost pending. -/
theorem evidence_unsignedFresh (nul : ℕ → N) (hinj : Function.Injective nul)
    (c : Ctx) (p δ' : ℕ) :
    Evidence nul c (.unsignedFresh p δ') ↔ p + 1 ≤ c.msgs := by
  constructor
  · rintro ⟨j, k, hj1, hj2, -, hk, hcol⟩
    simp only [ExhibitIdx] at hk
    have hjk := hinj hcol
    rcases hk with hk | hk <;> omega
  · intro h
    exact ⟨p + 1, p + 1, by omega, h, by simp [SameState], Or.inl rfl, rfl⟩

/-- **The safe-close characterization** (Spec-v2 §7, "Evidence
characterization"): among proof-valid closes, the safe ones are exactly the
genesis with nothing sent, the signed tip with nothing ghosted, the ghost
itself, and a fresh tip extension with nothing ghosted. Every stale and every
forked close is challengeable; every listed close is not. -/
theorem safe_iff (nul : ℕ → N) (hinj : Function.Injective nul) (D : ℕ)
    (c : Ctx) (hwf : c.WF D) (x : CloseObj) (hv : Valid D c x) :
    Safe nul D c x ↔
      (x = .genesis ∧ c.msgs = 0) ∨
      (x = .signed c.len ∧ c.msgs = c.len) ∨
      (x = .ghost) ∨
      (∃ δ', x = .unsignedFresh c.len δ' ∧ c.msgs = c.len) := by
  have hlb := hwf.msgs_lb
  have hub := hwf.msgs_ub
  cases x with
  | genesis =>
    simp only [Safe, evidence_genesis nul hinj]
    constructor
    · rintro ⟨-, hne⟩
      exact Or.inl ⟨trivial, by omega⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩ | h | ⟨δ', h, -⟩)
      · exact ⟨trivial, by omega⟩
      · cases h
      · cases h
      · cases h
  | signed i =>
    obtain ⟨hi1, hile⟩ := hv
    simp only [Safe, evidence_signed nul hinj]
    constructor
    · rintro ⟨-, hne⟩
      have hi : i = c.len := by omega
      have hm : c.msgs = c.len := by omega
      exact Or.inr (Or.inl ⟨by rw [hi], hm⟩)
    · rintro (⟨h, -⟩ | ⟨h, hm⟩ | h | ⟨δ', h, -⟩)
      · cases h
      · injection h with hi
        subst hi
        exact ⟨⟨hi1, hile⟩, by omega⟩
      · cases h
      · cases h
  | ghost =>
    simp only [Safe]
    constructor
    · intro _
      exact Or.inr (Or.inr (Or.inl trivial))
    · intro _
      exact ⟨hv, ghost_no_evidence nul hinj c hub⟩
  | unsignedFresh p δ' =>
    obtain ⟨hple, hcap⟩ := hv
    simp only [Safe, evidence_unsignedFresh nul hinj]
    constructor
    · rintro ⟨-, hne⟩
      have hp : p = c.len := by omega
      have hm : c.msgs = c.len := by omega
      exact Or.inr (Or.inr (Or.inr ⟨δ', by rw [hp], hm⟩))
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | h | ⟨δ'', h, hm⟩)
      · cases h
      · cases h
      · cases h
      · injection h with h1 h2
        exact ⟨⟨hple, hcap⟩, by omega⟩

/-! ## Payout facts -/

/-- Every proof-valid close pays at most the deposit (the in-circuit
`bal ≤ D` of every mode, Spec-v2 §6: "the contract never over- or
under-pays; there is no clamping rule"). -/
theorem balV_le (D : ℕ) (c : Ctx) (hwf : c.WF D) (x : CloseObj)
    (hv : Valid D c x) : balV c x ≤ D := by
  cases x with
  | genesis => simp [balV]
  | signed i => simpa [balV] using hwf.cap i
  | ghost =>
    simp only [Valid] at hv
    simpa [balV] using hwf.ghost_cap hv
  | unsignedFresh p δ' =>
    simp only [Valid] at hv
    simpa [balV] using hv.2

/-- **Safe closes never underpay Bob** (Spec-v2 §7, "Bob never loses", the
cooperative half): every safe close pays at least the latest countersigned
balance. With `challenge`/`timeoutForfeit` paying the whole deposit, this is
the complete payout floor. -/
theorem safe_payout_ge_earned (nul : ℕ → N) (hinj : Function.Injective nul)
    (D : ℕ) (c : Ctx) (hwf : c.WF D) (x : CloseObj)
    (hs : Safe nul D c x) : c.earned ≤ balV c x := by
  obtain ⟨hv, hne⟩ := hs
  have hlb := hwf.msgs_lb
  cases x with
  | genesis =>
    rw [evidence_genesis nul hinj] at hne
    have hl : c.len = 0 := by omega
    have : c.earned = 0 := by
      unfold Ctx.earned
      rw [hl, hwf.genesis_zero]
    simp [balV, this]
  | signed i =>
    obtain ⟨hi1, hile⟩ := hv
    rw [evidence_signed nul hinj] at hne
    have hi : i = c.len := by omega
    subst hi
    simp [balV, Ctx.earned]
  | ghost =>
    show c.earned ≤ c.earned + c.ghostδ
    omega
  | unsignedFresh p δ' =>
    obtain ⟨hple, -⟩ := hv
    rw [evidence_unsignedFresh nul hinj] at hne
    have hp : p = c.len := by omega
    subst hp
    show c.earned ≤ c.balOf c.len + δ'
    unfold Ctx.earned
    omega

/-! ## The canonical safe close (liveness witness) -/

/-- Alice's canonical exit (Spec-v2 §7, "Liveness for Alice"): the ghost if
one is outstanding, else the signed tip, else (nothing ever signed) the
genesis refund. -/
def canonical (c : Ctx) : CloseObj :=
  if c.msgs = c.len + 1 then .ghost
  else if c.len = 0 then .genesis
  else .signed c.len

theorem canonical_valid (D : ℕ) (c : Ctx) (_hwf : c.WF D) :
    Valid D c (canonical c) := by
  unfold canonical
  by_cases hg : c.msgs = c.len + 1
  · rw [if_pos hg]
    exact hg
  · rw [if_neg hg]
    by_cases hl : c.len = 0
    · rw [if_pos hl]
      exact trivial
    · rw [if_neg hl]
      exact ⟨by omega, le_refl _⟩

/-- The canonical close is safe: **a safe close exists from every
well-formed context**, whatever Bob signed or withheld. This is the G2
theorem: the withheld-countersignature wedge is repaired. -/
theorem canonical_safe (nul : ℕ → N) (hinj : Function.Injective nul)
    (D : ℕ) (c : Ctx) (hwf : c.WF D) : Safe nul D c (canonical c) := by
  refine ⟨canonical_valid D c hwf, ?_⟩
  have hlb := hwf.msgs_lb
  have hub := hwf.msgs_ub
  unfold canonical
  by_cases hg : c.msgs = c.len + 1
  · rw [if_pos hg]
    exact ghost_no_evidence nul hinj c hub
  · rw [if_neg hg]
    by_cases hl : c.len = 0
    · rw [if_pos hl, evidence_genesis nul hinj]
      omega
    · rw [if_neg hl, evidence_signed nul hinj]
      omega

/-- The canonical close pays exactly what the frontier owes: the
countersigned balance, plus the ghosted δ iff a ghost is outstanding. -/
theorem canonical_balV (D : ℕ) (c : Ctx) (hwf : c.WF D) :
    balV c (canonical c) = c.owed := by
  unfold canonical Ctx.owed
  by_cases hg : c.msgs = c.len + 1
  · rw [if_pos hg, if_pos hg]
    rfl
  · rw [if_neg hg, if_neg hg]
    by_cases hl : c.len = 0
    · rw [if_pos hl]
      show (0 : ℕ) = c.earned
      unfold Ctx.earned
      rw [hl, hwf.genesis_zero]
    · rw [if_neg hl]
      rfl

/-- **Genesis uniformity** (Spec-v2 §7): the refund close is safe iff no
message was ever sent — one rule, no genesis special case. -/
theorem genesis_safe_iff (nul : ℕ → N) (hinj : Function.Injective nul)
    (D : ℕ) (c : Ctx) : Safe nul D c .genesis ↔ c.msgs = 0 := by
  unfold Safe
  rw [evidence_genesis nul hinj]
  simp only [Valid, true_and]
  omega

end Zkpc.Chain.V2

-- Kernel audit (K2): only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Chain.V2.evidence_genesis
#print axioms Zkpc.Chain.V2.evidence_signed
#print axioms Zkpc.Chain.V2.ghost_no_evidence
#print axioms Zkpc.Chain.V2.evidence_unsignedFresh
#print axioms Zkpc.Chain.V2.safe_iff
#print axioms Zkpc.Chain.V2.safe_payout_ge_earned
#print axioms Zkpc.Chain.V2.canonical_safe
#print axioms Zkpc.Chain.V2.canonical_balV
#print axioms Zkpc.Chain.V2.genesis_safe_iff
