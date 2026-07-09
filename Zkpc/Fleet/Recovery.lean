import Zkpc.Fleet.T6

/-!
# Fleet slash-window recovery

This module formalizes the aggregate MC19 settlement rule used by the fleet
scope of T2.  Only claims committed before the identity-slash transaction are
eligible.  Outstanding redeemed-ticket claims have seniority; documented
conflict claims share only the remaining deposit.  Both classes are therefore
remainder-capped, matching the specification's explicit rejection of universal
fleet recovery.

The model works at aggregate level.  Pro-rata allocation among claimants in a
class does not affect the payee-total and conservation theorems proved here.
Fund-slashes are separate: they do not reveal the member key and consequently
cannot run per-nullifier claims; instantiation B instead forfeits the deposit
to its sole payee.
-/

namespace Zkpc.Fleet

/-- A claim backed by an opening against a gateway checkpoint. -/
structure CheckpointedClaim where
  /-- value requested by the claim -/
  amount : ℕ
  /-- ledger time at which the binding accepted-set checkpoint was posted -/
  checkpointTime : ℕ

/-- MC19 eligibility: the claim was bound into the accepted-set commitment
strictly before the identity slash landed. -/
def CheckpointedClaim.eligible (slashTime : ℕ) (c : CheckpointedClaim) : Bool :=
  decide (c.checkpointTime < slashTime)

/-- Aggregate value of all eligible claims in one seniority class. -/
def eligibleDemand (slashTime : ℕ) (claims : List CheckpointedClaim) : ℕ :=
  ((claims.filter fun c => c.eligible slashTime).map CheckpointedClaim.amount).sum

/-- Aggregate identity-slash recovery result. -/
structure RecoveryPayout where
  /-- paid to outstanding redeemed-ticket/sweep claims, the senior class -/
  sweepPaid : ℕ
  /-- paid to documented-conflict claims from the residual -/
  conflictPaid : ℕ
  /-- deposit left after both classes -/
  bountyRemainder : ℕ

/-- MC19 seniority allocator.  Sweeps take up to the entire deposit first;
conflicts take up to what remains; the rest is the bounty remainder. -/
def identityRecovery (D slashTime : ℕ)
    (sweeps conflicts : List CheckpointedClaim) : RecoveryPayout :=
  let sweepPaid := min D (eligibleDemand slashTime sweeps)
  let afterSweeps := D - sweepPaid
  let conflictPaid := min afterSweeps (eligibleDemand slashTime conflicts)
  ⟨sweepPaid, conflictPaid, afterSweeps - conflictPaid⟩

/-- Senior sweep claims are paid exactly up to the deposit cap. -/
theorem identityRecovery_sweepPaid (D slashTime : ℕ)
    (sweeps conflicts : List CheckpointedClaim) :
    (identityRecovery D slashTime sweeps conflicts).sweepPaid =
      min D (eligibleDemand slashTime sweeps) := rfl

/-- Conflict claims are paid exactly up to the post-sweep remainder. -/
theorem identityRecovery_conflictPaid (D slashTime : ℕ)
    (sweeps conflicts : List CheckpointedClaim) :
    (identityRecovery D slashTime sweeps conflicts).conflictPaid =
      min (D - min D (eligibleDemand slashTime sweeps))
        (eligibleDemand slashTime conflicts) := rfl

/-- Identity-slash recovery plus the bounty remainder conserves the deposit
exactly. -/
theorem identityRecovery_conservation (D slashTime : ℕ)
    (sweeps conflicts : List CheckpointedClaim) :
    let p := identityRecovery D slashTime sweeps conflicts
    p.sweepPaid + p.conflictPaid + p.bountyRemainder = D := by
  simp only [identityRecovery]
  omega

/-- Aggregate gateway recovery never exceeds the member's remaining deposit. -/
theorem identityRecovery_capped (D slashTime : ℕ)
    (sweeps conflicts : List CheckpointedClaim) :
    let p := identityRecovery D slashTime sweeps conflicts
    p.sweepPaid + p.conflictPaid ≤ D := by
  simp only [identityRecovery]
  omega

/-- If senior sweep demand fits, it is paid in full. -/
theorem identityRecovery_sweeps_full (D slashTime : ℕ)
    (sweeps conflicts : List CheckpointedClaim)
    (hfit : eligibleDemand slashTime sweeps ≤ D) :
    (identityRecovery D slashTime sweeps conflicts).sweepPaid =
      eligibleDemand slashTime sweeps := by
  simp [identityRecovery, min_eq_right hfit]

/-- If both eligible classes fit after applying seniority, both are paid in
full and only the unused residual remains. -/
theorem identityRecovery_all_full (D slashTime : ℕ)
    (sweeps conflicts : List CheckpointedClaim)
    (hfit : eligibleDemand slashTime sweeps +
      eligibleDemand slashTime conflicts ≤ D) :
    let p := identityRecovery D slashTime sweeps conflicts
    p.sweepPaid = eligibleDemand slashTime sweeps ∧
      p.conflictPaid = eligibleDemand slashTime conflicts ∧
      p.bountyRemainder = D -
        (eligibleDemand slashTime sweeps + eligibleDemand slashTime conflicts) := by
  dsimp [identityRecovery]
  have hs : eligibleDemand slashTime sweeps ≤ D := by omega
  rw [min_eq_right hs]
  have hc : eligibleDemand slashTime conflicts ≤
      D - eligibleDemand slashTime sweeps := by omega
  rw [min_eq_right hc]
  constructor
  · rfl
  constructor
  · rfl
  · omega

/-- A claim checkpointed at or after the slash is ineligible and contributes
nothing when considered alone.  This is the binding-checkpoint defense against
post-slash claim minting. -/
theorem postSlash_claim_ineligible (slashTime : ℕ) (c : CheckpointedClaim)
    (hlate : slashTime ≤ c.checkpointTime) :
    eligibleDemand slashTime [c] = 0 := by
  simp [eligibleDemand, CheckpointedClaim.eligible, hlate]

/-- A pre-slash singleton claim contributes exactly its requested amount. -/
theorem preSlash_claim_eligible (slashTime : ℕ) (c : CheckpointedClaim)
    (hearly : c.checkpointTime < slashTime) :
    eligibleDemand slashTime [c] = c.amount := by
  simp [eligibleDemand, CheckpointedClaim.eligible, hearly]

/-- Fund-slash settlement for the refund variant: with the identity secret
still hidden, per-nullifier claims are unavailable and the sole payee receives
the whole deposit by forfeit. -/
def fundSlashRecovery (D : ℕ) : RecoveryPayout := ⟨0, D, 0⟩

/-- Fund-slash forfeit pays and conserves the complete deposit. -/
theorem fundSlashRecovery_full (D : ℕ) :
    (fundSlashRecovery D).conflictPaid = D ∧
    (fundSlashRecovery D).sweepPaid +
      (fundSlashRecovery D).conflictPaid +
      (fundSlashRecovery D).bountyRemainder = D := by
  simp [fundSlashRecovery]

end Zkpc.Fleet

#print axioms Zkpc.Fleet.identityRecovery_conservation
#print axioms Zkpc.Fleet.identityRecovery_capped
#print axioms Zkpc.Fleet.identityRecovery_all_full
#print axioms Zkpc.Fleet.postSlash_claim_ineligible
#print axioms Zkpc.Fleet.fundSlashRecovery_full
