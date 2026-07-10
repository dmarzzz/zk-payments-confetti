import Zkpc.Refund.Fleet
import Zkpc.Crypto.ReceiptMac

/-!
# Authenticated refund-fleet composition

The refund state-machine theorems are conditional on admitted receipt links.
`ReceiptMac` now supplies the missing cryptographic admission boundary: an
adaptive attacker that sees each authentic tag before choosing a fresh-message
forgery breaks one independently keyed link with probability at most `1/|F|`,
and any link in a finite chain with probability at most `n/|F|`.

This module packages that cryptographic failure probability with the fleet's
deterministic no-overspend, conservation, and payer-floor guarantees.  It does
not pretend that a MAC failure is an ordinary symbolic transition: the result
states exactly the standard reduction boundary—outside an explicitly bounded
authentication-failure event, admitted traces enjoy the symbolic guarantees.
-/

open OracleSpec OracleComp

namespace Zkpc.Refund

open scoped BigOperators

variable {I Rep F : Type} [DecidableEq I]

/-- End-to-end refund-fleet guarantees at the authenticated-admission
boundary.  The first three fields are trace properties; the fourth is the
probability that adversarial receipt authentication invalidates that trace
boundary. -/
structure AuthenticatedFleetGuarantees
    [Fintype I] [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    (Cmax D : ℕ) (s : FleetSt I Rep) (m : F)
    (forges : List (F → F × F)) : Prop where
  noOverspend : (∑ i, (s i).sumc) ≤ Fintype.card I * D
  conservation :
    (∑ i, ((s i).payerPay + (s i).payeePay)) = Fintype.card I * D
  payerFloor :
    (∑ i, (s i).payerPay) + (∑ i, (s i).sumc) = Fintype.card I * D
  authenticationFailure :
    Pr[= true |
        Crypto.ReceiptMac.runForgeryChain
          (forges.map (Crypto.ReceiptMac.adaptiveForgeryGame m))]
      ≤ (forges.length : ENNReal) * (Fintype.card F : ENNReal)⁻¹

/-- **Authenticated refund-fleet theorem.** Reachability and honest terminal
conditions establish all accounting obligations, while adaptive receipt-chain
unforgeability supplies the exact additive cryptographic failure budget. -/
theorem authenticated_fleet_security
    [Fintype I] [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    {Cmax D : ℕ} {r0 : I → Rep} {s : FleetSt I Rep}
    (hreach : FleetReach Cmax D r0 s)
    (hsettled : ∀ i, (s i).settled = true)
    (hunslashed : ∀ i, (s i).slashed = false)
    (m : F) (forges : List (F → F × F))
    (fresh : ∀ forge ∈ forges, ∀ t, (forge t).1 ≠ m) :
    AuthenticatedFleetGuarantees Cmax D s m forges := by
  exact
    { noOverspend := fleet_no_overspend hreach
      conservation := fleet_conservation hreach hsettled
      payerFloor := fleet_payer_floor hreach hsettled hunslashed
      authenticationFailure :=
        Crypto.ReceiptMac.adaptive_mac_chain_bound m forges fresh }

end Zkpc.Refund

#print axioms Zkpc.Refund.authenticated_fleet_security
