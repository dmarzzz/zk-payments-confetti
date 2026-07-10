import Zkpc.Refund.Fleet
import Zkpc.Crypto.ReceiptMac

/-!
# Independent-key authentication bound plus refund-fleet accounting

The refund state-machine theorems are conditional on admitted receipt links.
`ReceiptMac` supplies a narrow reference bound: a deterministic strategy that
sees one tag before choosing a fresh-message forgery breaks one independently
keyed affine-MAC instance with probability at most `1/|F|`; a finite list of
such independent-key experiments has total failure at most `n/|F|`.

This module packages that cryptographic failure probability with the fleet's
deterministic no-overspend, conservation, and payer-floor guarantees.  It does
not pretend that a MAC failure is an ordinary symbolic transition: the result
states exactly the standard reduction boundary—outside an explicitly bounded
authentication-failure event, admitted traces enjoy the symbolic guarantees.

This is not the Spec-B shared-key receipt chain: it has no cross-link attacker
state, uses a fresh one-time key per experiment and one fixed message, and does
not discharge the production multi-query EUF-CMA assumption.
-/

open OracleSpec OracleComp

namespace Zkpc.Refund

open scoped BigOperators

variable {I Rep F : Type} [DecidableEq I]

/-- Product of refund-fleet accounting guarantees and the independent-key
reference authentication bound.  The first three fields are trace properties;
the fourth is a separate probability statement about the narrow forgery
experiment above. -/
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

/-- **Refund-fleet plus independent-key authentication theorem.** Reachability
and honest terminal conditions establish the accounting obligations, while
the separate deterministic one-query experiments supply an additive reference
failure budget. -/
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
