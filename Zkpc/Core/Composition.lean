import Zkpc.Core.T1
import Zkpc.Core.T2
import Zkpc.Core.T3
import Zkpc.Core.T5
import Zkpc.Games.SigmaInstance

/-!
# The channel composition theorem (issue #7)

`channel_endToEnd_composition` connects, over **one** channel trace
(`Reach C D τ honest`), the guarantees that were previously separate
endpoints: an honest payer who has posted a close reaches a settled state on
the SAME trace, and at that settled state the entire guarantee bundle holds
simultaneously — close settlement with the exact payer floor (T5/T3),
no-overspend for every member (T1), exact payee settlement (T2), and
exculpability of the honest closer (T1 exculpability clause).

`wire_endToEnd_composition` bundles the wire-protocol guarantees for the
same protocol object family: perfect spend unlinkability for the verified
Fiat--Shamir wire (T4 on `fsFlatInstance`) together with its zero-loss ZK
bridge to the proof-free game (O1). The remaining conditional guarantee —
the unconditional T7 FRAME bound — is exactly issue #3
(`FrameDeferredSampling`); its conditional form `T7_frame_bound` and its
query-budget form `T7_frame_query_bound` are already kernel-checked in
`Zkpc/Games/T7.lean` and compose with this bundle once the handler coupling
lands.
-/

namespace Zkpc.Core

variable {K M : Type} [DecidableEq K] [DecidableEq M]
variable {C D τ : ℕ} {honest : K → Prop}

/-- **The one-trace channel composition theorem.** On a single reachable
channel trace, an honest payer with a posted, unsettled close reaches (by
liveness) a settled successor state of the same trace at which ALL channel
guarantees hold simultaneously:

1. close settles and the payer receives the exact floor `D − j·C` (T5 + T3);
2. no member can overspend: every `k'` has `valueOf k' ≤ D` (T1);
3. the payee is settled exactly: `paidGw = C · |swept|` (T2);
4. the honest closer is never slashed (exculpability). -/
theorem channel_endToEnd_composition {s : St K M}
    (h : Reach C D τ honest s) (k : K) (hk : honest k)
    {U : Finset ℕ} {t : ℕ} (hc : s.closedAt k = some (U, t))
    (hnotYet : s.closeSettled k = false) :
    ∃ s' : St K M, Reach C D τ honest s' ∧
      -- (1) settlement and exact payer floor
      s'.closeSettled k = true ∧
      s'.paidPayer k = D - s.emittedCnt k * C ∧
      s'.paidPayer k + s.emittedCnt k * C = D ∧
      -- (2) T1 no-overspend at the settled state, every member
      (∀ k' : K, s'.valueOf k' C ≤ D) ∧
      -- (3) T2 exact payee settlement at the settled state
      s'.paidGw = C * s'.swept.card ∧
      -- (4) exculpability of the honest closer at the settled state
      s'.slashedAt k = none := by
  obtain ⟨s', hreach', hclock, hset, hpaid, hfloor⟩ :=
    T5_payer_close_liveness h k hk hc hnotYet
  refine ⟨s', hreach', hset, hpaid, hfloor, ?_, ?_, ?_⟩
  · exact fun k' => T1_no_overspend hreach' k'
  · exact T2_paid_exact hreach'
  · exact honest_never_slashed hreach' k hk

end Zkpc.Core

namespace Zkpc.Games

/-- **The wire-protocol guarantee bundle** for the verified Fiat--Shamir
wire family: perfect spend unlinkability (T4, advantage exactly `0` for
every adversary) together with the zero-loss ZK bridge to the proof-free
game (O1). Composes with `Zkpc.Core.channel_endToEnd_composition` as the
guarantee layer for the same protocol object family. -/
theorem wire_endToEnd_composition {F : Type} [Field F] [DecidableEq F]
    [SampleableType F] [Fintype F] [Inhabited F] (budget : ℕ) :
    (∀ A : UnlinkAdversary (fsFlatInstance (F := F) budget),
      unlinkAdvantage (fsFlatInstance (F := F) budget) A = 0) ∧
    zkBridgeObligation (fsFlatInstance (F := F) budget)
      (flatInstance (F := F) budget) 0 :=
  ⟨fun A => T4_fsFlat_unlinkability budget A, fsFlat_zkBridge budget⟩

end Zkpc.Games

#print axioms Zkpc.Core.channel_endToEnd_composition
#print axioms Zkpc.Games.wire_endToEnd_composition
