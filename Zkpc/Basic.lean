/-!
# zk-payments-confetti: Lean formalization root

Protocol-layer formalization of zk payment channels over an idealized ledger.
Crypto primitives enter as named axioms in `Zkpc.Assumptions` and nowhere else.
See `PROVING.md` for the model boundary and contribution rules.
-/

namespace Zkpc

/-- Marker for the library scaffold; replaced by real content as modules land. -/
def scaffoldVersion : String := "0.1.0"

end Zkpc
