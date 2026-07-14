import Mathlib.Algebra.Field.Basic

/-!
# The zk payment channel object (task B2; Spec.md §1–§2)

Algorithm signatures for the tuple (Setup, Open, Spend, Redeem, Close,
Dispute) as Lean types, no bodies. Every field below is traceable to a
sentence of `Spec.md` §2; the concrete instantiations (flat-ticket in
`Zkpc.Core`, refund variant in `Zkpc.Refund`) provide the bodies.

Sort discipline (Spec.md §1): monetary quantities, indices, counters, and
times are `ℕ` and all solvency/payout inequalities are integer inequalities;
only the signal algebra (secrets, line values) lives in the field `F`.

Model boundary notes (Spec.md §5), load-bearing for how these signatures
read:
- Randomness is the environment's: `Open` takes the sampled secret `k` as an
  argument rather than sampling internally; probabilistic games sample it.
- `Setup` is trusted and absorbed into `Params` plus the instantiation's
  fixed data (gateway roster, keys); there is no `setup` field here.
- The idealized ledger is a state type with the algorithms as transitions;
  its guarantees (total order, `Δ`-inclusion, automatic window settlement)
  are properties of the *transition system* built in `Zkpc.Core`, not of
  these signatures.
-/

namespace Zkpc.Spec

/-- Public parameters (Spec.md §1 table). Merkle depth `d` is absorbed by
modeling the membership tree as a finite set (we do not verify circuits, so
tree shape is irrelevant to the theorems). -/
structure Params where
  /-- flat price per spend (instantiation A) -/
  C : ℕ
  /-- maximum price per spend (instantiation B) -/
  Cmax : ℕ
  /-- deposit escrowed per channel at `Open` -/
  D : ℕ
  /-- epoch length (wall-clock duration of one RLN rate epoch) -/
  Te : ℕ
  /-- per-gateway, per-epoch rate budget (max *accepted* spends per epoch pseudonym per gateway) -/
  b : ℕ
  /-- number of gateways in the fleet (instantiation A; `N = 1` for B) -/
  N : ℕ
  /-- reconciliation lag, end-to-end (Spec.md §1, MC11) -/
  L : ℕ
  /-- close/dispute window duration -/
  tau : ℕ
  /-- idealized-ledger inclusion delay for honest transactions -/
  delta : ℕ
  C_pos : 0 < C
  Cmax_pos : 0 < Cmax
  Te_pos : 0 < Te
  N_pos : 0 < N

/-- A gateway-bound spend message `m = (G, m̂)` (Spec.md §1, MC14): the
serving gateway's identity paired with the request payload. `Redeem` at `G`
rejects tickets naming a different gateway. -/
structure Message (Gateway Payload : Type) where
  gw : Gateway
  payload : Payload

/-- `Redeem`'s three-way verdict plus plain rejection for failed admission
checks (Spec.md §2 Redeem, checks 1–6). `evidence` carries a conflicting
pair for `Dispute`. -/
inductive Verdict (Evidence : Type)
  /-- all checks pass; the ticket joins the spent set and the rate counter increments -/
  | accept
  /-- bit-identical tuple already present: the abort-retry path (MC2), no slash, no budget -/
  | rejectDuplicate
  /-- an admission check (1–5) failed -/
  | reject
  /-- same nullifier, different message digest: forward to `Dispute` (check 6, third branch) -/
  | evidence (ev : Evidence)

/-- The abstract zk payment channel scheme (Spec.md §2): carrier types and
the algorithm tuple as signatures. `F` is the signal field; the remaining
carriers are per-instantiation. -/
structure Scheme (F : Type) [Field F] where
  /-- gateway identities; the sweep-authorized roster is fixed at Setup (MC16) -/
  Gateway : Type
  /-- request payloads `m̂` -/
  Payload : Type
  /-- spend tickets `t = (π, root, e, nf_e, s, [E(R) presentation])` -/
  Ticket : Type
  /-- refund receipts `ρ = (ct', σ_S(ct'), r', c)` (instantiation B; `Unit` in A) -/
  Receipt : Type
  /-- dispute evidence `ev = (nf, (x,y), (x',y'))` -/
  Evidence : Type
  /-- payer private state `st_P = (k, i, R, refund evidence)` -/
  PayerSt : Type
  /-- payee local state `st_G = (SS_G, rate counters)` -/
  PayeeSt : Type
  /-- idealized-ledger state: membership set, escrow pool, `RedeemedNF`, windows, channel statuses -/
  LedgerSt : Type
  /-- an accepted spent-set tuple `(nf, x, y)`, the unit of fleet reconciliation -/
  SpentTuple : Type
  /-- `Open(pp, D; payer)`: with environment-sampled secret `k`, register
  `cm = H_id(k)`, escrow `D` into the pool, initialize payer state
  (B: including the genesis receipt exchange, MC7). `none` if the ledger
  refuses (e.g. duplicate commitment). -/
  open' : Params → F → LedgerSt → Option (PayerSt × LedgerSt)
  /-- `Spend(pp, st_P, m)`: emit the ticket at the current index and advance
  it (consumption at emission, MC2). `none` iff the solvency conjunct is
  unsatisfiable at the current index (Spec.md §2; the T4 game references
  this behavior). -/
  spend : Params → PayerSt → Message Gateway Payload → Option (Ticket × PayerSt)
  /-- re-send the last emitted ticket, bit-identical (MC2 retry; same
  gateway by MC14). `none` if nothing was emitted yet. -/
  retry : PayerSt → Option Ticket
  /-- `Redeem(pp, st_G, t)` at gateway `gw`: the six admission checks in
  Spec.md §2 order; on accept in B, also the declared cost and receipt. -/
  redeem : Params → Gateway → PayeeSt → LedgerSt → Ticket →
    Verdict Evidence × PayeeSt × Option Receipt
  /-- fleet reconciliation step (A only): merge one incoming accepted tuple
  into a gateway's spent set, emitting merge-time evidence on conflict
  (MC17 — required behavior). -/
  merge : PayeeSt → SpentTuple → PayeeSt × Option Evidence
  /-- payer close (MC20, Spec.md rev-8+): **no close signal exists.**
  In A the payer publishes `(cm, U, π_close)` — the PRF-fresh nullifiers
  of its claimed-unused indices — and is paid per proven-unused index; in
  B it publishes `(cm, j, nf_j, π_close)` at its receipt-certified count.
  The window `τ` admits close-disputes (checkpoint bit-match in A,
  receipt-bearing tuples with the upgrade sub-window in B) and ordinary
  `Dispute` evidence; settlement, the two-sided sweep-bar check, and
  voiding at expiry are ledger-internal window semantics (§2), not tuple
  algorithms — the symbolic machine models them as `closeDispute` /
  `settleClose` / `settleVoid` transitions. A fully spent-down payer can
  still close. -/
  payerClose : Params → PayerSt → LedgerSt → Option LedgerSt
  /-- payee close ("sweep"): a *registered* gateway (MC16) submits redeemed
  tuples; the ledger dedups by nullifier against `RedeemedNF` and pays per
  fresh nullifier from the pool. -/
  sweep : Params → Gateway → List SpentTuple → LedgerSt → LedgerSt
  /-- `Dispute(pp, ev, L)`: permissionless; validates the conflicting pair
  by line algebra, slashes and evicts the recovered commitment (root
  rotation, MC5), opens the gateway-priority window with its two claim
  kinds, remainder to submitter (MC4/MC16). This is the
  **identity-slash** path — `k` is recovered and published. The
  **fund-slash** paths (MC20 close-disputes, settlement-detected false
  claims; rev-10 taxonomy) never run the line algebra, keep `k` hidden,
  and settle per §2 (A: remainder pooled; B: forfeit); they live in the
  ledger's window semantics, not this algorithm. `none` if the evidence
  is invalid. -/
  dispute : Params → Evidence → LedgerSt → Option LedgerSt

end Zkpc.Spec
