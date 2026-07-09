import Zkpc.Games.Frame
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Ghost audit ornament for the FRAME handler

The audited handler runs the real `frameImpl` unchanged and decorates its
state with the candidate-secret probes, candidate-slope probes, and honest
slopes exposed by successful signal operations. The decoration cannot affect
responses or real caches. `auditedFrameImpl_run_project` proves exact
computation-level projection for an arbitrary adaptive adversary.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-- Ghost transcript needed to state all corrected T7 bad events. Lists retain
multiplicity so repeated honest slopes are observable as a collision. -/
structure FrameAudit (F : Type) where
  secretProbes : List F
  slopeProbes : List F
  honestSlopes : List F

/-- Empty audit transcript. -/
def FrameAudit.init : FrameAudit F := ⟨[], [], []⟩

/-- Decorated real state. -/
structure AuditedFrameSt (F M : Type) where
  base : FrameSt F M
  audit : FrameAudit F

/-- Corrected leakage event: a direct candidate hit on `k`, a candidate slope
matching an exposed honest slope, or a repeated honest slope. -/
def FrameLeakBad (k : F) (a : FrameAudit F) : Prop :=
  k ∈ a.secretProbes ∨
  (∃ slope ∈ a.slopeProbes, slope ∈ a.honestSlopes) ∨
  ¬ a.honestSlopes.Nodup

/-- Aggregate direct-secret probe classifier used by the audit resource
invariant; T7 retains separate budgets for its three summands. -/
def isSecretProbe : FrameOp F M → Bool
  | .roA _ _ | .roE _ _ | .roId _ => true
  | _ => false

/-- Candidate-slope probe classifier. -/
def isSlopeProbe : FrameOp F M → Bool
  | .roNf _ => true
  | _ => false

/-- Honest point-exposure classifier. -/
def isHonestSignalOp : FrameOp F M → Bool
  | .spend _ | .close | .nfAt _ => true
  | _ => false

instance (k : F) (a : FrameAudit F) : Decidable (FrameLeakBad k a) := by
  unfold FrameLeakBad
  infer_instance

/-- Update only the ghost transcript after one real operation. Successful
signal calls read their freshly cached slope at the pre-call honest index. -/
def auditAfter (k : F) (op : FrameOp F M) (before after : FrameSt F M)
    (audit : FrameAudit F) : FrameAudit F :=
  match op with
  | .spend _ | .close =>
      if before.closed then audit
      else match before.roA (k, before.idx) with
        | some _ => audit
        | none => match after.roA (k, before.idx) with
          | some slope => { audit with honestSlopes := slope :: audit.honestSlopes }
          | none => audit
  | .roA kq _ | .roE kq _ | .roId kq =>
      { audit with secretProbes := kq :: audit.secretProbes }
  | .roNf aq => { audit with slopeProbes := aq :: audit.slopeProbes }
  | .nfAt i =>
      match before.roA (k, i) with
      | some _ => audit
      | none => match after.roA (k, i) with
        | some slope => { audit with honestSlopes := slope :: audit.honestSlopes }
        | none => audit
  | .roX _ => audit

/-- Existing leakage remains after recording a direct secret candidate. -/
theorem FrameLeakBad.secret_cons (k q : F) (a : FrameAudit F)
    (h : FrameLeakBad k a) :
    FrameLeakBad k { a with secretProbes := q :: a.secretProbes } := by
  rcases h with h | h | h
  · exact Or.inl (List.mem_cons_of_mem q h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Existing leakage remains after recording a candidate slope. -/
theorem FrameLeakBad.slope_cons (k q : F) (a : FrameAudit F)
    (h : FrameLeakBad k a) :
    FrameLeakBad k { a with slopeProbes := q :: a.slopeProbes } := by
  rcases h with h | h | h
  · exact Or.inl h
  · rcases h with ⟨slope, hp, hs⟩
    exact Or.inr (Or.inl ⟨slope, List.mem_cons_of_mem q hp, hs⟩)
  · exact Or.inr (Or.inr h)

/-- Existing leakage remains after exposing another honest slope. -/
theorem FrameLeakBad.honest_cons (k slope : F) (a : FrameAudit F)
    (h : FrameLeakBad k a) :
    FrameLeakBad k { a with honestSlopes := slope :: a.honestSlopes } := by
  rcases h with h | h | h
  · exact Or.inl h
  · rcases h with ⟨candidate, hp, hs⟩
    exact Or.inr (Or.inl ⟨candidate, hp, List.mem_cons_of_mem slope hs⟩)
  · exact Or.inr (Or.inr (fun hnd => h hnd.tail))

/-- The ghost bad event is monotone under every audit update. -/
theorem auditAfter_preserves_bad (k : F) (op : FrameOp F M)
    (before after : FrameSt F M) (audit : FrameAudit F)
    (hbad : FrameLeakBad k audit) :
    FrameLeakBad k (auditAfter k op before after audit) := by
  cases op with
  | spend m | close =>
      unfold auditAfter
      by_cases hc : before.closed
      · simp [hc, hbad]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        cases hb : before.roA (k, before.idx) with
        | some a => simp [hb, hbad]
        | none =>
            simp only [hb]
            cases ha : after.roA (k, before.idx) with
            | none => simp [ha, hbad]
            | some slope =>
                simpa [ha] using FrameLeakBad.honest_cons k slope audit hbad
  | roA kq i | roE kq i | roId kq =>
      exact FrameLeakBad.secret_cons k kq audit hbad
  | roNf aq => exact FrameLeakBad.slope_cons k aq audit hbad
  | nfAt i =>
      unfold auditAfter
      cases hb : before.roA (k, i) with
      | some a => simp [hb, hbad]
      | none =>
          simp only [hb]
          cases ha : after.roA (k, i) with
          | none => simp [ha, hbad]
          | some slope =>
              simpa [ha] using FrameLeakBad.honest_cons k slope audit hbad
  | roX m => exact hbad

/-- A step adds at most one direct-secret probe, and only on a classified
operation. -/
theorem auditAfter_secret_length_le (k : F) (op : FrameOp F M)
    (before after : FrameSt F M) (audit : FrameAudit F) :
    (auditAfter k op before after audit).secretProbes.length ≤
      audit.secretProbes.length + if isSecretProbe op then 1 else 0 := by
  cases op <;> simp [auditAfter, isSecretProbe] <;> split <;> simp_all

/-- A step adds exactly one candidate-slope record only for `roNf`. -/
theorem auditAfter_slope_length_le (k : F) (op : FrameOp F M)
    (before after : FrameSt F M) (audit : FrameAudit F) :
    (auditAfter k op before after audit).slopeProbes.length ≤
      audit.slopeProbes.length + if isSlopeProbe op then 1 else 0 := by
  cases op <;> simp [auditAfter, isSlopeProbe] <;> split <;> simp_all

/-- A step exposes at most one honest slope, only for spend/legacy-close
operations; a closed call may expose none. -/
theorem auditAfter_honest_length_le (k : F) (op : FrameOp F M)
    (before after : FrameSt F M) (audit : FrameAudit F) :
    (auditAfter k op before after audit).honestSlopes.length ≤
      audit.honestSlopes.length + if isHonestSignalOp op then 1 else 0 := by
  cases op <;> simp [auditAfter, isHonestSignalOp] <;> split <;> simp_all

/-- Real handler plus an observational ghost audit. -/
def auditedFrameImpl (k : F) (mclose : M) :
    QueryImpl.Stateful unifSpec (frameSpec F M) (AuditedFrameSt F M) :=
  fun op => StateT.mk fun s => do
    let (answer, base') ← ((frameImpl k mclose) op).run s.base
    pure (answer, ⟨base', auditAfter k op s.base base' s.audit⟩)

/-- One audited query projects exactly to its real query. -/
theorem auditedFrameImpl_project_step (k : F) (mclose : M)
    (op : FrameOp F M) (s : AuditedFrameSt F M) :
    Prod.map id AuditedFrameSt.base <$> ((auditedFrameImpl k mclose) op).run s =
      ((frameImpl k mclose) op).run s.base := by
  simp [auditedFrameImpl]

/-- Every audited query preserves an already-raised leakage event on every
supported outcome. -/
theorem auditedFrameImpl_bad_monotone (k : F) (mclose : M)
    (op : FrameOp F M) (s : AuditedFrameSt F M)
    (hbad : FrameLeakBad k s.audit)
    (z : (frameSpec F M).Range op × AuditedFrameSt F M)
    (hz : z ∈ support (((auditedFrameImpl k mclose) op).run s)) :
    FrameLeakBad k z.2.audit := by
  unfold auditedFrameImpl at hz
  obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst z
  exact auditAfter_preserves_bad k op s.base p.2 s.audit hbad

/-- **Exact ghost-state erasure.** For every adaptive FRAME computation, the
audited execution has precisely the original response and real-state
distribution after erasing the audit. -/
theorem auditedFrameImpl_run_project (k : F) (mclose : M)
    (oa : OracleComp (frameSpec F M) α) (s : AuditedFrameSt F M) :
    Prod.map id AuditedFrameSt.base <$>
        (auditedFrameImpl k mclose).run s oa =
      (frameImpl k mclose).run s.base oa := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (auditedFrameImpl k mclose) (frameImpl k mclose)
    AuditedFrameSt.base (auditedFrameImpl_project_step k mclose) oa s

end Zkpc.Games

#print axioms Zkpc.Games.auditedFrameImpl_project_step
#print axioms Zkpc.Games.auditedFrameImpl_bad_monotone
#print axioms Zkpc.Games.auditAfter_secret_length_le
#print axioms Zkpc.Games.auditAfter_slope_length_le
#print axioms Zkpc.Games.auditAfter_honest_length_le
#print axioms Zkpc.Games.auditedFrameImpl_run_project
