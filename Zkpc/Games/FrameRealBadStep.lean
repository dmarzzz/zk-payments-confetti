import Zkpc.Games.FrameRealBadTransfer

/-!
# Stage-1 per-operation coupling steps (Spec.md §7 T7, route B)

This file discharges the per-operation cases of `RealDSStepCoupling`: from
`RealDSGood`-related states, each coupled real/deferred-slope oracle step
either returns equal answers with good-related next states or raises the
audited leakage event on both sides in the same step. The cases land here
one operation at a time; `Zkpc/Games/FrameRealBadTransfer.lean` consumes the
assembled predicate.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

/-! ## Component accessors of the coupling relation -/

namespace RealDSCoupled

variable {k : F} {r : AuditedFrameSt F M} {d : DSFrameSt F M}

omit [Field F] [SampleableType F] [DecidableEq M] in
theorem idx_eq (h : RealDSCoupled k r d) : d.ideal.idx = r.base.idx := by
  rw [← h.ideal]; rfl

omit [Field F] [SampleableType F] [DecidableEq M] in
theorem closed_eq (h : RealDSCoupled k r d) :
    d.ideal.closed = r.base.closed := by
  rw [← h.ideal]; rfl

omit [Field F] [SampleableType F] [DecidableEq M] in
theorem roX_eq (h : RealDSCoupled k r d) : d.ideal.roX = r.base.roX := by
  rw [← h.ideal]; rfl

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- Public `H_a` entries agree away from the hidden secret. -/
theorem roA_pub (h : RealDSCoupled k r d) {kq : F} (i : ℕ) (hk : kq ≠ k) :
    d.ideal.roA (kq, i) = r.base.roA (kq, i) := by
  rw [← h.ideal]; simp [idealizeFrame, hk]

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- Public `H_e` entries agree away from the hidden secret. -/
theorem roE_pub (h : RealDSCoupled k r d) {kq : F} (e : ℕ) (hk : kq ≠ k) :
    d.ideal.roE (kq, e) = r.base.roE (kq, e) := by
  rw [← h.ideal]; simp [idealizeFrame, hk]

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- Public `H_id` entries agree away from the hidden secret. -/
theorem roId_pub (h : RealDSCoupled k r d) {kq : F} (hk : kq ≠ k) :
    d.ideal.roId kq = r.base.roId kq := by
  rw [← h.ideal]; simp [idealizeFrame, hk]

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- Public `H_nf` entries agree away from the recorded honest slopes. -/
theorem roNf_pub (h : RealDSCoupled k r d) {aq : F}
    (ha : aq ∉ r.audit.honestSlopes) :
    d.ideal.roNf aq = r.base.roNf aq := by
  rw [← h.ideal]; simp [idealizeFrame, ha]

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- The private per-index nullifier cache is the real hidden composition. -/
theorem honestNf_eq (h : RealDSCoupled k r d) (i : ℕ) :
    d.ideal.honestNf i = (r.base.roA (k, i)).bind r.base.roNf := by
  rw [← h.ideal]; rfl

end RealDSCoupled

/-! ## Coupled lazy-oracle helpers -/

/-- Couple two lazy random-oracle reads whose caches agree at the queried
key: a hit continues deterministically on both sides, a miss continues with
one shared fresh uniform draw and the two updated caches. -/
theorem relTriple_lazyRO_bind {α : Type} [DecidableEq α]
    {γ δ : Type} (C₁ C₂ : α → Option F) (q : α) (hq : C₁ q = C₂ q)
    (f : F × (α → Option F) → ProbComp γ)
    (g : F × (α → Option F) → ProbComp δ) (S : γ → δ → Prop)
    (hsome : ∀ v, C₁ q = some v → RelTriple (f (v, C₁)) (g (v, C₂)) S)
    (hnone : C₁ q = none → ∀ v,
      RelTriple (f (v, Function.update C₁ q (some v)))
        (g (v, Function.update C₂ q (some v))) S) :
    RelTriple (lazyRO C₁ q >>= f) (lazyRO C₂ q >>= g) S := by
  unfold lazyRO
  cases hC : C₁ q with
  | some v =>
      rw [hq] at hC
      rw [hC]
      rw [hq] at hsome
      simpa using hsome v hC
  | none =>
      rw [hq] at hC
      rw [hC]
      rw [hq] at hnone
      simp only [bind_assoc, pure_bind]
      exact relTriple_bind relTriple_uniformSample_refl
        fun a b hab => by cases hab; exact hnone hC a

/-- Couple two lazy digest-oracle reads with equal caches at the queried
message. -/
theorem relTriple_lazyROX_bind {γ δ : Type}
    (C₁ C₂ : M → Option F) (m : M) (hq : C₁ m = C₂ m)
    (f : F × (M → Option F) → ProbComp γ)
    (g : F × (M → Option F) → ProbComp δ) (S : γ → δ → Prop)
    (hsome : ∀ v, C₁ m = some v → RelTriple (f (v, C₁)) (g (v, C₂)) S)
    (hnone : C₁ m = none → ∀ raw : F,
      RelTriple
        (f (nonzeroDigest raw,
          Function.update C₁ m (some (nonzeroDigest raw))))
        (g (nonzeroDigest raw,
          Function.update C₂ m (some (nonzeroDigest raw)))) S) :
    RelTriple (lazyROX C₁ m >>= f) (lazyROX C₂ m >>= g) S := by
  unfold lazyROX
  cases hC : C₁ m with
  | some v =>
      rw [hq] at hC
      rw [hC]
      rw [hq] at hsome
      simpa using hsome v hC
  | none =>
      rw [hq] at hC
      rw [hC]
      rw [hq] at hnone
      simp only [bind_assoc, pure_bind]
      exact relTriple_bind relTriple_uniformSample_refl
        fun a b hab => by cases hab; exact hnone hC a

/-- Jump to the both-absorbed branch of the step postcondition from unary
support facts. -/
theorem relTriple_bothBad {k : F} {γ : Type}
    {oa : ProbComp (γ × AuditedFrameSt F M)}
    {ob : ProbComp (γ × DSFrameSt F M)}
    (h₁ : ∀ z ∈ support oa, FrameLeakBad k z.2.audit)
    (h₂ : ∀ z ∈ support ob, FrameLeakBad k z.2.audit) :
    RelTriple oa ob
      (fun p₁ p₂ => (p₁.1 = p₂.1 ∧ RealDSGood k p₁.2 p₂.2) ∨
        (FrameLeakBad k p₁.2.audit ∧ FrameLeakBad k p₂.2.audit)) :=
  relTriple_post_mono (relTriple_prod h₁ h₂) fun _ _ h => Or.inr h

/-! ## Reduction equations for the lazy primitives -/

omit [Field F] in
/-- Cache-hit reduction of `lazyRO`. -/
theorem lazyRO_of_some {α : Type} [DecidableEq α] {cache : α → Option F}
    {q : α} {v : F} (h : cache q = some v) :
    lazyRO cache q = pure (v, cache) := by
  unfold lazyRO
  rw [h]

omit [Field F] in
/-- Cache-miss reduction of `lazyRO`. -/
theorem lazyRO_of_none {α : Type} [DecidableEq α] {cache : α → Option F}
    {q : α} (h : cache q = none) :
    lazyRO cache q = ($ᵗ F) >>= fun v =>
      pure (v, Function.update cache q (some v)) := by
  unfold lazyRO
  rw [h]

omit [Field F] [DecidableEq F] in
/-- Pinned reduction of `dsTouch`. -/
theorem dsTouch_of_some {gs : ℕ → Option F} {audit : FrameAudit F} {i : ℕ}
    {a : F} (h : gs i = some a) :
    dsTouch gs audit i = pure (a, gs, audit) := by
  unfold dsTouch
  rw [h]

omit [Field F] [DecidableEq F] in
/-- Fresh reduction of `dsTouch`. -/
theorem dsTouch_of_none {gs : ℕ → Option F} {audit : FrameAudit F} {i : ℕ}
    (h : gs i = none) :
    dsTouch gs audit i = ($ᵗ F) >>= fun v =>
      pure (v, Function.update gs i (some v),
        { audit with honestSlopes := v :: audit.honestSlopes }) := by
  unfold dsTouch
  rw [h]

/-! ## Per-operation step couplings: public random oracles -/

/-- The step postcondition, abbreviated. -/
private def StepPost (k : F) (γ : Type) :
    γ × AuditedFrameSt F M → γ × DSFrameSt F M → Prop :=
  fun p₁ p₂ => (p₁.1 = p₂.1 ∧ RealDSGood k p₁.2 p₂.2) ∨
    (FrameLeakBad k p₁.2.audit ∧ FrameLeakBad k p₂.2.audit)

/-- **Step coupling, `roX`.** Digest queries are answer- and audit-identical
under the coupling and preserve every good clause. -/
theorem realDSStep_roX (k : F) (mclose m : M)
    (r : AuditedFrameSt F M) (d : DSFrameSt F M) (hg : RealDSGood k r d) :
    RelTriple (((auditedFrameImpl k mclose) (.roX m)).run r)
      (((dsFrameImpl k mclose) (.roX m)).run d)
      (StepPost k ((frameSpec F M).Range (.roX m))) := by
  obtain ⟨hc, hcov, hnfcov, hinj, hbad⟩ := hg
  have hL : ((auditedFrameImpl k mclose) (.roX m)).run r
      = lazyROX r.base.roX m >>= fun p =>
          pure (p.1, (⟨{ r.base with roX := p.2 }, r.audit⟩ :
            AuditedFrameSt F M)) := by
    simp [auditedFrameImpl, frameImpl, StateT.run_mk, bind_assoc, auditAfter]
  have hR : ((dsFrameImpl k mclose) (.roX m)).run d
      = lazyROX d.ideal.roX m >>= fun p =>
          pure (p.1, (⟨{ d.ideal with roX := p.2 }, d.slope, d.audit⟩ :
            DSFrameSt F M)) := by
    simp [dsFrameImpl, StateT.run_mk]
  rw [hL, hR]
  have hkey : r.base.roX m = d.ideal.roX m := by rw [hc.roX_eq]
  have hgood : ∀ cX : M → Option F,
      RealDSGood k (⟨{ r.base with roX := cX }, r.audit⟩ : AuditedFrameSt F M)
        (⟨{ d.ideal with roX := cX }, d.slope, d.audit⟩ : DSFrameSt F M) := by
    intro cX
    refine ⟨⟨?_, hc.hiddenSlope, hc.audit⟩, hcov, hnfcov, hinj, hbad⟩
    rw [← hc.ideal]
    apply IdealFrameSt.ext <;> rfl
  refine relTriple_lazyROX_bind _ _ m hkey _ _ _ ?_ ?_
  · intro v hv
    refine relTriple_pure_pure (Or.inl ⟨rfl, ?_⟩)
    simpa [hc.roX_eq] using hgood d.ideal.roX
  · intro hnone raw
    refine relTriple_pure_pure (Or.inl ⟨rfl, ?_⟩)
    have := hgood (Function.update r.base.roX m
      (some (nonzeroDigest raw)))
    simpa [hc.roX_eq] using this

/-- **Step coupling, `roE`.** An epoch probe at the hidden secret raises the
leakage event on both sides in this step; away from the secret the step is
identical and clause-preserving. -/
theorem realDSStep_roE (k : F) (mclose : M) (kq : F) (e : ℕ)
    (r : AuditedFrameSt F M) (d : DSFrameSt F M) (hg : RealDSGood k r d) :
    RelTriple (((auditedFrameImpl k mclose) (.roE kq e)).run r)
      (((dsFrameImpl k mclose) (.roE kq e)).run d)
      (StepPost k ((frameSpec F M).Range (.roE kq e))) := by
  obtain ⟨hc, hcov, hnfcov, hinj, hbad⟩ := hg
  have hL : ((auditedFrameImpl k mclose) (.roE kq e)).run r
      = lazyRO r.base.roE (kq, e) >>= fun p =>
          pure (p.1, (⟨{ r.base with roE := p.2 },
            { r.audit with secretProbes := kq :: r.audit.secretProbes }⟩ :
            AuditedFrameSt F M)) := by
    simp [auditedFrameImpl, frameImpl, StateT.run_mk, bind_assoc, auditAfter]
  have hR : ((dsFrameImpl k mclose) (.roE kq e)).run d
      = lazyRO d.ideal.roE (kq, e) >>= fun p =>
          pure (p.1, (⟨{ d.ideal with roE := p.2 }, d.slope,
            { d.audit with secretProbes := kq :: d.audit.secretProbes }⟩ :
            DSFrameSt F M)) := by
    simp [dsFrameImpl, StateT.run_mk]
  rw [hL, hR]
  by_cases hk : kq = k
  · subst hk
    refine relTriple_bothBad ?_ ?_
    · intro z hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.secret_self kq r.audit
    · intro z hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.secret_self kq d.audit
  · have hkey : r.base.roE (kq, e) = d.ideal.roE (kq, e) :=
      (hc.roE_pub e hk).symm
    have haudit : ¬ FrameLeakBad k
        { r.audit with secretProbes := kq :: r.audit.secretProbes } := by
      intro h
      rcases h with h | h | h
      · rcases List.mem_cons.1 h with h | h
        · exact hk h.symm
        · exact hbad (Or.inl h)
      · exact hbad (Or.inr (Or.inl h))
      · exact hbad (Or.inr (Or.inr h))
    refine relTriple_lazyRO_bind _ _ (kq, e) hkey _ _ _ ?_ ?_
    · intro v hv
      refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, hc.hiddenSlope,
        by rw [hc.audit]⟩, hcov, hnfcov, hinj, haudit⟩⟩)
      rw [← hc.ideal]
      apply IdealFrameSt.ext <;> rfl
    · intro hnone v
      refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, hc.hiddenSlope,
        by rw [hc.audit]⟩, hcov, hnfcov, hinj, haudit⟩⟩)
      rw [← hc.ideal]
      apply IdealFrameSt.ext <;> try rfl
      exact maskFirst_update_of_ne r.base.roE k kq v e hk

/-- **Step coupling, `roA`.** A direct `H_a` probe at the hidden secret
raises the leakage event on both sides in this step; away from the secret
the step is identical and clause-preserving. -/
theorem realDSStep_roA (k : F) (mclose : M) (kq : F) (i : ℕ)
    (r : AuditedFrameSt F M) (d : DSFrameSt F M) (hg : RealDSGood k r d) :
    RelTriple (((auditedFrameImpl k mclose) (.roA kq i)).run r)
      (((dsFrameImpl k mclose) (.roA kq i)).run d)
      (StepPost k ((frameSpec F M).Range (.roA kq i))) := by
  obtain ⟨hc, hcov, hnfcov, hinj, hbad⟩ := hg
  have hL : ((auditedFrameImpl k mclose) (.roA kq i)).run r
      = lazyRO r.base.roA (kq, i) >>= fun p =>
          pure (p.1, (⟨{ r.base with roA := p.2 },
            { r.audit with secretProbes := kq :: r.audit.secretProbes }⟩ :
            AuditedFrameSt F M)) := by
    simp [auditedFrameImpl, frameImpl, StateT.run_mk, bind_assoc, auditAfter]
  have hR : ((dsFrameImpl k mclose) (.roA kq i)).run d
      = lazyRO d.ideal.roA (kq, i) >>= fun p =>
          pure (p.1, (⟨{ d.ideal with roA := p.2 }, d.slope,
            { d.audit with secretProbes := kq :: d.audit.secretProbes }⟩ :
            DSFrameSt F M)) := by
    simp [dsFrameImpl, StateT.run_mk]
  rw [hL, hR]
  by_cases hk : kq = k
  · subst hk
    refine relTriple_bothBad ?_ ?_
    · intro z hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.secret_self kq r.audit
    · intro z hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.secret_self kq d.audit
  · have hkey : r.base.roA (kq, i) = d.ideal.roA (kq, i) :=
      (hc.roA_pub i hk).symm
    have haudit : ¬ FrameLeakBad k
        { r.audit with secretProbes := kq :: r.audit.secretProbes } := by
      intro h
      rcases h with h | h | h
      · rcases List.mem_cons.1 h with h | h
        · exact hk h.symm
        · exact hbad (Or.inl h)
      · exact hbad (Or.inr (Or.inl h))
      · exact hbad (Or.inr (Or.inr h))
    refine relTriple_lazyRO_bind _ _ (kq, i) hkey _ _ _ ?_ ?_
    · intro v hv
      refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, hc.hiddenSlope,
        by rw [hc.audit]⟩, hcov, hnfcov, hinj, haudit⟩⟩)
      rw [← hc.ideal]
      apply IdealFrameSt.ext <;> rfl
    · intro hnone v
      have hhid : ∀ j, Function.update r.base.roA (kq, i) (some v) (k, j)
          = r.base.roA (k, j) := fun j =>
        update_pair_at_hidden_of_ne r.base.roA k kq v i j hk
      refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, ?_,
        by rw [hc.audit]⟩, hcov, hnfcov, ?_, haudit⟩⟩)
      · rw [← hc.ideal]
        apply IdealFrameSt.ext <;> try rfl
        · exact maskFirst_update_of_ne r.base.roA k kq v i hk
        · funext j
          show (Function.update r.base.roA (kq, i) (some v) (k, j)).bind
              r.base.roNf = (r.base.roA (k, j)).bind r.base.roNf
          rw [hhid j]
      · intro j
        show Function.update r.base.roA (kq, i) (some v) (k, j) = d.slope j
        rw [hhid j]
        exact hc.hiddenSlope j
      · intro j₁ j₂ a h₁ h₂
        apply hinj j₁ j₂ a
        · simpa only [hhid j₁] using h₁
        · simpa only [hhid j₂] using h₂

/-- **Step coupling, `roId`.** An identity-preimage probe at the hidden
secret raises the leakage event on both sides in this step (this is also
where the real handler's programmed `H_id(k) = cm` entry diverges from the
deferred handler — inside the absorbed branch); away from the secret the
step is identical and clause-preserving. -/
theorem realDSStep_roId (k : F) (mclose : M) (kq : F)
    (r : AuditedFrameSt F M) (d : DSFrameSt F M) (hg : RealDSGood k r d) :
    RelTriple (((auditedFrameImpl k mclose) (.roId kq)).run r)
      (((dsFrameImpl k mclose) (.roId kq)).run d)
      (StepPost k ((frameSpec F M).Range (.roId kq))) := by
  obtain ⟨hc, hcov, hnfcov, hinj, hbad⟩ := hg
  have hL : ((auditedFrameImpl k mclose) (.roId kq)).run r
      = lazyRO r.base.roId kq >>= fun p =>
          pure (p.1, (⟨{ r.base with roId := p.2 },
            { r.audit with secretProbes := kq :: r.audit.secretProbes }⟩ :
            AuditedFrameSt F M)) := by
    simp [auditedFrameImpl, frameImpl, StateT.run_mk, bind_assoc, auditAfter]
  have hR : ((dsFrameImpl k mclose) (.roId kq)).run d
      = lazyRO d.ideal.roId kq >>= fun p =>
          pure (p.1, (⟨{ d.ideal with roId := p.2 }, d.slope,
            { d.audit with secretProbes := kq :: d.audit.secretProbes }⟩ :
            DSFrameSt F M)) := by
    simp [dsFrameImpl, StateT.run_mk]
  rw [hL, hR]
  by_cases hk : kq = k
  · subst hk
    refine relTriple_bothBad ?_ ?_
    · intro z hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.secret_self kq r.audit
    · intro z hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.secret_self kq d.audit
  · have hkey : r.base.roId kq = d.ideal.roId kq := (hc.roId_pub hk).symm
    have haudit : ¬ FrameLeakBad k
        { r.audit with secretProbes := kq :: r.audit.secretProbes } := by
      intro h
      rcases h with h | h | h
      · rcases List.mem_cons.1 h with h | h
        · exact hk h.symm
        · exact hbad (Or.inl h)
      · exact hbad (Or.inr (Or.inl h))
      · exact hbad (Or.inr (Or.inr h))
    refine relTriple_lazyRO_bind _ _ kq hkey _ _ _ ?_ ?_
    · intro v hv
      refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, hc.hiddenSlope,
        by rw [hc.audit]⟩, hcov, hnfcov, hinj, haudit⟩⟩)
      rw [← hc.ideal]
      apply IdealFrameSt.ext <;> rfl
    · intro hnone v
      refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, hc.hiddenSlope,
        by rw [hc.audit]⟩, hcov, hnfcov, hinj, haudit⟩⟩)
      rw [← hc.ideal]
      apply IdealFrameSt.ext <;> try rfl
      exact maskKey_update_of_ne r.base.roId k kq v hk

/-- **Step coupling, `roNf`.** A nullifier-preimage probe at a recorded
honest slope raises the slope-hit branch of the leakage event on both sides
in this step (this is where the real handler's hidden `H_nf` entries at
honest slopes diverge from the deferred handler — inside the absorbed
branch); away from the recorded slopes the caches agree, the step is
identical, and audit completeness confines the update away from every
hidden composition. -/
theorem realDSStep_roNf (k : F) (mclose : M) (aq : F)
    (r : AuditedFrameSt F M) (d : DSFrameSt F M) (hg : RealDSGood k r d) :
    RelTriple (((auditedFrameImpl k mclose) (.roNf aq)).run r)
      (((dsFrameImpl k mclose) (.roNf aq)).run d)
      (StepPost k ((frameSpec F M).Range (.roNf aq))) := by
  obtain ⟨hc, hcov, hnfcov, hinj, hbad⟩ := hg
  have hL : ((auditedFrameImpl k mclose) (.roNf aq)).run r
      = lazyRO r.base.roNf aq >>= fun p =>
          pure (p.1, (⟨{ r.base with roNf := p.2 },
            { r.audit with slopeProbes := aq :: r.audit.slopeProbes }⟩ :
            AuditedFrameSt F M)) := by
    simp [auditedFrameImpl, frameImpl, StateT.run_mk, auditAfter]
  have hR : ((dsFrameImpl k mclose) (.roNf aq)).run d
      = lazyRO d.ideal.roNf aq >>= fun p =>
          pure (p.1, (⟨{ d.ideal with roNf := p.2 }, d.slope,
            { d.audit with slopeProbes := aq :: d.audit.slopeProbes }⟩ :
            DSFrameSt F M)) := by
    simp [dsFrameImpl, StateT.run_mk]
  rw [hL, hR]
  by_cases haq : aq ∈ r.audit.honestSlopes
  · refine relTriple_bothBad ?_ ?_
    · intro z hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.slope_hit k aq r.audit haq
    · intro z hz
      obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact FrameLeakBad.slope_hit k aq d.audit (hc.audit ▸ haq)
  · have hkey : r.base.roNf aq = d.ideal.roNf aq := (hc.roNf_pub haq).symm
    have haudit : ¬ FrameLeakBad k
        { r.audit with slopeProbes := aq :: r.audit.slopeProbes } := by
      intro h
      rcases h with h | ⟨s, hs, hs2⟩ | h
      · exact hbad (Or.inl h)
      · rcases List.mem_cons.1 hs with hs | hs
        · subst hs
          exact haq hs2
        · exact hbad (Or.inr (Or.inl ⟨s, hs, hs2⟩))
      · exact hbad (Or.inr (Or.inr h))
    have hcomplete : FrameAuditComplete k r := hc.frameAuditComplete hcov
    refine relTriple_lazyRO_bind _ _ aq hkey _ _ _ ?_ ?_
    · intro v hv
      refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, hc.hiddenSlope,
        by rw [hc.audit]⟩, hcov, ?_, hinj, haudit⟩⟩)
      · rw [← hc.ideal]
        apply IdealFrameSt.ext <;> rfl
      · intro q w hq
        rcases hnfcov q w hq with h | h
        · exact Or.inl (List.mem_cons_of_mem aq h)
        · exact Or.inr h
    · intro hnone v
      refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, hc.hiddenSlope,
        by rw [hc.audit]⟩, hcov, ?_, hinj, haudit⟩⟩)
      · rw [← hc.ideal]
        apply IdealFrameSt.ext <;> try rfl
        · exact maskSlopes_update_of_not_mem r.base.roNf
            r.audit.honestSlopes aq v haq
        · funext j
          exact update_roNf_at_honest_of_complete k aq v r hcomplete haq j
      · intro q w hq
        have hq' : Function.update r.base.roNf aq (some v) q = some w := hq
        by_cases hqa : q = aq
        · subst hqa
          exact Or.inl (List.mem_cons_self)
        · rw [Function.update_of_ne hqa] at hq'
          rcases hnfcov q w hq' with h | h
          · exact Or.inl (List.mem_cons_of_mem aq h)
          · exact Or.inr h

/-- A spend request after closure is an exact no-op in both handlers, hence
preserves the entire good-state relation without invoking slope sampling. -/
theorem realDSStep_spend_closed (k : F) (mclose m : M)
    (r : AuditedFrameSt F M) (d : DSFrameSt F M)
    (hg : RealDSGood k r d) (hcl : r.base.closed = true) :
    RelTriple (((auditedFrameImpl k mclose) (.spend m)).run r)
      (((dsFrameImpl k mclose) (.spend m)).run d)
      (StepPost k ((frameSpec F M).Range (.spend m))) := by
  have hdcl : d.ideal.closed = true := by
    rw [RealDSCoupled.closed_eq hg.1]
    exact hcl
  simpa [auditedFrameImpl, dsFrameImpl, frameImpl, StateT.run_mk, hcl, hdcl,
    auditAfter] using
      (relTriple_pure_pure (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := StepPost k ((frameSpec F M).Range (.spend m)))
        (Or.inl ⟨rfl, hg⟩))

omit [Field F] [SampleableType F] [DecidableEq M] in
/-- A fresh honest slope that misses all recorded probes and slopes
preserves goodness of the audit. -/
theorem not_frameLeakBad_honest_cons {k a : F} {audit : FrameAudit F}
    (hbad : ¬ FrameLeakBad k audit)
    (hp : a ∉ audit.slopeProbes) (hh : a ∉ audit.honestSlopes) :
    ¬ FrameLeakBad k
      { audit with honestSlopes := a :: audit.honestSlopes } := by
  intro h
  rcases h with h | ⟨s, hs, hs2⟩ | h
  · exact hbad (Or.inl h)
  · rcases List.mem_cons.1 hs2 with hs2 | hs2
    · subst hs2
      exact hp hs
    · exact hbad (Or.inr (Or.inl ⟨s, hs, hs2⟩))
  · rcases List.nodup_cons.not.1 h with h'
    by_cases hmem : a ∈ audit.honestSlopes
    · exact hh hmem
    · have : ¬ audit.honestSlopes.Nodup := by
        intro hnd
        exact h (List.nodup_cons.2 ⟨hmem, hnd⟩)
      exact hbad (Or.inr (Or.inr this))

/-- **Step coupling, `nfAt`.** The MC20 reveal at a pinned slope replays the
shared cached nullifier (or extends it identically); at a fresh index the
real slope draw and the deferred touch draw couple to the same value, whose
collisions with recorded probes or slopes raise the leakage event on both
sides, and whose good branch extends every clause of the relation. -/
theorem realDSStep_nfAt (k : F) (mclose : M) (i : ℕ)
    (r : AuditedFrameSt F M) (d : DSFrameSt F M) (hg : RealDSGood k r d) :
    RelTriple (((auditedFrameImpl k mclose) (.nfAt i)).run r)
      (((dsFrameImpl k mclose) (.nfAt i)).run d)
      (StepPost k ((frameSpec F M).Range (.nfAt i))) := by
  have hg0 := hg
  obtain ⟨hc, hcov, hnfcov, hinj, hbad⟩ := hg
  have hcomplete : FrameAuditComplete k r := hc.frameAuditComplete hcov
  cases hpin : r.base.roA (k, i) with
  | some a =>
      have hpin' : d.slope i = some a := by
        rw [← hc.hiddenSlope i]; exact hpin
      have hnfd : d.ideal.honestNf i = r.base.roNf a := by
        rw [hc.honestNf_eq i, hpin]; rfl
      cases hnf : r.base.roNf a with
      | some nf =>
          have hL : ((auditedFrameImpl k mclose) (.nfAt i)).run r
              = pure (nf, r) := by
            simp [auditedFrameImpl, frameImpl, StateT.run_mk, auditAfter,
              lazyRO_of_some hpin, lazyRO_of_some hnf, hpin]
          have hR : ((dsFrameImpl k mclose) (.nfAt i)).run d
              = pure (nf, d) := by
            simp [dsFrameImpl, StateT.run_mk, dsTouch_of_some hpin',
              lazyRO_of_some (hnfd.trans hnf)]
          rw [hL, hR]
          exact relTriple_pure_pure (Or.inl ⟨rfl, hg0⟩)
      | none =>
          have hL : ((auditedFrameImpl k mclose) (.nfAt i)).run r
              = ($ᵗ F) >>= fun nf =>
                  pure (nf, (⟨{ r.base with
                    roNf := Function.update r.base.roNf a (some nf) },
                    r.audit⟩ : AuditedFrameSt F M)) := by
            simp [auditedFrameImpl, frameImpl, StateT.run_mk, auditAfter,
              lazyRO_of_some hpin, lazyRO_of_none hnf, hpin]
          have hR : ((dsFrameImpl k mclose) (.nfAt i)).run d
              = ($ᵗ F) >>= fun nf =>
                  pure (nf, (⟨{ d.ideal with
                    honestNf := Function.update d.ideal.honestNf i (some nf) },
                    d.slope, d.audit⟩ : DSFrameSt F M)) := by
            simp [dsFrameImpl, StateT.run_mk, dsTouch_of_some hpin',
              lazyRO_of_none (hnfd.trans hnf)]
          rw [hL, hR]
          have hahs : a ∈ r.audit.honestSlopes := hcomplete i a hpin
          refine relTriple_bind relTriple_uniformSample_refl
            fun nf nf' hnf' => ?_
          cases hnf'
          refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, hc.hiddenSlope,
            by rw [hc.audit]⟩, hcov, ?_, hinj, hbad⟩⟩)
          · rw [← hc.ideal]
            apply IdealFrameSt.ext <;> try rfl
            · funext q
              show (if q ∈ r.audit.honestSlopes then none
                  else Function.update r.base.roNf a (some nf) q)
                = (if q ∈ r.audit.honestSlopes then none
                    else r.base.roNf q)
              by_cases hqa : q = a
              · subst hqa
                simp [hahs]
              · rw [Function.update_of_ne hqa]
            · funext j
              show (r.base.roA (k, j)).bind
                  (Function.update r.base.roNf a (some nf))
                = Function.update
                    (fun j' => (r.base.roA (k, j')).bind r.base.roNf)
                    i (some nf) j
              by_cases hji : j = i
              · subst hji
                simp [hpin, Function.update_self]
              · rw [Function.update_of_ne hji]
                cases hja : r.base.roA (k, j) with
                | none => rfl
                | some aj =>
                    have hne : aj ≠ a := fun h =>
                      hji (hinj j i a (h ▸ hja) hpin)
                    simp [Option.bind_some, Function.update_of_ne hne]
          · intro q w hq
            have hq' : Function.update r.base.roNf a (some nf) q
                = some w := hq
            by_cases hqa : q = a
            · subst hqa
              exact Or.inr hahs
            · rw [Function.update_of_ne hqa] at hq'
              exact hnfcov q w hq'
  | none =>
      have hpin' : d.slope i = none := by
        rw [← hc.hiddenSlope i]; exact hpin
      have hnfd : d.ideal.honestNf i = none := by
        rw [hc.honestNf_eq i, hpin]; rfl
      have hL : ((auditedFrameImpl k mclose) (.nfAt i)).run r
          = ($ᵗ F) >>= fun a =>
              lazyRO r.base.roNf a >>= fun pn =>
                pure (pn.1, (⟨{ r.base with
                  roA := Function.update r.base.roA (k, i) (some a),
                  roNf := pn.2 },
                  { r.audit with
                    honestSlopes := a :: r.audit.honestSlopes }⟩ :
                  AuditedFrameSt F M)) := by
        simp [auditedFrameImpl, frameImpl, StateT.run_mk, auditAfter,
          lazyRO_of_none hpin, hpin, Function.update_self]
      have hR : ((dsFrameImpl k mclose) (.nfAt i)).run d
          = ($ᵗ F) >>= fun nf =>
              ($ᵗ F) >>= fun v =>
                pure (nf, (⟨{ d.ideal with
                  honestNf := Function.update d.ideal.honestNf i (some nf) },
                  Function.update d.slope i (some v),
                  { d.audit with
                    honestSlopes := v :: d.audit.honestSlopes }⟩ :
                  DSFrameSt F M)) := by
        simp [dsFrameImpl, StateT.run_mk, dsTouch_of_none hpin',
          lazyRO_of_none hnfd]
      rw [hL, hR]
      refine relTriple_of_evalDist_eq_right
        (OracleComp.DeferredSampling.evalDist_bind_comm ($ᵗ F) ($ᵗ F)
          (fun v nf =>
            pure (nf, (⟨{ d.ideal with
              honestNf := Function.update d.ideal.honestNf i (some nf) },
              Function.update d.slope i (some v),
              { d.audit with
                honestSlopes := v :: d.audit.honestSlopes }⟩ :
              DSFrameSt F M)))) ?_
      refine relTriple_bind relTriple_uniformSample_refl
        fun a v hav => ?_
      cases hav
      by_cases hmem : a ∈ r.audit.slopeProbes ∨ a ∈ r.audit.honestSlopes
      · refine relTriple_bothBad ?_ ?_
        · intro z hz
          obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
          rw [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact FrameLeakBad.honest_collision k a r.audit hmem
        · intro z hz
          obtain ⟨p, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
          rw [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact FrameLeakBad.honest_collision k a d.audit (hc.audit ▸ hmem)
      · push_neg at hmem
        obtain ⟨hmp, hmh⟩ := hmem
        have hnfa : r.base.roNf a = none := by
          cases hnfa : r.base.roNf a with
          | none => rfl
          | some w =>
              rcases hnfcov a w hnfa with h | h
              · exact absurd h hmp
              · exact absurd h hmh
        rw [lazyRO_of_none hnfa]
        simp only [bind_assoc, pure_bind]
        refine relTriple_bind relTriple_uniformSample_refl
          fun nf nf' hnf' => ?_
        cases hnf'
        refine relTriple_pure_pure (Or.inl ⟨rfl, ⟨⟨?_, ?_,
          by rw [hc.audit]⟩, ?_, ?_, ?_,
          not_frameLeakBad_honest_cons hbad hmp hmh⟩⟩)
        · rw [← hc.ideal]
          apply IdealFrameSt.ext <;> try rfl
          · funext q
            show (if q.1 = k then none
                else Function.update r.base.roA (k, i) (some a) q)
              = (if q.1 = k then none else r.base.roA q)
            by_cases hq1 : q.1 = k
            · simp [hq1]
            · have hqne : q ≠ (k, i) := fun h => hq1 (by rw [h])
              simp [hq1, Function.update_of_ne hqne]
          · funext q
            show (if q ∈ a :: r.audit.honestSlopes then none
                else Function.update r.base.roNf a (some nf) q)
              = (if q ∈ r.audit.honestSlopes then none
                  else r.base.roNf q)
            by_cases hqa : q = a
            · subst hqa
              simp [List.mem_cons, hmh, hnfa]
            · by_cases hqh : q ∈ r.audit.honestSlopes
              · simp [List.mem_cons, hqh, hqa]
              · simp [List.mem_cons, hqh, hqa, Function.update_of_ne hqa]
          · funext j
            show (Function.update r.base.roA (k, i) (some a) (k, j)).bind
                (Function.update r.base.roNf a (some nf))
              = Function.update
                  (fun j' => (r.base.roA (k, j')).bind r.base.roNf)
                  i (some nf) j
            by_cases hji : j = i
            · subst hji
              simp [Function.update_self]
            · have hne : (k, j) ≠ (k, i) := fun h =>
                hji (congrArg Prod.snd h)
              rw [Function.update_of_ne hne, Function.update_of_ne hji]
              cases hja : r.base.roA (k, j) with
              | none => rfl
              | some aj =>
                  have haj : aj ∈ r.audit.honestSlopes := hcomplete j aj hja
                  have hane : aj ≠ a := fun h => hmh (h ▸ haj)
                  simp [Option.bind_some, Function.update_of_ne hane]
        · intro j
          show Function.update r.base.roA (k, i) (some a) (k, j)
            = Function.update d.slope i (some a) j
          by_cases hji : j = i
          · subst hji
            simp [Function.update_self]
          · have hne : (k, j) ≠ (k, i) := fun h => hji (congrArg Prod.snd h)
            rw [Function.update_of_ne hne, Function.update_of_ne hji]
            exact hc.hiddenSlope j
        · intro j b hb
          have hb' : Function.update d.slope i (some a) j = some b := hb
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self] at hb'
            cases hb'
            exact List.mem_cons_self
          · rw [Function.update_of_ne hji] at hb'
            exact List.mem_cons_of_mem a (hcov j b hb')
        · intro q w hq
          have hq' : Function.update r.base.roNf a (some nf) q = some w := hq
          by_cases hqa : q = a
          · subst hqa
            exact Or.inr List.mem_cons_self
          · rw [Function.update_of_ne hqa] at hq'
            rcases hnfcov q w hq' with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons_of_mem a h)
        · intro j₁ j₂ b h₁ h₂
          have h₁' : Function.update r.base.roA (k, i) (some a) (k, j₁)
              = some b := h₁
          have h₂' : Function.update r.base.roA (k, i) (some a) (k, j₂)
              = some b := h₂
          by_cases hj₁ : j₁ = i <;> by_cases hj₂ : j₂ = i
          · rw [hj₁, hj₂]
          · exfalso
            have hba : b = a := by
              rw [hj₁, Function.update_self] at h₁'
              exact (Option.some.inj h₁').symm
            subst b
            have hne : (k, j₂) ≠ (k, i) := fun h =>
              hj₂ (congrArg Prod.snd h)
            rw [Function.update_of_ne hne] at h₂'
            exact hmh (hcomplete j₂ a h₂')
          · exfalso
            have hba : b = a := by
              rw [hj₂, Function.update_self] at h₂'
              exact (Option.some.inj h₂').symm
            subst b
            have hne : (k, j₁) ≠ (k, i) := fun h =>
              hj₁ (congrArg Prod.snd h)
            rw [Function.update_of_ne hne] at h₁'
            exact hmh (hcomplete j₁ a h₁')
          · have hne₁ : (k, j₁) ≠ (k, i) := fun h =>
              hj₁ (congrArg Prod.snd h)
            have hne₂ : (k, j₂) ≠ (k, i) := fun h =>
              hj₂ (congrArg Prod.snd h)
            rw [Function.update_of_ne hne₁] at h₁'
            rw [Function.update_of_ne hne₂] at h₂'
            exact hinj j₁ j₂ b h₁' h₂'

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.realDSStep_roX
#print axioms Zkpc.Games.realDSStep_roE
#print axioms Zkpc.Games.realDSStep_roA
#print axioms Zkpc.Games.realDSStep_roId
#print axioms Zkpc.Games.realDSStep_roNf
#print axioms Zkpc.Games.realDSStep_spend_closed
#print axioms Zkpc.Games.realDSStep_nfAt
