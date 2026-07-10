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

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.realDSStep_roX
#print axioms Zkpc.Games.realDSStep_roE
#print axioms Zkpc.Games.realDSStep_roA
#print axioms Zkpc.Games.realDSStep_roId
#print axioms Zkpc.Games.realDSStep_roNf
