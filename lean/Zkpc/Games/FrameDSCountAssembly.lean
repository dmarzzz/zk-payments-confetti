import Zkpc.Games.FrameDSCount

/-!
# Assembly of deferred FRAME shadow leaves into `DSBadMassLe`

`FrameDSCount` proves the quantitative bound for one fixed k-free shadow
leaf.  This file packages the exact endpoint required from the adaptive
handler reparameterization and proves that no further probability or budget
bookkeeping remains once that endpoint is supplied.
-/

open OracleSpec OracleComp

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Fintype F]
variable {M : Type} [DecidableEq M]

/-- One well-formed leaf of the k-free deferred-run decomposition. -/
structure DSShadowLeaf (F : Type) [Field F] where
  direct : List F
  probes : List F
  shadow : List (DSEntry F)
  tapeLength : ℕ
  x_ne_zero : ∀ e ∈ shadow, e.XNe0
  separated : shadow.Pairwise DSEntry.Sep
  coord_lt : ∀ j ∈ entryCoords shadow, j < tapeLength
  coord_nodup : (entryCoords shadow).Nodup

/-- Independent tape-and-last-secret experiment associated to a leaf. -/
noncomputable def DSShadowLeaf.run (leaf : DSShadowLeaf F) : ProbComp (List F × F) :=
  drawList ($ᵗ F) leaf.tapeLength >>= fun vs =>
    ($ᵗ F) >>= fun k => pure (vs, k)

/-- Reconstructed leakage event of a leaf. -/
def DSShadowLeaf.bad (leaf : DSShadowLeaf F) (w : List F × F) : Prop :=
  FrameLeakBad w.2
    ⟨leaf.direct, leaf.probes,
      leaf.shadow.map (DSEntry.eval w.2 w.1)⟩

instance (leaf : DSShadowLeaf F) (w : List F × F) : Decidable (leaf.bad w) := by
  unfold DSShadowLeaf.bad
  infer_instance

/-- The fixed-leaf theorem in packaged form. -/
theorem DSShadowLeaf.bad_le (leaf : DSShadowLeaf F) :
    Pr[leaf.bad | leaf.run]
      ≤ ((leaf.direct.length + leaf.probes.length * leaf.shadow.length +
            scCount leaf.shadow : ℕ) : ENNReal) *
          (Fintype.card F : ENNReal)⁻¹ := by
  exact dsShadow_leaf_le leaf.direct leaf.probes leaf.shadow leaf.tapeLength
    leaf.x_ne_zero leaf.separated leaf.coord_lt leaf.coord_nodup

/-- **Adaptive run-to-shadow certificate.** `leaves` is a k-free outer
distribution produced by reparameterizing the deferred handler.  `bad_eq`
states exact preservation of the bad-event mass; `budget` is the structural
query-budget fact for every supported leaf.  These are precisely the two
outputs of the remaining handler induction. -/
structure DSShadowCertificate
    (mclose : M) (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) : Type where
  leaves : ProbComp (DSShadowLeaf F)
  bad_eq :
    Pr[fun w => FrameLeakBad w.1 w.2.2.audit | dsFrameJoint mclose A] =
      Pr[fun z : DSShadowLeaf F × (List F × F) => z.1.bad z.2 |
        leaves >>= fun leaf => leaf.run >>= fun w => pure (leaf, w)]
  budget : ∀ leaf ∈ support leaves,
    leaf.direct.length + leaf.probes.length * leaf.shadow.length +
        scCount leaf.shadow ≤ qb.total

/-- **Stage-2 closure.** An adaptive shadow decomposition immediately
discharges the complete deferred bad-mass residual. -/
theorem DSBadMassLe_of_shadowCertificate
    (mclose : M) (A : F → OracleComp (frameSpec F M) (Evidence F))
    (qb : FrameQueryBounds A) (cert : DSShadowCertificate mclose A qb) :
    DSBadMassLe mclose A qb := by
  unfold DSBadMassLe
  rw [cert.bad_eq]
  refine probEvent_bind_le_of_forall_le fun leaf hleaf => ?_
  rw [show (fun w : List F × F =>
      (pure (leaf, w) : ProbComp (DSShadowLeaf F × (List F × F)))) =
        pure ∘ (fun w : List F × F => (leaf, w)) from rfl,
    probEvent_bind_pure_comp]
  refine (leaf.bad_le).trans ?_
  exact mul_le_mul_right' (Nat.cast_le.2 (cert.budget leaf hleaf)) _

end Zkpc.Games

#print axioms Zkpc.Games.DSShadowLeaf.bad_le
#print axioms Zkpc.Games.DSBadMassLe_of_shadowCertificate
