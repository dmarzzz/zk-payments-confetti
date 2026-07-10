import Zkpc.Games.FrameGoodSliceTape

/-!
# Adaptive pending-slope tape induction

This module contains the in-flight induction that turns the front law
`drawPendingSlopes pending` for `futureDSFrameImpl` into the slope-free
`pendingFrameImpl` run.  It is separate from the source-clean substrate so
the project root remains buildable while the signal cases are assembled.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

namespace Zkpc.Games

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {M : Type} [DecidableEq M]

section TapeInduction

variable [Fintype F]

set_option maxHeartbeats 600000 in
/-- A front tape of independent pending slopes turns the live deferred
handler into the slope-free pending handler for every adaptive adversary
computation. -/
theorem futureDSFrameImpl_run_evidence_eq_pending (k : F) (mclose : M) :
    ∀ (oa : OracleComp (frameSpec F M) (Evidence F))
      (p : PendingFrameSt F M), PendingValid p →
      RoXCacheNonzero p.ideal.roX →
      𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
        Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose) oa).run
          ⟨p.ideal, gs⟩] =
      𝒟[Prod.fst <$>
        (simulateQ (pendingFrameImpl mclose) oa).run p] := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure ev =>
      intro p hp hx0
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (drawPendingSlopes (F := F) p.pending)
        (probFailure_drawPendingSlopes p.pending) _
  | query_bind op cont ih =>
      intro p hp hx0
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        monadLift_self, StateT.run_bind, map_bind]
      cases op with
      | spend m =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk]
          by_cases hc : p.ideal.closed
          · simp only [hc, if_pos, pure_bind]
            simpa using ih none p hp hx0
          · simp only [hc, if_neg]
      | close =>
          simp [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk]
      | nfAt i =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.honestNf i
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun pn =>
                (if i < p.ideal.idx then
                    Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
                      (cont pn.1)).run
                        ⟨{ p.ideal with honestNf := pn.2 }, gs⟩
                  else lazyRO gs i >>= fun q =>
                    Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
                      (cont pn.1)).run
                        ⟨{ p.ideal with honestNf := pn.2 }, q.2⟩)] =
            𝒟[step >>= fun pn => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont pn.1)).run
                ⟨{ p.ideal with honestNf := pn.2 },
                  if i < p.ideal.idx ∨ i ∈ p.pending then p.pending
                  else i :: p.pending⟩]
          calc
            _ = 𝒟[step >>= fun pn =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  (if i < p.ideal.idx then
                      Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
                        (cont pn.1)).run
                          ⟨{ p.ideal with honestNf := pn.2 }, gs⟩
                    else lazyRO gs i >>= fun q =>
                      Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
                        (cont pn.1)).run
                          ⟨{ p.ideal with honestNf := pn.2 }, q.2⟩)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun pn => ?_
              let ideal' := { p.ideal with honestNf := pn.2 }
              let futureCont : (ℕ → Option F) → ProbComp (Evidence F) :=
                fun gs => Prod.fst <$>
                  (simulateQ (futureDSFrameImpl k mclose) (cont pn.1)).run
                    ⟨ideal', gs⟩
              by_cases hi : i < p.ideal.idx
              · simp only [hi, if_pos, true_or]
                simpa [ideal', futureCont] using ih pn.1
                  (⟨ideal', p.pending⟩ : PendingFrameSt F M) hp hx0
              · have hle : p.ideal.idx ≤ i := Nat.le_of_not_gt hi
                by_cases hm : i ∈ p.pending
                · simp only [hi, hm, if_false, or_true, if_true]
                  calc
                    𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                        lazyRO gs i >>= fun q => futureCont q.2] =
                      𝒟[drawPendingSlopes (F := F) p.pending >>=
                        futureCont] := by
                          refine evalDist_bind_congr
                            (mx := drawPendingSlopes (F := F) p.pending)
                              fun gs hgs => ?_
                          have hn : gs i ≠ none := by
                            intro hnone
                            exact ((drawPendingSlopes_support_none_iff
                              p.pending gs hgs i).1 hnone) hm
                          cases hsi : gs i with
                          | none => exact absurd hsi hn
                          | some a => simp [lazyRO, hsi]
                    _ = 𝒟[Prod.fst <$>
                        (simulateQ (pendingFrameImpl mclose) (cont pn.1)).run
                          ⟨ideal', p.pending⟩] := by
                            simpa [futureCont] using ih pn.1
                              (⟨ideal', p.pending⟩ : PendingFrameSt F M) hp hx0
                · simp only [hi, hm, if_false, or_false]
                  have hpcons : PendingValid
                      (⟨ideal', i :: p.pending⟩ : PendingFrameSt F M) := by
                    refine ⟨List.nodup_cons.mpr ⟨hm, hp.1⟩, ?_⟩
                    intro j hj
                    rcases List.mem_cons.mp hj with rfl | hj
                    · exact hle
                    · exact hp.2 j hj
                  calc
                    𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                        lazyRO gs i >>= fun q => futureCont q.2] =
                      𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                        ($ᵗ F) >>= fun a =>
                          futureCont (Function.update gs i (some a))] := by
                            refine evalDist_bind_congr
                              (mx := drawPendingSlopes (F := F) p.pending)
                                fun gs hgs => ?_
                            have hnone :=
                              (drawPendingSlopes_support_none_iff
                                p.pending gs hgs i).2 hm
                            simp [lazyRO, hnone]
                    _ = 𝒟[drawPendingSlopes (F := F) (i :: p.pending) >>=
                        futureCont] :=
                          evalDist_drawPendingSlopes_cons p.pending i futureCont
                    _ = 𝒟[Prod.fst <$>
                        (simulateQ (pendingFrameImpl mclose) (cont pn.1)).run
                          ⟨ideal', i :: p.pending⟩] := by
                            simpa [futureCont] using ih pn.1
                              (⟨ideal', i :: p.pending⟩ :
                                PendingFrameSt F M) hpcons hx0
      | roA kq i =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.roA (kq, i)
          let next : (F × (F × ℕ → Option F)) ×
              (ℕ → Option F) → ProbComp (Evidence F) :=
            fun z => Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run
                ⟨{ p.ideal with roA := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roA := a.2 }, p.pending⟩]
          calc
            _ = 𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun a => ?_
              simpa [next] using ih a.1
                (⟨{ p.ideal with roA := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp hx0
      | roX m =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyROX p.ideal.roX m
          let next : (F × (M → Option F)) × (ℕ → Option F) →
              ProbComp (Evidence F) := fun z =>
            Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run ⟨{ p.ideal with roX := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roX := a.2 }, p.pending⟩]
          calc
            _ = 𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr (mx := step) fun a ha => ?_
              have hxn := lazyROX_support_nonzero hx0 m a ha
              simpa [next] using ih a.1
                (⟨{ p.ideal with roX := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp hxn.2
      | roNf aq =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.roNf aq
          let next : (F × (F → Option F)) × (ℕ → Option F) →
              ProbComp (Evidence F) := fun z =>
            Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run ⟨{ p.ideal with roNf := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roNf := a.2 }, p.pending⟩]
          calc
            _ = 𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun a => ?_
              simpa [next] using ih a.1
                (⟨{ p.ideal with roNf := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp hx0
      | roE kq e =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.roE (kq, e)
          let next : (F × (F × ℕ → Option F)) ×
              (ℕ → Option F) → ProbComp (Evidence F) := fun z =>
            Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run ⟨{ p.ideal with roE := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roE := a.2 }, p.pending⟩]
          calc
            _ = 𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun a => ?_
              simpa [next] using ih a.1
                (⟨{ p.ideal with roE := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp hx0
      | roId kq =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            bind_assoc, pure_bind]
          let step := lazyRO p.ideal.roId kq
          let next : (F × (F → Option F)) × (ℕ → Option F) →
              ProbComp (Evidence F) := fun z =>
            Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose)
              (cont z.1.1)).run ⟨{ p.ideal with roId := z.1.2 }, z.2⟩
          change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
              step >>= fun a => next (a, gs)] =
            𝒟[step >>= fun a => Prod.fst <$>
              (simulateQ (pendingFrameImpl mclose) (cont a.1)).run
                ⟨{ p.ideal with roId := a.2 }, p.pending⟩]
          calc
            _ = 𝒟[step >>= fun a =>
                drawPendingSlopes (F := F) p.pending >>= fun gs =>
                  next (a, gs)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              refine evalDist_bind_congr' step fun a => ?_
              simpa [next] using ih a.1
                (⟨{ p.ideal with roId := a.2 }, p.pending⟩ :
                  PendingFrameSt F M) hp hx0

/-- Deferred-slope execution from its initial state has the same evidence
distribution as the plain ideal handler.  This composes dead-slope erasure,
the empty pending-slope tape, and pending-index erasure; it is the final
distributional bridge used by the general good-slice transfer. -/
theorem dsFrameImpl_init_evidence_eq_ideal (k : F) (mclose : M)
    (oa : OracleComp (frameSpec F M) (Evidence F)) :
    𝒟[Prod.fst <$> (simulateQ (dsFrameImpl k mclose) oa).run
      (DSFrameSt.init F M)] =
      𝒟[Prod.fst <$> (simulateQ (idealFrameImpl mclose) oa).run
        (IdealFrameSt.init F M)] := by
  calc
    𝒟[Prod.fst <$> (simulateQ (dsFrameImpl k mclose) oa).run
        (DSFrameSt.init F M)] =
        𝒟[Prod.fst <$> (simulateQ (futureDSFrameImpl k mclose) oa).run
          (FutureDSSt.init F M)] := by
          simpa [dsFrameSt_init_future] using
            (dsFrameImpl_run_evidence_eq_future k mclose oa
              (DSFrameSt.init F M))
    _ = 𝒟[Prod.fst <$> (simulateQ (pendingFrameImpl mclose) oa).run
          (PendingFrameSt.init F M)] := by
          simpa [drawPendingSlopes, FutureDSSt.init, PendingFrameSt.init] using
            (futureDSFrameImpl_run_evidence_eq_pending k mclose oa
              (PendingFrameSt.init F M) pendingValid_init
              (roXCacheNonzero_init (F := F) (M := M)))
    _ = 𝒟[Prod.fst <$> (simulateQ (idealFrameImpl mclose) oa).run
          (IdealFrameSt.init F M)] :=
      pendingFrameImpl_run_evidence_eq_ideal mclose oa
        (PendingFrameSt.init F M)

end TapeInduction

end Zkpc.Games
