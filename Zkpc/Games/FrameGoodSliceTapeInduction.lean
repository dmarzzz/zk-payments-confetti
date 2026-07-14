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

omit [DecidableEq M] in
/-- Consuming a deferred slope at one index turns its RLN line value into a
fresh uniform ordinate and removes that index from the pending tape.  This
single statement covers both a previously pinned coordinate (tape
extraction) and a first-touch coordinate (fresh lazy lookup). -/
theorem evalDist_drawPendingSlopes_consume_rlnY {beta : Type}
    (k x : F) (hx : x ≠ 0) (is : List ℕ) (hnd : is.Nodup) (i : ℕ)
    (G : F → (ℕ → Option F) → ProbComp beta) :
    𝒟[drawPendingSlopes (F := F) is >>= fun gs =>
        lazyRO gs i >>= fun q =>
          G (rlnY k q.1 x) (Function.update q.2 i none)] =
      𝒟[($ᵗ F) >>= fun y =>
        drawPendingSlopes (F := F) (is.erase i) >>= fun gs => G y gs] := by
  have hphi : Function.Bijective (fun a : F => rlnY k a x) := by
    constructor
    · intro a b hab
      simp only [rlnY, add_right_inj] at hab
      exact mul_right_cancel₀ hx hab
    · intro y
      refine ⟨(y - k) / x, ?_⟩
      simp only [rlnY]
      rw [div_mul_cancel₀ _ hx]
      ring
  by_cases hm : i ∈ is
  · calc
      𝒟[drawPendingSlopes (F := F) is >>= fun gs =>
          lazyRO gs i >>= fun q =>
            G (rlnY k q.1 x) (Function.update q.2 i none)] =
        𝒟[drawPendingSlopes (F := F) is >>= fun gs =>
          G (rlnY k ((gs i).getD 0) x)
            (Function.update gs i none)] := by
              refine evalDist_bind_congr
                (mx := drawPendingSlopes (F := F) is) fun gs hgs => ?_
              have hn : gs i ≠ none := by
                intro hnone
                exact ((drawPendingSlopes_support_none_iff is gs hgs i).1
                  hnone) hm
              cases hsi : gs i with
              | none => exact absurd hsi hn
              | some a => simp [lazyRO, hsi]
      _ = 𝒟[($ᵗ F) >>= fun y =>
          drawPendingSlopes (F := F) (is.erase i) >>= fun gs => G y gs] :=
        evalDist_drawPendingSlopes_extract_bij is i hm hnd
          (fun a : F => rlnY k a x) hphi G
  · calc
      𝒟[drawPendingSlopes (F := F) is >>= fun gs =>
          lazyRO gs i >>= fun q =>
            G (rlnY k q.1 x) (Function.update q.2 i none)] =
        𝒟[drawPendingSlopes (F := F) is >>= fun gs =>
          ($ᵗ F) >>= fun a => G (rlnY k a x) gs] := by
            refine evalDist_bind_congr
              (mx := drawPendingSlopes (F := F) is) fun gs hgs => ?_
            have hnone :=
              (drawPendingSlopes_support_none_iff is gs hgs i).2 hm
            have hclear : Function.update gs i none = gs := by
              funext j
              by_cases hj : j = i
              · subst j
                simp [hnone]
              · simp [Function.update_of_ne hj]
            simp [lazyRO, hnone, Function.update_idem, hclear]
      _ = 𝒟[drawPendingSlopes (F := F) is >>= fun gs =>
          ($ᵗ F) >>= fun y => G y gs] := by
            refine evalDist_bind_congr' (drawPendingSlopes (F := F) is)
              fun gs => ?_
            have hpad := evalDist_bind_bijective_add_right_uniform F
              (fun a : F => rlnY k a x) hphi 0 (fun y => G y gs)
            simpa using hpad
      _ = 𝒟[($ᵗ F) >>= fun y =>
          drawPendingSlopes (F := F) is >>= fun gs => G y gs] :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
      _ = 𝒟[($ᵗ F) >>= fun y =>
          drawPendingSlopes (F := F) (is.erase i) >>= fun gs => G y gs] := by
            rw [List.erase_of_not_mem hm]

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
          · simp only [hc, Bool.false_eq_true, if_false,
              bind_assoc, pure_bind]
            let stepX := lazyROX p.ideal.roX m
            change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                stepX >>= fun px =>
                  lazyRO gs p.ideal.idx >>= fun q =>
                    lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                      Prod.fst <$>
                        (simulateQ (futureDSFrameImpl k mclose)
                          (cont (some ⟨px.1, rlnY k q.1 px.1, pn.1⟩))).run
                            ⟨{ p.ideal with
                                idx := p.ideal.idx + 1
                                closed := false
                                roX := px.2
                                honestNf := pn.2 },
                              Function.update q.2 p.ideal.idx none⟩] =
              𝒟[stepX >>= fun px =>
                ($ᵗ F) >>= fun y =>
                  lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                    Prod.fst <$>
                      (simulateQ (pendingFrameImpl mclose)
                        (cont (some ⟨px.1, y, pn.1⟩))).run
                          ⟨{ p.ideal with
                              idx := p.ideal.idx + 1
                              closed := false
                              roX := px.2
                              honestNf := pn.2 },
                            p.pending.erase p.ideal.idx⟩]
            calc
              _ = 𝒟[stepX >>= fun px =>
                  drawPendingSlopes (F := F) p.pending >>= fun gs =>
                    lazyRO gs p.ideal.idx >>= fun q =>
                      lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                        Prod.fst <$>
                          (simulateQ (futureDSFrameImpl k mclose)
                            (cont (some
                              ⟨px.1, rlnY k q.1 px.1, pn.1⟩))).run
                              ⟨{ p.ideal with
                                  idx := p.ideal.idx + 1
                                  closed := false
                                  roX := px.2
                                  honestNf := pn.2 },
                                Function.update q.2 p.ideal.idx none⟩] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
              _ = _ := by
                refine evalDist_bind_congr (mx := stepX) fun px hpx => ?_
                have hxn := lazyROX_support_nonzero hx0 m px hpx
                let futureCont : F →
                    (F × (ℕ → Option F)) →
                    (ℕ → Option F) → ProbComp (Evidence F) :=
                  fun y pn gs => Prod.fst <$>
                    (simulateQ (futureDSFrameImpl k mclose)
                      (cont (some ⟨px.1, y, pn.1⟩))).run
                        ⟨{ p.ideal with
                            idx := p.ideal.idx + 1
                            closed := false
                            roX := px.2
                            honestNf := pn.2 }, gs⟩
                let G : F → (ℕ → Option F) → ProbComp (Evidence F) :=
                  fun y gs => lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                    futureCont y pn gs
                calc
                  _ = 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                      lazyRO gs p.ideal.idx >>= fun q =>
                        G (rlnY k q.1 px.1)
                          (Function.update q.2 p.ideal.idx none)] := rfl
                  _ = 𝒟[($ᵗ F) >>= fun y =>
                      drawPendingSlopes (F := F)
                          (p.pending.erase p.ideal.idx) >>= fun gs =>
                        G y gs] :=
                    evalDist_drawPendingSlopes_consume_rlnY k px.1 hxn.1
                      p.pending hp.1 p.ideal.idx G
                  _ = 𝒟[($ᵗ F) >>= fun y =>
                      lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                        drawPendingSlopes (F := F)
                            (p.pending.erase p.ideal.idx) >>= fun gs =>
                          futureCont y pn gs] := by
                    refine evalDist_bind_congr' ($ᵗ F) fun y => ?_
                    exact OracleComp.DeferredSampling.evalDist_bind_comm
                      (drawPendingSlopes (F := F)
                        (p.pending.erase p.ideal.idx))
                      (lazyRO p.ideal.honestNf p.ideal.idx)
                      (fun gs pn => futureCont y pn gs)
                  _ = _ := by
                    refine evalDist_bind_congr' ($ᵗ F) fun y => ?_
                    refine evalDist_bind_congr'
                      (lazyRO p.ideal.honestNf p.ideal.idx) fun pn => ?_
                    let ideal' : IdealFrameSt F M :=
                      { p.ideal with
                        idx := p.ideal.idx + 1
                        closed := false
                        roX := px.2
                        honestNf := pn.2 }
                    have hp' : PendingValid
                        (⟨ideal', p.pending.erase p.ideal.idx⟩ :
                          PendingFrameSt F M) :=
                      hp.afterSignal ideal' rfl
                    simpa [futureCont, ideal'] using
                      ih (some ⟨px.1, y, pn.1⟩)
                        (⟨ideal', p.pending.erase p.ideal.idx⟩ :
                          PendingFrameSt F M) hp' hxn.2
      | close =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk]
          by_cases hc : p.ideal.closed
          · simp only [hc, if_pos, pure_bind]
            simpa using ih none p hp hx0
          · simp only [hc, Bool.false_eq_true, if_false,
              bind_assoc, pure_bind]
            let stepX := lazyROX p.ideal.roX mclose
            change 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                stepX >>= fun px =>
                  lazyRO gs p.ideal.idx >>= fun q =>
                    lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                      Prod.fst <$>
                        (simulateQ (futureDSFrameImpl k mclose)
                          (cont (some ⟨px.1, rlnY k q.1 px.1, pn.1⟩))).run
                            ⟨{ p.ideal with
                                idx := p.ideal.idx + 1
                                closed := true
                                roX := px.2
                                honestNf := pn.2 },
                              Function.update q.2 p.ideal.idx none⟩] =
              𝒟[stepX >>= fun px =>
                ($ᵗ F) >>= fun y =>
                  lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                    Prod.fst <$>
                      (simulateQ (pendingFrameImpl mclose)
                        (cont (some ⟨px.1, y, pn.1⟩))).run
                          ⟨{ p.ideal with
                              idx := p.ideal.idx + 1
                              closed := true
                              roX := px.2
                              honestNf := pn.2 },
                            p.pending.erase p.ideal.idx⟩]
            calc
              _ = 𝒟[stepX >>= fun px =>
                  drawPendingSlopes (F := F) p.pending >>= fun gs =>
                    lazyRO gs p.ideal.idx >>= fun q =>
                      lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                        Prod.fst <$>
                          (simulateQ (futureDSFrameImpl k mclose)
                            (cont (some
                              ⟨px.1, rlnY k q.1 px.1, pn.1⟩))).run
                              ⟨{ p.ideal with
                                  idx := p.ideal.idx + 1
                                  closed := true
                                  roX := px.2
                                  honestNf := pn.2 },
                                Function.update q.2 p.ideal.idx none⟩] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
              _ = _ := by
                refine evalDist_bind_congr (mx := stepX) fun px hpx => ?_
                have hxn := lazyROX_support_nonzero hx0 mclose px hpx
                let futureCont : F →
                    (F × (ℕ → Option F)) →
                    (ℕ → Option F) → ProbComp (Evidence F) :=
                  fun y pn gs => Prod.fst <$>
                    (simulateQ (futureDSFrameImpl k mclose)
                      (cont (some ⟨px.1, y, pn.1⟩))).run
                        ⟨{ p.ideal with
                            idx := p.ideal.idx + 1
                            closed := true
                            roX := px.2
                            honestNf := pn.2 }, gs⟩
                let G : F → (ℕ → Option F) → ProbComp (Evidence F) :=
                  fun y gs => lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                    futureCont y pn gs
                calc
                  _ = 𝒟[drawPendingSlopes (F := F) p.pending >>= fun gs =>
                      lazyRO gs p.ideal.idx >>= fun q =>
                        G (rlnY k q.1 px.1)
                          (Function.update q.2 p.ideal.idx none)] := rfl
                  _ = 𝒟[($ᵗ F) >>= fun y =>
                      drawPendingSlopes (F := F)
                          (p.pending.erase p.ideal.idx) >>= fun gs =>
                        G y gs] :=
                    evalDist_drawPendingSlopes_consume_rlnY k px.1 hxn.1
                      p.pending hp.1 p.ideal.idx G
                  _ = 𝒟[($ᵗ F) >>= fun y =>
                      lazyRO p.ideal.honestNf p.ideal.idx >>= fun pn =>
                        drawPendingSlopes (F := F)
                            (p.pending.erase p.ideal.idx) >>= fun gs =>
                          futureCont y pn gs] := by
                    refine evalDist_bind_congr' ($ᵗ F) fun y => ?_
                    exact OracleComp.DeferredSampling.evalDist_bind_comm
                      (drawPendingSlopes (F := F)
                        (p.pending.erase p.ideal.idx))
                      (lazyRO p.ideal.honestNf p.ideal.idx)
                      (fun gs pn => futureCont y pn gs)
                  _ = _ := by
                    refine evalDist_bind_congr' ($ᵗ F) fun y => ?_
                    refine evalDist_bind_congr'
                      (lazyRO p.ideal.honestNf p.ideal.idx) fun pn => ?_
                    let ideal' : IdealFrameSt F M :=
                      { p.ideal with
                        idx := p.ideal.idx + 1
                        closed := true
                        roX := px.2
                        honestNf := pn.2 }
                    have hp' : PendingValid
                        (⟨ideal', p.pending.erase p.ideal.idx⟩ :
                          PendingFrameSt F M) :=
                      hp.afterSignal ideal' rfl
                    simpa [futureCont, ideal'] using
                      ih (some ⟨px.1, y, pn.1⟩)
                        (⟨ideal', p.pending.erase p.ideal.idx⟩ :
                          PendingFrameSt F M) hp' hxn.2
      | nfAt i =>
          simp only [futureDSFrameImpl, pendingFrameImpl, StateT.run_mk,
            ite_bind, bind_assoc, pure_bind]
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

/-- The full deferred-slope run has the same evidence distribution as the
secret-free ideal evidence generator. -/
theorem dsFrameRun_evidence_eq_ideal (k : F) (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    𝒟[Prod.fst <$> dsFrameRun k mclose A] =
      𝒟[idealFrameEvidence mclose A] := by
  unfold dsFrameRun idealFrameEvidence QueryImpl.Stateful.run
  rw [map_bind]
  exact evalDist_bind_congr' ($ᵗ F) fun cm =>
    dsFrameImpl_init_evidence_eq_ideal k mclose (A cm)

/-- Consequently, every fixed-secret slash predicate has identical mass in
the deferred run and the ideal evidence generator. -/
theorem dsFrameRun_slashes_eq_ideal (k : F) (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    Pr[fun z : Evidence F × DSFrameSt F M => Slashes k z.1 |
      dsFrameRun k mclose A] =
      Pr[fun ev : Evidence F => Slashes k ev | idealFrameEvidence mclose A] := by
  have h := probEvent_congr' (p := fun ev : Evidence F => Slashes k ev)
    (fun _ _ => Iff.rfl) (dsFrameRun_evidence_eq_ideal k mclose A)
  simpa [probEvent_map] using h

/-- **General pointwise good-slice transfer.** The real audited run embeds
in the deferred run until leakage; the deferred pending-slope tape erases to
the ideal evidence generator; and the ghost evidence erases to that same
ideal generator.  Thus the formerly pinned-`nfAt` case is handled at run
level rather than by an invalid pointwise state coupling. -/
theorem framePointwiseGoodSlice_of_tape (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) (k : F) :
    FramePointwiseGoodSlice mclose A k := by
  unfold FramePointwiseGoodSlice
  rw [probOutput_bind_decide_eq_probEvent,
    probOutput_bind_decide_eq_probEvent]
  have hghostDist : 𝒟[Prod.fst <$> ghostFrameRun mclose A] =
      𝒟[idealFrameEvidence mclose A] := by
    rw [fst_map_ghostFrameRun, ghostFrameEvidence_evalDist_eq]
  have hghost := probEvent_congr' (p := fun ev : Evidence F => Slashes k ev)
    (fun _ _ => Iff.rfl) hghostDist
  calc
    Pr[fun z : Evidence F × AuditedFrameSt F M =>
        Slashes k z.1 ∧ ¬ FrameLeakBad k z.2.audit |
      auditedFrameRun mclose A k]
        ≤ Pr[fun z : Evidence F × DSFrameSt F M => Slashes k z.1 |
            dsFrameRun k mclose A] :=
      auditedFrameRun_goodSlice_le_dsFrameRun k mclose A
    _ = Pr[fun ev : Evidence F => Slashes k ev | idealFrameEvidence mclose A] :=
      dsFrameRun_slashes_eq_ideal k mclose A
    _ = Pr[fun z : Evidence F × GhostFrameSt F M => Slashes k z.1 |
          ghostFrameRun mclose A] := by
      simpa [probEvent_map] using hghost.symm

/-- The k-averaged good-slice transfer for arbitrary adaptive adversaries. -/
theorem frameGoodSliceTransfer_of_tape (mclose : M)
    (A : F → OracleComp (frameSpec F M) (Evidence F)) :
    FrameGoodSliceTransfer mclose A :=
  frameGoodSliceTransfer_of_pointwise mclose A fun k =>
    framePointwiseGoodSlice_of_tape mclose A k

end TapeInduction

end Zkpc.Games

-- Kernel audit: only Lean's own `propext`/`Classical.choice`/`Quot.sound`.
#print axioms Zkpc.Games.evalDist_drawPendingSlopes_consume_rlnY
#print axioms Zkpc.Games.futureDSFrameImpl_run_evidence_eq_pending
#print axioms Zkpc.Games.dsFrameImpl_init_evidence_eq_ideal
#print axioms Zkpc.Games.dsFrameRun_evidence_eq_ideal
#print axioms Zkpc.Games.dsFrameRun_slashes_eq_ideal
#print axioms Zkpc.Games.framePointwiseGoodSlice_of_tape
#print axioms Zkpc.Games.frameGoodSliceTransfer_of_tape
