import FSCofinalityProof.TokenLimitRequests
import FSCofinalityProof.TokenInsertion

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem limit_branch_forward
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (v : Token (raw eta heta x (.inl lam.val)))
    (w : Token (raw eta heta y (.inl lam.val)))
    (hbranch : ∀ n (j : SortEntries eta heta R (.inr (lam,n))),
      branch eta heta y lam n w (targetEntry eta heta R _ j) =
        branch eta heta x lam n v (sourceEntry eta heta R hR _ j))
    (mu : LimitIndex eta) (n : ℕ) (p) (hp : p ∈ R) :
    edgeAt eta heta _ _ (branch eta heta x mu n) (.inr ⟨.inl lam.val,v⟩) p.1 =
      edgeAt eta heta _ _ (branch eta heta y mu n) (.inr ⟨.inl lam.val,w⟩) p.2 := by
  by_cases hmu : mu=lam
  · subst mu
    by_cases ht : sortOf eta heta p.2 = some (.inr (lam,n))
    · let c := (tokenFiberEquiv eta heta y (.inr (lam,n))).symm ⟨p.2,ht⟩
      have hc : (.inr ⟨.inr (lam,n),c⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (.inr (lam,n))).apply_symm_apply _)
      obtain ⟨j,hj,_⟩ := targetEntry_covers eta heta R (.inr (lam,n)) p hp c hc.symm
      have hh : edgeAt eta heta _ _ (branch eta heta x lam n) (.inr ⟨.inl lam.val,v⟩) (R.get j.val).1 =
          edgeAt eta heta _ _ (branch eta heta y lam n) (.inr ⟨.inl lam.val,w⟩) (R.get j.val).2 := by
        rw [← sourceEntry_vertex eta heta R hR (.inr (lam,n)) j,
          ← targetEntry_vertex eta heta R (.inr (lam,n)) j]
        simpa only [edgeAt_inr] using (hbranch n j).symm
      simpa only [hj] using hh
    · have hy := (tokenAt_none_iff_sort eta heta (.inr (lam,n)) p.2).mpr ht
      have hx := (tokenAt_none_iff_sort eta heta (.inr (lam,n)) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      simp only [edgeAt,tokenAt_inr,hx,hy,Option.elim_some,Option.elim_none]
  · have hs : (.inl lam.val : TokenSort eta) ≠ .inl mu.val :=
      fun h => hmu (Subtype.ext (Sum.inl.inj h).symm)
    have hx : tokenAt eta heta (.inl mu.val) (.inr ⟨.inl lam.val,v⟩) = none := by simp [tokenAt,hs]
    have hy : tokenAt eta heta (.inl mu.val) (.inr ⟨.inl lam.val,w⟩) = none := by simp [tokenAt,hs]
    simp only [edgeAt,hx,hy,Option.elim_none]

theorem limit_relation_forward
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (v : Token (raw eta heta x (.inl lam.val)))
    (w : Token (raw eta heta y (.inl lam.val)))
    (hrelation : ∀ (n : ℕ) (i : SortEntries eta heta R (.inl lam.val)),
      Tokens.R (limitProfile eta heta y lam) n w (targetEntry eta heta R _ i) ↔
        Tokens.R (limitProfile eta heta x lam) n v (sourceEntry eta heta R hR _ i))
    (mu : LimitIndex eta) (n : ℕ) (p) (hp : p ∈ R) :
    localRelationAt eta heta x mu n (.inr ⟨.inl lam.val,v⟩) p.1 =
      localRelationAt eta heta y mu n (.inr ⟨.inl lam.val,w⟩) p.2 := by
  by_cases hmu : mu=lam
  · subst mu
    by_cases ht : sortOf eta heta p.2 = some (.inl lam.val)
    · let c := (tokenFiberEquiv eta heta y (.inl lam.val)).symm ⟨p.2,ht⟩
      have hc : (.inr ⟨.inl lam.val,c⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (.inl lam.val)).apply_symm_apply _)
      obtain ⟨j,hj,_⟩ := targetEntry_covers eta heta R (.inl lam.val) p hp c hc.symm
      have hh : localRelationAt eta heta x lam n (.inr ⟨.inl lam.val,v⟩) (R.get j.val).1 =
          localRelationAt eta heta y lam n (.inr ⟨.inl lam.val,w⟩) (R.get j.val).2 := by
        rw [← sourceEntry_vertex eta heta R hR (.inl lam.val) j,
          ← targetEntry_vertex eta heta R (.inl lam.val) j]
        unfold localRelationAt
        rw [edgeAt_inr,edgeAt_inr]
        exact decide_eq_decide.mpr (hrelation n j).symm
      simpa only [hj] using hh
    · have hy := (tokenAt_none_iff_sort eta heta (.inl lam.val) p.2).mpr ht
      have hx := (tokenAt_none_iff_sort eta heta (.inl lam.val) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      simp only [localRelationAt,edgeAt,tokenAt_inr,hx,hy,Option.elim_some,Option.elim_none]
  · have hs : (.inl lam.val : TokenSort eta) ≠ .inl mu.val :=
      fun h => hmu (Subtype.ext (Sum.inl.inj h).symm)
    have hx : tokenAt eta heta (.inl mu.val) (.inr ⟨.inl lam.val,v⟩) = none := by simp [tokenAt,hs]
    have hy : tokenAt eta heta (.inl mu.val) (.inr ⟨.inl lam.val,w⟩) = none := by simp [tokenAt,hs]
    simp only [localRelationAt,edgeAt,hx,hy,Option.elim_none]

/-- Actual one-point extension in every limit main sort, including the
entire infinite nested-equivalence diagram. -/
theorem limit_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (v : Token (raw eta heta x (.inl lam.val)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl lam.val,v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (.inl lam.val)),
      LiteralCompatible eta heta (bottom eta heta) x y
        {p | p ∈ R ++ [(.inr ⟨.inl lam.val,v⟩,.inr ⟨.inl lam.val,w⟩)]} := by
  obtain ⟨w,hw,hrelation,hbranch,hordinary⟩ := limit_requests_realized eta heta R hR lam v hfresh
    (oldLabelBound eta heta R (.inl lam.val))
  refine ⟨w,token_insert_compatible eta heta R hR (.inl lam.val) v w hfresh
    (token_fresh_of_labelBound eta heta R _ w hw)
    (ordinaryRequests_forward eta heta R hR _ v w hordinary)
    (ordinaryRequests_backward eta heta R hR _ v w hordinary)
    (limit_branch_forward eta heta R hR lam v w hbranch) ?_
    (limit_relation_forward eta heta R hR lam v w hrelation) ?_⟩
  · intro mu n p hp
    have hx : tokenAt eta heta (.inr (mu,n)) (.inr ⟨.inl lam.val,v⟩) = none := by simp [tokenAt]
    have hy : tokenAt eta heta (.inr (mu,n)) (.inr ⟨.inl lam.val,w⟩) = none := by simp [tokenAt]
    unfold edgeAt
    rw [hx,hy]
    cases tokenAt eta heta (.inl mu.val) p.1 <;> cases tokenAt eta heta (.inl mu.val) p.2 <;> rfl
  · intro p hp
    have hs : (.inl lam.val : TokenSort eta) ≠ zeroSort eta := by
      intro heq
      have hr := congrArg (fun s : TokenSort eta => match s with
        | .inl a => Frame.rank a
        | .inr _ => 0) heq
      have hz : Frame.rank lam.val = 0 := by simpa only [zeroSort,mainSort,Frame.rank_ofOrdinal] using hr
      exact lam.property.ne_zero hz
    have hx : tokenAt eta heta (zeroSort eta) (.inr ⟨.inl lam.val,v⟩) = none := by simp [tokenAt,hs]
    have hy : tokenAt eta heta (zeroSort eta) (.inr ⟨.inl lam.val,w⟩) = none := by simp [tokenAt,hs]
    simp only [bottomEdge,hx,hy,Option.elim_none]

end FSCofinality.CosetConstruction.TokenModel
