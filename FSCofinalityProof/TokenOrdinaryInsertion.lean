import FSCofinalityProof.TokenOrdinaryMaps
import FSCofinalityProof.TokenInsertion

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem edgeAt_token_left_of_ne (z : (fsTower eta).Carrier) (s t u : TokenSort eta)
    (h : s ≠ u) (f : Token (raw eta heta z s) → Token (raw eta heta z t) → Bool)
    (v : Token (raw eta heta z u)) (w : Vertex eta heta z) :
    edgeAt eta heta s t f (.inr ⟨u,v⟩) w = false := by
  have hn : tokenAt eta heta s (.inr ⟨u,v⟩) = none := by simp [tokenAt,Ne.symm h]
  simp only [edgeAt,hn,Option.elim_none]

theorem edgeAt_token_right_of_ne (z : (fsTower eta).Carrier) (s t u : TokenSort eta)
    (h : t ≠ u) (f : Token (raw eta heta z s) → Token (raw eta heta z t) → Bool)
    (v : Token (raw eta heta z u)) (w : Vertex eta heta z) :
    edgeAt eta heta s t f w (.inr ⟨u,v⟩) = false := by
  have hn : tokenAt eta heta t (.inr ⟨u,v⟩) = none := by simp [tokenAt,Ne.symm h]
  unfold edgeAt
  rw [hn]
  cases tokenAt eta heta s w <;> rfl

theorem bottomEdge_token_left_of_ne (z : (fsTower eta).Carrier) (s : TokenSort eta)
    (h : zeroSort eta ≠ s) (v : Token (raw eta heta z s)) (w : Vertex eta heta z) :
    bottomEdge eta heta z (.inr ⟨s,v⟩) w=false := by
  have hn : tokenAt eta heta (zeroSort eta) (.inr ⟨s,v⟩) = none := by simp [tokenAt,Ne.symm h]
  simp only [bottomEdge,hn,Option.elim_none]

theorem main_ne_limit (a : MainIndex eta) (ha : ¬ Order.IsSuccLimit (Frame.rank a))
    (lam : LimitIndex eta) : (.inl lam.val : TokenSort eta) ≠ .inl a := by
  intro h
  have he : lam.val=a := Sum.inl.inj h
  exact ha (he ▸ lam.property)

theorem nonlimit_requests_insert
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (a : MainIndex eta) (ha : ¬ Order.IsSuccLimit (Frame.rank a))
    (v : Token (raw eta heta x (.inl a))) (w : Token (raw eta heta y (.inl a)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl a,v⟩ : Vertex eta heta x) ≠ p.1)
    (hfresh' : ∀ p ∈ R, (.inr ⟨.inl a,w⟩ : Vertex eta heta y) ≠ p.2)
    (hw : OrdinaryRequestsRealized eta heta R hR (.inl a) v w)
    (hbottom : ∀ p, p ∈ R → bottomEdge eta heta x (.inr ⟨.inl a,v⟩) p.1 =
      bottomEdge eta heta y (.inr ⟨.inl a,w⟩) p.2) :
    LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨.inl a,v⟩,.inr ⟨.inl a,w⟩)]} := by
  apply token_insert_compatible eta heta R hR (.inl a) v w hfresh hfresh'
  · exact ordinaryRequests_forward eta heta R hR _ v w hw
  · exact ordinaryRequests_backward eta heta R hR _ v w hw
  · intro lam n p _
    exact (edgeAt_token_left_of_ne eta heta x _ _ _ (main_ne_limit eta a ha lam) _ v p.1).trans
      (edgeAt_token_left_of_ne eta heta y _ _ _ (main_ne_limit eta a ha lam) _ w p.2).symm
  · intro lam n p _
    exact (edgeAt_token_right_of_ne eta heta x _ _ _ (by intro h; cases h) _ v p.1).trans
      (edgeAt_token_right_of_ne eta heta y _ _ _ (by intro h; cases h) _ w p.2).symm
  · intro lam n p _
    exact (edgeAt_token_left_of_ne eta heta x _ _ _ (main_ne_limit eta a ha lam) _ v p.1).trans
      (edgeAt_token_left_of_ne eta heta y _ _ _ (main_ne_limit eta a ha lam) _ w p.2).symm
  · exact hbottom

theorem column_branch_backward
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ)
    (v : Token (raw eta heta x (.inr (lam,n)))) (w : Token (raw eta heta y (.inr (lam,n))))
    (hbranch : ∀ i : SortEntries eta heta R (.inl lam.val),
      branch eta heta x lam n (sourceEntry eta heta R hR _ i) v =
        branch eta heta y lam n (targetEntry eta heta R _ i) w)
    (mu : LimitIndex eta) (m : ℕ) (p) (hp : p ∈ R) :
    edgeAt eta heta _ _ (branch eta heta x mu m) p.1 (.inr ⟨.inr (lam,n),v⟩) =
      edgeAt eta heta _ _ (branch eta heta y mu m) p.2 (.inr ⟨.inr (lam,n),w⟩) := by
  by_cases hmn : (mu,m)=(lam,n)
  · rcases Prod.mk.inj hmn with ⟨hmu,hm⟩
    subst mu
    subst m
    by_cases ht : sortOf eta heta p.2 = some (.inl lam.val)
    · let u := (tokenFiberEquiv eta heta y (.inl lam.val)).symm ⟨p.2,ht⟩
      have hu : (.inr ⟨.inl lam.val,u⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (.inl lam.val)).apply_symm_apply _)
      obtain ⟨i,hi,_⟩ := targetEntry_covers eta heta R (.inl lam.val) p hp u hu.symm
      have he : edgeAt eta heta _ _ (branch eta heta x lam n)
          (R.get i.val).1 (.inr ⟨.inr (lam,n),v⟩) =
          edgeAt eta heta _ _ (branch eta heta y lam n) (R.get i.val).2 (.inr ⟨.inr (lam,n),w⟩) := by
        rw [← sourceEntry_vertex eta heta R hR (.inl lam.val) i,← targetEntry_vertex eta heta R (.inl lam.val) i]
        simpa only [edgeAt_inr] using hbranch i
      simpa only [hi] using he
    · have hy := (tokenAt_none_iff_sort eta heta (.inl lam.val) p.2).mpr ht
      have hx := (tokenAt_none_iff_sort eta heta (.inl lam.val) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      simp only [edgeAt,hx,hy,Option.elim_none]
  · exact (edgeAt_token_right_of_ne eta heta x _ _ _ (by exact fun h => hmn (Sum.inr.inj h)) _ v p.1).trans
      (edgeAt_token_right_of_ne eta heta y _ _ _ (by exact fun h => hmn (Sum.inr.inj h)) _ w p.2).symm

theorem column_requests_insert
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ)
    (v : Token (raw eta heta x (.inr (lam,n)))) (w : Token (raw eta heta y (.inr (lam,n))))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inr (lam,n),v⟩ : Vertex eta heta x) ≠ p.1)
    (hfresh' : ∀ p ∈ R, (.inr ⟨.inr (lam,n),w⟩ : Vertex eta heta y) ≠ p.2)
    (hw : OrdinaryRequestsRealized eta heta R hR (.inr (lam,n)) v w)
    (hbranch : ∀ i : SortEntries eta heta R (.inl lam.val),
      branch eta heta x lam n (sourceEntry eta heta R hR _ i) v =
        branch eta heta y lam n (targetEntry eta heta R _ i) w) :
    LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨.inr (lam,n),v⟩,.inr ⟨.inr (lam,n),w⟩)]} := by
  apply token_insert_compatible eta heta R hR _ v w hfresh hfresh'
  · exact ordinaryRequests_forward eta heta R hR _ v w hw
  · exact ordinaryRequests_backward eta heta R hR _ v w hw
  · intro mu m p _
    exact (edgeAt_token_left_of_ne eta heta x _ _ _ (by intro h; cases h) _ v p.1).trans
      (edgeAt_token_left_of_ne eta heta y _ _ _ (by intro h; cases h) _ w p.2).symm
  · exact column_branch_backward eta heta R hR lam n v w hbranch
  · intro mu m p _
    exact (edgeAt_token_left_of_ne eta heta x _ _ _ (by intro h; cases h) _ v p.1).trans
      (edgeAt_token_left_of_ne eta heta y _ _ _ (by intro h; cases h) _ w p.2).symm
  · intro p _
    exact (bottomEdge_token_left_of_ne eta heta x _ (by intro h; cases h) v p.1).trans
      (bottomEdge_token_left_of_ne eta heta y _ (by intro h; cases h) w p.2).symm

end FSCofinality.CosetConstruction.TokenModel
