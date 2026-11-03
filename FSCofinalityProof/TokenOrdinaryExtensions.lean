import FSCofinalityProof.TokenOrdinaryInsertion

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem column_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n))))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inr (lam,n),v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (.inr (lam,n))),
      LiteralCompatible eta heta (bottom eta heta) x y
        {p | p ∈ R ++ [(.inr ⟨.inr (lam,n),v⟩,.inr ⟨.inr (lam,n),w⟩)]} := by
  obtain ⟨w,hw,hOrd,hBr⟩ := column_requests_extension eta heta R hR lam n v
    (oldLabelBound eta heta R (.inr (lam,n)))
  exact ⟨w,column_requests_insert eta heta R hR lam n v w hfresh
    (token_fresh_of_labelBound eta heta R _ w hw) hOrd hBr⟩

theorem nonzero_nonlimit_main_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (a : MainIndex eta) (ha : ¬ Order.IsSuccLimit (Frame.rank a)) (hzero : Frame.rank a ≠ 0)
    (v : Token (raw eta heta x (.inl a)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl a,v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (.inl a)), LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨.inl a,v⟩,.inr ⟨.inl a,w⟩)]} := by
  obtain ⟨w,hw,_,hOrd⟩ := ordinary_requests_extension eta heta R hR (.inl a) v []
    (oldLabelBound eta heta R (.inl a))
  have hz : zeroSort eta ≠ .inl a := by
    intro h
    have he := congrArg Frame.rank (Sum.inl.inj h)
    have hh : (0 : Ordinal.{0}) = Frame.rank a := by
      simpa only [zeroSort,mainSort,Frame.rank_ofOrdinal] using he
    exact hzero hh.symm
  refine ⟨w,nonlimit_requests_insert eta heta R hR a ha v w hfresh
    (token_fresh_of_labelBound eta heta R _ w hw) hOrd ?_⟩
  intro p _
  exact (bottomEdge_token_left_of_ne eta heta x _ hz v p.1).trans
    (bottomEdge_token_left_of_ne eta heta y _ hz w p.2).symm

private theorem coordinate_vertex_of_sort_none (z : (fsTower eta).Carrier)
    (u : Vertex eta heta z) (hu : sortOf eta heta u=none) :
    u = .inl ((coordinateAt eta heta u).getD 0) := by
  cases u with
  | inl n => rfl
  | inr t => cases hu

theorem bottom_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (v : Token (raw eta heta x (zeroSort eta)))
    (hfresh : ∀ p ∈ R, (.inr ⟨zeroSort eta,v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (zeroSort eta)), LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨zeroSort eta,v⟩,.inr ⟨zeroSort eta,w⟩)]} := by
  let I := {i : Fin R.length // ∃ m : ℕ, (R.get i).2 = (.inl m : Vertex eta heta y)}
  letI : Fintype I := inferInstanceAs (Fintype {i : Fin R.length // _})
  let targetN (i : I) : ℕ := i.property.choose
  have target_spec (i : I) : (R.get i.val).2 = .inl (targetN i) := i.property.choose_spec
  let sourceN (i : I) : ℕ := (coordinateAt eta heta (R.get i.val).1).getD 0
  have source_spec (i : I) : (R.get i.val).1 = .inl (sourceN i) := by
    apply coordinate_vertex_of_sort_none eta heta x
    exact (hR.sort_eq eta heta _ (List.get_mem _ i.val)).trans (by rw [target_spec]; rfl)
  let epsilon (i : I) : Bool := bottom eta heta x v (sourceN i)
  have hconsistent (i j : I) (hij : targetN i=targetN j) : epsilon i=epsilon j := by
    have ht : (R.get i.val).2=(R.get j.val).2 := by rw [target_spec,target_spec,hij]
    have hs := (hR.1 _ (List.get_mem _ i.val) _ (List.get_mem _ j.val)).mpr ht
    exact congrArg (fun u => bottom eta heta x v ((coordinateAt eta heta u).getD 0)) hs
  let f : ℕ → Bool := fun m => if h : ∃ i : I, targetN i=m then epsilon h.choose else false
  have hf (i : I) : f (targetN i)=epsilon i := by
    dsimp [f]
    split_ifs with h
    · exact hconsistent h.choose i h.choose_spec
    · exact False.elim (h ⟨i,rfl⟩)
  let L := Finset.univ.sup targetN + 1
  let s := Bottom.bitsPrefix f L
  obtain ⟨w,hw,hOrd,hPref⟩ := ordinary_bottom_requests_extension eta heta R hR v s
    (oldLabelBound eta heta R (zeroSort eta))
  have hbits (i : I) : bottom eta heta y w (targetN i)=epsilon i := by
    have hi : targetN i < L := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
    have he := congrArg (fun t : List Bool => t[targetN i]?.getD false) hPref
    have he' : bottom eta heta y w (targetN i)=f (targetN i) := by
      simpa only [s,Bottom.bitsPrefix,List.length_ofFn,List.getElem?_ofFn,dif_pos hi,Option.getD_some] using he
    exact he'.trans (hf i)
  have hbottom (p : Vertex eta heta x × Vertex eta heta y) (hp : p ∈ R) :
      bottomEdge eta heta x (.inr ⟨zeroSort eta,v⟩) p.1 =
        bottomEdge eta heta y (.inr ⟨zeroSort eta,w⟩) p.2 := by
    cases ht : p.2 with
    | inl m =>
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hp
      let i : I := ⟨j,⟨m,by rw [hj]; exact ht⟩⟩
      have htarget : targetN i=m := Sum.inl.inj ((target_spec i).symm.trans (by rw [hj]; exact ht))
      have hsource : p.1 = .inl (sourceN i) :=
        (congrArg Prod.fst hj).symm.trans (source_spec i)
      rw [hsource]
      simp only [bottomEdge,tokenAt_inr,coordinateAt,Option.elim_some]
      have hh := hbits i
      rw [htarget] at hh
      exact hh.symm
    | inr t =>
      have hs := hR.sort_eq eta heta p hp
      have hn : coordinateAt eta heta p.1=none := by
        cases hx : p.1 with
        | inl m => simp only [hx,ht,sortOf] at hs; cases hs
        | inr u => rfl
      simp only [bottomEdge,tokenAt_inr,Option.elim_some]
      rw [hn]
      rfl
  have hnot : ¬ Order.IsSuccLimit (Frame.rank (Frame.ofOrdinal eta 0 zero_le)) := by
    intro h
    have hp := h.pos
    exact (lt_irrefl (0 : Ordinal.{0})) (by simpa only [Frame.rank_ofOrdinal] using hp)
  exact ⟨w,nonlimit_requests_insert eta heta R hR _ hnot v w hfresh
    (token_fresh_of_labelBound eta heta R _ w hw) hOrd hbottom⟩

theorem nonlimit_main_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (a : MainIndex eta) (ha : ¬ Order.IsSuccLimit (Frame.rank a))
    (v : Token (raw eta heta x (.inl a)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl a,v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (.inl a)), LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨.inl a,v⟩,.inr ⟨.inl a,w⟩)]} := by
  by_cases hz : Frame.rank a=0
  · have he : a=Frame.ofOrdinal eta 0 zero_le := by
      apply Ordinal.ToType.mk.symm.injective
      apply Subtype.ext
      change Frame.rank a=Frame.rank (Frame.ofOrdinal eta 0 zero_le)
      simpa only [Frame.rank_ofOrdinal] using hz
    subst a
    exact bottom_extension eta heta R hR v hfresh
  · exact nonzero_nonlimit_main_extension eta heta R hR a ha hz v hfresh

end FSCofinality.CosetConstruction.TokenModel
