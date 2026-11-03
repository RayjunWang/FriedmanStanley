import FSCofinalityProof.PaddingReflection
import Mathlib.Logic.Equiv.List

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

theorem getD_map_equiv_of_lt (e : ℕ ≃ ℕ) (s : List ℕ) (i : ℕ) (hi : i < s.length) :
    (s.map e).getD i 0 = e (s.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map,
    List.getD_eq_getElem _ _ hi]

theorem tupleColor_mapped {G H : GraphSpace} (e : ℕ ≃ ℕ)
    (he : ∀ m n, G.val (m,n) = H.val (e m,e n)) (s : List ℕ) :
    tupleColor H (s.map e) = tupleColor G s := by
  unfold tupleColor
  apply congrArg Encodable.encode
  unfold tupleData
  simp only [List.length_map]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    apply decide_eq_decide.mpr
    simp only [Fin.val_cast]
    rw [getD_map_equiv_of_lt e s i.val i.isLt,getD_map_equiv_of_lt e s j.val j.isLt]
    exact e.injective.eq_iff
  · apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    simp only [Fin.val_cast]
    rw [getD_map_equiv_of_lt e s i.val i.isLt,getD_map_equiv_of_lt e s j.val j.isLt]
    exact (he _ _).symm

theorem map_dropLast (e : ℕ ≃ ℕ) (s : List ℕ) :
    s.dropLast.map e = (s.map e).dropLast := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s n IH => simp

/-- A graph isomorphism acts on original tuples coordinatewise and
extends over the identical attached reservoirs. -/
theorem paddedGraphCode_isomorphic_of_graphIsomorphic
    (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (G H : GraphSpace)
    (h : GraphIsomorphic G H) : Isomorphic (paddedGraphCode a ha G) (paddedGraphCode a ha H) := by
  obtain ⟨e,he⟩ := h
  let q : PaddedNode a ≃ PaddedNode a :=
    Equiv.sumCongr (Equiv.listEquivOfEquiv e)
      (Equiv.prodCongr (Equiv.listEquivOfEquiv e) (Equiv.refl _))
  have hqL (s : List ℕ) : q (Sum.inl s) = Sum.inl (s.map e) := rfl
  have hqR (s : List ℕ) (v : {v : FatNode a // v ≠ FatNode.root}) :
      q (Sum.inr (s,v)) = Sum.inr (s.map e,v) := rfl
  have htree : TreeIso (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H)) := by
    refine ⟨q,rfl,?_,?_⟩
    · intro v
      cases v with
      | inl s =>
          change Sum.inl (s.dropLast.map e) = Sum.inl ((s.map e).dropLast)
          exact congrArg Sum.inl (map_dropLast e s)
      | inr v =>
          obtain ⟨s,v⟩ := v
          change q (PaddedNode.parent (Sum.inr (s,v))) = PaddedNode.parent (q (Sum.inr (s,v)))
          rw [hqR]
          dsimp only [PaddedNode.parent]
          split_ifs with hv
          · exact hqL s
          · exact hqR s ⟨FatNode.parent v.val,hv⟩
    · intro v
      cases v with
      | inl s => exact tupleColor_mapped e he s
      | inr v => rfl
  exact code_isomorphic_of_treeIso (PaddedNode.tree a (tupleColor G))
    (PaddedNode.tree a (tupleColor H)) (paddedEnumeration a ha) (paddedEnumeration a ha) htree

theorem graphIsomorphic_iff_paddedGraphCode_isomorphic
    (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (G H : GraphSpace) :
    GraphIsomorphic G H ↔ Isomorphic (paddedGraphCode a ha G) (paddedGraphCode a ha H) :=
  ⟨paddedGraphCode_isomorphic_of_graphIsomorphic a ha G H,
    graphIsomorphic_of_paddedGraphCode_isomorphic a ha G H⟩

theorem graphs_reduces_padded (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    BorelReducible GraphIsomorphic (@Isomorphic treeLanguage) :=
  ⟨paddedGraphCode a ha,measurable_paddedGraphCode a ha,
    graphIsomorphic_iff_paddedGraphCode_isomorphic a ha⟩

end FSCofinality.Padding

