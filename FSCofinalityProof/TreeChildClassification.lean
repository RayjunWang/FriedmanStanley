import FSCofinalityProof.TreePaddedChildren

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RootedTrees

theorem multiset_paddedChildren_of_isomorphic {T U : TreeSpace} (h : Isomorphic T U) :
    CountableMultisetRelation Isomorphic (paddedChildren T) (paddedChildren U) := by
  obtain ⟨e,he⟩ := h
  let ep : PresentChildren T ≃ PresentChildren U :=
    (((labelPresentEquiv T).symm).trans (childLabelEquiv e he)).trans (labelPresentEquiv U)
  let ec := absentEquiv T U
  let sigma : ℕ ≃ ℕ := Equiv.subtypeCongr ep ec
  have hleft (i : PresentChildren T) : sigma i.val = (ep i).val := by
    simp only [sigma,Equiv.subtypeCongr,Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_pos,Equiv.sumCongr_apply,Sum.map_inl,Equiv.sumCompl_apply_inl]
  have hright (i : AbsentChildren T) : sigma i.val = (ec i).val := by
    simp only [sigma,Equiv.subtypeCongr,Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_neg,Equiv.sumCongr_apply,Sum.map_inr,Equiv.sumCompl_apply_inr]
  refine ⟨sigma,fun i => ?_⟩
  by_cases hi : paddedChildren T i [] = true
  · let j : PresentChildren T := ⟨i,hi⟩
    let n := (labelPresentEquiv T).symm j
    have hj : labelPresentEquiv T n = j := (labelPresentEquiv T).apply_symm_apply j
    have hx : paddedChildren T i = childTree T n.val := by
      rw [← show (labelPresentEquiv T n).val = i from congrArg Subtype.val hj]
      exact labelPresentEquiv_tree T n
    have hy : paddedChildren U (sigma i) = childTree U (childLabelEquiv e he n).val := by
      rw [show sigma i = (ep j).val from hleft j]
      change paddedChildren U (labelPresentEquiv U (childLabelEquiv e he n)).val = _
      exact labelPresentEquiv_tree U _
    rw [hx,hy]
    exact child_isomorphic e he n
  · have hj : ¬ paddedChildren U (sigma i) [] = true := by
      rw [show sigma i = (ec ⟨i,hi⟩).val from hright ⟨i,hi⟩]
      exact (ec ⟨i,hi⟩).property
    rw [(noRoot_iff_eq_empty _).mp hi,(noRoot_iff_eq_empty _).mp hj]
    exact isomorphic_refl emptyTree

theorem isomorphic_of_multiset_paddedChildren {T U : TreeSpace}
    (ht : T [] = true) (hu : U [] = true)
    (h : CountableMultisetRelation Isomorphic (paddedChildren T) (paddedChildren U)) :
    Isomorphic T U := by
  obtain ⟨sigma,hsigma⟩ := h
  have hpres (i : ℕ) : paddedChildren T i [] = true ↔
      paddedChildren U (sigma i) [] = true := isomorphic_root_iff (hsigma i)
  let ep : PresentChildren T ≃ PresentChildren U := sigma.subtypeEquiv hpres
  let e : ChildLabels T ≃ ChildLabels U :=
    ((labelPresentEquiv T).trans ep).trans (labelPresentEquiv U).symm
  apply isomorphic_of_child_equiv ht hu e
  intro n
  have hmatch := hsigma (labelPresentEquiv T n).val
  rw [labelPresentEquiv_tree] at hmatch
  have heval : sigma (labelPresentEquiv T n).val = (labelPresentEquiv U (e n)).val := by
    have hh := (labelPresentEquiv U).apply_symm_apply (ep (labelPresentEquiv T n))
    exact (congrArg Subtype.val hh).symm
  rw [heval,labelPresentEquiv_tree] at hmatch
  exact hmatch

theorem isomorphic_iff_paddedChildren (T U : TreeSpace) :
    Isomorphic T U ↔ T [] = U [] ∧
      CountableMultisetRelation Isomorphic (paddedChildren T) (paddedChildren U) := by
  constructor
  · intro h
    refine ⟨?_,multiset_paddedChildren_of_isomorphic h⟩
    have hh := isomorphic_root_iff h
    cases ht : T [] <;> cases hu : U [] <;> simp_all
  · rintro ⟨hroot,hchildren⟩
    by_cases ht : T [] = true
    · exact isomorphic_of_multiset_paddedChildren ht (hroot ▸ ht) hchildren
    · have hu : U [] ≠ true := hroot ▸ ht
      rw [(noRoot_iff_eq_empty T).mp ht,(noRoot_iff_eq_empty U).mp hu]
      exact isomorphic_refl emptyTree

end FSCofinality.RootedTrees
