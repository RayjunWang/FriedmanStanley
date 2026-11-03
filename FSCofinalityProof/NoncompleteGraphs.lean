import FSCofinalityProof.PaddingBranches
import FSCofinalityProof.PaddingEnumeration
import FSCofinalityProof.Boundedness
import FSCofinalityProof.GraphEncoding
import Mathlib.SetTheory.Cardinal.Ordinal

set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace FSCofinality

theorem exists_positive_countable_padding_bound (b : Ordinal.{0}) (hb : b < Ordinal.omega 1) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ 0 < a ∧ Padding.cutoff b ≤ a := by
  let a := Padding.cutoff (Order.succ b)
  have hω : Ordinal.omega0 < Ordinal.omega 1 := by
    apply Cardinal.lt_omega_iff_card_lt.mpr
    simpa only [Ordinal.card_omega0] using Cardinal.aleph0_lt_aleph_one
  have hs : Order.succ b < Ordinal.omega 1 := (Cardinal.isSuccLimit_omega 1).succ_lt hb
  refine ⟨a,Ordinal.isPrincipal_mul_omega 1 hω hs,?_,?_⟩
  · change 0 < Padding.cutoff (Order.succ b)
    simpa [Padding.cutoff] using
      Padding.cutoff_add_nat_lt (Ordinal.succ_pos b) 0
  · exact Padding.cutoff_mono (Order.le_succ b)

theorem Padding.not_isomorphic_padded_fat
    (a : Ordinal.{0}) (C : List ℕ → ℕ) (eP : ℕ ≃ Padding.PaddedNode a)
    (eF : ℕ ≃ Padding.FatNode a) :
    ¬ Isomorphic (Padding.code (Padding.PaddedNode.tree a C) eP)
      (Padding.code (Padding.FatNode.tree a (C [])) eF) := by
  intro h
  obtain ⟨e⟩ := Padding.treeIso_of_code_isomorphic
    (Padding.PaddedNode.tree a C) (Padding.FatNode.tree a (C [])) eP eF h
  have hp := Padding.PaddedNode.branch_from_original a C []
  have hf := e.map_branch hp
  rw [show (Sum.inl [] : Padding.PaddedNode a) = (Padding.PaddedNode.tree a C).root from rfl,
    e.roots] at hf
  exact Padding.no_branch_of_finite_rank (Padding.FatNode.tree a (C []))
    (Padding.FatNode.tree a (C [])).root WithTop.coe_ne_top hf

/-- Graph isomorphism is non-Borel, derived here from analytic boundedness,
the fully constructed fat trees, and the faithful native graph encoding. -/
theorem graphIsomorphic_not_measurableSet :
    ¬ MeasurableSet {p : GraphSpace × GraphSpace | GraphIsomorphic p.1 p.2} := by
  intro hGraph
  let L := Padding.treeLanguage
  have hIso : MeasurableSet {p : Structures L × Structures L | Isomorphic p.1 p.2} := by
    have hpre := hGraph.preimage
      (((GraphCoding.measurable_encodeStructure L).comp measurable_fst).prodMk
        ((GraphCoding.measurable_encodeStructure L).comp measurable_snd))
    convert hpre using 1
    ext p
    exact GraphCoding.isomorphic_iff_graphIsomorphic p.1 p.2
  let S : Set (Structures L × Structures L) := {p | ¬ Isomorphic p.1 p.2}
  let treeMap : Structures L × Structures L → RootedTrees.TreeSpace :=
    fun p => PartialIso.attemptTree p.1 p.2
  have hS : MeasurableSet S := hIso.compl
  have hA : AnalyticSet (treeMap '' S) := hS.analyticSet_image PartialIso.measurable_attemptTree
  have hWF : ∀ T ∈ treeMap '' S, ¬ RootedTrees.HasBranch T := by
    rintro T ⟨⟨M,N⟩,hMN,rfl⟩ hbranch
    exact hMN ((PartialIso.branch_iff_isomorphic M N).mp hbranch)
  obtain ⟨b,hb,hbound⟩ := RootedTrees.analytic_wellFoundedTree_bounded (treeMap '' S) hA hWF
  obtain ⟨a,ha,hpos,hba⟩ := exists_positive_countable_padding_bound b hb
  let M := Padding.code (Padding.PaddedNode.tree a (fun _ => 0)) (Padding.paddedEnumeration a ha)
  let N := Padding.code (Padding.FatNode.tree a 0) (Padding.fatEnumeration a ha hpos)
  have hBF : PartialIso.BackAndForth M N b [] :=
    Padding.fat_padding_on_nat a b ha hpos hba (fun _ => 0)
  have hnon : ¬ Isomorphic M N := Padding.not_isomorphic_padded_fat a (fun _ => 0) _ _
  have hT : RootedTrees.BoundedTree (PartialIso.attemptTree M N) b :=
    hbound _ ⟨(M,N),hnon,rfl⟩
  exact PartialIso.not_bounded_attemptTree_of_backAndForth b hBF hT

end FSCofinality
