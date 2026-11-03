import FSCofinalityProof.PaddingForward
import FSCofinalityProof.NoncompleteGraphs
import FSCofinalityProof.NoncompleteBoundedInvariant
import FSCofinalityProof.NoncompletePrinciple

set_option autoImplicit false
noncomputable section

namespace FSCofinality

/-- The manuscript's invariant-real-parameter proposition, proved from
analytic boundedness and the explicit faithful fat-padding reduction. -/
theorem graph_invariantRealFiberProperty : InvariantRealFiberProperty GraphIsomorphic := by
  intro h hh hinv
  let parameter : Structures Padding.treeLanguage → (ℕ → Bool) :=
    h ∘ GraphCoding.encodeStructure
  have hp : Measurable parameter := hh.comp (GraphCoding.measurable_encodeStructure _)
  have hpinv : ∀ M N : Structures Padding.treeLanguage,
      Isomorphic M N → parameter M = parameter N := by
    intro M N hMN
    exact hinv _ _ ((GraphCoding.isomorphic_iff_graphIsomorphic M N).mp hMN)
  obtain ⟨b,hb,hconstant⟩ := exists_backAndForth_bound_for_invariant Padding.treeLanguage parameter hp hpinv
  obtain ⟨a,ha,hpos,hba⟩ := exists_positive_countable_padding_bound b hb
  let G₀ : GraphSpace := ⟨fun _ => false,⟨fun _ => rfl,fun _ _ => rfl⟩⟩
  let N : Structures Padding.treeLanguage :=
    Padding.code (Padding.FatNode.tree a (Padding.tupleColor G₀ []))
      (Padding.fatEnumeration a ha hpos)
  let g : GraphSpace → GraphSpace :=
    GraphCoding.encodeStructure ∘ Padding.paddedGraphCode a ha
  have hg : Measurable g := (GraphCoding.measurable_encodeStructure _).comp
    (Padding.measurable_paddedGraphCode a ha)
  have hred : ∀ G H : GraphSpace, GraphIsomorphic G H ↔ GraphIsomorphic (g G) (g H) := by
    intro G H
    exact (Padding.graphIsomorphic_iff_paddedGraphCode_isomorphic a ha G H).trans
      (GraphCoding.isomorphic_iff_graphIsomorphic _ _)
  refine ⟨parameter N,g,hg,hred,fun G => ?_⟩
  change parameter (Padding.paddedGraphCode a ha G) = parameter N
  have hBF := Padding.fat_padding_on_nat a b ha hpos hba (Padding.tupleColor G)
  have heq := hconstant _ _ hBF
  simpa only [Padding.tupleColor_nil G G₀] using heq

end FSCofinality
