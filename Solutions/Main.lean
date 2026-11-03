import Solutions.CosetCofinality
import FSCofinalityProof.ParameterClassGraphCapture
import FSCofinalityProof.TreeClassifiers

set_option autoImplicit false

theorem FSCofinality.theorem1_2 :
    ∃ L : FSCofinality.CountableRelationalLanguage,
      ∃ K : Set (FSCofinality.Structures L),
        MeasurableSet K ∧ FSCofinality.IsInvariant K ∧
        (∀ a : Ordinal.{0}, a < Ordinal.omega 1 →
          (FSCofinality.fsTower a).Reduces (FSCofinality.classRelation L K)) ∧
        ¬ FSCofinality.graphRelation.Reduces (FSCofinality.classRelation L K) ∧
        (∀ a : Ordinal.{0}, 0 < a → a < Ordinal.omega 1 →
          (FSCofinality.RootedTrees.treeRelation a).Reduces
            (FSCofinality.classRelation L K)) := by
  have hcofinal : ∀ a : Ordinal.{0}, a < Ordinal.omega 1 →
      (FSCofinality.fsTower a).Reduces
        (FSCofinality.classRelation FSCofinality.MarkedCoding.language
          FSCofinality.MarkedCoding.classSet) := by
    intro a ha
    obtain ⟨G,hG,π,hπ,_,_,hred⟩ := FSCofinality.coset_cofinality a ha
    exact hred.trans (FSCofinality.MarkedCoding.image_coset_reduces_class hG π hπ)
  refine ⟨FSCofinality.MarkedCoding.language,FSCofinality.MarkedCoding.classSet,
    FSCofinality.MarkedCoding.measurableSet_classSet,FSCofinality.MarkedCoding.isInvariant_classSet,
    hcofinal,FSCofinality.MarkedCoding.graphs_not_reducible_class,?_⟩
  intro a _ ha
  obtain ⟨b,hb,hred⟩ := FSCofinality.RootedTrees.treeRelation_reduces_some_fsTower a ha
  exact hred.trans (hcofinal b hb)
