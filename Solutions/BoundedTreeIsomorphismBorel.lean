import FSCofinalityProof.TreeClassifiers

set_option autoImplicit false

theorem FSCofinality.bounded_tree_isomorphism_borel
    (a : Ordinal.{0}) (ha_countable : a < Ordinal.omega 1) :
    @MeasurableSet
      ((FSCofinality.RootedTrees.treeRelation a).Carrier ×
        (FSCofinality.RootedTrees.treeRelation a).Carrier)
      ((FSCofinality.RootedTrees.treeRelation a).measurableSpace.prod
        (FSCofinality.RootedTrees.treeRelation a).measurableSpace)
      {p | (FSCofinality.RootedTrees.treeRelation a).rel p.1 p.2} := by
  obtain ⟨b,hb,hred⟩ := FSCofinality.RootedTrees.treeRelation_reduces_some_fsTower a ha_countable
  exact FSCofinality.measurable_graph_of_reduces hred (FSCofinality.regular_fsTower b).measurable_graph
