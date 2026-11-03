import FSCofinalityProof.TreeClassifiers

set_option autoImplicit false

theorem FSCofinality.original_tree_comparison
    (a : Ordinal.{0}) (ha_pos : 0 < a) (ha_countable : a < Ordinal.omega 1) :
    ∃ b : Ordinal.{0}, b < Ordinal.omega 1 ∧
      (FSCofinality.RootedTrees.treeRelation a).Reduces (FSCofinality.fsTower b) := by
  exact FSCofinality.RootedTrees.treeRelation_reduces_some_fsTower a ha_countable
