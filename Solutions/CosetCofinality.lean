import FSCofinalityProof.CosetConstructionCosets

set_option autoImplicit false

namespace FSCofinality

theorem coset_cofinality
    (a : Ordinal.{0}) (ha_countable : a < Ordinal.omega 1) :
    ∃ G : Subgroup PermutationGroup,
      IsClosed (G : Set PermutationGroup) ∧
      ∃ π : G →* PermutationGroup,
        Continuous π ∧ Function.Injective π ∧
        MeasurableSet (π.range : Set PermutationGroup) ∧
        (fsTower a).Reduces (imageCosetRelation π) :=
  CosetConstruction.coset_cofinality a ha_countable

end FSCofinality
