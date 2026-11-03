import FSCofinalityProof.NoncompleteInvariantReal

set_option autoImplicit false
noncomputable section
open Set

namespace FSCofinality

/-- Any class of structures with a Borel invariant named real and Borel
isomorphism on each fixed real fiber is not Borel complete. All graph
non-Borelness and invariant-fiber foundations are discharged. -/
theorem not_graph_reducible_of_borel_real_fibers
    {L : CountableRelationalLanguage} (K : Set (Structures L))
    (parameter : K → (ℕ → Bool)) (hp : Measurable parameter)
    (hinv : ∀ M N : K, IsomorphismOn K M N → parameter M = parameter N)
    (hfiber : ∀ r : ℕ → Bool,
      MeasurableSet {p : {M : K // parameter M = r} × {M : K // parameter M = r} |
        IsomorphismOn K p.1.val p.2.val}) :
    ¬ graphRelation.Reduces (classRelation L K) :=
  not_graph_reducible_of_invariant_parameter K graphIsomorphic_not_measurableSet
    graph_invariantRealFiberProperty parameter hp hinv hfiber

end FSCofinality
