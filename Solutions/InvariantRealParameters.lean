import FSCofinalityProof.NoncompleteInvariantReal

set_option autoImplicit false

theorem FSCofinality.invariant_real_parameters
    (h : FSCofinality.GraphSpace → (ℕ → Bool)) (h_borel : Measurable h)
    (h_invariant : ∀ G H, FSCofinality.GraphIsomorphic G H → h G = h H) :
    ∃ r : ℕ → Bool, ∃ g : FSCofinality.GraphSpace → FSCofinality.GraphSpace,
      Measurable g ∧
      (∀ G H, FSCofinality.GraphIsomorphic G H ↔
        FSCofinality.GraphIsomorphic (g G) (g H)) ∧
      ∀ G, h (g G) = r := by
  exact FSCofinality.graph_invariantRealFiberProperty h h_borel h_invariant
