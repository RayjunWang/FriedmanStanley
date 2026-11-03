import Solutions.BoundedTreeIsomorphismBorel
import Solutions.InvariantRealParameters
import Solutions.CosetCofinality
import Solutions.OriginalTreeComparison
import Solutions.Main
import Lean.Util.CollectAxioms

#print axioms FSCofinality.bounded_tree_isomorphism_borel
#print axioms FSCofinality.invariant_real_parameters
#print axioms FSCofinality.coset_cofinality
#print axioms FSCofinality.original_tree_comparison
#print axioms FSCofinality.theorem1_2

open Lean Elab Command

-- CI fails for any axiom outside the allowlist.
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[`FSCofinality.bounded_tree_isomorphism_borel,
      `FSCofinality.invariant_real_parameters, `FSCofinality.coset_cofinality,
      `FSCofinality.original_tree_comparison, `FSCofinality.theorem1_2] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
    logInfo m!"Axiom audit passed: {name}"
