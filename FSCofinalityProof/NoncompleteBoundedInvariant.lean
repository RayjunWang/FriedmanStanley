import FSCofinalityProof.PartialIsomorphismRank
import FSCofinalityProof.Boundedness

set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace FSCofinality

/-- Every Borel invariant real is constant on sufficiently high
back-and-forth equivalence. The countable ordinal bound follows from
analytic boundedness applied to the actual partial-isomorphism trees
of pairs with different parameter values. -/
theorem exists_backAndForth_bound_for_invariant
    (L : CountableRelationalLanguage)
    (parameter : Structures L → (ℕ → Bool)) (hp : Measurable parameter)
    (hinv : ∀ M N, Isomorphic M N → parameter M = parameter N) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧
      ∀ M N : Structures L, PartialIso.BackAndForth M N a [] → parameter M = parameter N := by
  let S : Set (Structures L × Structures L) := {p | parameter p.1 ≠ parameter p.2}
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun (hp.comp measurable_fst) (hp.comp measurable_snd)).compl
  let treeMap : Structures L × Structures L → RootedTrees.TreeSpace :=
    fun p => PartialIso.attemptTree p.1 p.2
  have hA : AnalyticSet (treeMap '' S) := hS.analyticSet_image PartialIso.measurable_attemptTree
  have hWF : ∀ T ∈ treeMap '' S, ¬ RootedTrees.HasBranch T := by
    rintro T ⟨⟨M,N⟩,hMN,rfl⟩ hbranch
    apply hMN
    apply hinv M N
    apply (PartialIso.branch_iff_isomorphic M N).mp
    exact hbranch
  obtain ⟨a,ha,hbound⟩ := RootedTrees.analytic_wellFoundedTree_bounded (treeMap '' S) hA hWF
  refine ⟨a,ha,fun M N hBF => ?_⟩
  by_contra hMN
  have hT : RootedTrees.BoundedTree (PartialIso.attemptTree M N) a :=
    hbound _ ⟨(M,N),hMN,rfl⟩
  exact PartialIso.not_bounded_attemptTree_of_backAndForth a hBF hT

end FSCofinality
