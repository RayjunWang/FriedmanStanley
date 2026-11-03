import FSCofinalityProof.BorelPrunedBranch
import FSCofinalityProof.PartialIsomorphism
import Definitions.Def_FSCofinalityCosets20261102

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

private theorem inverse_coordinates {L : CountableRelationalLanguage} {M N : Structures L}
    (b : ℕ → ℕ) (hb : ∀ n, attemptTree M N (initialSegment b n) = true) :
    (∀ i, b (2 * b (2*i)+1) = i) ∧ (∀ i, b (2 * b (2*i+1)) = i) := by
  have hpair (i : ℕ) {n : ℕ} (hn : 2*i < n) :
      (i,b (2*i)) ∈ pairsFrom 0 (initialSegment b n) := by
    simpa only [scheduledPair_even] using scheduledPair_mem_prefix b hn
  have hipair (i : ℕ) {n : ℕ} (hn : 2*i+1 < n) :
      (b (2*i+1),i) ∈ pairsFrom 0 (initialSegment b n) := by
    simpa only [scheduledPair_odd] using scheduledPair_mem_prefix b hn
  constructor
  · intro i
    let n := max (2*i) (2 * b (2*i)+1)+1
    exact ((compatible_of_branch hb n).1 (i,b (2*i)) (hpair i (by omega))
      (b (2 * b (2*i)+1),b (2*i)) (hipair (b (2*i)) (by omega))).mpr rfl |>.symm
  · intro i
    let n := max (2 * b (2*i+1)) (2*i+1)+1
    exact ((compatible_of_branch hb n).1 (b (2*i+1),b (2 * b (2*i+1)))
      (hpair (b (2*i+1)) (by omega)) (b (2*i+1),i) (hipair i (by omega))).mp rfl

/-- A branch gives a specific permutation, with explicitly measurable forward
and inverse coordinates. -/
def branchPermutation {L : CountableRelationalLanguage} {M N : Structures L}
    (b : ℕ → ℕ) (hb : ∀ n, attemptTree M N (initialSegment b n) = true) :
    PermutationGroup :=
  ⟨fun i => b (2*i),fun i => b (2*i+1),
    (inverse_coordinates b hb).1,(inverse_coordinates b hb).2⟩

theorem branchPermutation_preserves {L : CountableRelationalLanguage} {M N : Structures L}
    (b : ℕ → ℕ) (hb : ∀ n, attemptTree M N (initialSegment b n) = true) :
    ∀ s a, M ⟨s,a⟩ = N ⟨s,(branchPermutation b hb).toFun ∘ a⟩ := by
  intro s a
  let n : ℕ := (Finset.univ.sup (fun i : Fin (L.arity s) => 2*(a i)))+1
  exact (compatible_of_branch hb n).2 s (fun i => (a i,b (2*a i))) (fun i => by
    simpa only [scheduledPair_even] using scheduledPair_mem_prefix b
      (Nat.lt_succ_of_le (Finset.le_sup
        (f := fun i : Fin (L.arity s) => 2*(a i)) (Finset.mem_univ i))))

theorem measurable_permutation_of_coordinates {P : Type} [MeasurableSpace P]
    (f : P → PermutationGroup)
    (hf : ∀ n, Measurable (fun p => (f p).toFun n))
    (hg : ∀ n, Measurable (fun p => (f p).symm n)) : Measurable f := by
  have hemb : MeasurableEmbedding permutationCoordinates :=
    (show Topology.IsClosedEmbedding permutationCoordinates from
      ⟨permutationCoordinates_injective.isEmbedding_induced,
        range_permutationCoordinates ▸ isClosed_inversePairCondition⟩).measurableEmbedding
  apply hemb.measurable_comp_iff.mp
  exact (measurable_pi_lambda _ hf).prodMk (measurable_pi_lambda _ hg)

/-- The extra finite-map requirements of a construction can be retained in
the chosen tree: pruning is required of that actual tree, rather than inferred
from the mere existence of an isomorphism. -/
def prunedFamilyPermutation {P : Type} {L : CountableRelationalLanguage}
    (M N : P → Structures L) (T : P → RootedTrees.TreeSpace)
    (hroot : ∀ p, T p [] = true) (hpruned : ∀ p, RootedTrees.Pruned (T p))
    (hcompatible : ∀ p s, T p s = true →
      AtomicCompatible (M p) (N p) {q | q ∈ pairsFrom 0 s}) (p : P) :
    PermutationGroup :=
  branchPermutation (RootedTrees.branchChoice (T p)) (fun n => by
    apply decide_eq_true
    apply hcompatible p
    exact RootedTrees.branchChoice_spec (T p) (hroot p) (hpruned p) n)

theorem prunedFamilyPermutation_preserves {P : Type} {L : CountableRelationalLanguage}
    (M N : P → Structures L) (T : P → RootedTrees.TreeSpace)
    (hroot : ∀ p, T p [] = true) (hpruned : ∀ p, RootedTrees.Pruned (T p))
    (hcompatible : ∀ p s, T p s = true →
      AtomicCompatible (M p) (N p) {q | q ∈ pairsFrom 0 s}) (p : P) :
    ∀ s a, M p ⟨s,a⟩ = N p ⟨s,(prunedFamilyPermutation M N T hroot hpruned hcompatible p).toFun ∘ a⟩ :=
  branchPermutation_preserves _ _

theorem measurable_prunedFamilyPermutation {P : Type} [MeasurableSpace P]
    {L : CountableRelationalLanguage}
    (M N : P → Structures L) (T : P → RootedTrees.TreeSpace)
    (hroot : ∀ p, T p [] = true) (hpruned : ∀ p, RootedTrees.Pruned (T p))
    (hcompatible : ∀ p s, T p s = true →
      AtomicCompatible (M p) (N p) {q | q ∈ pairsFrom 0 s})
    (hT : Measurable T) :
    Measurable (prunedFamilyPermutation M N T hroot hpruned hcompatible) := by
  apply measurable_permutation_of_coordinates
  · intro n
    exact (measurable_pi_apply (2*n)).comp (RootedTrees.measurable_branchChoice.comp hT)
  · intro n
    exact (measurable_pi_apply (2*n+1)).comp (RootedTrees.measurable_branchChoice.comp hT)

end FSCofinality.PartialIso
