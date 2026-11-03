import Definitions.Def_FSCofinalityCosets20261102
import FSCofinalityProof.StructuresBasics
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology TopologicalSpace

namespace FSCofinality.OrbitCoding

def perm (g : PermutationGroup) : ℕ ≃ ℕ := g

/-- Every nonempty finite tuple names one relation, whose interpretation
is its orbit under the parameter group. -/
def language : CountableRelationalLanguage where
  Symbol := Σ n : ℕ, Fin (n+1) → ℕ
  arity := fun s => s.1+1
  countable := inferInstance

def canonicalStructure (H : Subgroup PermutationGroup) : Structures language :=
  fun ⟨s,a⟩ => decide (∃ g : H, ∀ i, (perm g.val) (s.2 i) = a i)

def sequenceStructure (d : ℕ → PermutationGroup) : Structures language :=
  fun ⟨s,a⟩ => decide (∃ j : ℕ, ∀ i, (perm (d j)) (s.2 i) = a i)

theorem continuous_apply (n : ℕ) :
    Continuous (fun g : PermutationGroup => (perm g) n) :=
  (_root_.continuous_apply n).comp continuous_permutationCoordinates.fst

/-- Closedness turns agreement on every finite initial segment into
actual membership in the permutation subgroup. -/
theorem mem_of_finite_agreement (H : Subgroup PermutationGroup)
    (hH : IsClosed (H : Set PermutationGroup)) (p : PermutationGroup)
    (hag : ∀ n : ℕ, ∃ g : H, ∀ i < n, (perm g.val) i = (perm p) i) :
    p ∈ H := by
  choose g hg using hag
  have hf : Tendsto (fun n => (permutationCoordinates (g n).val).1) atTop
      (𝓝 (permutationCoordinates p).1) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (i+1)] with n hn
    exact (hg n i (by omega)).symm
  have hi : Tendsto (fun n => (permutationCoordinates (g n).val).2) atTop
      (𝓝 (permutationCoordinates p).2) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ((perm p).symm i+1)] with n hn
    have he := hg n ((perm p).symm i) (by omega)
    have he' : perm (g n).val ((perm p).symm i) = i := by
      simpa only [Equiv.apply_symm_apply] using he
    exact ((perm (g n).val).symm_apply_eq.mpr he'.symm).symm
  have ht : Tendsto (fun n => (g n).val) atTop (𝓝 p) := by
    rw [nhds_induced]
    exact tendsto_comap_iff.mpr (hf.prodMk_nhds hi)
  exact hH.mem_of_tendsto ht (Eventually.of_forall (fun n => (g n).property))

/-- Every automorphism of the orbit-naming structure belongs to the
original closed subgroup; every subgroup element preserves its named
orbits. -/
theorem preserves_canonicalStructure_iff (H : Subgroup PermutationGroup)
    (hH : IsClosed (H : Set PermutationGroup)) (p : PermutationGroup) :
    (∀ (s : language.Symbol) (a : Fin (language.arity s) → ℕ),
      canonicalStructure H ⟨s,a⟩ =
        canonicalStructure H ⟨s,(perm p) ∘ a⟩) ↔ p ∈ H := by
  constructor
  · intro hpres
    apply mem_of_finite_agreement H hH p
    intro n
    let t : Fin (n+1) → ℕ := fun i => i.val
    have hself : canonicalStructure H ⟨⟨n,t⟩,t⟩ = true := by
      simp only [canonicalStructure,decide_eq_true_eq]
      exact ⟨1,fun _ => rfl⟩
    have hp := (hpres ⟨n,t⟩ t).symm.trans hself
    obtain ⟨g,hg⟩ : ∃ g : H, ∀ i : Fin (n+1),
        (perm g.val) i.val = (perm p) i.val := by
      simpa only [canonicalStructure,decide_eq_true_eq,Function.comp_def,t] using hp
    exact ⟨g,fun i hi => hg ⟨i,by omega⟩⟩
  · intro hp s a
    simp only [canonicalStructure,decide_eq_decide]
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨⟨p*g.val,H.mul_mem hp g.property⟩,fun i => ?_⟩
      exact congrArg (perm p) (hg i)
    · rintro ⟨g,hg⟩
      refine ⟨⟨p⁻¹*g.val,H.mul_mem (H.inv_mem hp) g.property⟩,fun i => ?_⟩
      apply (perm p).injective
      change (perm p) ((perm p).symm ((perm g.val) (s.2 i))) = (perm p) (a i)
      simpa only [Equiv.apply_symm_apply,Function.comp_apply] using hg i

/-- Countable dense sequences are sufficient to recover every orbit
relation; no selection theorem is used by this statement. -/
theorem sequenceStructure_eq_canonicalStructure (H : Subgroup PermutationGroup)
    (d : ℕ → H) (hd : DenseRange d) :
    sequenceStructure (fun j => (d j).val) = canonicalStructure H := by
  funext ⟨s,a⟩
  change decide (∃ j, ∀ i, (perm (d j).val) (s.2 i) = a i) =
    decide (∃ g : H, ∀ i, (perm g.val) (s.2 i) = a i)
  simp only [decide_eq_decide]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨d j,hj⟩
  · rintro ⟨g,hg⟩
    have ho : IsOpen {q : H | ∀ i : Fin (s.1+1), (perm q.val) (s.2 i) = a i} := by
      simp only [setOf_forall]
      apply isOpen_iInter_of_finite
      intro i
      exact (isOpen_discrete {a i}).preimage
        ((continuous_apply (s.2 i)).comp continuous_subtype_val)
    exact hd.exists_mem_open ho ⟨g,hg⟩

/-- The canonical structure produced from a sequence of permutations is
a Borel function of that sequence. -/
theorem measurable_sequenceStructure : Measurable sequenceStructure := by
  change @Measurable (ℕ → PermutationGroup) (Coordinate language → Bool) _
    (borel (Coordinate language → Bool)) sequenceStructure
  rw [← BorelSpace.measurable_eq (α := Coordinate language → Bool)]
  apply measurable_pi_iff.mpr
  rintro ⟨s,a⟩
  have htest : MeasurableSet {d : ℕ → PermutationGroup |
      ∃ j : ℕ, ∀ i : Fin (s.1+1), (perm (d j)) (s.2 i) = a i} := by
    simp only [setOf_exists,setOf_forall]
    apply MeasurableSet.iUnion
    intro j
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_eq_fun
      (((continuous_apply (s.2 i)).measurable).comp (measurable_pi_apply j)) measurable_const
  convert Measurable.ite htest (measurable_const (a := true))
    (measurable_const (a := false)) using 1

end FSCofinality.OrbitCoding

