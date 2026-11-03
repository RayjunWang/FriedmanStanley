import FSCofinalityProof.ParameterClassOrbits
import FSCofinalityProof.BorelBackAndForth

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CopyCoding
open PartialIso

/-- Every compatible finite correspondence into the structure extends to
an isomorphism. This formulation also includes copies on the fixed domain. -/
def FiniteMapExtension {L : CountableRelationalLanguage} (M : Structures L) : Prop :=
  ∀ N : Structures L, Isomorphic N M → ∀ R : List (ℕ × ℕ),
    AtomicCompatible N M {p | p ∈ R} →
    ∃ e : ℕ ≃ ℕ, (∀ s a, N ⟨s,a⟩ = M ⟨s,e ∘ a⟩) ∧
      ∀ p ∈ R, e p.1 = p.2

/-- A countable Borel test for being a copy of an ultrahomogeneous structure.
Both extension directions are stated explicitly. -/
def CopyTest {L : CountableRelationalLanguage} (N M : Structures L) : Prop :=
  AtomicCompatible N M ∅ ∧
  ∀ R : List (ℕ × ℕ), AtomicCompatible N M {p | p ∈ R} →
    (∀ x : ℕ, ∃ y : ℕ, AtomicCompatible N M {p | p ∈ R ++ [(x,y)]}) ∧
    (∀ y : ℕ, ∃ x : ℕ, AtomicCompatible N M {p | p ∈ R ++ [(x,y)]})

theorem canonical_finiteMapExtension (H : Subgroup PermutationGroup) :
    FiniteMapExtension (OrbitCoding.canonicalStructure H) := by
  intro N hNM R hR
  obtain ⟨e,he⟩ := hNM
  cases R with
  | nil => exact ⟨e,he,by simp⟩
  | cons p R =>
    let a : Fin (R.length+1) → ℕ := fun i => ((p::R).get i).1
    let b : Fin (R.length+1) → ℕ := fun i => ((p::R).get i).2
    let t : Fin (R.length+1) → ℕ := e ∘ a
    let s : OrbitCoding.language.Symbol := ⟨R.length,t⟩
    have ht : OrbitCoding.canonicalStructure H ⟨s,t⟩ = true := by
      simp only [OrbitCoding.canonicalStructure, decide_eq_true_eq]
      exact ⟨1,fun _ => rfl⟩
    have hNa : N ⟨s,a⟩ = true := (he s a).trans ht
    have hNb : OrbitCoding.canonicalStructure H ⟨s,b⟩ = true := by
      have hh := hR.2 s (fun i => (p::R).get i) (fun i => by
        change Fin (R.length+1) at i
        exact List.get_mem (p::R) i)
      exact hh.symm.trans hNa
    obtain ⟨g,hg⟩ : ∃ g : H, ∀ i, (OrbitCoding.perm g.val) (t i) = b i :=
      of_decide_eq_true hNb
    refine ⟨e.trans (OrbitCoding.perm g.val),?_,?_⟩
    · intro q c
      refine (he q c).trans ?_
      change OrbitCoding.canonicalStructure H ⟨q,e ∘ c⟩ =
        OrbitCoding.canonicalStructure H ⟨q,OrbitCoding.perm g.val ∘ (e ∘ c)⟩
      simp only [OrbitCoding.canonicalStructure, decide_eq_decide]
      constructor
      · rintro ⟨k,hk⟩
        exact ⟨g*k,fun i => congrArg (OrbitCoding.perm g.val) (hk i)⟩
      · rintro ⟨k,hk⟩
        refine ⟨g⁻¹*k,fun i => ?_⟩
        apply (OrbitCoding.perm g.val).injective
        change (OrbitCoding.perm g.val) ((OrbitCoding.perm g.val).symm
          ((OrbitCoding.perm k.val) (q.2 i))) = (OrbitCoding.perm g.val) (e (c i))
        simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hk i
    · intro q hq
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hq
      simpa only [Equiv.trans_apply,a,b,t,Function.comp_apply,hi] using hg i

theorem copyTest_of_isomorphic {L : CountableRelationalLanguage} {M N : Structures L}
    (hM : FiniteMapExtension M) (hNM : Isomorphic N M) : CopyTest N M := by
  constructor
  · obtain ⟨e,he⟩ := hNM
    exact compatible_graph e he (by simp)
  · intro R hR
    obtain ⟨e,he,hagree⟩ := hM N hNM R hR
    constructor
    · intro x
      refine ⟨e x,compatible_graph e he ?_⟩
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hagree p hp
      · rcases List.mem_singleton.mp hp with rfl
        rfl
    · intro y
      refine ⟨e.symm y,compatible_graph e he ?_⟩
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hagree p hp
      · rcases List.mem_singleton.mp hp with rfl
        exact e.apply_symm_apply y

theorem CopyTest.pruned {L : CountableRelationalLanguage} {N M : Structures L}
    (h : CopyTest N M) : RootedTrees.Pruned (attemptTree N M) := by
  intro s hs
  have hc : AtomicCompatible N M {p | p ∈ pairsFrom 0 s} := of_decide_eq_true hs
  have hh := h.2 (pairsFrom 0 s) hc
  by_cases heven : s.length % 2 = 0
  · obtain ⟨y,hy⟩ := hh.1 (s.length/2)
    refine ⟨y,decide_eq_true ?_⟩
    simpa only [pairsFrom_append,pairsFrom,List.length_nil,Nat.add_zero,Nat.zero_add,
      scheduledPair,heven,if_true] using hy
  · obtain ⟨x,hx⟩ := hh.2 (s.length/2)
    refine ⟨x,decide_eq_true ?_⟩
    simpa only [pairsFrom_append,pairsFrom,List.length_nil,Nat.add_zero,Nat.zero_add,
      scheduledPair,heven,if_false] using hx

theorem CopyTest.root {L : CountableRelationalLanguage} {N M : Structures L}
    (h : CopyTest N M) : attemptTree N M [] = true := by
  apply decide_eq_true
  simpa only [pairsFrom,List.not_mem_nil,setOf_false] using h.1

theorem CopyTest.isomorphic {L : CountableRelationalLanguage} {N M : Structures L}
    (h : CopyTest N M) : Isomorphic N M := by
  exact isomorphic_of_branch (RootedTrees.branchChoice (attemptTree N M))
    (RootedTrees.branchChoice_spec _ h.root h.pruned)

theorem copyTest_iff_isomorphic {L : CountableRelationalLanguage} {M N : Structures L}
    (hM : FiniteMapExtension M) : CopyTest N M ↔ Isomorphic N M :=
  ⟨CopyTest.isomorphic,copyTest_of_isomorphic hM⟩

theorem measurableSet_copyTest {L : CountableRelationalLanguage} :
    MeasurableSet {p : Structures L × Structures L | CopyTest p.1 p.2} := by
  unfold CopyTest
  rw [setOf_and]
  apply (measurableSet_atomicCompatible ∅).inter
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro R
  apply (measurableSet_atomicCompatible {p | p ∈ R}).imp
  rw [setOf_and]
  apply MeasurableSet.inter <;> simp only [setOf_forall,setOf_exists] <;>
    apply MeasurableSet.iInter <;> intro n <;>
    apply MeasurableSet.iUnion <;> intro m <;>
    exact measurableSet_atomicCompatible _

def chosenIsomorphism {P : Type} {L : CountableRelationalLanguage}
    (N M : P → Structures L) (h : ∀ p, CopyTest (N p) (M p)) :
    P → PermutationGroup :=
  prunedFamilyPermutation N M (fun p => attemptTree (N p) (M p))
    (fun p => (h p).root) (fun p => (h p).pruned)
    (fun _ _ hs => of_decide_eq_true hs)

theorem chosenIsomorphism_preserves {P : Type} {L : CountableRelationalLanguage}
    (N M : P → Structures L) (h : ∀ p, CopyTest (N p) (M p)) (p : P) :
    ∀ s a, N p ⟨s,a⟩ = M p ⟨s,(chosenIsomorphism N M h p).toFun ∘ a⟩ :=
  prunedFamilyPermutation_preserves N M _ _ _ _ p

theorem measurable_chosenIsomorphism {P : Type} [MeasurableSpace P]
    {L : CountableRelationalLanguage} (N M : P → Structures L)
    (h : ∀ p, CopyTest (N p) (M p)) (hN : Measurable N) (hM : Measurable M) :
    Measurable (chosenIsomorphism N M h) := by
  apply measurable_prunedFamilyPermutation
  exact measurable_attemptTree.comp (hN.prodMk hM)

end FSCofinality.CopyCoding
