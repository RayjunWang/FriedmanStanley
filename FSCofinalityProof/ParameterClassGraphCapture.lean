import FSCofinalityProof.ParameterClassCosetEmbedding
import FSCofinalityProof.ClosedGraphCapture

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.MarkedCoding

theorem automorphismGroup_canonical (H : Subgroup PermutationGroup)
    (hH : IsClosed (H : Set PermutationGroup)) :
    automorphismGroup (OrbitCoding.canonicalStructure H) = H := by
  ext p
  exact OrbitCoding.preserves_canonicalStructure_iff H hH p

theorem distinguished_canonical_eq_evens (H : Subgroup PermutationGroup)
    (hH : ∀ p : H, ∀ n, n ∈ TwoSort.Evens ↔ p.val.toFun n ∈ TwoSort.Evens) :
    {n | Distinguished (OrbitCoding.canonicalStructure H) n} = TwoSort.Evens := by
  ext n
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨g,hg⟩ : ∃ g : H, ∀ i : Fin 1,
        (OrbitCoding.perm g.val) (2*j) = n := of_decide_eq_true hj
    have hgj : g.val.toFun (2*j) = n := hg 0
    have heven : 2*j ∈ TwoSort.Evens := by simp [TwoSort.Evens]
    exact hgj ▸ (hH g (2*j)).mp heven
  · intro hn
    have hmod : n%2=0 := hn
    have hdouble : 2*(n/2)=n := by omega
    rw [← hdouble]
    exact distinguished_even H (n/2)

/-- Every continuous homomorphic image coset relation is represented in
the same concrete invariant Borel class. Injectivity is not needed here. -/
theorem image_coset_reduces_class {G : Subgroup PermutationGroup}
    (hG : IsClosed (G : Set PermutationGroup)) (π : G →* PermutationGroup)
    (hπ : Continuous π) :
    (imageCosetRelation π).Reduces (classRelation language classSet) := by
  let H := TwoSort.graphSubgroup π
  have hH : IsClosed (H : Set PermutationGroup) := TwoSort.isClosed_graphSubgroup hG π hπ
  let B := OrbitCoding.canonicalStructure H
  let Q : Set ℕ := {n | Distinguished B n}
  have hQeq : Q = TwoSort.Evens :=
    distinguished_canonical_eq_evens H (TwoSort.graphSubgroup_preserves_evens π)
  let e : ℕ ≃ Q := TwoSort.evenEnumeration.trans (Equiv.setCongr hQeq.symm)
  have he (j : ℕ) : (e j).val = 2*j := rfl
  have hQ (g : automorphismGroup B) (n : ℕ) : n ∈ Q ↔ g.val.toFun n ∈ Q :=
    distinguished_iff_of_isomorphism (show ℕ ≃ ℕ from g.val) g.property n
  have hmem (p : PermutationGroup) : p ∈ automorphismGroup B ↔ p ∈ H :=
    OrbitCoding.preserves_canonicalStructure_iff H hH p
  let f := DistinguishedRestriction.hom B Q e hQ
  have hcompare (g : automorphismGroup B) :
      f g = TwoSort.graphRestriction π ⟨g.val,(hmem g.val).mp g.property⟩ := by
    apply Equiv.ext
    intro n
    have h₁ := DistinguishedRestriction.restrictPerm_apply_val Q e g.val (hQ g) n
    change (e ((f g).toFun n)).val = g.val.toFun (e n).val at h₁
    rw [he,he] at h₁
    have h₂ := DistinguishedRestriction.restrictPerm_apply_val TwoSort.Evens
      TwoSort.evenEnumeration g.val
      (TwoSort.graphSubgroup_preserves_evens π ⟨g.val,(hmem g.val).mp g.property⟩) n
    change 2*((TwoSort.graphRestriction π ⟨g.val,(hmem g.val).mp g.property⟩).toFun n) =
      g.val.toFun (2*n) at h₂
    change (f g).toFun n =
      (TwoSort.graphRestriction π ⟨g.val,(hmem g.val).mp g.property⟩).toFun n
    omega
  have hrange : f.range = π.range := by
    rw [← TwoSort.range_graphRestriction π]
    ext p
    constructor
    · rintro ⟨g,hg⟩
      exact ⟨⟨g.val,(hmem g.val).mp g.property⟩,(hcompare g).symm.trans hg⟩
    · rintro ⟨g,hg⟩
      let g' : automorphismGroup B := ⟨g.val,(hmem g.val).mpr g.property⟩
      exact ⟨g',(hcompare g').trans hg⟩
  have hred := closed_restriction_coset_reduces_class H hH e hQ
  change (cosetRelation f.range).Reduces (classRelation language classSet) at hred
  rw [hrange] at hred
  exact hred

end FSCofinality.MarkedCoding
