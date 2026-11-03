import FSCofinalityProof.CosetConstructionNativeCoordinates
import FSCofinalityProof.CosetConstructionCommonIsotype
import FSCofinalityProof.PolishHomImage

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction

/-- Restriction to the distinguished coordinates realizes each countable tower
level as cosets of a Borel image of a closed permutation group. -/
theorem coset_cofinality (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1) :
    ∃ G : Subgroup PermutationGroup,
      IsClosed (G : Set PermutationGroup) ∧
      ∃ π : G →* PermutationGroup,
        Continuous π ∧ Function.Injective π ∧
        MeasurableSet (π.range : Set PermutationGroup) ∧
        (fsTower eta).Reduces (imageCosetRelation π) := by
  obtain ⟨base⟩ := (regular_fsTower eta).nonempty
  let B := TokenModel.nativeModel eta heta base
  let Q := TokenModel.nativeQ eta heta
  let eQ := TokenModel.coordinateEquiv eta heta
  have hQ : ∀ p : automorphismGroup B, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q := by
    intro p n
    exact TokenModel.nativeCarries_preservesQ eta heta base base p.val p.property n
  let π := DistinguishedRestriction.hom B Q eQ hQ
  have hfaithful : ∀ p q : automorphismGroup B,
      (∀ n ∈ Q, p.val.toFun n = q.val.toFun n) → p = q := by
    intro p q hpq
    let t : automorphismGroup B := q⁻¹ * p
    have hfix : ∀ n ∈ Q, t.val.toFun n = n := by
      intro n hn
      change q.val.symm.toFun (p.val.toFun n) = n
      rw [hpq n hn]
      exact q.val.left_inv n
    have htval := TokenModel.native_qFixed_rigid eta heta base t.val t.property hfix
    have ht : t = 1 := Subtype.ext htval
    exact (inv_mul_eq_one.mp ht).symm
  have hinj : Function.Injective π :=
    DistinguishedRestriction.hom_injective B Q eQ hQ hfaithful
  have hcont : Continuous π := DistinguishedRestriction.continuous_hom B Q eQ hQ
  have hclosed := isClosed_automorphismGroup B
  letI : PolishSpace (automorphismGroup B) := hclosed.polishSpace
  have hrange : MeasurableSet (π.range : Set PermutationGroup) := by
    change MeasurableSet (range π)
    exact measurableSet_range_continuousHom π hcont
  refine ⟨automorphismGroup B,hclosed,π,hcont,hinj,hrange,?_⟩
  let u := TokenModel.chosenNativeIsomorphism eta heta base
  have hu : ∀ x, Carries (TokenModel.nativeModel eta heta x) B (u x) :=
    TokenModel.chosenNativeIsomorphism_carries eta heta base
  have huQ : ∀ x n, n ∈ Q ↔ (u x).toFun n ∈ Q := by
    intro x n
    exact TokenModel.nativeCarries_preservesQ eta heta x base (u x) (hu x) n
  obtain ⟨f,hf,hred⟩ := DistinguishedRestriction.qFixed_reduces_coset
    (TokenModel.nativeModel eta heta) B Q eQ hQ u hu huQ
      (TokenModel.measurable_chosenNativeIsomorphism eta heta base)
  refine ⟨f,hf,?_⟩
  intro x y
  exact (TokenModel.native_qFixed_iff eta heta x y).trans (hred x y)

end FSCofinality.CosetConstruction
