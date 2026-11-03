import FSCofinalityProof.IsomorphismCosets

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality

def NamedIsomorphic {P : Type} {L : CountableRelationalLanguage}
    (M : P → Structures L) (c : P → ℕ → ℕ) (x y : P) : Prop :=
  ∃ t : PermutationGroup, Carries (M x) (M y) t ∧ ∀ j, t.toFun (c x j) = c y j

namespace DistinguishedRestriction

theorem named_iff_coset {P : Type} {L : CountableRelationalLanguage}
    (M : P → Structures L) (B : Structures L) (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup B, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q)
    (c : P → ℕ → ℕ) (u : P → PermutationGroup) (hu : ∀ x, Carries (M x) B (u x))
    (alpha : P → PermutationGroup)
    (hcoordinate : ∀ x j, (e ((alpha x).toFun j)).val = (u x).toFun (c x j))
    (x y : P) : NamedIsomorphic M c x y ↔
      CosetRelation (hom B Q e hQ).range ((alpha x)⁻¹) ((alpha y)⁻¹) := by
  have hcoord (g : automorphismGroup B) :
      hom B Q e hQ g = alpha y * (alpha x)⁻¹ ↔
        ∀ j, g.val.toFun ((u x).toFun (c x j)) = (u y).toFun (c y j) := by
    rw [eq_mul_inv_iff_mul_eq]
    constructor
    · intro h j
      have ht := congrArg (fun p : PermutationGroup => (e (p.toFun j)).val) h
      change (e ((restrictPerm Q e g.val (hQ g)).toFun ((alpha x).toFun j))).val =
        (e ((alpha y).toFun j)).val at ht
      simpa only [restrictPerm_apply_val,hcoordinate] using ht
    · intro h
      apply Equiv.ext
      intro j
      apply e.injective
      apply Subtype.ext
      change (e ((restrictPerm Q e g.val (hQ g)).toFun ((alpha x).toFun j))).val =
        (e ((alpha y).toFun j)).val
      simpa only [restrictPerm_apply_val,hcoordinate] using h j
  change NamedIsomorphic M c x y ↔ (alpha y)⁻¹⁻¹ * (alpha x)⁻¹ ∈ (hom B Q e hQ).range
  rw [inv_inv]
  constructor
  · rintro ⟨t,ht,hmarks⟩
    let g : automorphismGroup B := ⟨u y * t * (u x)⁻¹,(hu y).mul (ht.mul (hu x).inv)⟩
    refine ⟨g,(hcoord g).mpr ?_⟩
    intro j
    change (u y).toFun (t.toFun ((u x).symm.toFun ((u x).toFun (c x j)))) = _
    have hi : (u x).symm.toFun ((u x).toFun (c x j)) = c x j := (u x).left_inv _
    rw [hi,hmarks j]
  · rintro ⟨g,hg⟩
    have hc := (hcoord g).mp hg
    refine ⟨(u y)⁻¹*g.val*u x,((hu y).inv.mul g.property).mul (hu x),?_⟩
    intro j
    change (u y).symm.toFun (g.val.toFun ((u x).toFun (c x j))) = c y j
    rw [hc j]
    exact (u y).left_inv _

theorem named_reduces_coset {P : Type} [MeasurableSpace P]
    {L : CountableRelationalLanguage}
    (M : P → Structures L) (B : Structures L) (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup B, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q)
    (c : P → ℕ → ℕ) (u : P → PermutationGroup) (hu : ∀ x, Carries (M x) B (u x))
    (alpha : P → PermutationGroup)
    (hcoordinate : ∀ x j, (e ((alpha x).toFun j)).val = (u x).toFun (c x j))
    (hmeas : Measurable alpha) :
    BorelReducible (NamedIsomorphic M c) (CosetRelation (hom B Q e hQ).range) :=
  ⟨fun x => (alpha x)⁻¹,continuous_permutation_inv.measurable.comp hmeas,
    named_iff_coset M B Q e hQ c u hu alpha hcoordinate⟩

end DistinguishedRestriction
end FSCofinality
