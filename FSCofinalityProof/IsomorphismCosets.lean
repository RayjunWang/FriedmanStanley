import FSCofinalityProof.AutomorphismGroups

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality

def Carries {L : CountableRelationalLanguage} (M N : Structures L)
    (p : PermutationGroup) : Prop :=
  ∀ s a, M ⟨s,a⟩ = N ⟨s,p.toFun ∘ a⟩

theorem Carries.mul {L : CountableRelationalLanguage} {M N O : Structures L}
    {p q : PermutationGroup} (hp : Carries N O p) (hq : Carries M N q) :
    Carries M O (p*q) := fun s a => (hq s a).trans (hp s (q.toFun ∘ a))

theorem Carries.inv {L : CountableRelationalLanguage} {M N : Structures L}
    {p : PermutationGroup} (hp : Carries M N p) : Carries N M p⁻¹ := by
  intro s a
  have h := hp s (p.symm.toFun ∘ a)
  have heq : p.toFun ∘ (p.symm.toFun ∘ a) = a := funext (fun i => p.apply_symm_apply _)
  rw [heq] at h
  exact h.symm

def QFixedIsomorphic {L : CountableRelationalLanguage} (Q : Set ℕ) (M N : Structures L) :
    Prop := ∃ p : PermutationGroup, Carries M N p ∧ ∀ n ∈ Q, p.toFun n = n

namespace DistinguishedRestriction

theorem restrictPerm_eq_iff (Q : Set ℕ) (e : ℕ ≃ Q) (p q : PermutationGroup)
    (hp : ∀ n, n ∈ Q ↔ p.toFun n ∈ Q) (hq : ∀ n, n ∈ Q ↔ q.toFun n ∈ Q) :
    restrictPerm Q e p hp = restrictPerm Q e q hq ↔
      ∀ n ∈ Q, p.toFun n = q.toFun n := by
  constructor
  · intro h n hn
    obtain ⟨k,hk⟩ := e.surjective ⟨n,hn⟩
    have h' := congrArg (fun g : PermutationGroup => (e (g.toFun k)).val) h
    simpa only [restrictPerm_apply_val,hk] using h'
  · intro h
    apply Equiv.ext
    intro k
    apply e.injective
    apply Subtype.ext
    change (e ((restrictPerm Q e p hp).toFun k)).val =
      (e ((restrictPerm Q e q hq).toFun k)).val
    simpa only [restrictPerm_apply_val] using h (e k).val (e k).property

theorem measurable_restrictPerm {P : Type} [MeasurableSpace P]
    (Q : Set ℕ) (e : ℕ ≃ Q) (u : P → PermutationGroup)
    (huQ : ∀ p n, n ∈ Q ↔ (u p).toFun n ∈ Q) (hu : Measurable u) :
    Measurable (fun p => restrictPerm Q e (u p) (huQ p)) := by
  apply PartialIso.measurable_permutation_of_coordinates
  · intro n
    have hv : Measurable (fun p => (u p).toFun (e n).val) :=
      ((continuous_apply (e n).val).comp continuous_permutationCoordinates.fst).measurable.comp hu
    have hs : Measurable (fun p =>
        (⟨(u p).toFun (e n).val,(huQ p _).mp (e n).property⟩ : Q)) := hv.subtype_mk
    exact (measurable_of_countable e.symm).comp hs
  · intro n
    have hv : Measurable (fun p => (u p).symm.toFun (e n).val) :=
      ((continuous_apply (e n).val).comp continuous_permutationCoordinates.snd).measurable.comp hu
    have hm (p : P) : (u p).symm.toFun (e n).val ∈ Q := by
      apply (huQ p _).mpr
      have hi : (u p).toFun ((u p).symm.toFun (e n).val) = (e n).val :=
        (u p).right_inv _
      rw [hi]
      exact (e n).property
    have hs : Measurable (fun p =>
        (⟨(u p).symm.toFun (e n).val,hm p⟩ : Q)) := hv.subtype_mk
    exact (measurable_of_countable e.symm).comp hs

/-- Chosen isomorphisms into one base structure identify fixed-point
isomorphism with cosets of the base automorphism group's restriction image.
The inverse in the output is forced by the left-coset convention. -/
theorem qFixed_iff_coset {P : Type} {L : CountableRelationalLanguage}
    (M : P → Structures L) (B : Structures L) (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup B, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q)
    (u : P → PermutationGroup) (hu : ∀ x, Carries (M x) B (u x))
    (huQ : ∀ x n, n ∈ Q ↔ (u x).toFun n ∈ Q) (x y : P) :
    QFixedIsomorphic Q (M x) (M y) ↔
      (imageCosetRelation (hom B Q e hQ)).rel
        (show PermutationGroup from (restrictPerm Q e (u x) (huQ x))⁻¹)
        (show PermutationGroup from (restrictPerm Q e (u y) (huQ y))⁻¹) := by
  let alpha (z : P) := restrictPerm Q e (u z) (huQ z)
  have hcoord (g : automorphismGroup B) :
      hom B Q e hQ g = alpha y * (alpha x)⁻¹ ↔
        ∀ n ∈ Q, g.val.toFun ((u x).toFun n) = (u y).toFun n := by
    rw [eq_mul_inv_iff_mul_eq]
    constructor
    · intro h n hn
      obtain ⟨k,hk⟩ := e.surjective ⟨n,hn⟩
      have ht := congrArg (fun p : PermutationGroup => (e (p.toFun k)).val) h
      change (e ((restrictPerm Q e g.val (hQ g)).toFun ((alpha x).toFun k))).val =
        (e ((alpha y).toFun k)).val at ht
      simpa only [alpha,restrictPerm_apply_val,hk] using ht
    · intro h
      apply Equiv.ext
      intro k
      apply e.injective
      apply Subtype.ext
      change (e ((restrictPerm Q e g.val (hQ g)).toFun ((alpha x).toFun k))).val =
        (e ((alpha y).toFun k)).val
      simpa only [alpha,restrictPerm_apply_val] using h (e k).val (e k).property
  change QFixedIsomorphic Q (M x) (M y) ↔
    (alpha y)⁻¹⁻¹ * (alpha x)⁻¹ ∈ (hom B Q e hQ).range
  rw [inv_inv]
  constructor
  · rintro ⟨t,ht,hfix⟩
    let g : automorphismGroup B :=
      ⟨u y * t * (u x)⁻¹,(hu y).mul (ht.mul (hu x).inv)⟩
    refine ⟨g,?_⟩
    apply (hcoord g).mpr
    intro n hn
    change (u y).toFun (t.toFun ((u x).symm.toFun ((u x).toFun n))) = (u y).toFun n
    have hinv : (u x).symm.toFun ((u x).toFun n) = n := (u x).left_inv n
    rw [hinv,hfix n hn]
  · rintro ⟨g,hg⟩
    have hc := (hcoord g).mp hg
    refine ⟨(u y)⁻¹ * g.val * u x,((hu y).inv.mul g.property).mul (hu x),?_⟩
    intro n hn
    change (u y).symm.toFun (g.val.toFun ((u x).toFun n)) = n
    rw [hc n hn]
    exact (u y).symm_apply_apply n

theorem qFixed_reduces_coset {P : Type} [MeasurableSpace P]
    {L : CountableRelationalLanguage}
    (M : P → Structures L) (B : Structures L) (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup B, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q)
    (u : P → PermutationGroup) (hu : ∀ x, Carries (M x) B (u x))
    (huQ : ∀ x n, n ∈ Q ↔ (u x).toFun n ∈ Q) (hmeas : Measurable u) :
    BorelReducible (fun x y => QFixedIsomorphic Q (M x) (M y))
      (CosetRelation (hom B Q e hQ).range) := by
  refine ⟨fun x => (restrictPerm Q e (u x) (huQ x))⁻¹,?_,?_⟩
  · exact continuous_permutation_inv.measurable.comp (measurable_restrictPerm Q e u huQ hmeas)
  · exact qFixed_iff_coset M B Q e hQ u hu huQ

end DistinguishedRestriction
end FSCofinality
