import FSCofinalityProof.ParameterClassMarkedIsomorphisms

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.MarkedCoding

theorem measurable_permutation_of_apply {P : Type} [MeasurableSpace P]
    (f : P → PermutationGroup)
    (hf : ∀ n, Measurable (fun p => (f p).toFun n)) : Measurable f := by
  apply PartialIso.measurable_permutation_of_coordinates f hf
  intro n
  have hex (p : P) : ∃ j, (f p).toFun j = n := (f p).surjective n
  have hm : Measurable (fun p => Nat.find (hex p)) := by
    apply measurable_find hex
    intro j
    exact measurableSet_eq_fun (hf j) measurable_const
  have heq (p : P) : Nat.find (hex p) = (f p).symm.toFun n := by
    apply (f p).injective
    exact (Nat.find_spec (hex p)).trans ((f p).apply_symm_apply n).symm
  simpa only [heq] using hm

def markerImage {A : Structures language} (hA : MarkerConditions A)
    (B : Structures OrbitCoding.language) (u : PermutationGroup)
    (hu : Carries (reduct A) B u) (j : ℕ) : {n | Distinguished B n} :=
  ⟨u.toFun (markerChoice A hA.1 j),
    (distinguished_iff_of_isomorphism (show ℕ ≃ ℕ from u) hu _).mp
      ((hA.2.2.2 _).mpr ⟨j,markerChoice_spec A hA.1 j⟩)⟩

theorem markerImage_bijective {A : Structures language} (hA : MarkerConditions A)
    (B : Structures OrbitCoding.language) (u : PermutationGroup)
    (hu : Carries (reduct A) B u) : Function.Bijective (markerImage hA B u hu) := by
  constructor
  · intro i j hij
    apply markerChoice_injective A hA
    exact u.injective (congrArg Subtype.val hij)
  · intro q
    have hq : Distinguished (reduct A) (u.symm.toFun q.val) := by
      apply (distinguished_iff_of_isomorphism (show ℕ ≃ ℕ from u) hu _).mpr
      change Distinguished B (u.toFun (u.symm.toFun q.val))
      have heq : u.toFun (u.symm.toFun q.val) = q.val := u.right_inv q.val
      rw [heq]
      exact q.property
    obtain ⟨j,hj⟩ := (hA.2.2.2 _).mp hq
    refine ⟨j,Subtype.ext ?_⟩
    change u.toFun (markerChoice A hA.1 j) = q.val
    rw [(markerChoice_eq_iff A hA j _).mpr hj]
    exact u.apply_symm_apply q.val

def markerPermutation {A : Structures language} (hA : MarkerConditions A)
    (B : Structures OrbitCoding.language) (u : PermutationGroup)
    (hu : Carries (reduct A) B u) (e : ℕ ≃ {n | Distinguished B n}) :
    PermutationGroup :=
  (Equiv.ofBijective (markerImage hA B u hu) (markerImage_bijective hA B u hu)).trans e.symm

theorem markerPermutation_coordinate {A : Structures language} (hA : MarkerConditions A)
    (B : Structures OrbitCoding.language) (u : PermutationGroup)
    (hu : Carries (reduct A) B u) (e : ℕ ≃ {n | Distinguished B n}) (j : ℕ) :
    (e ((markerPermutation hA B u hu e).toFun j)).val =
      u.toFun (markerChoice A hA.1 j) := by
  change (e (e.symm (markerImage hA B u hu j))).val = _
  rw [e.apply_symm_apply]
  rfl

theorem measurable_markerPermutation {P : Type} [MeasurableSpace P]
    (A : P → Structures language) (hA : Measurable A)
    (hmarkers : ∀ p, MarkerConditions (A p))
    (B : Structures OrbitCoding.language) (u : P → PermutationGroup)
    (hu : ∀ p, Carries (reduct (A p)) B (u p)) (hmeas : Measurable u)
    (e : ℕ ≃ {n | Distinguished B n}) :
    Measurable (fun p => markerPermutation (hmarkers p) B (u p) (hu p) e) := by
  apply measurable_permutation_of_apply
  intro j
  have hev : Measurable (fun q : PermutationGroup × ℕ => q.1.toFun q.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact ((continuous_apply n).comp continuous_permutationCoordinates.fst).measurable
  have hcoord : Measurable (fun p => (u p).toFun (markerChoice (A p) (hmarkers p).1 j)) :=
    hev.comp (hmeas.prodMk (measurable_markerChoice A hA (fun p => (hmarkers p).1) j))
  have hsub : Measurable (fun p => markerImage (hmarkers p) B (u p) (hu p) j) :=
    hcoord.subtype_mk
  exact (measurable_of_countable e.symm).comp hsub

end FSCofinality.MarkedCoding
