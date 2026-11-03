import FSCofinalityProof.CosetConstructionNativeModel
import FSCofinalityProof.CosetConstructionPoolEquivalences
import FSCofinalityProof.IsomorphismCosets

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def coordinateCode (n : ℕ) : ℕ := (templateEnumeration eta heta).symm (.inl n)

theorem coordinateCode_injective : Function.Injective (coordinateCode eta heta) :=
  (templateEnumeration eta heta).symm.injective.comp Sum.inl_injective

def nativeQ : Set ℕ := range (coordinateCode eta heta)

def coordinateEquiv : ℕ ≃ nativeQ eta heta :=
  Equiv.ofInjective (coordinateCode eta heta) (coordinateCode_injective eta heta)

theorem nativeEnumeration_coordinateCode (x : (fsTower eta).Carrier) (n : ℕ) :
    nativeEnumeration eta heta x (coordinateCode eta heta n) = .inl n := by
  rw [show coordinateCode eta heta n = (nativeEnumeration eta heta x).symm (.inl n) from
    (nativeEnumeration_coordinate_preimage eta heta x n).symm]
  exact (nativeEnumeration eta heta x).apply_symm_apply _

theorem nativeQ_iff (x : (fsTower eta).Carrier) (k : ℕ) :
    k ∈ nativeQ eta heta ↔ sortOf eta heta (nativeEnumeration eta heta x k) = none := by
  constructor
  · rintro ⟨n,rfl⟩
    rw [nativeEnumeration_coordinateCode]
    rfl
  · intro hk
    cases hv : nativeEnumeration eta heta x k with
    | inl n =>
      refine ⟨n,?_⟩
      apply (nativeEnumeration eta heta x).injective
      rw [nativeEnumeration_coordinateCode,hv]
    | inr v => simp only [hv,sortOf] at hk; contradiction

def fromNative (x y : (fsTower eta).Carrier) (p : PermutationGroup) :
    Vertex eta heta x ≃ Vertex eta heta y :=
  (((nativeEnumeration eta heta x).symm).trans (p : ℕ ≃ ℕ)).trans (nativeEnumeration eta heta y)

theorem fromNative_preserves (x y : (fsTower eta).Carrier) (p : PermutationGroup)
    (hp : Carries (nativeModel eta heta x) (nativeModel eta heta y) p) :
    PreservesDiagram eta heta (fromNative eta heta x y p) := by
  intro s a
  have h := hp s ((nativeEnumeration eta heta x).symm ∘ a)
  simpa only [nativeModel,modelWithEnumeration,fromNative,Equiv.trans_apply,Function.comp_def,
    Equiv.apply_symm_apply] using h

def toNative (x y : (fsTower eta).Carrier) (e : Vertex eta heta x ≃ Vertex eta heta y) :
    PermutationGroup :=
  (((nativeEnumeration eta heta x).trans e).trans (nativeEnumeration eta heta y).symm)

theorem toNative_carries (x y : (fsTower eta).Carrier) (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : PreservesDiagram eta heta e) :
    Carries (nativeModel eta heta x) (nativeModel eta heta y) (toNative eta heta x y e) := by
  intro s a
  have h := he s (nativeEnumeration eta heta x ∘ a)
  change diagram eta heta (bottom eta heta) x s (fun i => nativeEnumeration eta heta x (a i)) =
    diagram eta heta (bottom eta heta) y s (fun i => nativeEnumeration eta heta y
      ((nativeEnumeration eta heta y).symm (e (nativeEnumeration eta heta x (a i)))))
  simpa only [Function.comp_def,Equiv.apply_symm_apply] using h

theorem fromNative_fixes_coordinate (x y : (fsTower eta).Carrier) (p : PermutationGroup)
    (hQ : ∀ k ∈ nativeQ eta heta, p.toFun k = k) (n : ℕ) :
    fromNative eta heta x y p (.inl n) = .inl n := by
  change nativeEnumeration eta heta y (p.toFun ((nativeEnumeration eta heta x).symm (.inl n))) = _
  rw [nativeEnumeration_coordinate_preimage]
  change nativeEnumeration eta heta y (p.toFun (coordinateCode eta heta n)) = _
  rw [hQ _ (mem_range_self n),nativeEnumeration_coordinateCode]

theorem toNative_fixesQ (x y : (fsTower eta).Carrier) (e : Vertex eta heta x ≃ Vertex eta heta y)
    (hQ : ∀ n, e (.inl n) = .inl n) :
    ∀ k ∈ nativeQ eta heta, (toNative eta heta x y e).toFun k = k := by
  rintro k ⟨n,rfl⟩
  change (nativeEnumeration eta heta y).symm (e (nativeEnumeration eta heta x (coordinateCode eta heta n))) = _
  rw [nativeEnumeration_coordinateCode,hQ,nativeEnumeration_coordinate_preimage]
  rfl

theorem nativeCarries_preservesQ (x y : (fsTower eta).Carrier) (p : PermutationGroup)
    (hp : Carries (nativeModel eta heta x) (nativeModel eta heta y) p) (n : ℕ) :
    n ∈ nativeQ eta heta ↔ p.toFun n ∈ nativeQ eta heta := by
  rw [nativeQ_iff eta heta x n,nativeQ_iff eta heta y (p.toFun n)]
  have h := hp (.inl none) (fun _ => n)
  change decide (sortOf eta heta (nativeEnumeration eta heta x n) = none) =
    decide (sortOf eta heta (nativeEnumeration eta heta y (p.toFun n)) = none) at h
  exact decide_eq_decide.mp h

theorem native_qFixed_iff (x y : (fsTower eta).Carrier) :
    (fsTower eta).rel x y ↔
      QFixedIsomorphic (nativeQ eta heta) (nativeModel eta heta x) (nativeModel eta heta y) := by
  constructor
  · intro hxy
    obtain ⟨e,he,hQ⟩ := source_equivalent_qFixed eta heta hxy
    exact ⟨toNative eta heta x y e,toNative_carries eta heta x y e he,toNative_fixesQ eta heta x y e hQ⟩
  · rintro ⟨p,hp,hQ⟩
    exact qFixed_reflects eta heta (fromNative eta heta x y p) (fromNative_preserves eta heta x y p hp)
      (fromNative_fixes_coordinate eta heta x y p hQ)

theorem native_qFixed_rigid (x : (fsTower eta).Carrier) (p : PermutationGroup)
    (hp : Carries (nativeModel eta heta x) (nativeModel eta heta x) p)
    (hQ : ∀ k ∈ nativeQ eta heta, p.toFun k = k) : p = 1 := by
  have he := qFixed_rigid eta heta (fromNative eta heta x x p) (fromNative_preserves eta heta x x p hp)
    (fromNative_fixes_coordinate eta heta x x p hQ)
  apply Equiv.ext
  intro n
  apply (nativeEnumeration eta heta x).injective
  have h := congrArg (fun e : Vertex eta heta x ≃ Vertex eta heta x => e (nativeEnumeration eta heta x n)) he
  simpa only [fromNative,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.refl_apply] using h

end FSCofinality.CosetConstruction.TokenModel
