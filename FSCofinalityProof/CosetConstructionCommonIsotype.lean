import FSCofinalityProof.TokenLiteralForth
import FSCofinalityProof.TokenLimitMaps
import FSCofinalityProof.TokenOrdinaryExtensions
import FSCofinalityProof.CosetConstructionNativeModel
import FSCofinalityProof.IsomorphismCosets

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- Every finite atomic partial isomorphism between two actual outputs
extends over any prescribed new point. -/
theorem literal_forth (x y : (fsTower eta).Carrier) :
    LiteralForth (L := language eta heta) (diagram eta heta (bottom eta heta) x)
      (diagram eta heta (bottom eta heta) y) := by
  apply literalForth_of_fresh
  intro R hR u hfresh
  cases u with
  | inl n =>
    obtain ⟨m,hm⟩ := coordinate_extension eta heta R hR n hfresh
    exact ⟨.inl m,hm⟩
  | inr u =>
    rcases u with ⟨s,v⟩
    rcases s with a | ⟨lam,n⟩
    · by_cases ha : Order.IsSuccLimit (Frame.rank a)
      · obtain ⟨w,hw⟩ := limit_extension eta heta R hR ⟨a,ha⟩ v hfresh
        exact ⟨.inr ⟨.inl a,w⟩,hw⟩
      · obtain ⟨w,hw⟩ := nonlimit_main_extension eta heta R hR a ha v hfresh
        exact ⟨.inr ⟨.inl a,w⟩,hw⟩
    · obtain ⟨w,hw⟩ := column_extension eta heta R hR lam n v hfresh
      exact ⟨.inr ⟨.inr (lam,n),w⟩,hw⟩

theorem language_arity_positive (s : (language eta heta).Symbol) :
    0 < (language eta heta).arity s := by
  cases s <;> simp [language,arity]

theorem nativeModel_forth (x y : (fsTower eta).Carrier) :
    ForthExtension (nativeModel eta heta x) (nativeModel eta heta y) :=
  forth_modelWithEnumeration_of_literal eta heta (bottom eta heta) x y
    (nativeEnumeration eta heta x) (nativeEnumeration eta heta y) (literal_forth eta heta x y)

theorem nativeModel_isomorphic (x y : (fsTower eta).Carrier) :
    Isomorphic (nativeModel eta heta x) (nativeModel eta heta y) :=
  isomorphic_of_extensions
    (AtomicCompatible.empty_of_positive_arity _ _ (language_arity_positive eta heta))
    (nativeModel_forth eta heta x y) (nativeModel_forth eta heta y x)

theorem literal_isomorphic (x y : (fsTower eta).Carrier) :
    LiteralIsomorphic eta heta (bottom eta heta) x y :=
  (isomorphic_modelWithEnumeration_iff eta heta (bottom eta heta) x y
    (nativeEnumeration eta heta x) (nativeEnumeration eta heta y)).mp
      (nativeModel_isomorphic eta heta x y)

/-- The least-branch back-and-forth choice into any selected base output. -/
def chosenNativeIsomorphism (base : (fsTower eta).Carrier) :
    (fsTower eta).Carrier → PermutationGroup :=
  familyIsomorphism (nativeModel eta heta) (language_arity_positive eta heta)
    (nativeModel_forth eta heta) base

theorem chosenNativeIsomorphism_carries (base x : (fsTower eta).Carrier) :
    Carries (nativeModel eta heta x) (nativeModel eta heta base)
      (chosenNativeIsomorphism eta heta base x) :=
  familyIsomorphism_preserves (nativeModel eta heta) (language_arity_positive eta heta)
    (nativeModel_forth eta heta) base x

theorem measurable_chosenNativeIsomorphism (base : (fsTower eta).Carrier) :
    Measurable (chosenNativeIsomorphism eta heta base) :=
  measurable_familyIsomorphism (nativeModel eta heta) (language_arity_positive eta heta)
    (nativeModel_forth eta heta) base (measurable_nativeModel eta heta)

end FSCofinality.CosetConstruction.TokenModel
