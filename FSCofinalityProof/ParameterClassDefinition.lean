import FSCofinalityProof.ParameterClassMarkedIsomorphisms
import FSCofinalityProof.ParameterClassRealCodes

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.MarkedCoding

def parameterCode (A : Structures language) : ParameterSequences.Code :=
  ParameterSequences.decode (bits A)

def baseModel (A : Structures language) : Structures OrbitCoding.language :=
  OrbitCoding.sequenceStructure (parameterCode A)

/-- The single invariant Borel class used for the cofinality counterexample.
Its named real codes a dense sequence in a closed subgroup, its reduct is
a copy of the corresponding orbit structure, and its markers enumerate
the intrinsic distinguished set without repetitions. -/
def classSet : Set (Structures language) :=
  {A | bits A ∈ ParameterSequences.EncodedValid ∧
    CopyCoding.CopyTest (reduct A) (baseModel A) ∧ MarkerConditions A}

theorem measurable_parameterCode : Measurable parameterCode :=
  ParameterSequences.measurable_decode.comp measurable_bits

theorem measurable_baseModel : Measurable baseModel :=
  OrbitCoding.measurable_sequenceStructure.comp measurable_parameterCode

theorem measurableSet_classSet : MeasurableSet classSet :=
  (ParameterSequences.measurableSet_encodedValid.preimage measurable_bits).inter
    ((CopyCoding.measurableSet_copyTest.preimage
      (measurable_reduct.prodMk measurable_baseModel)).inter measurableSet_markerConditions)

theorem valid_parameterCode {A : Structures language} (hA : A ∈ classSet) :
    ParameterSequences.Valid (parameterCode A) :=
  (ParameterSequences.mem_encodedValid_iff (bits A)).mp hA.1 |>.1

theorem baseModel_finiteMapExtension {A : Structures language} (hA : A ∈ classSet) :
    CopyCoding.FiniteMapExtension (baseModel A) := by
  have hh := ParameterSequences.canonicalStructure_eq_sequenceStructure
    (parameterCode A) (valid_parameterCode hA)
  change CopyCoding.FiniteMapExtension (OrbitCoding.sequenceStructure (parameterCode A))
  rw [← hh]
  exact CopyCoding.canonical_finiteMapExtension _

theorem isInvariant_classSet : IsInvariant classSet := by
  intro A B hA hAB
  obtain ⟨e,he⟩ := hAB
  have hbits := bits_eq_of_isomorphic e he
  have hmodel : baseModel A = baseModel B := by
    unfold baseModel parameterCode
    rw [hbits]
  refine ⟨hbits ▸ hA.1,?_,markerConditions_of_isomorphic hA.2.2 e he⟩
  have hMB : CopyCoding.FiniteMapExtension (baseModel B) := hmodel ▸ baseModel_finiteMapExtension hA
  apply (CopyCoding.copyTest_iff_isomorphic hMB).mpr
  have hBA : Isomorphic (reduct B) (reduct A) :=
    (show Isomorphic (reduct A) (reduct B) from ⟨e,isomorphic_reduct e he⟩).symm
  exact hmodel ▸ hBA.trans hA.2.1.isomorphic

def parameter (A : classSet) : ℕ → Bool := bits A.val

theorem measurable_parameter : Measurable parameter :=
  measurable_bits.comp measurable_subtype_coe

theorem parameter_invariant (A B : classSet) (h : IsomorphismOn classSet A B) :
    parameter A = parameter B := by
  obtain ⟨e,he⟩ := h
  exact bits_eq_of_isomorphic e he

end FSCofinality.MarkedCoding
