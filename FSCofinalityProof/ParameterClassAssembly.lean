import FSCofinalityProof.ParameterClassDefinition

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.MarkedCoding

def assemble (M : Structures OrbitCoding.language) (r : ℕ → Bool) (c : ℕ → ℕ) :
    Structures language := fun ⟨s,a⟩ => match s with
  | .inl s => M ⟨s,a⟩
  | .inr (.inl j) => r j
  | .inr (.inr j) => decide (a ⟨0,by simp [language]⟩ = c j)

@[simp] theorem reduct_assemble (M : Structures OrbitCoding.language) (r : ℕ → Bool)
    (c : ℕ → ℕ) : reduct (assemble M r c) = M := rfl

@[simp] theorem bits_assemble (M : Structures OrbitCoding.language) (r : ℕ → Bool)
    (c : ℕ → ℕ) : bits (assemble M r c) = r := rfl

@[simp] theorem marker_assemble (M : Structures OrbitCoding.language) (r : ℕ → Bool)
    (c : ℕ → ℕ) (j n : ℕ) : marker (assemble M r c) j n = decide (n = c j) := rfl

theorem measurable_assemble {P : Type} [MeasurableSpace P]
    (M : P → Structures OrbitCoding.language) (r : P → (ℕ → Bool))
    (c : P → ℕ → ℕ) (hM : Measurable M) (hr : Measurable r)
    (hc : ∀ j, Measurable (fun p => c p j)) :
    Measurable (fun p => assemble (M p) (r p) (c p)) := by
  change @Measurable P (Coordinate language → Bool) _ (borel _) _
  rw [← BorelSpace.measurable_eq (α := Coordinate language → Bool)]
  apply measurable_pi_iff.mpr
  rintro ⟨s,a⟩
  rcases s with s | (j | j)
  · have heval : Measurable (fun N : Structures OrbitCoding.language => N ⟨s,a⟩) :=
      (show Continuous (fun N : Structures OrbitCoding.language => N ⟨s,a⟩) from
        continuous_apply _).measurable
    exact heval.comp hM
  · exact (measurable_pi_apply j).comp hr
  · change Fin 1 → ℕ at a
    have htest : MeasurableSet {p : P | a 0 = c p j} :=
      measurableSet_eq_fun measurable_const (hc j)
    convert Measurable.ite htest (measurable_const (a := true))
      (measurable_const (a := false)) using 1

theorem markerConditions_assemble (M : Structures OrbitCoding.language) (r : ℕ → Bool)
    (c : ℕ → ℕ) (hc : Function.Injective c)
    (hrange : range c = {n | Distinguished M n}) : MarkerConditions (assemble M r c) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    exact ⟨c j,by simp⟩
  · intro j n m hn hm
    simp only [marker_assemble,decide_eq_true_eq] at hn hm
    exact hn.trans hm.symm
  · intro i j n hi hj
    simp only [marker_assemble,decide_eq_true_eq] at hi hj
    exact hc (hi.symm.trans hj)
  · intro n
    change Distinguished M n ↔ ∃ j, decide (n = c j) = true
    rw [← show n ∈ {n | Distinguished M n} ↔ Distinguished M n from Iff.rfl,
      ← hrange]
    simp only [mem_range,decide_eq_true_eq]
    exact exists_congr (fun j => eq_comm)

theorem markerChoice_assemble (M : Structures OrbitCoding.language) (r : ℕ → Bool)
    (c : ℕ → ℕ) (h : MarkerConditions (assemble M r c)) (j : ℕ) :
    markerChoice (assemble M r c) h.1 j = c j := by
  apply (markerChoice_eq_iff _ h j _).mpr
  simp

theorem assemble_mem_class (d : ParameterSequences.Code)
    (hd : ParameterSequences.Valid d) (c : ℕ → ℕ) (hc : Function.Injective c)
    (hrange : range c = {n | Distinguished (OrbitCoding.sequenceStructure d) n}) :
    assemble (OrbitCoding.sequenceStructure d) (ParameterSequences.encode d) c ∈ classSet := by
  refine ⟨?_,?_,markerConditions_assemble _ _ c hc hrange⟩
  · exact ⟨d,hd,rfl⟩
  · have hbase : baseModel (assemble (OrbitCoding.sequenceStructure d)
        (ParameterSequences.encode d) c) = OrbitCoding.sequenceStructure d := by
      simp only [baseModel,parameterCode,bits_assemble,ParameterSequences.decode_encode]
    rw [hbase,reduct_assemble]
    apply CopyCoding.copyTest_of_isomorphic
    · rw [← ParameterSequences.canonicalStructure_eq_sequenceStructure d hd]
      exact CopyCoding.canonical_finiteMapExtension _
    · exact Isomorphic.refl _

end FSCofinality.MarkedCoding
