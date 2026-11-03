import FSCofinalityProof.ParameterClassDefinition
import FSCofinalityProof.ParameterClassMarkerPermutations
import FSCofinalityProof.PolishHomImage
import FSCofinalityProof.NoncompleteFinal

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.MarkedCoding

theorem infinite_distinguished_canonical (H : Subgroup PermutationGroup) :
    Infinite {n | Distinguished (OrbitCoding.canonicalStructure H) n} := by
  apply Infinite.of_injective (fun j : ℕ =>
    (⟨2*j,distinguished_even H j⟩ : {n | Distinguished (OrbitCoding.canonicalStructure H) n}))
  intro i j hij
  have hv := congrArg Subtype.val hij
  change 2*i = 2*j at hv
  omega

/-- Isomorphism is Borel inside every fiber of the named real, although
the union of all fibers need not have Borel isomorphism. -/
theorem measurableSet_fiber_isomorphism (r : ℕ → Bool) :
    MeasurableSet {p : {A : classSet // parameter A = r} ×
        {A : classSet // parameter A = r} |
      IsomorphismOn classSet p.1.val p.2.val} := by
  let P := {A : classSet // parameter A = r}
  by_cases hP : Nonempty P
  · let w : P := Classical.choice hP
    let d := ParameterSequences.decode r
    have hd : ParameterSequences.Valid d := by
      have hv := valid_parameterCode w.val.property
      change ParameterSequences.Valid (ParameterSequences.decode (parameter w.val)) at hv
      rwa [w.property] at hv
    let B : Structures OrbitCoding.language := OrbitCoding.sequenceStructure d
    have hB : OrbitCoding.canonicalStructure (ParameterSequences.generatedClosure d) = B :=
      ParameterSequences.canonicalStructure_eq_sequenceStructure d hd
    let Q : Set ℕ := {n | Distinguished B n}
    have hi : Infinite Q := by
      change Infinite {n | Distinguished B n}
      rw [← hB]
      exact infinite_distinguished_canonical _
    letI := hi
    let e : ℕ ≃ Q := Classical.choice (show Nonempty (ℕ ≃ Q) from inferInstance)
    let A : P → Structures language := fun p => p.val.val
    let N : P → Structures OrbitCoding.language := fun p => reduct (A p)
    have hA : Measurable A := measurable_subtype_coe.comp measurable_subtype_coe
    have hN : Measurable N := measurable_reduct.comp hA
    have hc (p : P) : CopyCoding.CopyTest (N p) B := by
      have hcopy := p.val.property.2.1
      change CopyCoding.CopyTest (N p)
        (OrbitCoding.sequenceStructure (ParameterSequences.decode (parameter p.val))) at hcopy
      rw [p.property] at hcopy
      exact hcopy
    let u : P → PermutationGroup := CopyCoding.chosenIsomorphism N (fun _ => B) hc
    have hu (p : P) : Carries (N p) B (u p) :=
      CopyCoding.chosenIsomorphism_preserves N (fun _ => B) hc p
    have humeas : Measurable u :=
      CopyCoding.measurable_chosenIsomorphism N (fun _ => B) hc hN measurable_const
    have hm (p : P) : MarkerConditions (A p) := p.val.property.2.2
    let c : P → ℕ → ℕ := fun p => markerChoice (A p) (hm p).1
    let alpha : P → PermutationGroup := fun p => markerPermutation (hm p) B (u p) (hu p) e
    have hameas : Measurable alpha := measurable_markerPermutation A hA hm B u hu humeas e
    have hcoordinate (p : P) (j : ℕ) :
        (e ((alpha p).toFun j)).val = (u p).toFun (c p j) :=
      markerPermutation_coordinate (hm p) B (u p) (hu p) e j
    have hQ (g : automorphismGroup B) (n : ℕ) : n ∈ Q ↔ g.val.toFun n ∈ Q :=
      distinguished_iff_of_isomorphism (show ℕ ≃ ℕ from g.val) g.property n
    let f := DistinguishedRestriction.hom B Q e hQ
    letI : PolishSpace (automorphismGroup B) := (isClosed_automorphismGroup B).polishSpace
    have hrange : MeasurableSet (f.range : Set PermutationGroup) := by
      exact measurableSet_range_continuousHom f (DistinguishedRestriction.continuous_hom B Q e hQ)
    have hcos : MeasurableSet {p : PermutationGroup × PermutationGroup |
        CosetRelation f.range p.1 p.2} := by
      exact hrange.preimage (show Continuous (fun p : PermutationGroup × PermutationGroup =>
        p.2⁻¹*p.1) from continuous_snd.inv.mul continuous_fst).measurable
    obtain ⟨g,hg,hred⟩ := DistinguishedRestriction.named_reduces_coset
      N B Q e hQ c u hu alpha hcoordinate hameas
    have hnamed : MeasurableSet {p : P × P | NamedIsomorphic N c p.1 p.2} := by
      have hpull := hcos.preimage ((hg.comp measurable_fst).prodMk (hg.comp measurable_snd))
      have heq : {p : P × P | NamedIsomorphic N c p.1 p.2} =
          {p : P × P | CosetRelation f.range (g p.1) (g p.2)} := by
        ext p
        exact hred p.1 p.2
      rw [heq]
      exact hpull
    convert hnamed using 1
    ext p
    apply isomorphic_iff_named (hm p.1) (hm p.2)
    change parameter p.1.val = parameter p.2.val
    exact p.1.property.trans p.2.property.symm
  · have hempty : IsEmpty P := not_nonempty_iff.mp hP
    have hset : {p : P × P | IsomorphismOn classSet p.1.val p.2.val} = ∅ := by
      ext p
      exact False.elim (hempty.false p.1)
    rw [hset]
    exact MeasurableSet.empty

theorem graphs_not_reducible_class : ¬graphRelation.Reduces (classRelation language classSet) :=
  not_graph_reducible_of_borel_real_fibers classSet parameter measurable_parameter
    parameter_invariant measurableSet_fiber_isomorphism

end FSCofinality.MarkedCoding
