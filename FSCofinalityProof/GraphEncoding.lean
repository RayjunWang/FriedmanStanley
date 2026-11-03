import FSCofinalityProof.GraphEncodingReflection

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set TopologicalSpace

namespace FSCofinality.GraphCoding

theorem continuous_incidenceColor {L : CountableRelationalLanguage} (v : IncidenceVertex L) :
    Continuous (fun M : Structures L => incidenceColor M v) := by
  cases v with
  | element n => exact continuous_const
  | occurrence c i => exact continuous_const
  | tuple c =>
    have hc : Continuous (fun M : Structures L => M c) := continuous_apply c
    exact (continuous_of_discreteTopology : Continuous (fun b : Bool =>
      2 * Nat.pair (symbolCode L c.1) b.toNat + 1)).comp hc

theorem continuous_markerAdj {P V : Type} [TopologicalSpace P]
    (E : V → V → Prop) (c : P → V → ℕ) (hc : ∀ v, Continuous (fun p => c p v))
    (x y : MarkerVertex V) :
    Continuous (fun p => decide (MarkerAdj E (c p) x y)) := by
  have hconst (q : P → Prop) (r : Prop) (h : ∀ p, q p ↔ r) :
      Continuous (fun p => decide (q p)) := by
    have heq : (fun p => decide (q p)) = (fun _ : P => decide r) :=
      funext (fun p => decide_eq_decide.mpr (h p))
    rw [heq]
    exact continuous_const
  cases x with
  | core v =>
    cases y with
    | core w => exact hconst _ (E v w) (fun _ => Iff.rfl)
    | leaf w n => exact hconst _ (v=w) (fun _ => Iff.rfl)
    | ring w i => exact hconst _ (v=w ∧ i=0) (fun _ => Iff.rfl)
  | leaf v n =>
    cases y with
    | core w => exact hconst _ (v=w) (fun _ => Iff.rfl)
    | leaf w m => exact hconst _ False (fun _ => Iff.rfl)
    | ring w i => exact hconst _ False (fun _ => Iff.rfl)
  | ring v i =>
    cases y with
    | core w => exact hconst _ (v=w ∧ i=0) (fun _ => Iff.rfl)
    | leaf w n => exact hconst _ False (fun _ => Iff.rfl)
    | ring w j =>
      have hc' := (continuous_of_discreteTopology : Continuous (fun k : ℕ =>
        decide (v=w ∧ i<k+3 ∧ j<k+3 ∧
          (i+1=j ∨ j+1=i ∨ (i=0 ∧ j+1=k+3) ∨ (j=0 ∧ i+1=k+3))))).comp (hc v)
      convert hc' using 1
      funext p
      exact decide_eq_decide.mpr Iff.rfl

def vertexEnumeration (L : CountableRelationalLanguage) :
    ℕ ≃ MarkerVertex (IncidenceVertex L) := Classical.choice inferInstance

def graphCode {L : CountableRelationalLanguage} (M : Structures L) (p : ℕ × ℕ) : Bool :=
  decide (MarkerAdj (@IncidenceAdj L) (incidenceColor M)
    (vertexEnumeration L p.1) (vertexEnumeration L p.2))

theorem graphCode_condition {L : CountableRelationalLanguage} (M : Structures L) :
    GraphCondition (graphCode M) := by
  constructor
  · intro n
    exact decide_eq_false_iff_not.mpr
      (markerAdj_irrefl (@IncidenceAdj L) (incidenceColor M) incidenceAdj_irrefl _)
  · intro m n
    apply decide_eq_decide.mpr
    have hs : Symmetric (@IncidenceAdj L) := fun _ _ h => (incidenceAdj_symm _ _).mp h
    exact ⟨fun h => markerAdj_symm (@IncidenceAdj L) (incidenceColor M) hs h,
      fun h => markerAdj_symm (@IncidenceAdj L) (incidenceColor M) hs h⟩

def encodeStructure {L : CountableRelationalLanguage} (M : Structures L) : GraphSpace :=
  ⟨graphCode M,graphCode_condition M⟩

theorem continuous_encodeStructure (L : CountableRelationalLanguage) :
    Continuous (encodeStructure (L := L)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro p
  exact continuous_markerAdj (@IncidenceAdj L) incidenceColor continuous_incidenceColor
    (vertexEnumeration L p.1) (vertexEnumeration L p.2)

theorem measurable_encodeStructure (L : CountableRelationalLanguage) :
    Measurable (encodeStructure (L := L)) := (continuous_encodeStructure L).measurable

/-- Uniform graph coding for every fixed countable relational language.
The map is continuous, and its graph isomorphisms reflect actual structure
isomorphism, including all nullary relation truth values. -/
theorem isomorphic_iff_graphIsomorphic {L : CountableRelationalLanguage}
    (M N : Structures L) :
    Isomorphic M N ↔ GraphIsomorphic (encodeStructure M) (encodeStructure N) := by
  rw [incidence_encoding_iff]
  constructor
  · rintro ⟨e,hc,hE⟩
    let q := liftCoreEquiv e
    have hq : MarkerIsomorphism (@IncidenceAdj L) (@IncidenceAdj L)
        (incidenceColor M) (incidenceColor N) q := liftCoreEquiv_isomorphism e hc hE
    let p : ℕ ≃ ℕ := ((vertexEnumeration L).trans q).trans (vertexEnumeration L).symm
    refine ⟨p,fun m n => ?_⟩
    change decide (MarkerAdj _ _ _ _) = decide (MarkerAdj _ _ _ _)
    apply decide_eq_decide.mpr
    simpa only [p,Equiv.trans_apply,Equiv.apply_symm_apply] using
      hq (vertexEnumeration L m) (vertexEnumeration L n)
  · rintro ⟨p,hp⟩
    let q : MarkerVertex (IncidenceVertex L) ≃ MarkerVertex (IncidenceVertex L) :=
      (((vertexEnumeration L).symm).trans p).trans (vertexEnumeration L)
    have hq : MarkerIsomorphism (@IncidenceAdj L) (@IncidenceAdj L)
        (incidenceColor M) (incidenceColor N) q := by
      intro x y
      have h := hp ((vertexEnumeration L).symm x) ((vertexEnumeration L).symm y)
      change decide (MarkerAdj _ _ _ _) = decide (MarkerAdj _ _ _ _) at h
      have h' := decide_eq_decide.mp h
      simpa only [q,Equiv.trans_apply,Equiv.apply_symm_apply] using h'
    exact (marker_encoding_iff (@IncidenceAdj L) (@IncidenceAdj L)
      (incidenceColor M) (incidenceColor N)).mp ⟨q,hq⟩

theorem structures_reduces_graphs (L : CountableRelationalLanguage) :
    BorelReducible (@Isomorphic L) GraphIsomorphic :=
  ⟨encodeStructure,measurable_encodeStructure L,isomorphic_iff_graphIsomorphic⟩

end FSCofinality.GraphCoding
