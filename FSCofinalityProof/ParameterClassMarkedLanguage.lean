import FSCofinalityProof.ParameterClassCopies

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.MarkedCoding

def language : CountableRelationalLanguage where
  Symbol := OrbitCoding.language.Symbol ⊕ (ℕ ⊕ ℕ)
  arity := fun s => match s with
    | .inl s => OrbitCoding.language.arity s
    | .inr (.inl _) => 0
    | .inr (.inr _) => 1
  countable := inferInstance

def reduct (A : Structures language) : Structures OrbitCoding.language :=
  fun ⟨s,a⟩ => A ⟨.inl s,a⟩

def bits (A : Structures language) (j : ℕ) : Bool :=
  A ⟨.inr (.inl j),Fin.elim0⟩

def marker (A : Structures language) (j n : ℕ) : Bool :=
  A ⟨.inr (.inr j),fun _ => n⟩

/-- The union of the named unary orbits of the even natural numbers.
It is invariant in every structure, without a separate sort predicate. -/
def Distinguished (M : Structures OrbitCoding.language) (n : ℕ) : Prop :=
  ∃ j : ℕ, M ⟨⟨0,fun _ => 2*j⟩,fun _ => n⟩ = true

theorem measurable_reduct : Measurable reduct := by
  change @Measurable _ (Coordinate OrbitCoding.language → Bool) _
    (borel _) reduct
  rw [← BorelSpace.measurable_eq (α := Coordinate OrbitCoding.language → Bool)]
  apply measurable_pi_iff.mpr
  rintro ⟨s,a⟩
  exact (show Continuous (fun A : Structures language => A ⟨Sum.inl s,a⟩) from
    _root_.continuous_apply _).measurable

theorem measurable_bits : Measurable bits := by
  apply measurable_pi_iff.mpr
  intro j
  exact (show Continuous (fun A : Structures language =>
    A ⟨Sum.inr (Sum.inl j),Fin.elim0⟩) from _root_.continuous_apply _).measurable

theorem measurable_marker (j n : ℕ) :
    Measurable (fun A : Structures language => marker A j n) :=
  (show Continuous (fun A : Structures language =>
    A ⟨Sum.inr (Sum.inr j),fun _ => n⟩) from _root_.continuous_apply _).measurable

theorem measurableSet_distinguished (n : ℕ) :
    MeasurableSet {M : Structures OrbitCoding.language | Distinguished M n} := by
  simp only [Distinguished,setOf_exists]
  apply MeasurableSet.iUnion
  intro j
  exact measurableSet_eq_fun
    (show Continuous (fun M : Structures OrbitCoding.language =>
      M ⟨⟨0,fun _ => 2*j⟩,fun _ => n⟩) from
      _root_.continuous_apply _).measurable measurable_const

theorem distinguished_iff_of_isomorphism {M N : Structures OrbitCoding.language}
    (e : ℕ ≃ ℕ) (he : ∀ s a, M ⟨s,a⟩ = N ⟨s,e ∘ a⟩) (n : ℕ) :
    Distinguished M n ↔ Distinguished N (e n) := by
  apply exists_congr
  intro j
  exact (congrArg (fun b : Bool => b = true)
    (he ⟨0,fun _ => 2*j⟩ (fun _ => n))).to_iff

theorem distinguished_even (H : Subgroup PermutationGroup) (j : ℕ) :
    Distinguished (OrbitCoding.canonicalStructure H) (2*j) := by
  refine ⟨j,?_⟩
  apply decide_eq_true
  exact ⟨1,fun _ => rfl⟩

def MarkerConditions (A : Structures language) : Prop :=
  (∀ j : ℕ, ∃ n : ℕ, marker A j n = true) ∧
  (∀ j n m : ℕ, marker A j n = true → marker A j m = true → n = m) ∧
  (∀ i j n : ℕ, marker A i n = true → marker A j n = true → i = j) ∧
  ∀ n : ℕ, Distinguished (reduct A) n ↔ ∃ j : ℕ, marker A j n = true

theorem measurableSet_markerConditions :
    MeasurableSet {A : Structures language | MarkerConditions A} := by
  have hm (j n : ℕ) : MeasurableSet {A : Structures language | marker A j n = true} :=
    measurableSet_eq_fun (measurable_marker j n) measurable_const
  have heq (n m : ℕ) : MeasurableSet {A : Structures language | n = m} := by
    by_cases h : n = m <;> simp [h]
  simp only [MarkerConditions,setOf_and,setOf_forall,setOf_exists]
  refine (MeasurableSet.iInter (fun j => MeasurableSet.iUnion (fun n => hm j n))).inter
    ((MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun n =>
      MeasurableSet.iInter (fun m => (hm j n).imp ((hm j m).imp (heq n m)))))).inter
    ((MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
      MeasurableSet.iInter (fun n => (hm i n).imp ((hm j n).imp (heq i j)))))).inter ?_))
  apply MeasurableSet.iInter
  intro n
  apply ((measurableSet_distinguished n).preimage measurable_reduct).iff
  simpa only [setOf_exists] using MeasurableSet.iUnion (fun j => hm j n)

def markerChoice (A : Structures language)
    (h : ∀ j : ℕ, ∃ n : ℕ, marker A j n = true) (j : ℕ) : ℕ :=
  Nat.find (h j)

theorem markerChoice_spec (A : Structures language)
    (h : ∀ j : ℕ, ∃ n : ℕ, marker A j n = true) (j : ℕ) :
    marker A j (markerChoice A h j) = true := Nat.find_spec (h j)

theorem measurable_markerChoice {P : Type} [MeasurableSpace P]
    (A : P → Structures language) (hA : Measurable A)
    (h : ∀ p j, ∃ n, marker (A p) j n = true) (j : ℕ) :
    Measurable (fun p => markerChoice (A p) (h p) j) := by
  apply measurable_find (fun p => h p j)
  intro n
  exact measurableSet_eq_fun ((measurable_marker j n).comp hA) measurable_const

theorem markerChoice_eq_iff (A : Structures language) (h : MarkerConditions A)
    (j n : ℕ) : markerChoice A h.1 j = n ↔ marker A j n = true := by
  constructor
  · intro hn
    rw [← hn]
    exact markerChoice_spec A h.1 j
  · intro hn
    exact h.2.1 j _ n (markerChoice_spec A h.1 j) hn

theorem markerChoice_injective (A : Structures language) (h : MarkerConditions A) :
    Function.Injective (markerChoice A h.1) := by
  intro i j hij
  exact h.2.2.1 i j _ (markerChoice_spec A h.1 i)
    (hij ▸ markerChoice_spec A h.1 j)

theorem range_markerChoice (A : Structures language) (h : MarkerConditions A) :
    Set.range (markerChoice A h.1) = {n | Distinguished (reduct A) n} := by
  ext n
  simp only [Set.mem_range,Set.mem_setOf_eq]
  constructor
  · rintro ⟨j,rfl⟩
    exact (h.2.2.2 _).mpr ⟨j,markerChoice_spec A h.1 j⟩
  · intro hn
    obtain ⟨j,hj⟩ := (h.2.2.2 n).mp hn
    exact ⟨j,(markerChoice_eq_iff A h j n).mpr hj⟩

theorem isomorphic_reduct {A B : Structures language} (e : ℕ ≃ ℕ)
    (he : ∀ s a, A ⟨s,a⟩ = B ⟨s,e ∘ a⟩) :
    ∀ s a, reduct A ⟨s,a⟩ = reduct B ⟨s,e ∘ a⟩ :=
  fun s a => he (.inl s) a

theorem bits_eq_of_isomorphic {A B : Structures language} (e : ℕ ≃ ℕ)
    (he : ∀ s a, A ⟨s,a⟩ = B ⟨s,e ∘ a⟩) : bits A = bits B := by
  funext j
  have h := he (.inr (.inl j)) Fin.elim0
  apply h.trans
  exact congrArg (fun a : Fin 0 → ℕ => B ⟨.inr (.inl j),a⟩)
    (funext (fun i => Fin.elim0 i))

theorem marker_preserved {A B : Structures language} (e : ℕ ≃ ℕ)
    (he : ∀ s a, A ⟨s,a⟩ = B ⟨s,e ∘ a⟩) (j n : ℕ) :
    marker A j n = marker B j (e n) := he (.inr (.inr j)) (fun _ => n)

end FSCofinality.MarkedCoding
