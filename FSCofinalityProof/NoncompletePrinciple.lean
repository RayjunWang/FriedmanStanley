import FSCofinalityProof.StructuresBasics

set_option autoImplicit false
noncomputable section
open Set

namespace FSCofinality

/-- The precise conclusion needed from the invariant-real-parameter
argument: every Borel invariant real has a fiber containing a full copy
of the original classification problem. -/
def InvariantRealFiberProperty {X : Type} [MeasurableSpace X]
    (E : X → X → Prop) : Prop :=
  ∀ h : X → (ℕ → Bool), Measurable h →
    (∀ x y, E x y → h x = h y) →
    ∃ (r : ℕ → Bool) (g : X → X), Measurable g ∧
      (∀ x y, E x y ↔ E (g x) (g y)) ∧ ∀ x, h (g x) = r

/-- The noncompleteness implication is purely measurable once the
invariant-real-fiber theorem and non-Borelness of the source relation
have been established. Both substantive source facts remain explicit. -/
theorem not_borelReducible_of_invariant_parameter
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop)
    (hE : ¬ MeasurableSet {p : X × X | E p.1 p.2})
    (hprime : InvariantRealFiberProperty E)
    (parameter : Y → (ℕ → Bool)) (hp : Measurable parameter)
    (hinv : ∀ y z, F y z → parameter y = parameter z)
    (hfiber : ∀ r : ℕ → Bool,
      MeasurableSet {p : {y : Y // parameter y = r} × {y : Y // parameter y = r} |
        F p.1.val p.2.val}) :
    ¬ BorelReducible E F := by
  rintro ⟨f,hf,hred⟩
  obtain ⟨r,g,hg,hredg,hconstant⟩ := hprime (parameter ∘ f) (hp.comp hf)
    (fun x y hxy => hinv (f x) (f y) ((hred x y).mp hxy))
  let q : X → {y : Y // parameter y = r} := fun x => ⟨f (g x),hconstant x⟩
  have hq : Measurable q := (hf.comp hg).subtype_mk
  have htest : MeasurableSet {p : X × X | F (f (g p.1)) (f (g p.2))} := by
    exact (hfiber r).preimage ((hq.comp measurable_fst).prodMk (hq.comp measurable_snd))
  apply hE
  convert htest using 1
  ext p
  exact (hredg p.1 p.2).trans (hred (g p.1) (g p.2))

/-- The manuscript's noncompleteness theorem, with its two source
foundations isolated for later discharge. -/
theorem not_graph_reducible_of_invariant_parameter
    {L : CountableRelationalLanguage} (K : Set (Structures L))
    (graph_nonBorel : ¬ MeasurableSet {p : GraphSpace × GraphSpace |
      GraphIsomorphic p.1 p.2})
    (graph_parameter_fiber : InvariantRealFiberProperty GraphIsomorphic)
    (parameter : K → (ℕ → Bool)) (hp : Measurable parameter)
    (hinv : ∀ M N : K, IsomorphismOn K M N → parameter M = parameter N)
    (hfiber : ∀ r : ℕ → Bool,
      MeasurableSet {p : {M : K // parameter M = r} × {M : K // parameter M = r} |
        IsomorphismOn K p.1.val p.2.val}) :
    ¬ graphRelation.Reduces (classRelation L K) :=
  not_borelReducible_of_invariant_parameter GraphIsomorphic (IsomorphismOn K)
    graph_nonBorel graph_parameter_fiber parameter hp hinv hfiber

end FSCofinality
