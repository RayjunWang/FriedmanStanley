import Definitions.Def_FSCofinalityHierarchy20261102
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic

noncomputable section
open Set MeasureTheory TopologicalSpace

namespace FSCofinality

/-- Regularity of a concrete code space; its actual given sigma algebra is used. -/
structure RegularRelation (E : CodedRelation) : Prop where
  equivalence : Equivalence E.rel
  nonempty : Nonempty E.Carrier
  standardBorel : @StandardBorelSpace E.Carrier E.measurableSpace
  measurable_graph : @MeasurableSet (E.Carrier × E.Carrier)
    (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2}

def optionSumEquiv (X : Type) : Option X ≃ Unit ⊕ X where
  toFun x := match x with | none => Sum.inl () | some x => Sum.inr x
  invFun x := match x with | Sum.inl _ => none | Sum.inr x => some x
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨⟨⟩⟩ | x <;> rfl

theorem setJump_measurableSpace_eq (E : CodedRelation) :
    (setJump E).measurableSpace =
      MeasurableSpace.comap (optionSumEquiv (ℕ → E.Carrier))
        (inferInstance : MeasurableSpace (Unit ⊕ (ℕ → E.Carrier))) := by
  change MeasurableSpace.comap
    (fun x : Option (ℕ → E.Carrier) => match x with
      | none => (Sum.inl () : Unit ⊕ (ℕ → E.Carrier)) | some u => Sum.inr u)
    (inferInstance : MeasurableSpace (Unit ⊕ (ℕ → E.Carrier))) = _
  apply congrArg (fun f : Option (ℕ → E.Carrier) → Unit ⊕ (ℕ → E.Carrier) =>
    MeasurableSpace.comap f (inferInstance : MeasurableSpace (Unit ⊕ (ℕ → E.Carrier))))
  funext x
  cases x <;> rfl

theorem standardBorel_comap_equiv {X Y : Type} [MeasurableSpace Y]
    [StandardBorelSpace Y] (e : X ≃ Y) :
    @StandardBorelSpace X (MeasurableSpace.comap e inferInstance) := by
  obtain ⟨t,ht,hp⟩ := StandardBorelSpace.polish (α := Y)
  letI : TopologicalSpace Y := t
  letI : BorelSpace Y := ht
  letI : PolishSpace Y := hp
  letI : TopologicalSpace X := TopologicalSpace.induced e inferInstance
  letI : MeasurableSpace X := MeasurableSpace.comap e inferInstance
  letI : PolishSpace X := e.polishSpace_induced
  letI : BorelSpace X := ⟨by
    change MeasurableSpace.comap e _ = @borel X (TopologicalSpace.induced e _)
    rw [borel_comap,← BorelSpace.measurable_eq]⟩
  infer_instance

theorem standardBorel_sum {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] : StandardBorelSpace (X ⊕ Y) := by
  obtain ⟨tX,hbX,hpX⟩ := StandardBorelSpace.polish (α := X)
  obtain ⟨tY,hbY,hpY⟩ := StandardBorelSpace.polish (α := Y)
  letI : TopologicalSpace X := tX
  letI : TopologicalSpace Y := tY
  letI : BorelSpace X := hbX
  letI : BorelSpace Y := hbY
  letI : PolishSpace X := hpX
  letI : PolishSpace Y := hpY
  have hb : (inferInstance : MeasurableSpace (X ⊕ Y)) = borel (X ⊕ Y) := by
    apply le_antisymm
    · intro s hs
      obtain ⟨hsX,hsY⟩ := measurableSet_sum_iff.mp hs
      letI : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
      letI : BorelSpace (X ⊕ Y) := ⟨rfl⟩
      exact MeasurableSet.of_union_range_cover
        Topology.IsOpenEmbedding.inl.measurableEmbedding Topology.IsOpenEmbedding.inr.measurableEmbedding
        (by intro z _; cases z <;> simp) hsX hsY
    · have hL : @Measurable X (X ⊕ Y) inferInstance (borel (X ⊕ Y)) Sum.inl := by
        rw [BorelSpace.measurable_eq (α := X)]
        exact continuous_inl.borel_measurable
      have hR : @Measurable Y (X ⊕ Y) inferInstance (borel (X ⊕ Y)) Sum.inr := by
        rw [BorelSpace.measurable_eq (α := Y)]
        exact continuous_inr.borel_measurable
      have hi : @Measurable (X ⊕ Y) (X ⊕ Y) inferInstance (borel (X ⊕ Y)) id :=
        measurable_fun_sum (f := id) hL hR
      simpa only [MeasurableSpace.comap_id] using hi.comap_le
  letI : BorelSpace (X ⊕ Y) := ⟨hb⟩
  letI : PolishSpace (X ⊕ Y) :=
    { toSecondCountableTopology := inferInstance
      toIsCompletelyMetrizableSpace := inferInstance }
  infer_instance

theorem regular_cantorEquality : RegularRelation cantorEquality := by
  refine ⟨⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩,
    ⟨fun _ => false⟩,?_,?_⟩
  · change StandardBorelSpace (ℕ → Bool)
    infer_instance
  · change MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | p.1 = p.2}
    exact measurableSet_eq_fun measurable_fst measurable_snd

theorem equivalence_countableSetJump {X : Type} {E : X → X → Prop}
    (hE : Equivalence E) : Equivalence (CountableSetJumpRelation E) := by
  constructor
  · intro x
    cases x with
    | none => trivial
    | some u => exact ⟨fun i => ⟨i,hE.refl _⟩,fun i => ⟨i,hE.refl _⟩⟩
  · intro x y h
    cases x <;> cases y
    · trivial
    · exact False.elim h
    · exact False.elim h
    · exact ⟨fun j => by obtain ⟨i,hi⟩ := h.2 j; exact ⟨i,hE.symm hi⟩,
        fun i => by obtain ⟨j,hj⟩ := h.1 i; exact ⟨j,hE.symm hj⟩⟩
  · intro x y z hxy hyz
    cases x <;> cases y <;> cases z
    · trivial
    · exact False.elim hyz
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hyz
    · exact ⟨fun i => by
        obtain ⟨j,hj⟩ := hxy.1 i
        obtain ⟨k,hk⟩ := hyz.1 j
        exact ⟨k,hE.trans hj hk⟩,
        fun k => by
        obtain ⟨j,hj⟩ := hyz.2 k
        obtain ⟨i,hi⟩ := hxy.2 j
        exact ⟨i,hE.trans hi hj⟩⟩

theorem regular_countableProduct (E : ℕ → CodedRelation)
    (hE : ∀ n, RegularRelation (E n)) : RegularRelation (countableProduct E) := by
  letI : ∀ n, StandardBorelSpace (E n).Carrier := fun n => (hE n).standardBorel
  refine ⟨?_,⟨fun n => Classical.choice (hE n).nonempty⟩,?_,?_⟩
  · exact ⟨fun _ n => (hE n).equivalence.refl _,
      fun h n => (hE n).equivalence.symm (h n),
      fun h k n => (hE n).equivalence.trans (h n) (k n)⟩
  · change StandardBorelSpace (∀ n, (E n).Carrier)
    infer_instance
  · change MeasurableSet {p : (∀ n, (E n).Carrier) × (∀ n, (E n).Carrier) |
      ∀ n, (E n).rel (p.1 n) (p.2 n)}
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro n
    exact (hE n).measurable_graph.preimage
      (f := fun p : (∀ n, (E n).Carrier) × (∀ n, (E n).Carrier) => (p.1 n,p.2 n))
      (((measurable_pi_apply n).comp measurable_fst).prodMk
        ((measurable_pi_apply n).comp measurable_snd))

theorem regular_setJump (E : CodedRelation) (hE : RegularRelation E) :
    RegularRelation (setJump E) := by
  letI : StandardBorelSpace E.Carrier := hE.standardBorel
  letI : StandardBorelSpace (Unit ⊕ (ℕ → E.Carrier)) := standardBorel_sum
  letI : MeasurableSpace (Option (ℕ → E.Carrier)) := (setJump E).measurableSpace
  have hc : Measurable (optionSumEquiv (ℕ → E.Carrier)) := by
    change @Measurable (Option (ℕ → E.Carrier)) (Unit ⊕ (ℕ → E.Carrier))
      (setJump E).measurableSpace
      inferInstance (optionSumEquiv (ℕ → E.Carrier))
    rw [setJump_measurableSpace_eq]
    exact comap_measurable _
  refine ⟨equivalence_countableSetJump hE.equivalence,⟨none⟩,?_,?_⟩
  · change @StandardBorelSpace (Option (ℕ → E.Carrier))
      (setJump E).measurableSpace
    rw [setJump_measurableSpace_eq]
    exact standardBorel_comap_equiv (optionSumEquiv (ℕ → E.Carrier))
  change MeasurableSet {p : Option (ℕ → E.Carrier) × Option (ℕ → E.Carrier) |
    CountableSetJumpRelation E.rel p.1 p.2}
  let x₀ : ℕ → E.Carrier := fun _ => Classical.choice hE.nonempty
  let get : Option (ℕ → E.Carrier) → (ℕ → E.Carrier) :=
    fun x => (Sum.elim (fun _ : Unit => x₀) id) (optionSumEquiv _ x)
  have hg : Measurable get := (measurable_const.sumElim measurable_id).comp hc
  have hn : MeasurableSet {x : Option (ℕ → E.Carrier) | x = none} := by
    convert (measurableSet_singleton (Sum.inl () : Unit ⊕ (ℕ → E.Carrier))).preimage hc using 1
    ext x
    cases x <;> simp [optionSumEquiv]
  have hseq : MeasurableSet {p : (ℕ → E.Carrier) × (ℕ → E.Carrier) |
      (∀ i, ∃ j, E.rel (p.1 i) (p.2 j)) ∧ (∀ j, ∃ i, E.rel (p.1 i) (p.2 j))} := by
    have hcoord (i j : ℕ) : MeasurableSet {p : (ℕ → E.Carrier) × (ℕ → E.Carrier) |
        E.rel (p.1 i) (p.2 j)} := hE.measurable_graph.preimage
      (f := fun p : (ℕ → E.Carrier) × (ℕ → E.Carrier) => (p.1 i,p.2 j))
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd))
    simpa only [setOf_and,setOf_forall,setOf_exists] using
      (MeasurableSet.iInter (fun i => MeasurableSet.iUnion (hcoord i))).inter
        (MeasurableSet.iInter (fun j => MeasurableSet.iUnion (fun i => hcoord i j)))
  have hpair := hseq.preimage ((hg.comp measurable_fst).prodMk (hg.comp measurable_snd))
  have hnone := (hn.preimage measurable_fst).inter (hn.preimage measurable_snd)
  have hsome := ((hn.preimage measurable_fst).compl.inter
    (hn.preimage measurable_snd).compl).inter hpair
  convert hnone.union hsome using 1
  ext p
  rcases p with ⟨x,y⟩
  cases x <;> cases y <;> simp [CountableSetJumpRelation,get,optionSumEquiv]

/-- Every tower code, with the fixed sigma algebra in the definitions, is a
nonempty standard Borel space and carries a Borel equivalence relation. -/
theorem regular_fsTower (a : Ordinal.{0}) : RegularRelation (fsTower a) := by
  induction a using Ordinal.limitRecOn with
  | zero => simpa only [fsTower_zero] using regular_cantorEquality
  | add_one a ih => simpa only [fsTower_add_one] using regular_setJump (fsTower a) ih
  | limit a ha ih =>
    rw [fsTower_limit a ha]
    exact regular_countableProduct _ (fun n =>
      ih (fundamentalSequence a ha n) (fundamentalSequence_lt a ha n))

end FSCofinality
