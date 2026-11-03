import FSCofinalityProof.CosetConstructionFiniteEval
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction

theorem liftFinite_none_iff {C Z : Type} (base : Z) (f : C → Option Z) (A : Finset C) :
    liftFinite base f A = none ↔ ∃ c ∈ A, f c = none := by
  simp [liftFinite]

private theorem getD_eq_iff {Z : Type} (base : Z) (x y : Option Z)
    (hx : x ≠ none) (hy : y ≠ none) : x.getD base = y.getD base ↔ x=y := by
  cases x <;> cases y <;> simp_all

theorem liftFinite_eq_iff {C D Z : Type} (base : Z) (f : C → Option Z) (g : D → Option Z)
    (A : Finset C) (B : Finset D) :
    liftFinite base f A = liftFinite base g B ↔
      ((∃ c ∈ A, f c = none) ∧ (∃ d ∈ B, g d = none)) ∨
      ((∀ c ∈ A, f c ≠ none) ∧ (∀ d ∈ B, g d ≠ none) ∧
        (∀ c ∈ A, ∃ d ∈ B, f c = g d) ∧ (∀ d ∈ B, ∃ c ∈ A, f c = g d)) := by
  have hbadF : (∃ c ∈ A, f c = none) ↔ ¬ (∀ c ∈ A, f c ≠ none) := by simp
  have hbadG : (∃ d ∈ B, g d = none) ↔ ¬ (∀ d ∈ B, g d ≠ none) := by simp
  by_cases hA : ∀ c ∈ A, f c ≠ none <;> by_cases hB : ∀ d ∈ B, g d ≠ none
  · rw [liftFinite_some base f A hA,liftFinite_some base g B hB,Option.some.injEq]
    have hA' : ¬ ∃ c ∈ A, f c = none := by simpa using hA
    have hB' : ¬ ∃ d ∈ B, g d = none := by simpa using hB
    simp only [hA',hB',false_and,false_or]
    constructor
    · intro hEq
      refine ⟨hA,hB,?_,?_⟩
      · intro c hc
        have hm : (f c).getD base ∈ B.image (fun d => (g d).getD base) :=
          hEq ▸ Finset.mem_image.mpr ⟨c,hc,rfl⟩
        obtain ⟨d,hd,heq⟩ := Finset.mem_image.mp hm
        exact ⟨d,hd,(getD_eq_iff base _ _ (hA c hc) (hB d hd)).mp heq.symm⟩
      · intro d hd
        have hm : (g d).getD base ∈ A.image (fun c => (f c).getD base) :=
          hEq.symm ▸ Finset.mem_image.mpr ⟨d,hd,rfl⟩
        obtain ⟨c,hc,heq⟩ := Finset.mem_image.mp hm
        exact ⟨c,hc,(getD_eq_iff base _ _ (hA c hc) (hB d hd)).mp heq⟩
    · rintro ⟨_,_,hfg,hgf⟩
      apply Finset.ext
      intro z
      constructor
      · rintro hz
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨d,hd,heq⟩ := hfg c hc
        exact Finset.mem_image.mpr ⟨d,hd,congrArg (fun o => o.getD base) heq.symm⟩
      · rintro hz
        obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨c,hc,heq⟩ := hgf d hd
        exact Finset.mem_image.mpr ⟨c,hc,congrArg (fun o => o.getD base) heq⟩
  · rw [liftFinite_some base f A hA,
      (liftFinite_none_iff base g B).mpr (hbadG.mpr hB)]
    constructor
    · intro hEq; cases hEq
    · rintro (⟨hbad,_⟩ | ⟨_,hgood,_,_⟩)
      · obtain ⟨c,hc,hn⟩ := hbad
        exact False.elim (hA c hc hn)
      · exact False.elim (hB hgood)
  · rw [(liftFinite_none_iff base f A).mpr (hbadF.mpr hA),liftFinite_some base g B hB]
    constructor
    · intro hEq; cases hEq
    · rintro (⟨_,hbad⟩ | ⟨hgood,_,_,_⟩)
      · obtain ⟨d,hd,hn⟩ := hbad
        exact False.elim (hB d hd hn)
      · exact False.elim (hA hgood)
  · rw [(liftFinite_none_iff base f A).mpr (hbadF.mpr hA),
      (liftFinite_none_iff base g B).mpr (hbadG.mpr hB)]
    exact ⟨fun _ => Or.inl ⟨hbadF.mpr hA,hbadG.mpr hB⟩,fun _ => rfl⟩

theorem measurableSet_liftFinite_none {X C Z : Type} [MeasurableSpace X] [Countable C]
    (base : Z) (F : C → X → Option Z)
    (hnone : ∀ c, MeasurableSet {x | F c x = none}) (A : Finset C) :
    MeasurableSet {x | liftFinite base (fun c => F c x) A = none} := by
  simp only [liftFinite_none_iff,← exists_prop,setOf_exists]
  exact MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ : c∈A => hnone c))

theorem measurableSet_liftFinite_eq {X Y C D Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [Countable C] [Countable D]
    (base : Z) (F : C → X → Option Z) (G : D → Y → Option Z)
    (hF : ∀ c, MeasurableSet {x | F c x = none})
    (hG : ∀ d, MeasurableSet {y | G d y = none})
    (heq : ∀ c d, MeasurableSet {p : X × Y | F c p.1 = G d p.2})
    (A : Finset C) (B : Finset D) :
    MeasurableSet {p : X × Y |
      liftFinite base (fun c => F c p.1) A = liftFinite base (fun d => G d p.2) B} := by
  simp only [liftFinite_eq_iff,setOf_or,setOf_and]
  apply MeasurableSet.union
  · simpa only [Set.preimage_setOf_eq,liftFinite_none_iff] using
      ((measurableSet_liftFinite_none base F hF A).preimage measurable_fst).inter
        ((measurableSet_liftFinite_none base G hG B).preimage measurable_snd)
  · have hpresentF : MeasurableSet {p : X × Y | ∀ c ∈ A, F c p.1 ≠ none} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter (fun c => MeasurableSet.iInter (fun _ =>
        ((hF c).preimage measurable_fst).compl))
    have hpresentG : MeasurableSet {p : X × Y | ∀ d ∈ B, G d p.2 ≠ none} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter (fun d => MeasurableSet.iInter (fun _ =>
        ((hG d).preimage measurable_snd).compl))
    have hfg : MeasurableSet {p : X × Y | ∀ c ∈ A, ∃ d ∈ B, F c p.1 = G d p.2} := by
      simp only [← exists_prop,setOf_forall,setOf_exists]
      exact MeasurableSet.iInter (fun c => MeasurableSet.iInter (fun _ =>
        MeasurableSet.iUnion (fun d => MeasurableSet.iUnion (fun _ => heq c d))))
    have hgf : MeasurableSet {p : X × Y | ∀ d ∈ B, ∃ c ∈ A, F c p.1 = G d p.2} := by
      simp only [← exists_prop,setOf_forall,setOf_exists]
      exact MeasurableSet.iInter (fun d => MeasurableSet.iInter (fun _ =>
        MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ => heq c d))))
    exact hpresentF.inter (hpresentG.inter (hfg.inter hgf))

theorem option_map_eq_iff_of_injective {Z W : Type} (k : Z → W) (hk : Function.Injective k)
    (u v : Option Z) : u.map k = v.map k ↔ u=v := by
  cases u <;> cases v <;> simp [hk.eq_iff]

theorem option_map_none_iff {Z W : Type} (k : Z → W) (u : Option Z) :
    u.map k = none ↔ u=none := by cases u <;> simp

theorem measurableSet_map_liftFinite_eq {X Y C D Z W : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [Countable C] [Countable D]
    (base : Z) (F : C → X → Option Z) (G : D → Y → Option Z)
    (hF : ∀ c, MeasurableSet {x | F c x = none})
    (hG : ∀ d, MeasurableSet {y | G d y = none})
    (heq : ∀ c d, MeasurableSet {p : X × Y | F c p.1 = G d p.2})
    (A : Finset C) (B : Finset D) (k : Finset Z → W) (hk : Function.Injective k) :
    MeasurableSet {p : X × Y |
      (liftFinite base (fun c => F c p.1) A).map k =
        (liftFinite base (fun d => G d p.2) B).map k} := by
  simpa only [option_map_eq_iff_of_injective k hk] using
    measurableSet_liftFinite_eq base F G hF hG heq A B

theorem measurableSet_finite_match {X Y C Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [Countable C]
    (F : C → X → Option Z) (G : Y → Option Z)
    (heq : ∀ c, MeasurableSet {p : X × Y | F c p.1 = G p.2}) (A : Finset C) :
    MeasurableSet {p : X × Y | ∃ c ∈ A, F c p.1 = G p.2} := by
  simp only [← exists_prop,setOf_exists]
  exact MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ : c∈A => heq c))

end FSCofinality.CosetConstruction
