import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option autoImplicit false
noncomputable section
open Set

namespace FSCofinality.CosetConstruction

theorem measurableSet_selected {X C : Type} [MeasurableSpace X]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]
    (P : C → X → Prop) (hP : ∀ c, MeasurableSet {x | P c x})
    (f : X → C) (hf : Measurable f) : MeasurableSet {x | P (f x) x} := by
  have heq : {x | P (f x) x} = ⋃ c, ({x | f x = c} ∩ {x | P c x}) := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion,mem_inter_iff]
    exact ⟨fun h => ⟨f x,rfl,h⟩,fun ⟨c,hc,h⟩ => hc ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun c => (hf (measurableSet_singleton c)).inter (hP c))

theorem measurableSet_selected₂ {X C D : Type} [MeasurableSpace X]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D]
    (P : C → D → X → Prop) (hP : ∀ c d, MeasurableSet {x | P c d x})
    (f : X → C) (g : X → D) (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | P (f x) (g x) x} := by
  apply measurableSet_selected (fun c x => P c (g x) x) _ f hf
  intro c
  exact measurableSet_selected (P c) (hP c) g hg

end FSCofinality.CosetConstruction
