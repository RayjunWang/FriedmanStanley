import FSCofinalityProof.BorelClosedChoice
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology TopologicalSpace

namespace FSCofinality

/-- The image of a continuous homomorphism of Polish groups is Borel.
The proof selects a canonical point in each closed kernel coset and applies
Lusin--Souslin to the resulting Borel transversal. -/
theorem measurableSet_range_continuousHom {G H : Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [PolishSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (f : G →* H) (hf : Continuous f) : MeasurableSet (range f) := by
  letI := upgradeIsCompletelyMetrizable G
  let S : G → Set G := fun x => {y | f y = f x}
  have hne (x : G) : (S x).Nonempty := ⟨x,rfl⟩
  have hclosed (x : G) : IsClosed (S x) := isClosed_eq hf continuous_const
  have hHit (U : Set G) (hU : IsOpen U) : MeasurableSet {x | (S x ∩ U).Nonempty} := by
    have heq : {x | (S x ∩ U).Nonempty} = ⋃ n : f.ker, {x | x*n.val ∈ U} := by
      ext x
      simp only [mem_setOf_eq,mem_iUnion]
      constructor
      · rintro ⟨y,hy,hyU⟩
        have hfy : f y = f x := hy
        have hker : x⁻¹*y ∈ f.ker := by
          change f (x⁻¹*y) = 1
          rw [map_mul,map_inv,hfy,inv_mul_cancel]
        exact ⟨⟨x⁻¹*y,hker⟩,by simpa only [mul_inv_cancel_left] using hyU⟩
      · rintro ⟨n,hn⟩
        refine ⟨x*n.val,?_,hn⟩
        change f (x*n.val) = f x
        rw [map_mul,show f n.val = 1 from n.property,mul_one]
    rw [heq]
    exact (isOpen_iUnion (fun n : f.ker => hU.preimage
      (continuous_id.mul continuous_const))).measurableSet
  obtain ⟨s,hs,hmem,hconstant⟩ := ClosedChoice.exists_measurable_closed_selector S hne hclosed hHit
  have hvalue (x : G) : f (s x) = f x := hmem x
  have hequal (x y : G) (hxy : f x = f y) : S x = S y := by
    ext z
    change (f z = f x) ↔ f z = f y
    rw [hxy]
  let R : Set G := {x | s x = x}
  have hR : MeasurableSet R := measurableSet_eq_fun hs measurable_id
  have hinj : R.InjOn f := by
    intro x hx y hy hxy
    exact hx.symm.trans ((hconstant x y (hequal x y hxy)).trans hy)
  have himage : f '' R = range f := by
    apply Subset.antisymm
    · rintro _ ⟨x,_,rfl⟩
      exact mem_range_self x
    · rintro _ ⟨x,rfl⟩
      refine ⟨s x,?_,hvalue x⟩
      exact hconstant (s x) x (hequal (s x) x (hvalue x))
  rw [← himage]
  exact hR.image_of_measurable_injOn hf.measurable hinj

end FSCofinality
