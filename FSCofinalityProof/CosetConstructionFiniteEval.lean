import Mathlib.Data.Finset.Image
import Mathlib.Tactic

noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.CosetConstruction

def liftFinite {C Z : Type*} (base : Z) (f : C → Option Z) (A : Finset C) : Option (Finset Z) :=
  if ∀ c ∈ A, f c ≠ none then some (A.image (fun c => (f c).getD base)) else none

theorem liftFinite_some {C Z : Type*} (base : Z) (f : C → Option Z) (A : Finset C)
    (hA : ∀ c ∈ A, f c ≠ none) :
    liftFinite base f A = some (A.image (fun c => (f c).getD base)) := by
  simp only [liftFinite,if_pos hA]

theorem liftFinite_mem {C Z : Type*} (base : Z) (f : C → Option Z) (A : Finset C) (B : Finset Z)
    (h : liftFinite base f A = some B) : ∀ u ∈ B, ∃ c ∈ A, f c = some u := by
  classical
  unfold liftFinite at h
  split_ifs at h with hA
  · cases h
    intro u hu
    obtain ⟨c,hc,hu⟩ := Finset.mem_image.mp hu
    refine ⟨c,hc,?_⟩
    cases heq : f c with
    | none => exact False.elim (hA c hc heq)
    | some z => simpa only [heq,Option.getD_some,Option.some.injEq] using hu

theorem liftFinite_mem_iff {C Z : Type*} (base : Z) (f : C → Option Z) (A : Finset C)
    (B : Finset Z) (h : liftFinite base f A = some B) (u : Z) :
    u ∈ B ↔ ∃ c ∈ A, f c = some u := by
  constructor
  · exact liftFinite_mem base f A B h u
  · rintro ⟨c,hc,hv⟩
    unfold liftFinite at h
    split_ifs at h with hA
    cases h
    exact Finset.mem_image.mpr ⟨c,hc,by simp only [hv,Option.getD_some]⟩

theorem liftFinite_covers {C Z : Type*} (base : Z) (f : C → Option Z) (B : Finset Z)
    (hB : ∀ u ∈ B, ∃ c, f c = some u) : ∃ A : Finset C, liftFinite base f A = some B := by
  classical
  let g : B → C := fun u => Classical.choose (hB u.val u.property)
  have hg (u : B) : f (g u) = some u.val := Classical.choose_spec (hB u.val u.property)
  let A : Finset C := Finset.univ.image g
  have hA : ∀ c ∈ A, f c ≠ none := by
    rintro c hc
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hc
    rw [hg]
    simp
  refine ⟨A,?_⟩
  rw [liftFinite_some base f A hA]
  congr 1
  ext u
  constructor
  · intro hu
    obtain ⟨c,hc,hu⟩ := Finset.mem_image.mp hu
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hc
    have heq : v.val = u := by simpa only [hg,Option.getD_some] using hu
    exact heq ▸ v.property
  · intro hu
    exact Finset.mem_image.mpr ⟨g ⟨u,hu⟩,
      Finset.mem_image.mpr ⟨⟨u,hu⟩,Finset.mem_univ _,rfl⟩,
      by simp only [hg,Option.getD_some]⟩

end FSCofinality.CosetConstruction
