import FSCofinalityProof.TokenLiteralMaps

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

theorem literalForth_of_fresh {L : CountableRelationalLanguage} {X Y : Type}
    {M : Diagram L X} {N : Diagram L Y}
    (h : ∀ R : List (X × Y), CompatibleOn M N {p | p ∈ R} →
      ∀ x : X, (∀ p ∈ R, x ≠ p.1) →
        ∃ y : Y, CompatibleOn M N {p | p ∈ R ++ [(x,y)]}) : LiteralForth M N := by
  intro R hR x
  by_cases hfresh : ∀ p ∈ R, x ≠ p.1
  · exact h R hR x hfresh
  · push_neg at hfresh
    obtain ⟨p,hp,hpx⟩ := hfresh
    refine ⟨p.2,hR.mono ?_⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hq
    · have heq : q = (x,p.2) := List.mem_singleton.mp hq
      have hpair : (x,p.2) = p := Prod.ext hpx rfl
      exact heq.symm ▸ hpair.symm ▸ hp

end FSCofinality.PartialIso
