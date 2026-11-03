import FSCofinalityProof.TokenAtomicExtensions
import FSCofinalityProof.ParameterClassCopies

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

def ForthExtension {L : CountableRelationalLanguage} (M N : Structures L) : Prop :=
  ∀ R : List (ℕ × ℕ), AtomicCompatible M N {p | p ∈ R} →
    ∀ x : ℕ, ∃ y : ℕ, AtomicCompatible M N {p | p ∈ R ++ [(x,y)]}

/-- Old domain points can be handled without invoking a realization lemma;
only genuinely new points require the construction's extension property. -/
theorem forthExtension_of_fresh {L : CountableRelationalLanguage} {M N : Structures L}
    (h : ∀ R : List (ℕ × ℕ), AtomicCompatible M N {p | p ∈ R} →
      ∀ x : ℕ, (∀ p ∈ R, x ≠ p.1) →
        ∃ y : ℕ, AtomicCompatible M N {p | p ∈ R ++ [(x,y)]}) : ForthExtension M N := by
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

theorem copyTest_of_extensions {L : CountableRelationalLanguage} {M N : Structures L}
    (hempty : AtomicCompatible M N ∅) (hMN : ForthExtension M N)
    (hNM : ForthExtension N M) : CopyCoding.CopyTest M N := by
  refine ⟨hempty,fun R hR => ⟨hMN R hR,?_⟩⟩
  intro y
  obtain ⟨x,hx⟩ := hNM (R.map Prod.swap) hR.swap_list y
  refine ⟨x,?_⟩
  have hh := hx.swap_list
  simpa [List.map_map,Function.comp_def] using hh

theorem isomorphic_of_extensions {L : CountableRelationalLanguage} {M N : Structures L}
    (hempty : AtomicCompatible M N ∅) (hMN : ForthExtension M N)
    (hNM : ForthExtension N M) : Isomorphic M N :=
  (copyTest_of_extensions hempty hMN hNM).isomorphic

/-- Once the actual one-point realization theorem has been proved for a
family, the measurable isomorphism selector has no further choice inputs. -/
def familyIsomorphism {P : Type} {L : CountableRelationalLanguage}
    (M : P → Structures L) (hArity : ∀ s, 0 < L.arity s)
    (hExtension : ∀ p q, ForthExtension (M p) (M q)) (base : P) : P → PermutationGroup :=
  CopyCoding.chosenIsomorphism M (fun _ => M base) (fun p =>
    copyTest_of_extensions (AtomicCompatible.empty_of_positive_arity _ _ hArity)
      (hExtension p base) (hExtension base p))

theorem familyIsomorphism_preserves {P : Type} {L : CountableRelationalLanguage}
    (M : P → Structures L) (hArity : ∀ s, 0 < L.arity s)
    (hExtension : ∀ p q, ForthExtension (M p) (M q)) (base p : P) :
    ∀ s a, M p ⟨s,a⟩ = M base ⟨s,(familyIsomorphism M hArity hExtension base p).toFun ∘ a⟩ :=
  CopyCoding.chosenIsomorphism_preserves _ _ _ p

theorem measurable_familyIsomorphism {P : Type} [MeasurableSpace P]
    {L : CountableRelationalLanguage} (M : P → Structures L)
    (hArity : ∀ s, 0 < L.arity s)
    (hExtension : ∀ p q, ForthExtension (M p) (M q)) (base : P)
    (hM : Measurable M) : Measurable (familyIsomorphism M hArity hExtension base) :=
  CopyCoding.measurable_chosenIsomorphism _ _ _ hM measurable_const

end FSCofinality.PartialIso
