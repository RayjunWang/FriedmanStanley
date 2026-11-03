import FSCofinalityProof.ParameterClassAssembly
import FSCofinalityProof.ParameterClassFibers

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.MarkedCoding

theorem coset_restriction_reduces_class (d : ParameterSequences.Code)
    (hd : ParameterSequences.Valid d)
    (e : ℕ ≃ {n | Distinguished (OrbitCoding.sequenceStructure d) n})
    (hQ : ∀ g : automorphismGroup (OrbitCoding.sequenceStructure d), ∀ n,
      Distinguished (OrbitCoding.sequenceStructure d) n ↔
        Distinguished (OrbitCoding.sequenceStructure d) (g.val.toFun n)) :
    (cosetRelation (DistinguishedRestriction.hom (OrbitCoding.sequenceStructure d)
      {n | Distinguished (OrbitCoding.sequenceStructure d) n} e hQ).range).Reduces
      (classRelation language classSet) := by
  let B := OrbitCoding.sequenceStructure d
  let Q : Set ℕ := {n | Distinguished B n}
  let c (p : PermutationGroup) (j : ℕ) : ℕ := (e (p.symm.toFun j)).val
  have hcinj (p : PermutationGroup) : Function.Injective (c p) := by
    intro i j hij
    apply p.symm.injective
    apply e.injective
    exact Subtype.ext hij
  have hcrange (p : PermutationGroup) : range (c p) = Q := by
    ext n
    constructor
    · rintro ⟨j,rfl⟩
      exact (e (p.symm.toFun j)).property
    · intro hn
      obtain ⟨k,hk⟩ := e.surjective ⟨n,hn⟩
      refine ⟨p.toFun k,?_⟩
      change (e (p.symm.toFun (p.toFun k))).val = n
      have hinv : p.symm.toFun (p.toFun k) = k := p.left_inv k
      rw [hinv,hk]
  let F (p : PermutationGroup) : Structures language :=
    assemble B (ParameterSequences.encode d) (c p)
  have hFmem (p : PermutationGroup) : F p ∈ classSet :=
    assemble_mem_class d hd (c p) (hcinj p) (hcrange p)
  have hFm : Measurable F := by
    apply measurable_assemble _ _ c measurable_const measurable_const
    intro j
    have hp : Measurable (fun p : PermutationGroup => p.symm.toFun j) :=
      ((continuous_apply j).comp continuous_permutationCoordinates.snd).measurable
    exact (measurable_of_countable (fun n => (e n).val)).comp hp
  let f : PermutationGroup → classSet := fun p => ⟨F p,hFmem p⟩
  refine ⟨f,hFm.subtype_mk,?_⟩
  intro p q
  have hmarkers (z : PermutationGroup) : MarkerConditions (F z) := (hFmem z).2.2
  have hchoice (z : PermutationGroup) (j : ℕ) :
      markerChoice (F z) (hmarkers z).1 j = c z j :=
    markerChoice_assemble B _ (c z) (hmarkers z) j
  have hiso : Isomorphic (F p) (F q) ↔ NamedIsomorphic (fun _ : PermutationGroup => B) c p q := by
    have hh := isomorphic_iff_named (hmarkers p) (hmarkers q)
      (show bits (F p) = bits (F q) from rfl)
    simpa only [reduct_assemble,hchoice,NamedIsomorphic,F] using hh
  have hcos := DistinguishedRestriction.named_iff_coset (fun _ : PermutationGroup => B)
    B Q e hQ c (fun _ => 1) (fun _ _ _ => rfl) (fun z => z⁻¹)
    (fun _ _ => rfl) p q
  change CosetRelation _ p q ↔ Isomorphic (F p) (F q)
  apply Iff.trans ?_ hiso.symm
  simpa only [inv_inv] using hcos.symm

theorem closed_restriction_coset_reduces_class (H : Subgroup PermutationGroup)
    (hH : IsClosed (H : Set PermutationGroup))
    (e : ℕ ≃ {n | Distinguished (OrbitCoding.canonicalStructure H) n})
    (hQ : ∀ g : automorphismGroup (OrbitCoding.canonicalStructure H), ∀ n,
      Distinguished (OrbitCoding.canonicalStructure H) n ↔
        Distinguished (OrbitCoding.canonicalStructure H) (g.val.toFun n)) :
    (cosetRelation (DistinguishedRestriction.hom (OrbitCoding.canonicalStructure H)
      {n | Distinguished (OrbitCoding.canonicalStructure H) n} e hQ).range).Reduces
      (classRelation language classSet) := by
  obtain ⟨d,hd,hclosure⟩ := ParameterSequences.exists_valid_sequence H hH
  have hmodel : OrbitCoding.sequenceStructure d = OrbitCoding.canonicalStructure H := by
    rw [← ParameterSequences.canonicalStructure_eq_sequenceStructure d hd,hclosure]
  have h := coset_restriction_reduces_class d hd
  rw [hmodel] at h
  exact h e hQ

end FSCofinality.MarkedCoding
