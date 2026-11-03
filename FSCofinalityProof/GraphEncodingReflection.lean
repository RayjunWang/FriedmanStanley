import FSCofinalityProof.GraphEncodingIncidence

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.GraphCoding

theorem element_range_iff {L : CountableRelationalLanguage} (M : Structures L)
    (v : IncidenceVertex L) :
    v ∈ Set.range (IncidenceVertex.element (L := L)) ↔ incidenceColor M v = 0 := by
  constructor
  · rintro ⟨n,rfl⟩
    rfl
  · intro h
    obtain ⟨n,hn⟩ := (incidenceColor_eq_zero_iff M v).mp h
    exact ⟨n,hn.symm⟩

def elementRangeEquiv (L : CountableRelationalLanguage) :
    ℕ ≃ Set.range (IncidenceVertex.element (L := L)) :=
  Equiv.ofInjective IncidenceVertex.element (fun _ _ h => IncidenceVertex.element.inj h)

def elementSubtypeEquiv {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v)) :
    Set.range (IncidenceVertex.element (L := L)) ≃
      Set.range (IncidenceVertex.element (L := L)) :=
  e.subtypeEquiv (fun v => by rw [element_range_iff M,element_range_iff N,hc v])

def elementPermutation {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v)) : ℕ ≃ ℕ :=
  ((elementRangeEquiv L).trans (elementSubtypeEquiv e hc)).trans (elementRangeEquiv L).symm

theorem elementPermutation_spec {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v)) (n : ℕ) :
    e (.element n) = .element (elementPermutation e hc n) := by
  have h := congrArg Subtype.val ((elementRangeEquiv L).apply_symm_apply
    (elementSubtypeEquiv e hc (elementRangeEquiv L n)))
  exact h.symm

theorem tuple_image {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v)) (c : Coordinate L) :
    ∃ b : Coordinate L, e (.tuple c) = .tuple b ∧ b.1 = c.1 ∧ M c = N b := by
  have hh := hc (.tuple c)
  cases he : e (.tuple c) with
  | element n =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    omega
  | occurrence b i =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    omega
  | tuple b =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    have hp : Nat.pair (symbolCode L c.1) (M c).toNat =
        Nat.pair (symbolCode L b.1) (N b).toNat := by omega
    obtain ⟨hs,hb⟩ := Nat.pair_eq_pair.mp hp
    refine ⟨b,rfl,(symbolCode L).injective hs.symm,?_⟩
    cases hm : M c <;> cases hn : N b <;> simp_all

theorem occurrence_image {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v))
    (c : Coordinate L) (i : Fin (L.arity c.1)) :
    ∃ (b : Coordinate L) (j : Fin (L.arity b.1)),
      e (.occurrence c i) = .occurrence b j ∧ j.val = i.val := by
  have hh := hc (.occurrence c i)
  cases he : e (.occurrence c i) with
  | element n =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    omega
  | tuple b =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    omega
  | occurrence b j =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    exact ⟨b,j,rfl,by omega⟩

theorem isomorphic_of_incidence {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v))
    (hE : ∀ v w, IncidenceAdj v w ↔ IncidenceAdj (e v) (e w)) : Isomorphic M N := by
  let f := elementPermutation e hc
  refine ⟨f,fun s a => ?_⟩
  obtain ⟨⟨t,b⟩,ht,hsym,htruth⟩ := tuple_image e hc (⟨s,a⟩ : Coordinate L)
  dsimp at hsym
  subst t
  have hb : b = f ∘ a := by
    funext i
    obtain ⟨c,j,hj,hji⟩ := occurrence_image e hc (⟨s,a⟩ : Coordinate L) i
    have htu : IncidenceAdj (.occurrence (⟨s,a⟩ : Coordinate L) i) (.tuple ⟨s,a⟩) := rfl
    have htu' := (hE _ _).mp htu
    rw [hj,ht] at htu'
    change c = (⟨s,b⟩ : Coordinate L) at htu'
    subst c
    have hji' : j = i := Fin.ext hji
    subst j
    have hel : IncidenceAdj (.occurrence (⟨s,a⟩ : Coordinate L) i) (.element (a i)) := rfl
    have hel' := (hE _ _).mp hel
    rw [hj,elementPermutation_spec e hc (a i)] at hel'
    exact hel'
  simpa only [hb] using htruth

theorem incidence_encoding_iff {L : CountableRelationalLanguage} (M N : Structures L) :
    Isomorphic M N ↔ ∃ e : IncidenceVertex L ≃ IncidenceVertex L,
      (∀ v, incidenceColor M v = incidenceColor N (e v)) ∧
      ∀ v w, IncidenceAdj v w ↔ IncidenceAdj (e v) (e w) := by
  constructor
  · exact Isomorphic.incidence
  · rintro ⟨e,hc,hE⟩
    exact isomorphic_of_incidence e hc hE

end FSCofinality.GraphCoding
