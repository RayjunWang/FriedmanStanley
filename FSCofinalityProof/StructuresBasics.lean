import Definitions.Def_FSCofinalityStructures20261102

set_option autoImplicit false
noncomputable section

namespace FSCofinality

theorem Isomorphic.refl {L : CountableRelationalLanguage} (M : Structures L) :
    Isomorphic M M := ⟨Equiv.refl ℕ, fun _ _ => rfl⟩

theorem Isomorphic.symm {L : CountableRelationalLanguage} {M N : Structures L}
    (h : Isomorphic M N) : Isomorphic N M := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,fun s a => ?_⟩
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using (he s (e.symm ∘ a)).symm

theorem Isomorphic.trans {L : CountableRelationalLanguage} {M N P : Structures L}
    (hMN : Isomorphic M N) (hNP : Isomorphic N P) : Isomorphic M P := by
  obtain ⟨e,he⟩ := hMN
  obtain ⟨f,hf⟩ := hNP
  refine ⟨e.trans f,fun s a => ?_⟩
  exact (he s a).trans (hf s (e ∘ a))

theorem isomorphic_equivalence (L : CountableRelationalLanguage) :
    Equivalence (@Isomorphic L) :=
  ⟨Isomorphic.refl,Isomorphic.symm,Isomorphic.trans⟩

def structuresSetoid (L : CountableRelationalLanguage) : Setoid (Structures L) :=
  ⟨Isomorphic,isomorphic_equivalence L⟩

theorem IsInvariant.mem_iff {L : CountableRelationalLanguage} {K : Set (Structures L)}
    (hK : IsInvariant K) {M N : Structures L} (hMN : Isomorphic M N) : M ∈ K ↔ N ∈ K :=
  ⟨fun hM => hK hM hMN,fun hN => hK hN hMN.symm⟩

theorem GraphIsomorphic.refl (G : GraphSpace) : GraphIsomorphic G G :=
  ⟨Equiv.refl ℕ,fun _ _ => rfl⟩

theorem GraphIsomorphic.symm {G H : GraphSpace} (h : GraphIsomorphic G H) :
    GraphIsomorphic H G := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,fun m n => ?_⟩
  simpa only [Equiv.apply_symm_apply] using (he (e.symm m) (e.symm n)).symm

theorem GraphIsomorphic.trans {G H K : GraphSpace}
    (hGH : GraphIsomorphic G H) (hHK : GraphIsomorphic H K) : GraphIsomorphic G K := by
  obtain ⟨e,he⟩ := hGH
  obtain ⟨f,hf⟩ := hHK
  exact ⟨e.trans f,fun m n => (he m n).trans (hf (e m) (e n))⟩

theorem graphIsomorphic_equivalence : Equivalence GraphIsomorphic :=
  ⟨GraphIsomorphic.refl,GraphIsomorphic.symm,GraphIsomorphic.trans⟩

def graphSetoid : Setoid GraphSpace := ⟨GraphIsomorphic,graphIsomorphic_equivalence⟩

theorem BorelReducible.refl {X : Type} [MeasurableSpace X] (E : X → X → Prop) :
    BorelReducible E E := ⟨id,measurable_id,fun _ _ => Iff.rfl⟩

theorem BorelReducible.trans {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {E : X → X → Prop} {F : Y → Y → Prop} {R : Z → Z → Prop}
    (hEF : BorelReducible E F) (hFR : BorelReducible F R) : BorelReducible E R := by
  obtain ⟨f,hf,hredf⟩ := hEF
  obtain ⟨g,hg,hredg⟩ := hFR
  exact ⟨g ∘ f,hg.comp hf,fun x y => (hredf x y).trans (hredg (f x) (f y))⟩

theorem CodedRelation.Reduces.refl (E : CodedRelation) : E.Reduces E :=
  BorelReducible.refl E.rel

theorem CodedRelation.Reduces.trans {E F R : CodedRelation}
    (hEF : E.Reduces F) (hFR : F.Reduces R) : E.Reduces R :=
  BorelReducible.trans hEF hFR

theorem BorelReducible.target_nonempty {X Y : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X]
    {E : X → X → Prop} {F : Y → Y → Prop} (h : BorelReducible E F) : Nonempty Y := by
  obtain ⟨f,_,_⟩ := h
  exact ⟨f (Classical.choice inferInstance)⟩

end FSCofinality
