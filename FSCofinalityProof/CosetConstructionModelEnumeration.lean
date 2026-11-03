import FSCofinalityProof.CosetConstructionTokenModelProperties
import Mathlib.Logic.Equiv.List

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

abbrev Template := ℕ ⊕ Σ s : TokenSort eta, Token ℕ

instance template_countable : Countable (Template eta) := by
  letI := sort_countable eta heta
  exact inferInstanceAs (Countable (ℕ ⊕ Σ _s : TokenSort eta, List ℕ × ℕ))

instance template_infinite : Infinite (Template eta) :=
  Infinite.of_injective (Sum.inl : ℕ → Template eta) Sum.inl_injective

def templateEnumeration : ℕ ≃ Template eta := by
  letI := template_countable eta heta
  exact Classical.choice (inferInstanceAs (Nonempty (ℕ ≃ Template eta)))

def tokenEquiv {U V : Type} (e : U ≃ V) : Token U ≃ Token V :=
  Equiv.prodCongr (Equiv.listEquivOfEquiv e) (Equiv.refl ℕ)

theorem tokenEquiv_apply {U V : Type} (e : U ≃ V) (v : Token U) :
    tokenEquiv e v = mapToken e v := rfl

def templateVertexEquiv (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) : Template eta ≃ Vertex eta heta x :=
  Equiv.sumCongr (Equiv.refl ℕ) (Equiv.sigmaCongrRight (fun s => tokenEquiv (e s)))

theorem templateVertexEquiv_coordinate (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (n : ℕ) :
    templateVertexEquiv eta heta x e (.inl n) = .inl n := rfl

theorem templateVertexEquiv_token (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (s : TokenSort eta) (v : Token ℕ) :
    templateVertexEquiv eta heta x e (.inr ⟨s,v⟩) = .inr ⟨s,mapToken (e s) v⟩ := rfl

def vertexEnumeration (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (x : (fsTower eta).Carrier) : ℕ ≃ Vertex eta heta x :=
  (templateEnumeration eta heta).trans (templateVertexEquiv eta heta x (e x))

theorem vertexEnumeration_coordinate_preimage
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (x : (fsTower eta).Carrier) (n : ℕ) :
    (vertexEnumeration eta heta e x).symm (.inl n) =
      (templateEnumeration eta heta).symm (.inl n) := by
  apply (vertexEnumeration eta heta e x).injective
  simp only [Equiv.apply_symm_apply,vertexEnumeration,Equiv.trans_apply,
    Equiv.apply_symm_apply,templateVertexEquiv_coordinate]

theorem measurable_vertexEnumeration_coordinate_preimage
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s) (n : ℕ) :
    Measurable (fun x => (vertexEnumeration eta heta e x).symm (.inl n)) := by
  simp only [vertexEnumeration_coordinate_preimage]
  exact measurable_const

def templateTokenAt (s : TokenSort eta) : Template eta → Option (Token ℕ)
  | .inl _ => none
  | .inr ⟨t,v⟩ => if t=s then some v else none

def templateCoordinateAt : Template eta → Option ℕ
  | .inl n => some n
  | .inr _ => none

def templateSortOf : Template eta → Option (TokenSort eta)
  | .inl _ => none
  | .inr ⟨s,_⟩ => some s

theorem tokenAt_templateVertexEquiv (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (s : TokenSort eta) (v : Template eta) :
    tokenAt eta heta s (templateVertexEquiv eta heta x e v) =
      (templateTokenAt eta s v).map (mapToken (e s)) := by
  rcases v with n|⟨t,v⟩
  · rfl
  · by_cases h : t=s
    · subst t
      simp [templateVertexEquiv_token,tokenAt,templateTokenAt]
    · simp only [templateVertexEquiv_token,tokenAt,templateTokenAt,dif_neg h,if_neg h,Option.map_none]

theorem coordinateAt_templateVertexEquiv (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (v : Template eta) :
    coordinateAt eta heta (templateVertexEquiv eta heta x e v) = templateCoordinateAt eta v := by
  rcases v with n|⟨s,v⟩ <;> rfl

theorem sortOf_templateVertexEquiv (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (v : Template eta) :
    sortOf eta heta (templateVertexEquiv eta heta x e v) = templateSortOf eta v := by
  rcases v with n|⟨s,v⟩ <;> rfl

end FSCofinality.CosetConstruction.TokenModel
