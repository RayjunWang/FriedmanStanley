import FSCofinalityProof.StructuresBasics
import FSCofinalityProof.GraphEncodingRecovery

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.GraphCoding

def symbolCode (L : CountableRelationalLanguage) : L.Symbol ↪ ℕ := by
  letI := Encodable.ofCountable L.Symbol
  exact ⟨Encodable.encode,Encodable.encode_injective⟩

inductive IncidenceVertex (L : CountableRelationalLanguage) where
  | element : ℕ → IncidenceVertex L
  | tuple : Coordinate L → IncidenceVertex L
  | occurrence : (c : Coordinate L) → Fin (L.arity c.1) → IncidenceVertex L

def incidenceVertexCode (L : CountableRelationalLanguage) : IncidenceVertex L →
    ℕ ⊕ (Coordinate L ⊕ (Σ c : Coordinate L, Fin (L.arity c.1)))
  | .element n => .inl n
  | .tuple c => .inr (.inl c)
  | .occurrence c i => .inr (.inr ⟨c,i⟩)

theorem incidenceVertexCode_injective (L : CountableRelationalLanguage) :
    Function.Injective (incidenceVertexCode L) := by
  intro x y h
  cases x <;> cases y <;> simp_all [incidenceVertexCode]

instance (L : CountableRelationalLanguage) : Countable (IncidenceVertex L) :=
  (incidenceVertexCode_injective L).countable

instance (L : CountableRelationalLanguage) : Infinite (IncidenceVertex L) :=
  Infinite.of_injective IncidenceVertex.element (fun _ _ h => IncidenceVertex.element.inj h)

def IncidenceAdj {L : CountableRelationalLanguage} :
    IncidenceVertex L → IncidenceVertex L → Prop
  | .element n,.occurrence c i => c.2 i = n
  | .occurrence c i,.element n => c.2 i = n
  | .tuple d,.occurrence c _ => c = d
  | .occurrence c _,.tuple d => c = d
  | _,_ => False

theorem incidenceAdj_symm {L : CountableRelationalLanguage} (x y : IncidenceVertex L) :
    IncidenceAdj x y ↔ IncidenceAdj y x := by
  cases x <;> cases y <;> exact Iff.rfl

theorem incidenceAdj_irrefl {L : CountableRelationalLanguage} (x : IncidenceVertex L) :
    ¬ IncidenceAdj x x := by
  cases x <;> exact not_false

def incidenceColor {L : CountableRelationalLanguage} (M : Structures L) :
    IncidenceVertex L → ℕ
  | .element _ => 0
  | .tuple c => 2 * Nat.pair (symbolCode L c.1) (M c).toNat + 1
  | .occurrence _ i => 2 * i.val + 2

theorem incidenceColor_eq_zero_iff {L : CountableRelationalLanguage}
    (M : Structures L) (v : IncidenceVertex L) :
    incidenceColor M v = 0 ↔ ∃ n, v = .element n := by
  cases v <;> simp only [incidenceColor]
  · simp
  · constructor <;> intro h
    · omega
    · obtain ⟨n,hn⟩ := h; cases hn
  · constructor <;> intro h
    · omega
    · obtain ⟨n,hn⟩ := h; cases hn

def coordinateMap {L : CountableRelationalLanguage} (e : ℕ ≃ ℕ)
    (c : Coordinate L) : Coordinate L := ⟨c.1,e ∘ c.2⟩

def coordinateEquiv (L : CountableRelationalLanguage) (e : ℕ ≃ ℕ) :
    Coordinate L ≃ Coordinate L where
  toFun := coordinateMap e
  invFun := coordinateMap e.symm
  left_inv := by intro c; rcases c with ⟨s,a⟩; simp [coordinateMap,Function.comp_def]
  right_inv := by intro c; rcases c with ⟨s,a⟩; simp [coordinateMap,Function.comp_def]

@[simp] theorem coordinateMap_eq_iff {L : CountableRelationalLanguage} (e : ℕ ≃ ℕ)
    (c d : Coordinate L) : coordinateMap e c = coordinateMap e d ↔ c = d :=
  (coordinateEquiv L e).injective.eq_iff

def relabelVertex {L : CountableRelationalLanguage} (e : ℕ ≃ ℕ) :
    IncidenceVertex L → IncidenceVertex L
  | .element n => .element (e n)
  | .tuple c => .tuple (coordinateMap e c)
  | .occurrence c i => .occurrence (coordinateMap e c) i

def incidenceEquiv (L : CountableRelationalLanguage) (e : ℕ ≃ ℕ) :
    IncidenceVertex L ≃ IncidenceVertex L where
  toFun := relabelVertex e
  invFun := relabelVertex e.symm
  left_inv := by
    intro v
    cases v with
    | element n => simp [relabelVertex]
    | tuple c => rcases c with ⟨s,a⟩; simp [relabelVertex,coordinateMap,Function.comp_def]
    | occurrence c i => rcases c with ⟨s,a⟩; simp [relabelVertex,coordinateMap,Function.comp_def]
  right_inv := by
    intro v
    cases v with
    | element n => simp [relabelVertex]
    | tuple c => rcases c with ⟨s,a⟩; simp [relabelVertex,coordinateMap,Function.comp_def]
    | occurrence c i => rcases c with ⟨s,a⟩; simp [relabelVertex,coordinateMap,Function.comp_def]

theorem incidenceEquiv_adj (L : CountableRelationalLanguage) (e : ℕ ≃ ℕ)
    (v w : IncidenceVertex L) : IncidenceAdj v w ↔
      IncidenceAdj (incidenceEquiv L e v) (incidenceEquiv L e w) := by
  cases v <;> cases w <;>
    simp only [incidenceEquiv,Equiv.coe_fn_mk,relabelVertex,IncidenceAdj,coordinateMap_eq_iff]
  all_goals first | exact Iff.rfl | exact e.injective.eq_iff.symm

theorem isomorphic_incidenceColor {L : CountableRelationalLanguage} {M N : Structures L}
    (e : ℕ ≃ ℕ) (he : ∀ s a, M ⟨s,a⟩ = N ⟨s,e ∘ a⟩) (v : IncidenceVertex L) :
    incidenceColor M v = incidenceColor N (incidenceEquiv L e v) := by
  cases v with
  | element n => rfl
  | tuple c =>
    rcases c with ⟨s,a⟩
    simp only [incidenceColor,incidenceEquiv,Equiv.coe_fn_mk,relabelVertex,coordinateMap]
    rw [he s a]
  | occurrence c i => rfl

theorem Isomorphic.incidence {L : CountableRelationalLanguage} {M N : Structures L}
    (h : Isomorphic M N) :
    ∃ e : IncidenceVertex L ≃ IncidenceVertex L,
      (∀ v, incidenceColor M v = incidenceColor N (e v)) ∧
      ∀ v w, IncidenceAdj v w ↔ IncidenceAdj (e v) (e w) := by
  obtain ⟨e,he⟩ := h
  exact ⟨incidenceEquiv L e,isomorphic_incidenceColor e he,incidenceEquiv_adj L e⟩

end FSCofinality.GraphCoding
