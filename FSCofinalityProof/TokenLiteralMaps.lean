import FSCofinalityProof.TokenCommonIsotype
import FSCofinalityProof.CosetConstructionTokenModels

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

abbrev Diagram (L : CountableRelationalLanguage) (X : Type) :=
  ∀ s : L.Symbol, (Fin (L.arity s) → X) → Bool

/-- Complete atomic agreement on a correspondence between two literal
domains, before either domain is enumerated by the natural numbers. -/
def CompatibleOn {L : CountableRelationalLanguage} {X Y : Type}
    (M : Diagram L X) (N : Diagram L Y) (R : Set (X × Y)) : Prop :=
  (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 ↔ p.2 = q.2) ∧
    ∀ s (a : Fin (L.arity s) → X × Y), (∀ i, a i ∈ R) →
      M s (fun i => (a i).1) = N s (fun i => (a i).2)

theorem CompatibleOn.mono {L : CountableRelationalLanguage} {X Y : Type}
    {M : Diagram L X} {N : Diagram L Y} {R S : Set (X × Y)}
    (h : CompatibleOn M N S) (hRS : R ⊆ S) : CompatibleOn M N R :=
  ⟨fun p hp q hq => h.1 p (hRS hp) q (hRS hq),
    fun s a ha => h.2 s a (fun i => hRS (ha i))⟩

theorem CompatibleOn.pair_diagram {L : CountableRelationalLanguage} {X Y : Type}
    {M : Diagram L X} {N : Diagram L Y} {R : Set (X × Y)}
    (h : CompatibleOn M N R) (s : L.Symbol) (p) (hp : p ∈ R) (q) (hq : q ∈ R) :
    M s (twoTuple p.1 q.1) = N s (twoTuple p.2 q.2) := by
  have hh := h.2 s (fun i => if i.val = 0 then p else q) (fun i => by
    dsimp only
    split_ifs
    · exact hp
    · exact hq)
  simpa only [twoTuple,apply_ite] using hh

theorem CompatibleOn.insert_of_unary_binary {L : CountableRelationalLanguage} {X Y : Type}
    {M : Diagram L X} {N : Diagram L Y} {R : Set (X × Y)} (hR : CompatibleOn M N R)
    (hArity : ∀ s, L.arity s ≤ 2) (x : X) (y : Y)
    (hEq : ∀ p ∈ R, x = p.1 ↔ y = p.2)
    (hUnary : ∀ s, L.arity s = 1 → M s (fun _ => x) = N s (fun _ => y))
    (hDiagonal : ∀ s, L.arity s = 2 → M s (fun _ => x) = N s (fun _ => y))
    (hForward : ∀ s, L.arity s = 2 → ∀ p ∈ R,
      M s (twoTuple x p.1) = N s (twoTuple y p.2))
    (hBackward : ∀ s, L.arity s = 2 → ∀ p ∈ R,
      M s (twoTuple p.1 x) = N s (twoTuple p.2 y)) :
    CompatibleOn M N (insert (x,y) R) := by
  constructor
  · intro p hp q hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · simp
    · exact hEq q hq
    · simpa only [eq_comm] using hEq p hp
    · exact hR.1 p hp q hq
  · intro s a ha
    have hcases : L.arity s = 0 ∨ L.arity s = 1 ∨ L.arity s = 2 := by
      have := hArity s
      omega
    rcases hcases with hzero | hone | htwo
    · apply hR.2 s a
      intro i
      exact False.elim (by have := i.isLt; omega)
    · let i₀ : Fin (L.arity s) := ⟨0,by omega⟩
      have hall (i : Fin (L.arity s)) : i = i₀ := by apply Fin.ext; have := i.isLt; omega
      rcases ha i₀ with hn | ho
      · have heq : ∀ i, a i = (x,y) := fun i => (congrArg a (hall i)).trans hn
        simpa only [heq] using hUnary s hone
      · apply hR.2 s a
        intro i
        simpa only [hall i] using ho
    · let i₀ : Fin (L.arity s) := ⟨0,by omega⟩
      let i₁ : Fin (L.arity s) := ⟨1,by omega⟩
      have hcoordinates (i : Fin (L.arity s)) :
          a i = if i.val = 0 then a i₀ else a i₁ := by
        split_ifs with hi
        · exact congrArg a (Fin.ext hi)
        · apply congrArg a
          apply Fin.ext
          change i.val = 1
          have := i.isLt
          omega
      rcases ha i₀ with h₀ | h₀ <;> rcases ha i₁ with h₁ | h₁
      · have heq : ∀ i, a i = (x,y) := by
          intro i
          rw [hcoordinates,h₀,h₁]
          split_ifs <;> rfl
        simpa only [heq] using hDiagonal s htwo
      · have hf : (fun i => (a i).1) = twoTuple x (a i₁).1 := by
          funext i
          rw [hcoordinates,h₀]
          unfold twoTuple
          split_ifs <;> rfl
        have hg : (fun i => (a i).2) = twoTuple y (a i₁).2 := by
          funext i
          rw [hcoordinates,h₀]
          unfold twoTuple
          split_ifs <;> rfl
        rw [hf,hg]
        exact hForward s htwo (a i₁) h₁
      · have hf : (fun i => (a i).1) = twoTuple (a i₀).1 x := by
          funext i
          rw [hcoordinates,h₁]
          unfold twoTuple
          split_ifs <;> rfl
        have hg : (fun i => (a i).2) = twoTuple (a i₀).2 y := by
          funext i
          rw [hcoordinates,h₁]
          unfold twoTuple
          split_ifs <;> rfl
        rw [hf,hg]
        exact hBackward s htwo (a i₀) h₀
      · apply hR.2 s a
        intro i
        rw [hcoordinates]
        split_ifs
        · exact h₀
        · exact h₁


def enumerateDiagram {L : CountableRelationalLanguage} {X : Type}
    (M : Diagram L X) (e : ℕ ≃ X) : Structures L :=
  fun ⟨s,a⟩ => M s (e ∘ a)

theorem compatibleOn_iff_enumeration {L : CountableRelationalLanguage} {X Y : Type}
    (M : Diagram L X) (N : Diagram L Y) (e : ℕ ≃ X) (f : ℕ ≃ Y)
    (R : Set (X × Y)) : CompatibleOn M N R ↔
      AtomicCompatible (enumerateDiagram M e) (enumerateDiagram N f)
        {p | (e p.1,f p.2) ∈ R} := by
  constructor
  · intro h
    constructor
    · intro p hp q hq
      exact ⟨fun heq => f.injective ((h.1 _ hp _ hq).mp (congrArg e heq)),
        fun heq => e.injective ((h.1 _ hp _ hq).mpr (congrArg f heq))⟩
    · intro s a ha
      exact h.2 s (fun i => (e (a i).1,f (a i).2)) ha
  · intro h
    constructor
    · intro p hp q hq
      have hh := h.1 (e.symm p.1,f.symm p.2) (by simpa using hp)
        (e.symm q.1,f.symm q.2) (by simpa using hq)
      exact ⟨fun heq => f.symm.injective (hh.mp (congrArg e.symm heq)),
        fun heq => e.symm.injective (hh.mpr (congrArg f.symm heq))⟩
    · intro s a ha
      have hh := h.2 s (fun i => (e.symm (a i).1,f.symm (a i).2))
        (fun i => by simpa using ha i)
      simpa only [enumerateDiagram,Function.comp_def,Equiv.apply_symm_apply] using hh

theorem preimage_equiv_list (X Y : Type) (e : ℕ ≃ X) (f : ℕ ≃ Y)
    (R : List (ℕ × ℕ)) :
    {p : ℕ × ℕ | (e p.1,f p.2) ∈ R.map (fun q => (e q.1,f q.2))} =
      {p | p ∈ R} := by
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hp
    have hfst := e.injective (congrArg Prod.fst hqp)
    have hsnd := f.injective (congrArg Prod.snd hqp)
    exact (Prod.ext hfst hsnd) ▸ hq
  · intro hp
    exact List.mem_map.mpr ⟨p,hp,rfl⟩

def LiteralForth {L : CountableRelationalLanguage} {X Y : Type}
    (M : Diagram L X) (N : Diagram L Y) : Prop :=
  ∀ R : List (X × Y), CompatibleOn M N {p | p ∈ R} →
    ∀ x : X, ∃ y : Y, CompatibleOn M N {p | p ∈ R ++ [(x,y)]}

theorem forthExtension_of_literal {L : CountableRelationalLanguage} {X Y : Type}
    (M : Diagram L X) (N : Diagram L Y) (e : ℕ ≃ X) (f : ℕ ≃ Y)
    (h : LiteralForth M N) : ForthExtension (enumerateDiagram M e) (enumerateDiagram N f) := by
  intro R hR x
  let S := R.map (fun q => (e q.1,f q.2))
  have hS : CompatibleOn M N {p | p ∈ S} := by
    apply (compatibleOn_iff_enumeration M N e f _).mpr
    change AtomicCompatible (enumerateDiagram M e) (enumerateDiagram N f)
      {p | (e p.1,f p.2) ∈ R.map (fun q => (e q.1,f q.2))}
    rw [preimage_equiv_list]
    exact hR
  obtain ⟨y,hy⟩ := h S hS (e x)
  refine ⟨f.symm y,?_⟩
  have hhy := (compatibleOn_iff_enumeration M N e f _).mp hy
  apply hhy.mono
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · rcases List.mem_singleton.mp hp with rfl
    apply List.mem_append_right
    simp only [List.mem_singleton,Equiv.apply_symm_apply]

end FSCofinality.PartialIso

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def LiteralCompatible (bottom : ∀ x : (fsTower eta).Carrier,
    Tokens.Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x y : (fsTower eta).Carrier) (R : Set (Vertex eta heta x × Vertex eta heta y)) : Prop :=
  CompatibleOn (L := language eta heta) (diagram eta heta bottom x) (diagram eta heta bottom y) R

theorem forth_modelWithEnumeration_of_literal
    (bottom : ∀ x : (fsTower eta).Carrier,
      Tokens.Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x y : (fsTower eta).Carrier) (e : ℕ ≃ Vertex eta heta x) (f : ℕ ≃ Vertex eta heta y)
    (h : LiteralForth (L := language eta heta) (diagram eta heta bottom x) (diagram eta heta bottom y)) :
    ForthExtension (modelWithEnumeration eta heta bottom x e)
      (modelWithEnumeration eta heta bottom y f) :=
  forthExtension_of_literal _ _ e f h

end FSCofinality.CosetConstruction.TokenModel
