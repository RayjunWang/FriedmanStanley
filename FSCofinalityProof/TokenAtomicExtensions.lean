import FSCofinalityProof.PartialIsomorphism

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

def twoTuple {α : Type*} {n : ℕ} (x y : α) : Fin n → α :=
  fun i => if i.val = 0 then x else y

/-- In a unary/binary relational language, all complete atomic requirements
for one new point reduce to its unary type, its diagonal binary type, and
the two directed incidences with old points. -/
theorem AtomicCompatible.insert_of_unary_binary {L : CountableRelationalLanguage}
    {M N : Structures L} {R : Set (ℕ × ℕ)} (hR : AtomicCompatible M N R)
    (hArity : ∀ s, L.arity s ≤ 2) (x y : ℕ)
    (hEq : ∀ p ∈ R, x = p.1 ↔ y = p.2)
    (hUnary : ∀ s, L.arity s = 1 → M ⟨s,fun _ => x⟩ = N ⟨s,fun _ => y⟩)
    (hDiagonal : ∀ s, L.arity s = 2 → M ⟨s,fun _ => x⟩ = N ⟨s,fun _ => y⟩)
    (hForward : ∀ s, L.arity s = 2 → ∀ p ∈ R,
      M ⟨s,twoTuple x p.1⟩ = N ⟨s,twoTuple y p.2⟩)
    (hBackward : ∀ s, L.arity s = 2 → ∀ p ∈ R,
      M ⟨s,twoTuple p.1 x⟩ = N ⟨s,twoTuple p.2 y⟩) :
    AtomicCompatible M N (insert (x,y) R) := by
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

theorem AtomicCompatible.empty_of_positive_arity {L : CountableRelationalLanguage}
    (M N : Structures L) (hArity : ∀ s, 0 < L.arity s) :
    AtomicCompatible M N ∅ := by
  constructor
  · simp
  · intro s a ha
    exact False.elim (ha ⟨0,hArity s⟩)

theorem AtomicCompatible.swap {L : CountableRelationalLanguage} {M N : Structures L}
    {R : Set (ℕ × ℕ)} (hR : AtomicCompatible M N R) :
    AtomicCompatible N M (Prod.swap ⁻¹' R) := by
  constructor
  · intro p hp q hq
    exact (hR.1 p.swap hp q.swap hq).symm
  · intro s a ha
    exact (hR.2 s (fun i => (a i).swap) ha).symm

theorem AtomicCompatible.swap_list {L : CountableRelationalLanguage} {M N : Structures L}
    {R : List (ℕ × ℕ)} (hR : AtomicCompatible M N {p | p ∈ R}) :
    AtomicCompatible N M {p | p ∈ R.map Prod.swap} := by
  apply hR.swap.mono
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hq

end FSCofinality.PartialIso
