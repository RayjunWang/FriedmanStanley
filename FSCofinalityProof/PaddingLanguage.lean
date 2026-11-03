import FSCofinalityProof.PaddingBasics

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.Padding

/-- One fixed relational language for rooted colored predecessor trees:
one root predicate, the predecessor graph, and countably many colors. -/
def treeLanguage : CountableRelationalLanguage where
  Symbol := Unit ⊕ (Unit ⊕ ℕ)
  arity := fun s => match s with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl _) => 2
    | Sum.inr (Sum.inr _) => 1
  countable := inferInstance

def code (T : RankedTree) (e : ℕ ≃ T.Vertex) : Structures treeLanguage :=
  fun ⟨s,a⟩ => match s with
    | Sum.inl _ => decide (e (a ⟨0,by simp [treeLanguage]⟩) = T.root)
    | Sum.inr (Sum.inl _) => decide
        (T.parent (e (a ⟨0,by simp [treeLanguage]⟩)) = e (a ⟨1,by simp [treeLanguage]⟩))
    | Sum.inr (Sum.inr c) => decide (T.color (e (a ⟨0,by simp [treeLanguage]⟩)) = c)

theorem GoodPartial.parent_iff {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) {p q : T.Vertex × U.Vertex}
    (hp : p ∈ f.pairs) (hq : q ∈ f.pairs) :
    T.parent p.1 = q.1 ↔ U.parent p.2 = q.2 :=
  f.bijective _ (f.parents p hp) q hq

theorem GoodPartial.root_iff {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) {p : T.Vertex × U.Vertex} (hp : p ∈ f.pairs) :
    p.1 = T.root ↔ p.2 = U.root := f.bijective p hp _ f.roots

/-- Ancestor closure is sufficient to preserve every atomic relation
in the fixed tree language. -/
theorem GoodPartial.atomicCompatible {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (eT : ℕ ≃ T.Vertex) (eU : ℕ ≃ U.Vertex)
    (R : Set (ℕ × ℕ)) (hR : ∀ p ∈ R, (eT p.1,eU p.2) ∈ f.pairs) :
    PartialIso.AtomicCompatible (code T eT) (code U eU) R := by
  refine ⟨?_,?_⟩
  · intro p hp q hq
    exact eT.injective.eq_iff.symm.trans
      ((f.bijective _ (hR p hp) _ (hR q hq)).trans eU.injective.eq_iff)
  · intro s a ha
    rcases s with _ | (_ | c)
    · change (Fin 1 → ℕ × ℕ) at a
      change (∀ i : Fin 1, a i ∈ R) at ha
      simp only [code,decide_eq_decide]
      exact f.root_iff (hR (a 0) (ha 0))
    · change (Fin 2 → ℕ × ℕ) at a
      change (∀ i : Fin 2, a i ∈ R) at ha
      simp only [code,decide_eq_decide]
      exact f.parent_iff (hR (a 0) (ha 0)) (hR (a 1) (ha 1))
    · change (Fin 1 → ℕ × ℕ) at a
      change (∀ i : Fin 1, a i ∈ R) at ha
      simp only [code]
      change decide (T.color (eT (a 0).1) = c) = decide (U.color (eU (a 0).2) = c)
      have hc : T.color (eT (a 0).1) = U.color (eU (a 0).2) :=
        f.colors _ (hR (a 0) (ha 0))
      rw [hc]

end FSCofinality.Padding
