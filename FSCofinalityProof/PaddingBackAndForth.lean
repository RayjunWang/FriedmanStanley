import FSCofinalityProof.PaddingLanguage

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

/-- Good partial tree maps yield the ordinary back-and-forth relation
once their explicit extension property has been proved. The two
extension hypotheses are the finite-path reservoir argument. -/
theorem backAndForth_of_goodPartial
    (T U : RankedTree) (eT : ℕ ≃ T.Vertex) (eU : ℕ ≃ U.Vertex)
    (B : Ordinal.{0})
    (hforth : ∀ b ≤ B, ∀ d < b, ∀ f : GoodPartial T U b, ∀ x : T.Vertex,
      ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ x ∈ g.source)
    (hback : ∀ b ≤ B, ∀ d < b, ∀ f : GoodPartial T U b, ∀ y : U.Vertex,
      ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ y ∈ g.target)
    (b : Ordinal.{0}) (hbB : b ≤ B) (f : GoodPartial T U b)
    (R : List (ℕ × ℕ)) (hR : ∀ p ∈ R, (eT p.1,eU p.2) ∈ f.pairs) :
    PartialIso.BackAndForth (code T eT) (code U eU) b R := by
  classical
  induction b using WellFoundedLT.induction generalizing R with
  | ind b IH =>
      rw [PartialIso.BackAndForth]
      refine ⟨f.atomicCompatible eT eU {p | p ∈ R} hR,fun d hdb => ⟨?_,?_⟩⟩
      · intro x
        obtain ⟨g,hfg,hx⟩ := hforth b hbB d hdb f (eT x)
        obtain ⟨⟨v,w⟩,hvw,hvx⟩ := Finset.mem_image.mp hx
        dsimp at hvx
        subst v
        refine ⟨eU.symm w,IH d hdb (le_trans hdb.le hbB) g
          (R ++ [(x,eU.symm w)]) ?_⟩
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hfg (hR p hp)
        · have hpe : p = (x,eU.symm w) := List.mem_singleton.mp hp
          subst p
          simpa only [Equiv.apply_symm_apply] using hvw
      · intro y
        obtain ⟨g,hfg,hy⟩ := hback b hbB d hdb f (eU y)
        obtain ⟨⟨v,w⟩,hvw,hwy⟩ := Finset.mem_image.mp hy
        dsimp at hwy
        subst w
        refine ⟨eT.symm v,IH d hdb (le_trans hdb.le hbB) g
          (R ++ [(eT.symm v,y)]) ?_⟩
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hfg (hR p hp)
        · have hpe : p = (eT.symm v,y) := List.mem_singleton.mp hp
          subst p
          simpa only [Equiv.apply_symm_apply] using hvw

end FSCofinality.Padding
