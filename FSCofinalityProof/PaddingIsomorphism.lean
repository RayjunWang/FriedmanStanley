import FSCofinalityProof.PaddingLanguage

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

structure TreeIso (T U : RankedTree) where
  equiv : T.Vertex ≃ U.Vertex
  roots : equiv T.root = U.root
  parents : ∀ v, equiv (T.parent v) = U.parent (equiv v)
  colors : ∀ v, U.color (equiv v) = T.color v

/-- The native countable-structure code retains the actual rooted
colored predecessor-tree isomorphism. -/
theorem treeIso_of_code_isomorphic
    (T U : RankedTree) (eT : ℕ ≃ T.Vertex) (eU : ℕ ≃ U.Vertex)
    (h : Isomorphic (code T eT) (code U eU)) : Nonempty (TreeIso T U) := by
  obtain ⟨e,he⟩ := h
  let φ : T.Vertex ≃ U.Vertex := (eT.symm.trans e).trans eU
  have hroot (n : ℕ) : eT n = T.root ↔ eU (e n) = U.root := by
    have hh := he (Sum.inl ()) (fun _ => n)
    simpa only [code,decide_eq_decide,Function.comp_apply] using hh
  have hparent (n m : ℕ) : T.parent (eT n) = eT m ↔ U.parent (eU (e n)) = eU (e m) := by
    let a : Fin (treeLanguage.arity (Sum.inr (Sum.inl ()))) → ℕ :=
      fun i => if i.val = 0 then n else m
    have hh := he (Sum.inr (Sum.inl ())) a
    simpa [code,a,Function.comp_def] using hh
  have hcolor (n c : ℕ) : T.color (eT n) = c ↔ U.color (eU (e n)) = c := by
    have hh := he (Sum.inr (Sum.inr c)) (fun _ => n)
    simpa only [code,decide_eq_decide,Function.comp_apply] using hh
  refine ⟨⟨φ,?_,?_,?_⟩⟩
  · exact (hroot (eT.symm T.root)).mp (eT.apply_symm_apply _)
  · intro v
    have hp := (hparent (eT.symm v) (eT.symm (T.parent v))).mp (by simp)
    exact hp.symm
  · intro v
    exact (hcolor (eT.symm v) (T.color v)).mp (by simp)

theorem code_isomorphic_of_treeIso
    (T U : RankedTree) (eT : ℕ ≃ T.Vertex) (eU : ℕ ≃ U.Vertex) (e : TreeIso T U) :
    Isomorphic (code T eT) (code U eU) := by
  let q : ℕ ≃ ℕ := (eT.trans e.equiv).trans eU.symm
  have hq (n : ℕ) : eU (q n) = e.equiv (eT n) := by simp only [q,Equiv.trans_apply,Equiv.apply_symm_apply]
  refine ⟨q,fun s a => ?_⟩
  rcases s with _ | (_ | c)
  · simp only [code,Function.comp_apply]
    apply decide_eq_decide.mpr
    rw [hq]
    rw [← e.roots]
    exact e.equiv.injective.eq_iff.symm
  · simp only [code,Function.comp_apply]
    apply decide_eq_decide.mpr
    rw [hq,hq,← e.parents]
    exact e.equiv.injective.eq_iff.symm
  · simp only [code,Function.comp_apply]
    apply decide_eq_decide.mpr
    rw [hq,e.colors]

end FSCofinality.Padding
