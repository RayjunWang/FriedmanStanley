import FSCofinalityProof.PaddingIsomorphism
import FSCofinalityProof.PaddingPaddedTree
import FSCofinalityProof.PaddingOrdinalBasics

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

def HasInfiniteBranchFrom (T : RankedTree) (v : T.Vertex) : Prop :=
  ∃ f : ℕ → T.Vertex, f 0 = v ∧
    ∀ n, T.parent (f (n+1)) = f n ∧ f (n+1) ≠ f n

def TreeIso.symm {T U : RankedTree} (e : TreeIso T U) : TreeIso U T where
  equiv := e.equiv.symm
  roots := by
    apply e.equiv.injective
    simp only [Equiv.apply_symm_apply,e.roots]
  parents := by
    intro v
    apply e.equiv.injective
    simp only [Equiv.apply_symm_apply,e.parents]
  colors := by
    intro v
    simpa only [Equiv.apply_symm_apply] using (e.colors (e.equiv.symm v)).symm

theorem TreeIso.map_branch {T U : RankedTree} (e : TreeIso T U) {v : T.Vertex}
    (h : HasInfiniteBranchFrom T v) : HasInfiniteBranchFrom U (e.equiv v) := by
  obtain ⟨f,hf0,hf⟩ := h
  refine ⟨e.equiv ∘ f,congrArg e.equiv hf0,fun n => ?_⟩
  exact ⟨(e.parents (f (n+1))).symm.trans (congrArg e.equiv (hf n).1),
    fun h => (hf n).2 (e.equiv.injective h)⟩

/-- A finite ordinal rank excludes an infinite branch. -/
theorem no_branch_of_finite_rank (T : RankedTree) (v : T.Vertex)
    (hv : T.rank v ≠ ⊤) : ¬ HasInfiniteBranchFrom T v := by
  rintro ⟨f,hf0,hf⟩
  have hle : ∀ n, T.rank (f n) ≤ T.rank v := by
    intro n
    induction n with
    | zero => simpa only [hf0] using (le_rfl : T.rank v ≤ T.rank v)
    | succ n IH =>
        have hp : T.rank (f (n+1)) ≤ T.rank (f n) := by
          simpa only [(hf n).1] using T.rank_parent (f (n+1))
        exact hp.trans IH
  have hfinite (n : ℕ) : T.rank (f n) ≠ ⊤ := by
    intro ht
    have hh := hle n
    rw [ht] at hh
    exact hv (le_antisymm le_top hh)
  let σ : ℕ → Ordinal.{0} := fun n => finiteOrdinal (T.rank (f n))
  have hco (n : ℕ) : (σ n : WithTop Ordinal.{0}) = T.rank (f n) := by
    obtain ⟨r,hr⟩ := WithTop.ne_top_iff_exists.mp (hfinite n)
    change (finiteOrdinal (T.rank (f n)) : WithTop Ordinal.{0}) = T.rank (f n)
    rw [← hr]
    rfl
  have hdecr (n : ℕ) : σ (n+1) < σ n := by
    apply WithTop.coe_lt_coe.mp
    rw [hco (n+1),hco n]
    have hroot : f (n+1) ≠ T.root := by
      intro heq
      have hp : T.root = f n := by simpa only [heq,T.parent_root] using (hf n).1
      exact (hf n).2 (heq.trans hp)
    simpa only [(hf n).1] using T.finite_rank_strict (f (n+1)) hroot (hfinite (n+1))
  exact (not_acc_iff_exists_descending_chain.mpr ⟨σ,rfl,hdecr⟩) (Ordinal.lt_wf.apply (σ 0))

theorem PaddedNode.branch_from_original (a : Ordinal.{0}) (C : List ℕ → ℕ) (s : List ℕ) :
    HasInfiniteBranchFrom (PaddedNode.tree a C) (Sum.inl s) := by
  refine ⟨fun n => Sum.inl (s ++ List.replicate n 0),by simp,fun n => ⟨?_,?_⟩⟩
  · simp [PaddedNode.tree,PaddedNode.parent,List.replicate_succ',← List.append_assoc]
  · intro h
    have hh := congrArg PaddedNode.height h
    simp only [PaddedNode.height,List.length_append,List.length_replicate] at hh
    omega

/-- Original tuple vertices are intrinsically the vertices on infinite
branches. Hence padding is faithful under actual tree isomorphisms. -/
theorem PaddedNode.branch_iff_original (a : Ordinal.{0}) (C : List ℕ → ℕ) (v : PaddedNode a) :
    HasInfiniteBranchFrom (PaddedNode.tree a C) v ↔ ∃ s : List ℕ, v = Sum.inl s := by
  cases v with
  | inl s => exact ⟨fun _ => ⟨s,rfl⟩,fun _ => PaddedNode.branch_from_original a C s⟩
  | inr v =>
      constructor
      · intro h
        exact False.elim (no_branch_of_finite_rank (PaddedNode.tree a C) (Sum.inr v)
          (by exact WithTop.coe_ne_top) h)
      · rintro ⟨s,h⟩
        cases h

end FSCofinality.Padding
