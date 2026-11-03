import FSCofinalityProof.PaddingBasics

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

theorem RankedTree.height_iterate_parent (T : RankedTree) (v : T.Vertex)
    (n : ℕ) (hn : n ≤ T.height v) :
    T.height ((T.parent^[n]) v) = T.height v-n := by
  induction n with
  | zero => simp
  | succ n IH =>
      have hi := IH (by omega)
      rw [Function.iterate_succ_apply']
      have hneq : (T.parent^[n]) v ≠ T.root := by
        intro heq
        rw [heq,T.height_root] at hi
        omega
      have hp := T.parent_height ((T.parent^[n]) v) hneq
      omega

theorem RankedTree.iterate_parent_height (T : RankedTree) (v : T.Vertex) :
    (T.parent^[T.height v]) v = T.root :=
  T.height_zero _ (by simpa using T.height_iterate_parent v (T.height v) le_rfl)

theorem GoodPartial.exists_mapped_ancestor {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) :
    ∃ n : ℕ, (T.parent^[n]) x ∈ f.source :=
  ⟨T.height x,by rw [T.iterate_parent_height]; exact f.root_mem_source⟩

/-- The first already matched ancestor separates a new finite path
from the ancestor-closed domain of an existing partial map. -/
def GoodPartial.firstMappedAncestorDepth {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) : ℕ := by
  classical
  exact Nat.find (f.exists_mapped_ancestor x)

theorem GoodPartial.firstMappedAncestor_mem {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) :
    (T.parent^[f.firstMappedAncestorDepth x]) x ∈ f.source := by
  classical
  exact Nat.find_spec (f.exists_mapped_ancestor x)

theorem GoodPartial.before_firstMappedAncestor {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) {n : ℕ}
    (hn : n < f.firstMappedAncestorDepth x) : (T.parent^[n]) x ∉ f.source := by
  classical
  exact Nat.find_min (f.exists_mapped_ancestor x) hn

/-- The reservoir argument for one fresh edge, with its ordinal rank
chosen explicitly by the finite-path rank template. -/
theorem exists_one_edge_extension
    {T U : RankedTree} {a b : Ordinal.{0}}
    (hU : HasFatReservoirs U a) (f : GoodPartial T U b)
    (x : T.Vertex) (hx : x ∉ f.source) (y : U.Vertex)
    (hparent : (T.parent x,y) ∈ f.pairs)
    (r : Ordinal.{0}) (hra : r < a)
    (hry : (r : WithTop Ordinal.{0}) < U.rank y)
    (hrank : RankAgrees b (T.rank x) (r : WithTop Ordinal.{0})) :
    ∃ g : GoodPartial T U b, f.pairs ⊆ g.pairs ∧ x ∈ g.source := by
  classical
  obtain ⟨w,hwfresh,_,hwparent,hwrank,hwcolor⟩ :=
    exists_fresh_child hU y r hra hry (T.color x) f.target
  have hp : (T.parent x,U.parent w) ∈ f.pairs := by rwa [hwparent]
  have hr : RankAgrees b (T.rank x) (U.rank w) := by rwa [hwrank]
  let g := f.extend x w hx hwfresh hp hwcolor.symm hr
  refine ⟨g,?_,?_⟩
  · exact Finset.subset_insert (x,w) f.pairs
  · exact Finset.mem_image.mpr ⟨(x,w),Finset.mem_insert_self _ _,rfl⟩

end FSCofinality.Padding
