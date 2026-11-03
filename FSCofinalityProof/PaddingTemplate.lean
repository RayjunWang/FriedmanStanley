import FSCofinalityProof.PaddingPath
import Mathlib.Data.List.Range
import Mathlib.Data.List.Nodup

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

def ancestorPath (T : RankedTree) (x : T.Vertex) (σ : ℕ → Ordinal.{0}) (m : ℕ) :
    List (T.Vertex × Ordinal.{0}) :=
  (List.range m).reverse.map (fun j => ((T.parent^[j]) x,σ j))

theorem ancestorPath_succ (T : RankedTree) (x : T.Vertex) (σ : ℕ → Ordinal.{0}) (m : ℕ) :
    ancestorPath T x σ (m+1) = ((T.parent^[m]) x,σ m) :: ancestorPath T x σ m := by
  simp [ancestorPath,List.range_succ,List.reverse_append]

/-- Strictly increasing ranks indexed from the leaf give the required
decreasing template when the ancestor path is read from its anchor. -/
theorem ancestorPath_template
    (T : RankedTree) (a d : Ordinal.{0}) (x : T.Vertex) (σ : ℕ → Ordinal.{0})
    (m : ℕ) (anchorRank : WithTop Ordinal.{0})
    (ha : ∀ j < m, σ j < a)
    (hinc : ∀ j < m, σ j < σ (j+1))
    (hag : ∀ j < m, RankAgrees d (T.rank ((T.parent^[j]) x)) (σ j : WithTop Ordinal.{0}))
    (hanchor : (σ m : WithTop Ordinal.{0}) ≤ anchorRank) :
    PathTemplate T a d ((T.parent^[m]) x) anchorRank (ancestorPath T x σ m) := by
  induction m generalizing anchorRank with
  | zero => trivial
  | succ m IH =>
      rw [ancestorPath_succ]
      refine ⟨?_,ha m (by omega),?_,hag m (by omega),?_⟩
      · exact (Function.iterate_succ_apply' T.parent m x).symm
      · exact (WithTop.coe_lt_coe.mpr (hinc m (by omega))).trans_le hanchor
      · exact IH (σ m) (fun j hj => ha j (by omega))
          (fun j hj => hinc j (by omega)) (fun j hj => hag j (by omega)) le_rfl

theorem RankedTree.iterate_parent_injective_below_height
    (T : RankedTree) (x : T.Vertex) {i j : ℕ}
    (hi : i ≤ T.height x) (hj : j ≤ T.height x)
    (h : (T.parent^[i]) x = (T.parent^[j]) x) : i = j := by
  have hh := congrArg T.height h
  rw [T.height_iterate_parent x i hi,T.height_iterate_parent x j hj] at hh
  omega

theorem ancestorPath_nodup (T : RankedTree) (x : T.Vertex)
    (σ : ℕ → Ordinal.{0}) (m : ℕ) (hm : m ≤ T.height x) :
    ((ancestorPath T x σ m).map Prod.fst).Nodup := by
  rw [ancestorPath,List.map_map]
  apply List.Nodup.map_on ?_ (List.nodup_reverse.mpr
    (show (List.range m).Nodup from List.nodup_range))
  intro i hi j hj hij
  have hi' : i < m := List.mem_range.mp (List.mem_reverse.mp hi)
  have hj' : j < m := List.mem_range.mp (List.mem_reverse.mp hj)
  exact T.iterate_parent_injective_below_height x (by omega) (by omega) hij

theorem GoodPartial.firstMappedAncestorDepth_le_height
    {T U : RankedTree} {b : Ordinal.{0}} (f : GoodPartial T U b) (x : T.Vertex) :
    f.firstMappedAncestorDepth x ≤ T.height x := by
  classical
  apply Nat.find_min'
  rw [T.iterate_parent_height]
  exact f.root_mem_source

theorem ancestorPath_fresh {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) (σ : ℕ → Ordinal.{0}) :
    ∀ p ∈ ancestorPath T x σ (f.firstMappedAncestorDepth x), p.1 ∉ f.source := by
  intro p hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  exact f.before_firstMappedAncestor x (List.mem_range.mp (List.mem_reverse.mp hj))

end FSCofinality.Padding
