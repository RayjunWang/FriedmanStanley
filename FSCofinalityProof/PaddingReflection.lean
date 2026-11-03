import FSCofinalityProof.PaddingOriginalEquiv
import FSCofinalityProof.PaddingTupleBranch
import FSCofinalityProof.BorelPrunedBranch

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.Padding

def TupleWordValid (φ : List ℕ → List ℕ) (s : List ℕ) : Prop :=
  ∀ k ≤ s.length, φ (sourceTuple (s.take k)) = targetTuple (s.take k)

theorem take_append_singleton_of_le (s : List ℕ) (n k : ℕ) (hk : k ≤ s.length) :
    (s ++ [n]).take k = s.take k := by
  simp [List.take_append,Nat.sub_eq_zero_of_le hk]

def tupleMatchTree (φ : List ℕ → List ℕ) : RootedTrees.TreeSpace where
  val := fun s => decide (TupleWordValid φ s)
  property := by
    intro s n h
    have hs := of_decide_eq_true h
    apply decide_eq_true
    intro k hk
    have hc := hs k (by simpa only [List.length_append,List.length_singleton] using (show k ≤ s.length+1 from by omega))
    simpa only [take_append_singleton_of_le s n k hk] using hc

theorem tupleWordValid_extend {φ : List ℕ → List ℕ} {s : List ℕ} {n : ℕ}
    (hs : TupleWordValid φ s)
    (hn : φ (sourceTuple (s ++ [n])) = targetTuple (s ++ [n])) :
    TupleWordValid φ (s ++ [n]) := by
  intro k hk
  by_cases hks : k ≤ s.length
  · rw [take_append_singleton_of_le s n k hks]
    exact hs k hks
  · have heq : k = (s ++ [n]).length := by
      simp only [List.length_append,List.length_singleton] at hk ⊢
      omega
    rw [heq,List.take_length]
    exact hn

theorem tupleMatchTree_pruned (φ : List ℕ → List ℕ)
    (hforth : ∀ s n, ∃ m, φ (s ++ [n]) = φ s ++ [m])
    (hback : ∀ s m, ∃ n, φ (s ++ [n]) = φ s ++ [m]) :
    RootedTrees.Pruned (tupleMatchTree φ) := by
  intro s hs
  have hvalid : TupleWordValid φ s := of_decide_eq_true hs
  have hcurrent : φ (sourceTuple s) = targetTuple s := by
    simpa only [List.take_length] using hvalid s.length le_rfl
  by_cases heven : s.length % 2 = 0
  · obtain ⟨n,hn⟩ := hforth (sourceTuple s) (s.length/2)
    refine ⟨n,decide_eq_true (tupleWordValid_extend hvalid ?_)⟩
    rw [sourceTuple_append,targetTuple_append]
    simpa only [PartialIso.scheduledPair,if_pos heven,hcurrent] using hn
  · obtain ⟨n,hn⟩ := hback (sourceTuple s) (s.length/2)
    refine ⟨n,decide_eq_true (tupleWordValid_extend hvalid ?_)⟩
    rw [sourceTuple_append,targetTuple_append]
    simpa only [PartialIso.scheduledPair,if_neg heven,hcurrent] using hn

theorem exists_scheduled_tuple_branch (φ : List ℕ → List ℕ) (hroot : φ [] = [])
    (hforth : ∀ s n, ∃ m, φ (s ++ [n]) = φ s ++ [m])
    (hback : ∀ s m, ∃ n, φ (s ++ [n]) = φ s ++ [m]) :
    ∃ b : ℕ → ℕ, ∀ n, φ (sourceTuple (PartialIso.initialSegment b n)) =
      targetTuple (PartialIso.initialSegment b n) := by
  have hr : tupleMatchTree φ [] = true := by
    apply decide_eq_true
    intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact hroot
  let b := RootedTrees.branchChoice (tupleMatchTree φ)
  refine ⟨b,fun n => ?_⟩
  have hb := RootedTrees.branchChoice_spec (tupleMatchTree φ) hr
    (tupleMatchTree_pruned φ hforth hback) n
  have hv : TupleWordValid φ (PartialIso.initialSegment b n) := of_decide_eq_true hb
  simpa only [List.take_length] using hv (PartialIso.initialSegment b n).length le_rfl

/-- Padding reflects actual graph isomorphism. The original tuple tree
is recovered through its intrinsic infinite-branch vertices. -/
theorem graphIsomorphic_of_paddedGraphCode_isomorphic
    (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (G H : GraphSpace)
    (h : Isomorphic (paddedGraphCode a ha G) (paddedGraphCode a ha H)) : GraphIsomorphic G H := by
  obtain ⟨e⟩ := treeIso_of_code_isomorphic
    (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H))
    (paddedEnumeration a ha) (paddedEnumeration a ha) h
  obtain ⟨b,hb⟩ := exists_scheduled_tuple_branch e.originalEquiv e.originalEquiv_root
    e.originalEquiv_extension e.originalEquiv_backextension
  apply graphIsomorphic_of_tuple_branch G H b
  intro n
  have hc := (e.originalEquiv_colors (sourceTuple (PartialIso.initialSegment b n))).symm
  rwa [hb n] at hc

end FSCofinality.Padding
