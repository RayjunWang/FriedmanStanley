import FSCofinalityProof.PaddingOrdinalBasics

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

/-- The two cases of the source padding argument: below the old cutoff
retain the exact source ranks, and above it use finite slack over the
new cutoff. -/
theorem exists_ancestor_rank_template
    (T : RankedTree) (x : T.Vertex) (m : ℕ) (a b d : Ordinal.{0})
    (hdb : d < b) (hba : cutoff b ≤ a) (targetRank : WithTop Ordinal.{0})
    (hmatch : RankAgrees b (T.rank ((T.parent^[m]) x)) targetRank)
    (hne : ∀ j < m, (T.parent^[j]) x ≠ T.root) :
    ∃ σ : ℕ → Ordinal.{0}, PathTemplate T a d ((T.parent^[m]) x) targetRank
      (ancestorPath T x σ m) := by
  classical
  by_cases hlow : T.rank ((T.parent^[m]) x) < (cutoff b : WithTop Ordinal.{0})
  · let σ : ℕ → Ordinal.{0} := fun j => finiteOrdinal (T.rank ((T.parent^[j]) x))
    have hlt (j : ℕ) (hj : j ≤ m) :
        T.rank ((T.parent^[j]) x) < (cutoff b : WithTop Ordinal.{0}) :=
      (T.rank_iterate_parent_monotone x hj).trans_lt hlow
    have hco (j : ℕ) (hj : j ≤ m) : (σ j : WithTop Ordinal.{0}) = T.rank ((T.parent^[j]) x) :=
      coe_untopD_of_lt (hlt j hj)
    refine ⟨σ,ancestorPath_template T a d x σ m targetRank ?_ ?_ ?_ ?_⟩
    · intro j hj
      apply WithTop.coe_lt_coe.mp
      rw [hco j hj.le]
      exact (hlt j hj.le).trans_le (WithTop.coe_le_coe.mpr hba)
    · intro j hj
      apply WithTop.coe_lt_coe.mp
      rw [hco j hj.le,hco (j+1) (by omega)]
      have hfinite : T.rank ((T.parent^[j]) x) ≠ ⊤ := by
        intro ht
        have hl := hlt j hj.le
        rw [ht] at hl
        exact (not_lt_of_ge le_top) hl
      simpa only [Function.iterate_succ_apply'] using
        T.finite_rank_strict ((T.parent^[j]) x) (hne j hj) hfinite
    · intro j hj
      exact Or.inl (hco j hj.le).symm
    · rw [hco m le_rfl,hmatch.eq_of_lt_left hlow]
  · refine ⟨pathRank T x d,ancestorPath_template T a d x (pathRank T x d) m targetRank
      (fun j _ => pathRank_lt x hdb hba j)
      (fun j hj => pathRank_lt_succ T x d j (hne j hj))
      (fun j _ => pathRank_agrees T x d j) ?_⟩
    exact pathRank_anchor_le hdb m targetRank (le_of_not_gt hlow) hmatch

/-- Every good finite partial map has a lower-level extension covering
one prescribed source point. This discharges the actual finite-path
reservoir extension obligation. -/
theorem exists_good_extension
    {T U : RankedTree} {a b d : Ordinal.{0}}
    (hU : HasFatReservoirs U a) (f : GoodPartial T U b)
    (hdb : d < b) (hba : cutoff b ≤ a) (x : T.Vertex) :
    ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ x ∈ g.source := by
  classical
  by_cases hx : x ∈ f.source
  · exact ⟨f.lower hdb.le,(fun _ h => h),hx⟩
  let m := f.firstMappedAncestorDepth x
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    have hf := f.firstMappedAncestor_mem x
    rw [show f.firstMappedAncestorDepth x = 0 from hm0] at hf
    exact hx hf
  obtain ⟨⟨v,y⟩,hvy,hv⟩ := Finset.mem_image.mp (f.firstMappedAncestor_mem x)
  dsimp at hv
  subst v
  have hmatch : RankAgrees b (T.rank ((T.parent^[m]) x)) (U.rank y) := f.ranks _ hvy
  have hne : ∀ j < m, (T.parent^[j]) x ≠ T.root := by
    intro j hj heq
    exact f.before_firstMappedAncestor x hj (heq ▸ f.root_mem_source)
  obtain ⟨σ,ht⟩ := exists_ancestor_rank_template T x m a b d hdb hba (U.rank y) hmatch hne
  let f' := f.lower hdb.le
  obtain ⟨g,hg,hpath⟩ := extend_path hU f' ((T.parent^[m]) x) y hvy
    (ancestorPath T x σ m) ht (ancestorPath_fresh f x σ)
    (ancestorPath_nodup T x σ m (f.firstMappedAncestorDepth_le_height x))
  refine ⟨g,hg,?_⟩
  have hmem : (x,σ 0) ∈ ancestorPath T x σ m := by
    apply List.mem_map.mpr
    refine ⟨0,List.mem_reverse.mpr (List.mem_range.mpr hm),?_⟩
    rfl
  obtain ⟨w,hw,_⟩ := hpath (x,σ 0) hmem
  exact Finset.mem_image.mpr ⟨(x,w),hw,rfl⟩

end FSCofinality.Padding

