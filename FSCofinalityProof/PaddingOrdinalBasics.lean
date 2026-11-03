import FSCofinalityProof.PaddingTemplate

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.Padding

theorem RankAgrees.eq_of_lt_left {b : Ordinal.{0}} {r s : WithTop Ordinal.{0}}
    (h : RankAgrees b r s) (hr : r < (cutoff b : WithTop Ordinal.{0})) : r = s := by
  rcases h with heq | ⟨hhigh,_⟩
  · exact heq
  · exact False.elim ((not_lt_of_ge hhigh) hr)

theorem RankAgrees.high_right {b : Ordinal.{0}} {r s : WithTop Ordinal.{0}}
    (h : RankAgrees b r s) (hr : (cutoff b : WithTop Ordinal.{0}) ≤ r) :
    (cutoff b : WithTop Ordinal.{0}) ≤ s := by
  rcases h with heq | ⟨_,hs⟩
  · exact heq ▸ hr
  · exact hs

/-- The finite slack in a new path fits below every strictly later
omega-multiple cutoff. -/
theorem cutoff_add_nat_lt {d b : Ordinal.{0}} (hdb : d < b) (n : ℕ) :
    cutoff d + (n : Ordinal.{0}) < cutoff b := by
  calc
    cutoff d + (n : Ordinal.{0}) < cutoff d + Ordinal.omega0 :=
      (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 n)
    _ = cutoff (Order.succ d) := by simp only [cutoff,Ordinal.mul_succ]
    _ ≤ cutoff b := cutoff_mono (Order.succ_le_of_lt hdb)

def finiteOrdinal (r : WithTop Ordinal.{0}) : Ordinal.{0} :=
  @WithTop.untopD Ordinal.{0} 0 r

theorem coe_untopD_of_lt {r : WithTop Ordinal.{0}} {a : Ordinal.{0}}
    (hr : r < (a : WithTop Ordinal.{0})) : (finiteOrdinal r : WithTop Ordinal.{0}) = r := by
  rcases r with _ | r
  · exact False.elim ((not_lt_of_ge le_top) hr)
  · rfl

theorem RankedTree.rank_iterate_parent_monotone (T : RankedTree) (x : T.Vertex) :
    Monotone (fun n : ℕ => T.rank ((T.parent^[n]) x)) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [Function.iterate_succ_apply'] using T.rank_parent ((T.parent^[n]) x)

/-- The ordinal rank assigned to a new path vertex in the high-anchor
case. Low vertices retain their exact rank; high vertices use finite
slack above the new cutoff. -/
def pathRank (T : RankedTree) (x : T.Vertex) (d : Ordinal.{0}) (j : ℕ) : Ordinal.{0} :=
  if T.rank ((T.parent^[j]) x) < (cutoff d : WithTop Ordinal.{0}) then
    finiteOrdinal (T.rank ((T.parent^[j]) x)) else cutoff d+j

theorem pathRank_agrees (T : RankedTree) (x : T.Vertex) (d : Ordinal.{0}) (j : ℕ) :
    RankAgrees d (T.rank ((T.parent^[j]) x)) (pathRank T x d j : WithTop Ordinal.{0}) := by
  unfold pathRank
  split_ifs with hj
  · exact Or.inl (coe_untopD_of_lt hj).symm
  · exact Or.inr ⟨le_of_not_gt hj,WithTop.coe_le_coe.mpr (le_self_add)⟩

theorem pathRank_lt {T : RankedTree} (x : T.Vertex) {a b d : Ordinal.{0}}
    (hdb : d < b) (hba : cutoff b ≤ a) (j : ℕ) : pathRank T x d j < a := by
  unfold pathRank
  split_ifs with hj
  · have hco : (finiteOrdinal (T.rank ((T.parent^[j]) x)) : WithTop Ordinal.{0}) =
        T.rank ((T.parent^[j]) x) := coe_untopD_of_lt hj
    have hlt : finiteOrdinal (T.rank ((T.parent^[j]) x)) < cutoff d :=
      WithTop.coe_lt_coe.mp (by rwa [hco])
    exact hlt.trans_le ((cutoff_mono hdb.le).trans hba)
  · exact (cutoff_add_nat_lt hdb j).trans_le hba

theorem pathRank_lt_succ (T : RankedTree) (x : T.Vertex) (d : Ordinal.{0}) (j : ℕ)
    (hne : (T.parent^[j]) x ≠ T.root) : pathRank T x d j < pathRank T x d (j+1) := by
  have hp : T.rank ((T.parent^[j]) x) ≤ T.rank ((T.parent^[j+1]) x) :=
    T.rank_iterate_parent_monotone x (by omega)
  unfold pathRank
  by_cases hj : T.rank ((T.parent^[j]) x) < (cutoff d : WithTop Ordinal.{0})
  · have he : (finiteOrdinal (T.rank ((T.parent^[j]) x)) : WithTop Ordinal.{0}) =
        T.rank ((T.parent^[j]) x) := coe_untopD_of_lt hj
    by_cases hj' : T.rank ((T.parent^[j+1]) x) < (cutoff d : WithTop Ordinal.{0})
    · simp only [if_pos hj,if_pos hj']
      have he' := coe_untopD_of_lt hj'
      apply WithTop.coe_lt_coe.mp
      rw [he,he']
      have hfinite : T.rank ((T.parent^[j]) x) ≠ ⊤ := by
        intro htop
        rw [htop] at hj
        exact (not_lt_of_ge le_top) hj
      simpa only [Function.iterate_succ_apply'] using
        T.finite_rank_strict ((T.parent^[j]) x) hne hfinite
    · simp only [if_pos hj,if_neg hj']
      have hl : finiteOrdinal (T.rank ((T.parent^[j]) x)) < cutoff d :=
        WithTop.coe_lt_coe.mp (by rwa [he])
      exact hl.trans_le le_self_add
  · by_cases hj' : T.rank ((T.parent^[j+1]) x) < (cutoff d : WithTop Ordinal.{0})
    · exact False.elim (hj (hp.trans_lt hj'))
    · simp only [if_neg hj,if_neg hj']
      apply (add_lt_add_iff_left _).mpr
      exact_mod_cast Nat.lt_succ_self j

theorem pathRank_anchor_le {T : RankedTree} {x : T.Vertex} {b d : Ordinal.{0}}
    (hdb : d < b) (m : ℕ) (targetRank : WithTop Ordinal.{0})
    (hhigh : (cutoff b : WithTop Ordinal.{0}) ≤ T.rank ((T.parent^[m]) x))
    (hmatch : RankAgrees b (T.rank ((T.parent^[m]) x)) targetRank) :
    (pathRank T x d m : WithTop Ordinal.{0}) ≤ targetRank := by
  have htarget := hmatch.high_right hhigh
  have hnot : ¬ T.rank ((T.parent^[m]) x) < (cutoff d : WithTop Ordinal.{0}) := by
    apply not_lt_of_ge
    exact (WithTop.coe_le_coe.mpr (cutoff_mono hdb.le)).trans hhigh
  simp only [pathRank,if_neg hnot]
  exact (WithTop.coe_lt_coe.mpr (cutoff_add_nat_lt hdb m)).le.trans htarget

end FSCofinality.Padding


