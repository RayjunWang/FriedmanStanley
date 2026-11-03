import FSCofinalityProof.GenericTablesHistories

noncomputable section

namespace FSCofinality.GenericTables

/-- A sorted activation list activates an initial segment, exactly as used
by `Tokens.activeTuple`; no later slot is silently selected out of order. -/
theorem filter_le_eq_take (a : List ℕ) (ha : a.Pairwise (· ≤ ·)) (n : ℕ) :
    a.filter (fun t => decide (t ≤ n)) =
      a.take ((a.filter (fun t => decide (t ≤ n))).length) := by
  induction a with
  | nil => rfl
  | cons x a IH =>
    have hpair := List.pairwise_cons.mp ha
    by_cases hx : x ≤ n
    · simp only [List.filter_cons,decide_eq_true hx,if_true,List.length_cons]
      rw [List.take_succ_cons,← IH hpair.2]
    · have he : a.filter (fun t => decide (t ≤ n)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simpa only [decide_eq_true_eq] using
          not_le.mpr ((lt_of_not_ge hx).trans_le (hpair.1 y hy))
      simp [hx,he]

theorem activeTimes_is_initial_segment (h : History) (n : ℕ) :
    h.activeTimes n = h.activation.take (h.activeTimes n).length :=
  filter_le_eq_take h.activation h.ordered n

end FSCofinality.GenericTables
