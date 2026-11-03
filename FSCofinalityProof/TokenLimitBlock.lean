import FSCofinalityProof.TokenLimitStep

noncomputable section

namespace FSCofinality.Tokens
open GenericTables

theorem branchEdge_eq_of_snapshot {U : Type*} {Col : ℕ → Type*}
    (profile : ∀ n, U → Col n → Bool) (A : Table) (e n : ℕ) {v w : Token U}
    (hc : localCode v n = localCode w n) (ht : activeTuple v n = activeTuple w n)
    (c : Token (Col n)) : branchEdge profile A e n v c = branchEdge profile A e n w c := by
  simp only [branchEdge,activeProfiles,hc,ht]

/-- The finite branch-level induction in limit one-point extension. Every
processed level is retained literally while later levels add new slots. -/
theorem limit_branch_block {U : Type} [Nonempty U] {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool)
    (hcol : ∀ n, Function.Injective (fun c : Col n => fun u => profile n u c))
    (e count : ℕ → ℕ) (c : ∀ n, Fin (count n) → Token (Col n))
    (epsilon : ∀ n, Fin (count n) → Bool)
    (hconsistent : ∀ n i j, c n i = c n j → epsilon n i = epsilon n j)
    (labelBound : ℕ → ℕ) (v : Token U) (start steps : ℕ)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ start) :
    ∃ w : Token U,
      (∀ a ∈ (history w).val.activation, a ≤ start+steps) ∧
      (∀ m < start, localCode w m = localCode v m ∧ activeTuple w m = activeTuple v m) ∧
      ∀ i < steps, labelBound (start+i) < localCode w (start+i) ∧
        ∀ j, branchEdge profile genericTable (e (start+i)) (start+i) w (c (start+i) j) =
          epsilon (start+i) j := by
  induction steps with
  | zero =>
    refine ⟨v,?_,fun _ _ => ⟨rfl,rfl⟩,?_⟩
    · simpa only [Nat.add_zero] using hbound
    · intro i hi
      omega
  | succ steps IH =>
    obtain ⟨v0,hb0,hpast,hbits⟩ := IH
    obtain ⟨w,extra,_,hlabel,hbw,hkeep,hnew⟩ := limit_branch_step profile
      (e (start+steps)) (start+steps) (hcol _) v0 hb0
      (c (start+steps)) (epsilon (start+steps)) (hconsistent _) (labelBound (start+steps))
    refine ⟨w,?_,?_,?_⟩
    · intro a ha
      exact (hbw a ha).trans (by omega)
    · intro m hm
      have hk := hkeep m (by omega)
      have hp := hpast m hm
      exact ⟨hk.1.trans hp.1,hk.2.trans hp.2⟩
    · intro i hi
      by_cases hold : i < steps
      · have hk := hkeep (start+i) (by omega)
        have hb := hbits i hold
        refine ⟨by rw [hk.1]; exact hb.1,fun j => ?_⟩
        exact (branchEdge_eq_of_snapshot profile genericTable (e (start+i)) (start+i)
          hk.1 hk.2 (c (start+i) j)).trans (hb.2 j)
      · have heq : i = steps := by omega
        subst i
        exact ⟨hlabel,hnew⟩

end FSCofinality.Tokens
