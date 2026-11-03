import FSCofinalityProof.TokenLimitExtension

noncomputable section

namespace FSCofinality.Tokens

theorem finite_type_down {Old : Type*} (r : ℕ → Old → Prop)
    (hdown : ∀ n i, r (n+1) i → r n i) {m n : ℕ} (hmn : m ≤ n)
    (i : Old) (hr : r n i) : r m i := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact hr
  | succ n IH =>
    by_cases hm : m = n+1
    · rw [hm]
      exact hr
    · exact IH (by omega) (hdown n i hr)

/-- Every consistent finite one-point type in nested eventually separating
equivalence relations is either wholly separate, or anchored through one
last finite level and wholly separate thereafter. -/
theorem classify_finite_limit_type {Old : Type*} [Fintype Old]
    (E : ℕ → Old → Old → Prop) (r : ℕ → Old → Prop)
    (hdown : ∀ n i, r (n+1) i → r n i)
    (hsep : ∀ i, ∃ N, ∀ n ≥ N, ¬ r n i)
    (hcoherent : ∀ n i, r n i → ∀ j, r n j ↔ E n i j) :
    (∀ n i, ¬ r n i) ∨ ∃ N i, r N i ∧
      (∀ m ≤ N, ∀ j, r m j ↔ E m i j) ∧ ∀ n > N, ∀ j, ¬ r n j := by
  classical
  by_cases hnone : ∀ n i, ¬ r n i
  · exact Or.inl hnone
  right
  choose bound hbound using hsep
  let B := Finset.univ.sup bound
  have hlt (n : ℕ) (i : Old) (hr : r n i) : n < B := by
    have hi : bound i ≤ B := Finset.le_sup (f := bound) (Finset.mem_univ i)
    by_contra hn
    exact hbound i n (by omega) hr
  let S := (Finset.range B).filter (fun n => ∃ i, r n i)
  have hS : S.Nonempty := by
    push_neg at hnone
    obtain ⟨n,i,hr⟩ := hnone
    exact ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hlt n i hr),i,hr⟩⟩
  let N := S.max' hS
  have hN : N ∈ S := Finset.max'_mem _ _
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hN).2
  refine ⟨N,i,hi,?_,?_⟩
  · intro m hm j
    exact hcoherent m i (finite_type_down r hdown hm i hi) j
  · intro n hn j hr
    have hnS : n ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hlt n j hr),j,hr⟩
    have hle : n ≤ N := Finset.le_max' _ _ hnS
    omega

end FSCofinality.Tokens
