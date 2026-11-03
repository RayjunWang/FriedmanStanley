import FSCofinalityProof.RawObjectsPoolColumns

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

section BirthAbsoluteness
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}

theorem columnSet_mono (h : ∀ b hb, lower b hb ⊆ upper b hb) (n : ℕ) :
    ColumnSet η hη lam hlam lower n ⊆ ColumnSet η hη lam hlam upper n := by
  induction n with
  | zero =>
    rw [columnSet_zero,columnSet_zero]
    intro c hc
    exact newColumn_mono η hη lam hlam h 0 hc
  | succ n ih =>
    rw [columnSet_succ,columnSet_succ]
    apply union_subset_union
    · rintro c ⟨d,hd,rfl⟩
      exact ⟨d,ih hd,rfl⟩
    · intro c hc
      exact newColumn_mono η hη lam hlam h (n+1) hc

/-- Restricted columns have exactly the same birth status as their ambient
semantic names. No new ambient predecessor appears after restricting pools. -/
theorem newColumn_birth_absolute (htop : lam ≤ Frame.top η)
    (h : ∀ b hb, lower b hb ⊆ upper b hb) (n : ℕ) :
    {c | NewColumn η hη lam hlam lower n c} =
      ColumnSet η hη lam hlam lower n ∩ {c | NewColumn η hη lam hlam upper n c} := by
  ext c
  constructor
  · intro hc
    obtain ⟨d,hd⟩ := encodeNew_surjective η hη lam hlam lower n hc
    refine ⟨⟨freshColumn η hη lam hlam lower n d,?_⟩,
      newColumn_mono η hη lam hlam h n hc⟩
    exact (encodeColumn_fresh η hη lam hlam lower n d).trans hd
  · rintro ⟨hc,hnew⟩
    cases n with
    | zero => rwa [columnSet_zero] at hc
    | succ n =>
      rw [columnSet_succ] at hc
      rcases hc with ⟨d,hd,rfl⟩ | hc
      · exact False.elim (oldColumn_ne_new η hη lam hlam htop upper n d _ hnew rfl)
      · exact hc

/-- Even across different restricted pools, an actual column object has one
semantic birth ancestor. -/
theorem encoded_columns_same_birth (htop : lam ≤ Frame.top η) (n : ℕ)
    (c : Column η hη lam hlam lower n) (d : Column η hη lam hlam upper n)
    (h : encodeColumn η hη lam hlam lower n c = encodeColumn η hη lam hlam upper n d) :
    encodeBirth η hη lam hlam lower c.val = encodeBirth η hη lam hlam upper d.val := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    rcases d with ⟨⟨j,d⟩,hj⟩
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst k
    subst j
    exact Prod.ext rfl h
  | succ n ih =>
    rcases column_succ_cases η hη lam hlam lower n c with ⟨c,rfl⟩ | ⟨c,rfl⟩ <;>
      rcases column_succ_cases η hη lam hlam upper n d with ⟨d,rfl⟩ | ⟨d,rfl⟩
    · rw [encodeColumn_fresh,encodeColumn_fresh] at h
      exact Prod.ext rfl h
    · rw [encodeColumn_fresh,encodeColumn_propagate] at h
      exact False.elim (oldColumn_ne_new η hη lam hlam htop lower n _ _
        (encodeNew_mem η hη lam hlam lower (n+1) c) h.symm)
    · rw [encodeColumn_propagate,encodeColumn_fresh] at h
      exact False.elim (oldColumn_ne_new η hη lam hlam htop upper n _ _
        (encodeNew_mem η hη lam hlam upper (n+1) d) h)
    · rw [encodeColumn_propagate,encodeColumn_propagate] at h
      exact ih c d (oldColumn_injective η hη lam hlam htop n h)

end BirthAbsoluteness
end FSCofinality.RawObjects
