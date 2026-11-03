import FSCofinalityProof.RawObjectsProfiles

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects
section Encoding
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))

def freshColumn (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    Column η hη lam hlam lower n := ⟨⟨n,c⟩,le_rfl⟩

theorem column_succ_cases (n : ℕ) (c : Column η hη lam hlam lower (n+1)) :
    (∃ d, c = freshColumn η hη lam hlam lower (n+1) d) ∨
      (∃ d, c = propagate η hη lam hlam lower n d) := by
  rcases c with ⟨⟨k,c⟩,hk⟩
  change k ≤ n+1 at hk
  by_cases h : k = n+1
  · subst k
    exact Or.inl ⟨c,rfl⟩
  · exact Or.inr ⟨⟨⟨k,c⟩,by change k ≤ n; omega⟩,rfl⟩

/-- Encode a column by advancing its unique birth ancestor through the
actual P-family maps. -/
def encodeColumn : (n : ℕ) → Column η hη lam hlam lower n → Ambient η hη
  | 0,⟨⟨k,c⟩,hk⟩ => encodeNew η hη lam hlam lower 0 ((Nat.eq_zero_of_le_zero hk) ▸ c)
  | n+1,c => if h : c.val.1 = n+1 then encodeNew η hη lam hlam lower (n+1) (h ▸ c.val.2)
    else oldColumn η hη lam hlam n (encodeColumn n ⟨c.val,by have hc := c.property; omega⟩)

@[simp] theorem encodeColumn_fresh (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    encodeColumn η hη lam hlam lower n (freshColumn η hη lam hlam lower n c) =
      encodeNew η hη lam hlam lower n c := by
  cases n <;> simp [encodeColumn,freshColumn]

@[simp] theorem encodeColumn_propagate (n : ℕ) (c : Column η hη lam hlam lower n) :
    encodeColumn η hη lam hlam lower (n+1) (propagate η hη lam hlam lower n c) =
      oldColumn η hη lam hlam n (encodeColumn η hη lam hlam lower n c) := by
  have h : c.val.1 ≠ n+1 := Nat.ne_of_lt (Nat.lt_succ_of_le c.property)
  simp only [encodeColumn,propagate,dif_neg h]
  apply congrArg (oldColumn η hη lam hlam n)
  apply congrArg (encodeColumn η hη lam hlam lower n)
  exact Subtype.ext rfl

theorem encodeColumn_injective (htop : lam ≤ Frame.top η) (n : ℕ) :
    Function.Injective (encodeColumn η hη lam hlam lower n) := by
  induction n with
  | zero =>
    rintro ⟨⟨k,c⟩,hk⟩ ⟨⟨j,d⟩,hj⟩ h
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst k
    subst j
    have hcd := encodeNew_injective η hη lam hlam lower htop 0 h
    exact congrArg (freshColumn η hη lam hlam lower 0) hcd
  | succ n ih =>
    intro c d h
    rcases column_succ_cases η hη lam hlam lower n c with ⟨c,rfl⟩ | ⟨c,rfl⟩ <;>
      rcases column_succ_cases η hη lam hlam lower n d with ⟨d,rfl⟩ | ⟨d,rfl⟩
    · rw [encodeColumn_fresh,encodeColumn_fresh] at h
      exact congrArg (freshColumn η hη lam hlam lower (n+1))
        (encodeNew_injective η hη lam hlam lower htop (n+1) h)
    · rw [encodeColumn_fresh,encodeColumn_propagate] at h
      exact False.elim (oldColumn_ne_new η hη lam hlam htop lower n _ _
        (encodeNew_mem η hη lam hlam lower (n+1) c) h.symm)
    · rw [encodeColumn_propagate,encodeColumn_fresh] at h
      exact False.elim (oldColumn_ne_new η hη lam hlam htop lower n _ _
        (encodeNew_mem η hη lam hlam lower (n+1) d) h)
    · rw [encodeColumn_propagate,encodeColumn_propagate] at h
      exact congrArg (propagate η hη lam hlam lower n)
        (ih (oldColumn_injective η hη lam hlam htop n h))

def ColumnSet (n : ℕ) : Set (Ambient η hη) := range (encodeColumn η hη lam hlam lower n)

theorem columnSet_zero : ColumnSet η hη lam hlam lower 0 =
    {c | NewColumn η hη lam hlam lower 0 c} := by
  ext c
  constructor
  · rintro ⟨⟨⟨k,d⟩,hk⟩,rfl⟩
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact encodeNew_mem η hη lam hlam lower 0 d
  · intro hc
    obtain ⟨d,rfl⟩ := encodeNew_surjective η hη lam hlam lower 0 hc
    exact ⟨freshColumn η hη lam hlam lower 0 d,encodeColumn_fresh η hη lam hlam lower 0 d⟩

theorem columnSet_succ (n : ℕ) : ColumnSet η hη lam hlam lower (n+1) =
    oldColumn η hη lam hlam n '' ColumnSet η hη lam hlam lower n ∪
      {c | NewColumn η hη lam hlam lower (n+1) c} := by
  ext c
  constructor
  · rintro ⟨d,rfl⟩
    rcases column_succ_cases η hη lam hlam lower n d with ⟨d,rfl⟩ | ⟨d,rfl⟩
    · exact Or.inr (by rw [encodeColumn_fresh]; exact encodeNew_mem η hη lam hlam lower (n+1) d)
    · exact Or.inl ⟨_,⟨d,rfl⟩,(encodeColumn_propagate η hη lam hlam lower n d).symm⟩
  · rintro (⟨d,⟨d,rfl⟩,rfl⟩ | hc)
    · exact ⟨propagate η hη lam hlam lower n d,encodeColumn_propagate η hη lam hlam lower n d⟩
    · obtain ⟨d,rfl⟩ := encodeNew_surjective η hη lam hlam lower (n+1) hc
      exact ⟨freshColumn η hη lam hlam lower (n+1) d,encodeColumn_fresh η hη lam hlam lower (n+1) d⟩

end Encoding
end FSCofinality.RawObjects
