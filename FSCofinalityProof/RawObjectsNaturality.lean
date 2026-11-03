import FSCofinalityProof.RawObjectsBirthAbsoluteness

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

section Naturality
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}
    (h : ∀ b hb, lower b hb ⊆ upper b hb)

def mapBirthData (n : ℕ) : BirthData η hη lam hlam lower n → BirthData η hη lam hlam upper n
  | Sum.inl v => Sum.inl ⟨v.val,h _ _ v.property⟩
  | Sum.inr (Sum.inl u) => Sum.inr (Sum.inl u)
  | Sum.inr (Sum.inr v) => Sum.inr (Sum.inr ⟨v.val,h _ _ v.property⟩)

theorem mapBirthData_injective (n : ℕ) :
    Function.Injective (mapBirthData η hη lam hlam h n) := by
  intro c d hc
  rcases c with v | ⟨u | v⟩ <;> rcases d with w | ⟨z | w⟩
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact congrArg (fun t : {v : Ambient η hη // v ∈ upper (Frame.q η lam hlam n)
      (Frame.q_lt η lam hlam n)} => t.val) (Sum.inl.inj hc)
  · cases hc
  · cases hc
  · cases hc
  · exact congrArg (Sum.inr ∘ Sum.inl) (Sum.inl.inj (Sum.inr.inj hc))
  · have hc' := _root_.Sum.inr.inj hc; cases hc'
  · cases hc
  · have hc' := _root_.Sum.inr.inj hc; cases hc'
  · apply congrArg (Sum.inr ∘ Sum.inr)
    apply Subtype.ext
    exact congrArg (fun t : {v : Ambient η hη // v ∈ upper (Frame.rho η lam hlam n)
      (Frame.rho_lt η lam hlam n)} => t.val) (Sum.inr.inj (Sum.inr.inj hc))

def mapBirth : Birth η hη lam hlam lower ↪ Birth η hη lam hlam upper where
  toFun b := ⟨b.1,mapBirthData η hη lam hlam h b.1 b.2⟩
  inj' := by
    rintro ⟨n,c⟩ ⟨m,d⟩ heq
    have hnm : n=m := congrArg Sigma.fst heq
    subst m
    exact congrArg (Sigma.mk n) ((mapBirthData_injective η hη lam hlam h n)
      (eq_of_heq (Sigma.mk.inj_iff.mp heq).2))

def mapSourceTuple (s : SourceTuple η hη lam hlam lower) : SourceTuple η hη lam hlam upper :=
  fun n => ⟨(s n).val,h _ _ (s n).property⟩

def mapRow : LimitRow η hη lam hlam lower → LimitRow η hη lam hlam upper
  | Sum.inl s => Sum.inl (mapSourceTuple η hη lam hlam h s)
  | Sum.inr A => Sum.inr (A.map (mapBirth η hη lam hlam h))

def mapColumn (n : ℕ) (c : Column η hη lam hlam lower n) : Column η hη lam hlam upper n :=
  ⟨mapBirth η hη lam hlam h c.val,c.property⟩

@[simp] theorem encodeNew_map (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    encodeNew η hη lam hlam upper n (mapBirthData η hη lam hlam h n c) =
      encodeNew η hη lam hlam lower n c := by
  rcases c with v | ⟨u | v⟩ <;> rfl

@[simp] theorem encodeBirth_map (b : Birth η hη lam hlam lower) :
    encodeBirth η hη lam hlam upper (mapBirth η hη lam hlam h b) =
      encodeBirth η hη lam hlam lower b := by
  rcases b with ⟨n,c⟩
  exact Prod.ext rfl (encodeNew_map η hη lam hlam h n c)

theorem mapColumn_fresh (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    mapColumn η hη lam hlam h n (freshColumn η hη lam hlam lower n c) =
      freshColumn η hη lam hlam upper n (mapBirthData η hη lam hlam h n c) := rfl

theorem mapColumn_propagate (n : ℕ) (c : Column η hη lam hlam lower n) :
    mapColumn η hη lam hlam h (n+1) (propagate η hη lam hlam lower n c) =
      propagate η hη lam hlam upper n (mapColumn η hη lam hlam h n c) := rfl

@[simp] theorem encodeColumn_map (n : ℕ) (c : Column η hη lam hlam lower n) :
    encodeColumn η hη lam hlam upper n (mapColumn η hη lam hlam h n c) =
      encodeColumn η hη lam hlam lower n c := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    have hk0 : k=0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact encodeNew_map η hη lam hlam h 0 c
  | succ n ih =>
    rcases column_succ_cases η hη lam hlam lower n c with ⟨c,rfl⟩ | ⟨c,rfl⟩
    · rw [mapColumn_fresh,encodeColumn_fresh,encodeColumn_fresh,encodeNew_map]
    · rw [mapColumn_propagate,encodeColumn_propagate,encodeColumn_propagate,ih]

@[simp] theorem rowObject_map (htop : lam ≤ Frame.top η) (r : LimitRow η hη lam hlam lower) :
    rowObject η hη lam hlam upper htop (mapRow η hη lam hlam h r) =
      rowObject η hη lam hlam lower htop r := by
  rcases r with s | A
  · rfl
  · simp only [mapRow,rowObject,Finset.map_map]
    congr 1
    apply congrArg (fun f => A.map f)
    apply Function.Embedding.ext
    intro b
    exact encodeBirth_map η hη lam hlam h b

@[simp] theorem rowBit_map (r : LimitRow η hη lam hlam lower) (b : Birth η hη lam hlam lower) :
    rowBit η hη lam hlam upper (mapRow η hη lam hlam h r) (mapBirth η hη lam hlam h b) =
      rowBit η hη lam hlam lower r b := by
  rcases r with s | A
  · rcases b with ⟨n,v | ⟨u | v⟩⟩
    · change decide (_ = _) = decide (_ = _)
      apply decide_eq_decide.mpr
      simp only [Subtype.ext_iff,mapSourceTuple]
    · rfl
    · rfl
  · change decide (_ ∈ A.map _) = decide (b ∈ A)
    apply decide_eq_decide.mpr
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨c,hc,heq⟩
      exact (mapBirth η hη lam hlam h).injective heq ▸ hc
    · intro hb
      exact ⟨b,hb,rfl⟩

@[simp] theorem profile_map (n : ℕ) (r : LimitRow η hη lam hlam lower)
    (c : Column η hη lam hlam lower n) :
    profile η hη lam hlam upper n (mapRow η hη lam hlam h r) (mapColumn η hη lam hlam h n c) =
      profile η hη lam hlam lower n r c := rowBit_map η hη lam hlam h r c.val

end Naturality

/-- Profiles depend on the actual row and column semantic names, even when
the two countable pools and their subtype presentations differ. -/
theorem profile_semantic_congr (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)} (n : ℕ)
    (r : LimitRow η hη lam hlam lower) (s : LimitRow η hη lam hlam upper)
    (c : Column η hη lam hlam lower n) (d : Column η hη lam hlam upper n)
    (hrow : rowObject η hη lam hlam lower htop r = rowObject η hη lam hlam upper htop s)
    (hcol : encodeColumn η hη lam hlam lower n c = encodeColumn η hη lam hlam upper n d) :
    profile η hη lam hlam lower n r c = profile η hη lam hlam upper n s d := by
  let common : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη) :=
    fun b hb => lower b hb ∪ upper b hb
  have hleft : ∀ b hb, lower b hb ⊆ common b hb := fun _ _ => subset_union_left
  have hright : ∀ b hb, upper b hb ⊆ common b hb := fun _ _ => subset_union_right
  have hr : mapRow η hη lam hlam hleft r = mapRow η hη lam hlam hright s :=
    rowObject_injective η hη lam hlam common htop
      ((rowObject_map η hη lam hlam hleft htop r).trans
        (hrow.trans (rowObject_map η hη lam hlam hright htop s).symm))
  have hc : mapColumn η hη lam hlam hleft n c = mapColumn η hη lam hlam hright n d :=
    encodeColumn_injective η hη lam hlam common htop n
      ((encodeColumn_map η hη lam hlam hleft n c).trans
        (hcol.trans (encodeColumn_map η hη lam hlam hright n d).symm))
  calc
    profile η hη lam hlam lower n r c =
        profile η hη lam hlam common n (mapRow η hη lam hlam hleft r)
          (mapColumn η hη lam hlam hleft n c) := (profile_map η hη lam hlam hleft n r c).symm
    _ = profile η hη lam hlam common n (mapRow η hη lam hlam hright s)
          (mapColumn η hη lam hlam hright n d) := by rw [hr,hc]
    _ = profile η hη lam hlam upper n s d := profile_map η hη lam hlam hright n s d

theorem ambientProfile_restricted (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    {lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}
    (h : ∀ b hb, lower b hb ⊆ fullLower η hη lam b hb)
    (n : ℕ) (r : LimitRow η hη lam hlam lower) (c : Column η hη lam hlam lower n) :
    ambientProfile η hη lam hlam htop n (rowObject η hη lam hlam lower htop r)
      (mapColumn η hη lam hlam h n c) = profile η hη lam hlam lower n r c := by
  have hx : rowObject η hη lam hlam lower htop r ∈ Valid η hη lam := by
    have hm := rowObject_mem_limitSet η hη lam hlam (fullLower η hη lam) htop
      (mapRow η hη lam hlam h r)
    rw [rowObject_map] at hm
    rwa [valid_limit η hη lam hlam] 
  have hr : ambientRow η hη lam hlam htop (rowObject η hη lam hlam lower htop r) hx =
      mapRow η hη lam hlam h r := by
    apply rowObject_injective η hη lam hlam (fullLower η hη lam) htop
    exact (rowObject_ambientRow η hη lam hlam htop _ hx).trans
      (rowObject_map η hη lam hlam h htop r).symm
  simp only [ambientProfile,dif_pos hx,hr]
  exact profile_map η hη lam hlam h n r c

end FSCofinality.RawObjects
