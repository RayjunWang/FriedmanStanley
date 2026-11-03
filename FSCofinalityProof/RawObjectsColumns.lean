import FSCofinalityProof.RawObjectsCountablePools

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem tag_ne (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (ha : a ≤ Frame.top η) {n m : ℕ} (hnm : n ≠ m) :
    tag η hη a n ≠ tag η hη a m := fun h => hnm (tag_injective η hη a ha h)

theorem dataColumn_injective (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η) (n : ℕ) :
    Function.Injective (dataColumn η hη lam hlam n) := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  intro u v h
  apply lift_injective η hη (Frame.q η lam hlam n) (Frame.sigma η lam hlam n)
    (Frame.q_le_sigma η lam hlam n) hs
  exact Enc_injective _ _ _ _ (tag_ne η hη _ hs (by decide : (1 : ℕ) ≠ 3)) h

theorem dataColumn_ne_marker (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (u : Ambient η hη) :
    dataColumn η hη lam hlam n u ≠ markerColumn η hη lam hlam n := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  exact Enc_ne _ _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (1 : ℕ) ≠ 3))
    (tag_ne η hη _ hs (by decide : (1 : ℕ) ≠ 2))

theorem dataColumn_ne_singleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (u v : Ambient η hη) :
    dataColumn η hη lam hlam n u ≠ singleton (level η (Frame.delta η lam hlam n)) v := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  exact Enc_ne_singleton _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (1 : ℕ) ≠ 3))

theorem markerColumn_ne_singleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (v : Ambient η hη) :
    markerColumn η hη lam hlam n ≠ singleton (level η (Frame.delta η lam hlam n)) v := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  exact Enc_ne_singleton _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (2 : ℕ) ≠ 3))

def oldColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) (c : Ambient η hη) : Ambient η hη :=
  Enc (level η (Frame.rho η lam hlam (n+1))) (level η (Frame.delta η lam hlam (n+1)))
    (tag η hη (Frame.sigma η lam hlam (n+1)) 0) (tag η hη (Frame.sigma η lam hlam (n+1)) 3)
    (lift η hη (Frame.delta η lam hlam n) (Frame.sigma η lam hlam (n+1)) c)

theorem oldColumn_injective (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η) (n : ℕ) :
    Function.Injective (oldColumn η hη lam hlam n) := by
  have hs := (Frame.sigma_lt η lam hlam (n+1)).le.trans htop
  intro u v h
  apply lift_injective η hη (Frame.delta η lam hlam n) (Frame.sigma η lam hlam (n+1))
    (Frame.delta_le_sigma_next η lam hlam n) hs
  exact Enc_injective _ _ _ _ (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 3)) h

theorem oldColumn_ne_new (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)) (n : ℕ)
    (c d : Ambient η hη) (hd : NewColumn η hη lam hlam lower (n+1) d) :
    oldColumn η hη lam hlam n c ≠ d := by
  have hs := (Frame.sigma_lt η lam hlam (n+1)).le.trans htop
  rcases hd with ⟨v,hv,rfl⟩ | rfl | ⟨v,hv,rfl⟩
  · exact Enc_ne _ _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 3))
      (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 1))
  · exact Enc_ne _ _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 3))
      (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 2))
  · exact Enc_ne_singleton _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 3))

section Births
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))

def BirthData (n : ℕ) :=
  {v : Ambient η hη // v ∈ lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n)} ⊕
    (Unit ⊕ {v : Ambient η hη // v ∈ lower (Frame.rho η lam hlam n) (Frame.rho_lt η lam hlam n)})

def encodeNew (n : ℕ) : BirthData η hη lam hlam lower n → Ambient η hη
  | Sum.inl v => dataColumn η hη lam hlam n v.val
  | Sum.inr (Sum.inl _) => markerColumn η hη lam hlam n
  | Sum.inr (Sum.inr v) => singleton (level η (Frame.delta η lam hlam n)) v.val

theorem encodeNew_mem (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    NewColumn η hη lam hlam lower n (encodeNew η hη lam hlam lower n c) := by
  rcases c with v | ⟨⟨⟩⟩ | v
  · exact Or.inl ⟨v.val,v.property,rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨v.val,v.property,rfl⟩)

theorem encodeNew_surjective (n : ℕ) {c : Ambient η hη}
    (hc : NewColumn η hη lam hlam lower n c) :
    ∃ d, encodeNew η hη lam hlam lower n d = c := by
  rcases hc with ⟨v,hv,rfl⟩ | rfl | ⟨v,hv,rfl⟩
  · exact ⟨Sum.inl ⟨v,hv⟩,rfl⟩
  · exact ⟨Sum.inr (Sum.inl ()),rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨v,hv⟩),rfl⟩

theorem encodeNew_injective (htop : lam ≤ Frame.top η) (n : ℕ) :
    Function.Injective (encodeNew η hη lam hlam lower n) := by
  intro c d h
  rcases c with v | ⟨⟨⟩⟩ | v <;> rcases d with w | ⟨⟨⟩⟩ | w
  · exact congrArg Sum.inl (Subtype.ext (dataColumn_injective η hη lam hlam htop n h))
  · exact False.elim (dataColumn_ne_marker η hη lam hlam htop n v.val h)
  · exact False.elim (dataColumn_ne_singleton η hη lam hlam htop n v.val w.val h)
  · exact False.elim (dataColumn_ne_marker η hη lam hlam htop n w.val h.symm)
  · rfl
  · exact False.elim (markerColumn_ne_singleton η hη lam hlam htop n w.val h)
  · exact False.elim (dataColumn_ne_singleton η hη lam hlam htop n w.val v.val h.symm)
  · exact False.elim (markerColumn_ne_singleton η hη lam hlam htop n v.val h.symm)
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext ((singleton_eq_iff _ _ _).mp h))

abbrev Birth := Σ n, BirthData η hη lam hlam lower n

def encodeBirth (b : Birth η hη lam hlam lower) : ℕ × Ambient η hη :=
  (b.1,encodeNew η hη lam hlam lower b.1 b.2)

theorem encodeBirth_injective (htop : lam ≤ Frame.top η) :
    Function.Injective (encodeBirth η hη lam hlam lower) := by
  rintro ⟨n,c⟩ ⟨m,d⟩ h
  have hnm : n = m := congrArg Prod.fst h
  subst m
  have hcd := encodeNew_injective η hη lam hlam lower htop n (congrArg Prod.snd h)
  exact congrArg (Sigma.mk n) hcd

end Births
end FSCofinality.RawObjects
