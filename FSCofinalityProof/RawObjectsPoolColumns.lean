import FSCofinalityProof.RawObjectsPoolValidity
import FSCofinalityProof.RawObjectsColumnEncoding

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem pool_Enc (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    {t b u : Ambient η hη} (ht : t ∈ Pool η hη seeds a)
    (hb : b ∈ Pool η hη seeds a) (hu : u ∈ Pool η hη seeds a) :
    Enc (level η (a+1)) (level η (a+2)) t b u ∈ Pool η hη seeds (a+2) ∧
      ∀ c, Member c (Enc (level η (a+1)) (level η (a+2)) t b u) →
        c ∈ Pool η hη seeds (a+1) := by
  have hs := pool_singleton η hη seeds a ht
  have hp := pool_doubleton η hη seeds a hb hu
  constructor
  · simpa only [add_assoc,one_add_one_eq_two] using
      pool_doubleton η hη seeds (a+1) hs hp
  · intro c hc
    rcases (Enc_member_iff _ _ _ _ _ _).mp hc with rfl | rfl
    · exact hs
    · exact hp

theorem pool_newColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) {c : Ambient η hη}
    (hc : NewColumn η hη lam hlam (fun b _ => Pool η hη seeds b) n c) :
    c ∈ Pool η hη seeds (Frame.delta η lam hlam n) ∧
      ∀ u, Member u c → u ∈ Pool η hη seeds (Frame.rho η lam hlam n) := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  have ht (m : ℕ) := pool_tag η hη seeds (Frame.sigma η lam hlam n) hs m
  rcases hc with ⟨v,hv,rfl⟩ | rfl | ⟨v,hv,rfl⟩
  · have hd := pool_lift η hη seeds (Frame.q η lam hlam n) (Frame.sigma η lam hlam n)
      (Frame.q_le_sigma η lam hlam n) hs hv
    exact pool_Enc η hη seeds (Frame.sigma η lam hlam n) (ht 1) (ht 3) hd
  · exact pool_Enc η hη seeds (Frame.sigma η lam hlam n) (ht 2) (ht 3) (ht 3)
  · constructor
    · simpa only [Frame.rho,Frame.delta,add_assoc,one_add_one_eq_two] using
        pool_singleton η hη seeds (Frame.rho η lam hlam n) hv
    · intro u hu
      exact ((member_singleton _ _ _).mp hu).symm ▸ hv

theorem pool_oldColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) {c : Ambient η hη} (hc : c ∈ Pool η hη seeds (Frame.delta η lam hlam n)) :
    oldColumn η hη lam hlam n c ∈ Pool η hη seeds (Frame.delta η lam hlam (n+1)) ∧
      ∀ u, Member u (oldColumn η hη lam hlam n c) →
        u ∈ Pool η hη seeds (Frame.rho η lam hlam (n+1)) := by
  have hs := (Frame.sigma_lt η lam hlam (n+1)).le.trans htop
  have ht (m : ℕ) := pool_tag η hη seeds (Frame.sigma η lam hlam (n+1)) hs m
  have hd := pool_lift η hη seeds (Frame.delta η lam hlam n) (Frame.sigma η lam hlam (n+1))
    (Frame.delta_le_sigma_next η lam hlam n) hs hc
  exact pool_Enc η hη seeds (Frame.sigma η lam hlam (n+1)) (ht 0) (ht 3) hd

/-- Every actual dedicated column belongs to its correct main pool and all
members of its set payload belong to the correct lower main pool. -/
theorem pool_encodeColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (c : Column η hη lam hlam (fun b _ => Pool η hη seeds b) n) :
    encodeColumn η hη lam hlam (fun b _ => Pool η hη seeds b) n c ∈
        Pool η hη seeds (Frame.delta η lam hlam n) ∧
      ∀ u, Member u (encodeColumn η hη lam hlam (fun b _ => Pool η hη seeds b) n c) →
        u ∈ Pool η hη seeds (Frame.rho η lam hlam n) := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,d⟩,hk⟩
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact pool_newColumn η hη seeds lam hlam htop 0
      (encodeNew_mem η hη lam hlam _ 0 d)
  | succ n ih =>
    rcases column_succ_cases η hη lam hlam (fun b _ => Pool η hη seeds b) n c with ⟨d,rfl⟩ | ⟨d,rfl⟩
    · rw [encodeColumn_fresh]
      exact pool_newColumn η hη seeds lam hlam htop (n+1)
        (encodeNew_mem η hη lam hlam _ (n+1) d)
    · rw [encodeColumn_propagate]
      exact pool_oldColumn η hη seeds lam hlam htop n (ih d).1

theorem pool_columnSet_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (hseeds : ∀ a, (seeds a).Countable)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η) (n : ℕ) :
    (ColumnSet η hη lam hlam (fun b _ => Pool η hη seeds b) n).Countable := by
  apply (pool_countable η hη seeds hseeds (Frame.delta η lam hlam n)).mono
  rintro c ⟨d,rfl⟩
  exact (pool_encodeColumn η hη seeds lam hlam htop n d).1

end FSCofinality.RawObjects
