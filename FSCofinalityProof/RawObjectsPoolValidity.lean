import FSCofinalityProof.RawObjectsProfiles

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem valid_finiteCollection (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (A : Finset (Ambient η hη))
    (hA : ∀ u ∈ A, u ∈ Valid η hη a) :
    finiteCollection (level η (a+1)) A ∈ Valid η hη (a+1) := by
  obtain ⟨x,hx⟩ := finiteCollection_is_collection (level η (a+1)) A
  rw [valid_add_one]
  refine ⟨x,hx,?_⟩
  intro f hf i
  have hm : Member (f i) (finiteCollection (level η (a+1)) A) := by
    rw [hx,hf]
    exact (member_collection_some _ _ _).mpr ⟨i,rfl⟩
  exact hA (f i) ((member_finiteCollection _ _ _).mp hm)

theorem newColumn_mono (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}
    (h : ∀ b hb, lower b hb ⊆ upper b hb) (n : ℕ) {c : Ambient η hη}
    (hc : NewColumn η hη lam hlam lower n c) : NewColumn η hη lam hlam upper n c := by
  rcases hc with ⟨v,hv,rfl⟩ | rfl | ⟨v,hv,rfl⟩
  · exact Or.inl ⟨v,h _ _ hv,rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨v,h _ _ hv,rfl⟩)

theorem limitSet_mono (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}
    (h : ∀ b hb, lower b hb ⊆ upper b hb) :
    LimitSet η hη lam hlam lower ⊆ LimitSet η hη lam hlam upper := by
  intro x hx
  rcases hx with ⟨s,rfl,hs⟩ | ⟨A,rfl,hA⟩
  · exact Or.inl ⟨s,rfl,fun n => h _ _ (hs n)⟩
  · exact Or.inr ⟨A,rfl,fun p hp => newColumn_mono η hη lam hlam h p.1 (hA p hp)⟩

theorem pool_subset_valid (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (hseeds : ∀ a, seeds a ⊆ Valid η hη a) (a : Ordinal.{0}) :
    Pool η hη seeds a ⊆ Valid η hη a := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    rw [pool_zero,valid_zero]
    exact union_subset (by simpa only [valid_zero] using hseeds 0) subset_union_right
  | add_one a ih =>
    rw [pool_add_one]
    intro x hx
    rcases hx with hs | hx
    · exact hseeds (a+1) hs
    · obtain ⟨A,hA,rfl⟩ := (mem_finiteImages_iff _ _ _).mp hx
      exact valid_finiteCollection η hη a A (fun u hu => ih (hA u hu))
  | limit a ha ih =>
    rw [pool_limit η hη seeds a ha]
    intro x hx
    rcases hx with hs | hx
    · exact hseeds a hs
    · obtain ⟨A,hA,rfl⟩ := (mem_finiteImages_iff _ _ _).mp hx
      rw [valid_limit η hη a ha]
      exact Or.inr ⟨A,rfl,fun p hp => newColumn_mono η hη a ha ih p.1 (hA p hp)⟩

def fullLower (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (lam : Ordinal.{0}) :
    ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη) := fun b _ => Valid η hη b

def ambientRow (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (x : Ambient η hη) (hx : x ∈ Valid η hη lam) :
    LimitRow η hη lam hlam (fullLower η hη lam) :=
  (exists_rowObject_of_mem_limitSet η hη lam hlam (fullLower η hη lam) htop (x := x)
    (by
      change x ∈ LimitSet η hη lam hlam (fun b _ => Valid η hη b)
      rwa [← valid_limit η hη lam hlam])).choose

theorem rowObject_ambientRow (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (x : Ambient η hη) (hx : x ∈ Valid η hη lam) :
    rowObject η hη lam hlam (fullLower η hη lam) htop (ambientRow η hη lam hlam htop x hx) = x :=
  (exists_rowObject_of_mem_limitSet η hη lam hlam (fullLower η hη lam) htop (x := x)
    (by
      change x ∈ LimitSet η hη lam hlam (fun b _ => Valid η hη b)
      rwa [← valid_limit η hη lam hlam])).choose_spec

def ambientProfile (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (x : Ambient η hη) (c : Column η hη lam hlam (fullLower η hη lam) n) : Bool :=
  if hx : x ∈ Valid η hη lam then
    profile η hη lam hlam (fullLower η hη lam) n (ambientRow η hη lam hlam htop x hx) c
  else false

theorem ambientProfile_propagate (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (x : Ambient η hη) (c : Column η hη lam hlam (fullLower η hη lam) n) :
    ambientProfile η hη lam hlam htop (n+1) x (propagate η hη lam hlam (fullLower η hη lam) n c) =
      ambientProfile η hη lam hlam htop n x c := by
  by_cases hx : x ∈ Valid η hη lam
  · simp only [ambientProfile,dif_pos hx,profile_propagate]
  · simp only [ambientProfile,dif_neg hx]

theorem ambientFullProfile_injOn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η) :
    InjOn (fun x : Ambient η hη => fun n => ambientProfile η hη lam hlam htop n x)
      (Valid η hη lam) := by
  intro x hx y hy h
  have hp : (fun n => profile η hη lam hlam (fullLower η hη lam) n
      (ambientRow η hη lam hlam htop x hx)) =
      (fun n => profile η hη lam hlam (fullLower η hη lam) n
      (ambientRow η hη lam hlam htop y hy)) := by
    funext n c
    have hquery := congrFun (congrFun h n) c
    simpa only [ambientProfile,dif_pos hx,dif_pos hy] using hquery
  have hr := fullProfile_injective η hη lam hlam (fullLower η hη lam) hp
  exact (rowObject_ambientRow η hη lam hlam htop x hx).symm.trans
    ((congrArg (rowObject η hη lam hlam (fullLower η hη lam) htop) hr).trans
      (rowObject_ambientRow η hη lam hlam htop y hy))

end FSCofinality.RawObjects
