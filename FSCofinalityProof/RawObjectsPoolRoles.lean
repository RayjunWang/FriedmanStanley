import FSCofinalityProof.RawObjectsPoolColumns

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem pool_infinite (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0}) :
    Infinite (Pool η hη seeds a) := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    let f (n : ℕ) : Pool η hη seeds 0 := ⟨extraAtom n,by rw [pool_zero]; exact Or.inr ⟨n,rfl⟩⟩
    exact Infinite.of_injective f (fun n m h => extraAtom_injective (congrArg Subtype.val h))
  | add_one a ih =>
    letI := ih
    let f (u : Pool η hη seeds a) : Pool η hη seeds (a+1) :=
      ⟨singleton (level η (a+1)) u.val,pool_singleton η hη seeds a u.property⟩
    apply Infinite.of_injective f
    intro u v h
    exact Subtype.ext ((singleton_eq_iff _ _ _).mp (congrArg Subtype.val h))
  | limit a ha ih =>
    let f (n : ℕ) : Pool η hη seeds a :=
      ⟨finiteFiller (level η a) {(n,markerColumn η hη a ha n)},by
        rw [pool_limit η hη seeds a ha]
        apply Or.inr
        apply (mem_finiteImages_iff _ _ _).mpr
        refine ⟨_,?_,rfl⟩
        intro p hp
        have hp' := Finset.mem_singleton.mp hp
        subst p
        exact Or.inr (Or.inl rfl)⟩
    apply Infinite.of_injective f
    intro n m h
    have hA := finiteFiller_injective (level η a) (congrArg Subtype.val h)
    exact congrArg Prod.fst (Finset.singleton_injective hA)

def ordinaryRaw {η : Ordinal.{0}} {hη : η < Ordinal.omega 1}
    (row col : Ambient η hη) : Bool := decide (Member col row)

theorem ordinary_role_injOn {η : Ordinal.{0}} {hη : η < Ordinal.omega 1}
    (l : Frame.Layer η) (P Q : Set (Ambient η hη))
    (hc : ∀ r ∈ P, ∃ x, r = collection l x)
    (hlower : ∀ r ∈ P, ∀ c, Member c r → c ∈ Q) :
    InjOn (fun r => fun c : Q => ordinaryRaw r c.val) P := by
  intro x hx y hy h
  obtain ⟨u,rfl⟩ := hc x hx
  obtain ⟨v,rfl⟩ := hc y hy
  apply collection_ext
  intro c
  by_cases hQ : c ∈ Q
  · have hquery := congrFun h (⟨c,hQ⟩ : Q)
    by_cases hcu : Member c (collection l u) <;> by_cases hcv : Member c (collection l v) <;>
      simp_all [ordinaryRaw]
  · have hcu : ¬ Member c (collection l u) := fun hm => hQ (hlower _ hx c hm)
    have hcv : ¬ Member c (collection l v) := fun hm => hQ (hlower _ hy c hm)
    simp only [hcu,hcv]

theorem pool_successor_collection (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (hseeds : ∀ a, seeds a ⊆ Valid η hη a) (a : Ordinal.{0})
    {x : Ambient η hη} (hx : x ∈ Pool η hη seeds (a+1)) :
    ∃ u, x = collection (level η (a+1)) u := by
  have ht := pool_subset_valid η hη seeds hseeds (a+1) hx
  rw [valid_add_one] at ht
  exact ⟨ht.choose,ht.choose_spec.1⟩

theorem pool_member_lower (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    (hseed : ∀ x ∈ seeds (a+1), ∀ c, Member c x → c ∈ Pool η hη seeds a)
    {x c : Ambient η hη} (hx : x ∈ Pool η hη seeds (a+1)) (hcx : Member c x) :
    c ∈ Pool η hη seeds a := by
  rw [pool_add_one] at hx
  rcases hx with hs | hx
  · exact hseed x hs c hcx
  · obtain ⟨A,hA,rfl⟩ := (mem_finiteImages_iff _ _ _).mp hx
    exact hA c ((member_finiteCollection _ _ _).mp hcx)

/-- The exact common-lower-pool injectivity used in between-pool token recovery. -/
theorem ordinary_pool_union_injOn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (X Y : Ordinal.{0} → Set (Ambient η hη))
    (hX : ∀ a, X a ⊆ Valid η hη a) (hY : ∀ a, Y a ⊆ Valid η hη a)
    (a : Ordinal.{0})
    (hdX : ∀ x ∈ X (a+1), ∀ c, Member c x → c ∈ Pool η hη X a)
    (hdY : ∀ x ∈ Y (a+1), ∀ c, Member c x → c ∈ Pool η hη Y a) :
    InjOn (fun r => fun c : (Pool η hη X a ∪ Pool η hη Y a : Set (Ambient η hη)) => ordinaryRaw r c.val)
      (Pool η hη X (a+1) ∪ Pool η hη Y (a+1)) := by
  apply ordinary_role_injOn (level η (a+1))
  · intro r hr
    rcases hr with hr | hr
    · exact pool_successor_collection η hη X hX a hr
    · exact pool_successor_collection η hη Y hY a hr
  · intro r hr c hcr
    rcases hr with hr | hr
    · exact Or.inl (pool_member_lower η hη X a hdX hr hcr)
    · exact Or.inr (pool_member_lower η hη Y a hdY hr hcr)

theorem ordinary_pool_column_separating (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0}) :
    Function.Injective (fun c : Pool η hη seeds a =>
      fun r : Pool η hη seeds (a+1) => ordinaryRaw r.val c.val) := by
  intro c d h
  let r : Pool η hη seeds (a+1) :=
    ⟨singleton (level η (a+1)) c.val,pool_singleton η hη seeds a c.property⟩
  have hquery := congrFun h r
  have heq : d.val = c.val := by
    by_contra hne
    simp only [ordinaryRaw,member_singleton] at hquery
    simp [r,hne] at hquery
  exact Subtype.ext heq.symm

end FSCofinality.RawObjects
