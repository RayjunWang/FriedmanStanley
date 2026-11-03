import FSCofinalityProof.RawObjectsPools
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Set.Countable

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

/-- Images of every finite subset of a specified pool. -/
def finiteImages {α β : Type} (f : Finset α → β) (H : Set α) : Set β :=
  range (fun A : Finset H => f (A.map (Function.Embedding.subtype _)))

theorem mem_finiteImages_iff {α β : Type} (f : Finset α → β) (H : Set α) (x : β) :
    x ∈ finiteImages f H ↔ ∃ A : Finset α, (∀ u ∈ A, u ∈ H) ∧ f A = x := by
  classical
  constructor
  · rintro ⟨A,rfl⟩
    exact ⟨_,fun _ hu => Finset.property_of_mem_map_subtype A hu,rfl⟩
  · rintro ⟨A,hA,hx⟩
    refine ⟨A.subtype (· ∈ H),?_⟩
    simpa only [Finset.subtype_map_of_mem hA] using hx

theorem finiteImages_countable {α β : Type} (f : Finset α → β) {H : Set α}
    (hH : H.Countable) : (finiteImages f H).Countable := by
  letI : Countable H := hH.to_subtype
  exact countable_range _

theorem newColumn_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))
    (hcount : ∀ b hb, (lower b hb).Countable) (n : ℕ) :
    {c | NewColumn η hη lam hlam lower n c}.Countable := by
  have heq : {c | NewColumn η hη lam hlam lower n c} =
      dataColumn η hη lam hlam n '' lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n) ∪
      ({markerColumn η hη lam hlam n} ∪
        singleton (level η (Frame.delta η lam hlam n)) ''
          lower (Frame.rho η lam hlam n) (Frame.rho_lt η lam hlam n)) := by
    ext c
    simp only [NewColumn,mem_union,mem_image,mem_singleton_iff,mem_setOf_eq]
    aesop
  rw [heq]
  exact ((hcount _ _).image _).union ((countable_singleton _).union ((hcount _ _).image _))

theorem birthSet_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))
    (hcount : ∀ b hb, (lower b hb).Countable) :
    {p : ℕ × Ambient η hη | NewColumn η hη lam hlam lower p.1 p.2}.Countable := by
  have heq : {p : ℕ × Ambient η hη | NewColumn η hη lam hlam lower p.1 p.2} =
      ⋃ n, Prod.mk n '' {c | NewColumn η hη lam hlam lower n c} := by
    ext ⟨n,c⟩
    simp
  rw [heq]
  exact countable_iUnion (fun n => (newColumn_countable η hη lam hlam lower hcount n).image _)

/-- The source-seeded pools from the manuscript. The top source seed, when
desired, is included explicitly in `seeds` at the top layer. -/
def Pool (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0}) : Set (Ambient η hη) :=
  Ordinal.limitRecOn a (seeds 0 ∪ range extraAtom)
    (fun b H => seeds (b+1) ∪ finiteImages (finiteCollection (level η (b+1))) H)
    (fun lam hlam lower => seeds lam ∪ finiteImages (finiteFiller (level η lam))
      {p : ℕ × Ambient η hη | NewColumn η hη lam hlam lower p.1 p.2})

@[simp] theorem pool_zero (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) :
    Pool η hη seeds 0 = seeds 0 ∪ range extraAtom := by
  unfold Pool
  rw [Ordinal.limitRecOn_zero]

theorem pool_add_one (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0}) :
    Pool η hη seeds (a+1) =
      seeds (a+1) ∪ finiteImages (finiteCollection (level η (a+1))) (Pool η hη seeds a) := by
  unfold Pool
  rw [Ordinal.limitRecOn_add_one]

theorem pool_limit (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    Pool η hη seeds lam = seeds lam ∪ finiteImages (finiteFiller (level η lam))
      {p : ℕ × Ambient η hη | NewColumn η hη lam hlam (fun b _ => Pool η hη seeds b) p.1 p.2} := by
  unfold Pool
  rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]

theorem pool_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (hseeds : ∀ a, (seeds a).Countable) (a : Ordinal.{0}) : (Pool η hη seeds a).Countable := by
  induction a using Ordinal.limitRecOn with
  | zero => rw [pool_zero]; exact (hseeds 0).union (countable_range _)
  | add_one a ih => rw [pool_add_one]; exact (hseeds (a+1)).union (finiteImages_countable _ ih)
  | limit a ha ih =>
    rw [pool_limit η hη seeds a ha]
    exact (hseeds a).union (finiteImages_countable _ (birthSet_countable η hη a ha _ ih))

theorem pool_finiteCollection (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    (A : Finset (Ambient η hη)) (hA : ∀ u ∈ A, u ∈ Pool η hη seeds a) :
    finiteCollection (level η (a+1)) A ∈ Pool η hη seeds (a+1) := by
  rw [pool_add_one]
  exact Or.inr ((mem_finiteImages_iff _ _ _).mpr ⟨A,hA,rfl⟩)

theorem pool_singleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    {u : Ambient η hη} (hu : u ∈ Pool η hη seeds a) :
    singleton (level η (a+1)) u ∈ Pool η hη seeds (a+1) := by
  simpa only [finiteCollection_singleton] using
    pool_finiteCollection η hη seeds a {u} (by intro v hv; simpa only [Finset.mem_singleton.mp hv] using hu)

theorem pool_doubleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    {u v : Ambient η hη} (hu : u ∈ Pool η hη seeds a) (hv : v ∈ Pool η hη seeds a) :
    doubleton (level η (a+1)) u v ∈ Pool η hη seeds (a+1) := by
  have hm := pool_finiteCollection η hη seeds a {u,v} (by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · exact h.symm ▸ hu
    · exact (Finset.mem_singleton.mp h).symm ▸ hv)
  simpa only [finiteCollection_doubleton] using hm

/-- Lift closure is built into the finite filler operations and needs no
closure assumption on the source seeds. -/
theorem pool_lift (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (b a : Ordinal.{0}) (hba : b ≤ a) (ha : a ≤ Frame.top η)
    {u : Ambient η hη} (hu : u ∈ Pool η hη seeds b) :
    lift η hη b a u ∈ Pool η hη seeds a := by
  induction a using Ordinal.limitRecOn generalizing b u with
  | zero =>
    have hb : b = 0 := le_antisymm hba zero_le
    subst b
    simpa only [lift_self] using hu
  | add_one a ih =>
    by_cases h : b = a+1
    · subst b
      simpa only [lift_self] using hu
    · have hba' : b ≤ a := lt_add_one_iff.mp (lt_of_le_of_ne hba h)
      have haa : a ≤ Frame.top η := (le_of_lt (lt_add_one a)).trans ha
      rw [lift_add_one,if_neg h]
      exact pool_singleton η hη seeds a (ih b hba' haa hu)
  | limit a haLim ih =>
    by_cases h : b = a
    · subst b
      simpa only [lift_self] using hu
    · have hblt : b < a := lt_of_le_of_ne hba h
      rw [lift_limit η hη a haLim ha b hblt,pool_limit η hη seeds a haLim]
      let n := liftIndex η hη a haLim ha b hblt
      have hlow : lift η hη b (Frame.rho η a haLim n) u ∈ Pool η hη seeds (Frame.rho η a haLim n) :=
        ih (Frame.rho η a haLim n) (Frame.rho_lt η a haLim n) b
          (liftIndex_spec η hη a haLim ha b hblt)
          ((Frame.rho_lt η a haLim n).le.trans ha) hu
      apply Or.inr
      apply (mem_finiteImages_iff _ _ _).mpr
      refine ⟨_,?_,rfl⟩
      intro p hp
      have hp' := Finset.mem_singleton.mp hp
      subst p
      exact Or.inr (Or.inr ⟨_,hlow,rfl⟩)

theorem pool_tag (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (a : Ordinal.{0}) (ha : a ≤ Frame.top η) (n : ℕ) : tag η hη a n ∈ Pool η hη seeds a := by
  apply pool_lift η hη seeds 0 a zero_le ha
  rw [pool_zero]
  exact Or.inr (mem_range_self n)

end FSCofinality.RawObjects
