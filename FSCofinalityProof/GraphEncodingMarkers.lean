import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Denumerable
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.GraphCoding

/-- Core vertices receive countably many leaves and one finite marker ring.
Unused ring positions are isolated, so the carrier is independent of colors. -/
inductive MarkerVertex (V : Type) where
  | core : V → MarkerVertex V
  | leaf : V → ℕ → MarkerVertex V
  | ring : V → ℕ → MarkerVertex V

variable {V : Type}

def vertexCode : MarkerVertex V → V ⊕ ((V × ℕ) ⊕ (V × ℕ))
  | .core v => .inl v
  | .leaf v n => .inr (.inl (v,n))
  | .ring v n => .inr (.inr (v,n))

theorem vertexCode_injective : Function.Injective (vertexCode (V := V)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [vertexCode]

instance [Countable V] : Countable (MarkerVertex V) :=
  vertexCode_injective.countable

instance [Infinite V] : Infinite (MarkerVertex V) :=
  Infinite.of_injective MarkerVertex.core (fun _ _ h => MarkerVertex.core.inj h)

def MarkerAdj (E : V → V → Prop) (c : V → ℕ) : MarkerVertex V → MarkerVertex V → Prop
  | .core v,.core w => E v w
  | .core v,.leaf w _ => v = w
  | .leaf v _,.core w => v = w
  | .core v,.ring w i => v = w ∧ i = 0
  | .ring v i,.core w => v = w ∧ i = 0
  | .ring v i,.ring w j => v = w ∧ i < c v + 3 ∧ j < c v + 3 ∧
      (i+1=j ∨ j+1=i ∨ (i=0 ∧ j+1=c v+3) ∨ (j=0 ∧ i+1=c v+3))
  | _,_ => False

theorem markerAdj_symm (E : V → V → Prop) (c : V → ℕ)
    (hE : Symmetric E) : Symmetric (MarkerAdj E c) := by
  intro x y h
  cases x with
  | core v =>
    cases y with
    | core w => exact hE h
    | leaf w n => exact h.symm
    | ring w i => exact ⟨h.1.symm,h.2⟩
  | leaf v n =>
    cases y with
    | core w => exact h.symm
    | leaf w m => exact h
    | ring w i => exact h
  | ring v i =>
    cases y with
    | core w => exact ⟨h.1.symm,h.2⟩
    | leaf w n => exact h
    | ring w j =>
      obtain ⟨rfl,hi,hj,hrel⟩ := h
      exact ⟨rfl,hj,hi,by omega⟩

theorem markerAdj_irrefl (E : V → V → Prop) (c : V → ℕ)
    (hE : Irreflexive E) : Irreflexive (MarkerAdj E c) := by
  intro x h
  cases x with
  | core v => exact hE v h
  | leaf v n => exact h
  | ring v i => simp only [MarkerAdj] at h; omega

theorem core_neighbors_infinite (E : V → V → Prop) (c : V → ℕ) (v : V) :
    {w | MarkerAdj E c (.core v) w}.Infinite := by
  have hi : Function.Injective (fun n : ℕ => MarkerVertex.leaf v n) := by
    intro m n h
    exact (MarkerVertex.leaf.inj h).2
  apply (Set.infinite_range_of_injective hi).mono
  rintro w ⟨n,rfl⟩
  exact rfl

theorem leaf_neighbors_finite (E : V → V → Prop) (c : V → ℕ) (v : V) (n : ℕ) :
    {w | MarkerAdj E c (.leaf v n) w}.Finite := by
  apply (Set.finite_singleton (.core v : MarkerVertex V)).subset
  intro w hw
  cases w <;> simp_all [MarkerAdj]

theorem ring_neighbors_finite (E : V → V → Prop) (c : V → ℕ) (v : V) (i : ℕ) :
    {w | MarkerAdj E c (.ring v i) w}.Finite := by
  have hf : ({MarkerVertex.core v} ∪
      (MarkerVertex.ring v '' {j : ℕ | j < c v+3})).Finite :=
    (Set.finite_singleton _).union ((Set.finite_Iio _).image _)
  apply hf.subset
  intro w hw
  cases w with
  | core u =>
    change v = u ∧ i = 0 at hw
    obtain ⟨rfl,_⟩ := hw
    exact Or.inl rfl
  | leaf u n => exact False.elim hw
  | ring u j =>
    obtain ⟨rfl,_,hj,_⟩ := hw
    exact Or.inr ⟨j,hj,rfl⟩

theorem infinite_neighbors_iff_core (E : V → V → Prop) (c : V → ℕ)
    (w : MarkerVertex V) : {u | MarkerAdj E c w u}.Infinite ↔ ∃ v, w = .core v := by
  cases w with
  | core v => exact ⟨fun _ => ⟨v,rfl⟩,fun _ => core_neighbors_infinite E c v⟩
  | leaf v n => simpa using (leaf_neighbors_finite E c v n).not_infinite
  | ring v i => simpa using (ring_neighbors_finite E c v i).not_infinite

def MarkerIsomorphism (E F : V → V → Prop) (c d : V → ℕ)
    (e : MarkerVertex V ≃ MarkerVertex V) : Prop :=
  ∀ x y, MarkerAdj E c x y ↔ MarkerAdj F d (e x) (e y)

theorem MarkerIsomorphism.symm {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) :
    MarkerIsomorphism F E d c e.symm := by
  intro x y
  simpa only [Equiv.apply_symm_apply] using (h (e.symm x) (e.symm y)).symm

theorem MarkerIsomorphism.infinite_neighbors {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e)
    (v : MarkerVertex V) :
    {u | MarkerAdj E c v u}.Infinite ↔ {u | MarkerAdj F d (e v) u}.Infinite := by
  have heq : {u | MarkerAdj F d (e v) u} = e '' {u | MarkerAdj E c v u} := by
    ext u
    constructor
    · intro hu
      exact ⟨e.symm u,(h v (e.symm u)).mpr (by simpa using hu),by simp⟩
    · rintro ⟨w,hw,rfl⟩
      exact (h v w).mp hw
  rw [heq]
  exact (Set.infinite_image_iff e.injective.injOn).symm

theorem MarkerIsomorphism.core_image {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e)
    (v : V) : ∃ w : V, e (.core v) = .core w :=
  (infinite_neighbors_iff_core F d _).mp
    ((h.infinite_neighbors _).mp (core_neighbors_infinite E c v))

def MarkerIsomorphism.coreMap {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) : V :=
  Classical.choose (h.core_image v)

theorem MarkerIsomorphism.coreMap_spec {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    e (.core v) = .core (h.coreMap v) := Classical.choose_spec (h.core_image v)

theorem MarkerIsomorphism.coreMap_bijective {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) :
    Function.Bijective h.coreMap := by
  constructor
  · intro v w hvw
    have : e (.core v) = e (.core w) := by rw [h.coreMap_spec,h.coreMap_spec,hvw]
    exact MarkerVertex.core.inj (e.injective this)
  · intro w
    refine ⟨h.symm.coreMap w,?_⟩
    have he : e (.core (h.symm.coreMap w)) = .core w := by
      rw [← h.symm.coreMap_spec]
      simp
    exact MarkerVertex.core.inj ((h.coreMap_spec _).symm.trans he)

def MarkerIsomorphism.coreEquiv {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) : V ≃ V :=
  Equiv.ofBijective h.coreMap h.coreMap_bijective

theorem MarkerIsomorphism.coreEquiv_spec {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    e (.core v) = .core (h.coreEquiv v) := h.coreMap_spec v

end FSCofinality.GraphCoding
