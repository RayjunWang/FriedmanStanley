import FSCofinalityProof.GraphEncodingMarkers

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.GraphCoding

variable {V : Type}

theorem MarkerIsomorphism.is_core_iff {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e)
    (x : MarkerVertex V) : (∃ v, x = .core v) ↔ ∃ v, e x = .core v := by
  rw [← infinite_neighbors_iff_core E c x,← infinite_neighbors_iff_core F d (e x)]
  exact h.infinite_neighbors x

theorem MarkerIsomorphism.ring_image_not_core {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e)
    (v : V) (i : ℕ) (w : V) : e (.ring v i) ≠ .core w := by
  intro he
  obtain ⟨u,hu⟩ := (h.is_core_iff (.ring v i)).mpr ⟨w,he⟩
  cases hu

theorem leaf_adj_iff_core (E : V → V → Prop) (c : V → ℕ)
    (v : V) (n : ℕ) (x : MarkerVertex V) :
    MarkerAdj E c (.leaf v n) x ↔ x = .core v := by
  cases x <;> simp [MarkerAdj,eq_comm]

theorem ring_adj_noncore (E : V → V → Prop) (c : V → ℕ)
    (v : V) (i : ℕ) (x : MarkerVertex V)
    (h : MarkerAdj E c (.ring v i) x) (hn : ∀ w, x ≠ .core w) :
    ∃ j, j < c v+3 ∧ x = .ring v j := by
  cases x with
  | core w => exact False.elim (hn w rfl)
  | leaf w n => exact False.elim h
  | ring w j =>
    obtain ⟨rfl,_,hj,_⟩ := h
    exact ⟨j,hj,rfl⟩

theorem MarkerIsomorphism.ring_zero_image {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    e (.ring v 0) = .ring (h.coreEquiv v) 0 := by
  have hb : MarkerAdj F d (e (.ring v 0)) (.core (h.coreEquiv v)) := by
    rw [← h.coreEquiv_spec v]
    exact (h _ _).mp ⟨rfl,rfl⟩
  cases he : e (.ring v 0) with
  | core w => exact False.elim (h.ring_image_not_core v 0 w he)
  | leaf w n =>
    have he01 : MarkerAdj E c (.ring v 0) (.ring v 1) :=
      ⟨rfl,by omega,by omega,Or.inl rfl⟩
    have hi := (h _ _).mp he01
    rw [he] at hi
    have hc := (leaf_adj_iff_core F d w n _).mp hi
    exact False.elim (h.ring_image_not_core v 1 w hc)
  | ring w i =>
    rw [he] at hb
    obtain ⟨rfl,rfl⟩ := hb
    rfl

theorem MarkerIsomorphism.ring_image_exists {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    ∀ i, i < c v+3 → ∃ j, j < d (h.coreEquiv v)+3 ∧
      e (.ring v i) = .ring (h.coreEquiv v) j := by
  intro i
  induction i with
  | zero =>
    intro hi
    exact ⟨0,by omega,h.ring_zero_image v⟩
  | succ i ih =>
    intro hi
    obtain ⟨j,hj,he⟩ := ih (by omega)
    have hs : MarkerAdj E c (.ring v i) (.ring v (i+1)) :=
      ⟨rfl,by omega,hi,Or.inl rfl⟩
    have ht := (h _ _).mp hs
    rw [he] at ht
    exact ring_adj_noncore F d _ j _ ht (h.ring_image_not_core v (i+1))

theorem MarkerIsomorphism.ring_size_le {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    c v+3 ≤ d (h.coreEquiv v)+3 := by
  let f : Fin (c v+3) → Fin (d (h.coreEquiv v)+3) := fun i =>
    ⟨Classical.choose (h.ring_image_exists v i i.isLt),
      (Classical.choose_spec (h.ring_image_exists v i i.isLt)).1⟩
  have hf (i : Fin (c v+3)) : e (.ring v i) = .ring (h.coreEquiv v) (f i) :=
    (Classical.choose_spec (h.ring_image_exists v i i.isLt)).2
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have heq : e (.ring v i) = e (.ring v j) := by rw [hf i,hf j,hij]
    exact (MarkerVertex.ring.inj (e.injective heq)).2
  simpa using Fintype.card_le_of_injective f hinj

theorem MarkerIsomorphism.symm_coreEquiv_apply {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    h.symm.coreEquiv (h.coreEquiv v) = v := by
  have hh := h.symm.coreEquiv_spec (h.coreEquiv v)
  rw [← h.coreEquiv_spec v,Equiv.symm_apply_apply] at hh
  exact MarkerVertex.core.inj hh.symm

theorem MarkerIsomorphism.color_preserved {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    c v = d (h.coreEquiv v) := by
  have hle := h.ring_size_le v
  have hge := h.symm.ring_size_le (h.coreEquiv v)
  rw [h.symm_coreEquiv_apply] at hge
  omega

theorem MarkerIsomorphism.core_adj_preserved {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v w : V) :
    E v w ↔ F (h.coreEquiv v) (h.coreEquiv w) := by
  have hh := h (.core v) (.core w)
  rw [h.coreEquiv_spec,h.coreEquiv_spec] at hh
  exact hh

def liftCoreEquiv (f : V ≃ V) : MarkerVertex V ≃ MarkerVertex V where
  toFun
    | .core v => .core (f v)
    | .leaf v n => .leaf (f v) n
    | .ring v n => .ring (f v) n
  invFun
    | .core v => .core (f.symm v)
    | .leaf v n => .leaf (f.symm v) n
    | .ring v n => .ring (f.symm v) n
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro x; cases x <;> simp

theorem liftCoreEquiv_isomorphism {E F : V → V → Prop} {c d : V → ℕ}
    (f : V ≃ V) (hc : ∀ v, c v = d (f v))
    (hE : ∀ v w, E v w ↔ F (f v) (f w)) :
    MarkerIsomorphism E F c d (liftCoreEquiv f) := by
  intro x y
  cases x with
  | core v =>
    cases y with
    | core w => exact hE v w
    | leaf w n => exact f.injective.eq_iff.symm
    | ring w i => exact and_congr f.injective.eq_iff.symm Iff.rfl
  | leaf v n =>
    cases y with
    | core w => exact f.injective.eq_iff.symm
    | leaf w m => exact Iff.rfl
    | ring w i => exact Iff.rfl
  | ring v i =>
    cases y with
    | core w => exact and_congr f.injective.eq_iff.symm Iff.rfl
    | leaf w n => exact Iff.rfl
    | ring w j =>
      change (v=w ∧ i<c v+3 ∧ j<c v+3 ∧ _) ↔
        (f v=f w ∧ i<d (f v)+3 ∧ j<d (f v)+3 ∧ _)
      rw [hc v]
      exact and_congr f.injective.eq_iff.symm Iff.rfl

/-- Finite marker rings preserve exactly the original colored-graph
isomorphism problem. This statement includes arbitrary underlying relations. -/
theorem marker_encoding_iff (E F : V → V → Prop) (c d : V → ℕ) :
    (∃ e : MarkerVertex V ≃ MarkerVertex V, MarkerIsomorphism E F c d e) ↔
      ∃ f : V ≃ V, (∀ v, c v = d (f v)) ∧
        ∀ v w, E v w ↔ F (f v) (f w) := by
  constructor
  · rintro ⟨e,h⟩
    exact ⟨h.coreEquiv,h.color_preserved,h.core_adj_preserved⟩
  · rintro ⟨f,hc,hE⟩
    exact ⟨liftCoreEquiv f,liftCoreEquiv_isomorphism f hc hE⟩

end FSCofinality.GraphCoding
