import FSCofinalityProof.TokenLiteralMaps
import FSCofinalityProof.CosetConstructionTokenModelProperties

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.Tokens

/-- Repeated rows cause no problem if their prescribed bits agree. -/
theorem bottomListMap_consistent_finite_independence {U I : Type}
    [MeasurableSpace U] [StandardBorelSpace U] [Fintype I]
    (p : I → Token U) (epsilon : I → Bool)
    (hconsistent : ∀ i j, p i = p j → epsilon i = epsilon j) (N : ℕ) :
    ∃ q > N, ∀ i, bottomListMap (p i).1 (p i).2 q = epsilon i := by
  classical
  let S : Finset (Token U) := Finset.univ.image p
  have hpre (v : S) : ∃ i, p i = v.val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp v.property
    exact ⟨i,hi⟩
  let bit (v : S) : Bool := epsilon (hpre v).choose
  obtain ⟨q,hq,hbits⟩ := bottomListMap_finite_independence
    (fun v : S => v.val) Subtype.val_injective bit N
  refine ⟨q,hq,fun i => ?_⟩
  let v : S := ⟨p i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩
  exact (hbits v).trans (hconsistent (hpre v).choose i (hpre v).choose_spec)

end FSCofinality.Tokens

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem decodedBottom_injective (x : (fsTower eta).Carrier) :
    Function.Injective (decodedBottom eta heta x) := by
  intro v w h
  apply tokenName_injective eta heta x (zeroSort eta)
  exact (decodedBottom_reencode eta heta x v).symm.trans
    ((congrArg (mapToken (atomObject eta heta)) h).trans (decodedBottom_reencode eta heta x w))

theorem bottom_finite_independence (x : (fsTower eta).Carrier) {I : Type} [Fintype I]
    (v : I → Token (raw eta heta x (zeroSort eta))) (epsilon : I → Bool)
    (hconsistent : ∀ i j, v i = v j → epsilon i = epsilon j) (N : ℕ) :
    ∃ q > N, ∀ i, bottom eta heta x (v i) q = epsilon i := by
  exact bottomListMap_consistent_finite_independence
    (fun i => decodedBottom eta heta x (v i)) epsilon
    (fun i j hij => hconsistent i j (decodedBottom_injective eta heta x hij)) N

theorem tokenAt_eq_some_iff {x : (fsTower eta).Carrier} (s : TokenSort eta)
    (u : Vertex eta heta x) (v : Token (raw eta heta x s)) :
    tokenAt eta heta s u = some v ↔ u = .inr ⟨s,v⟩ := by
  cases u with
  | inl n => simp [tokenAt]
  | inr w =>
    rcases w with ⟨t,w⟩
    by_cases ht : t=s
    · subst t
      rw [tokenAt_inr]
      simp only [Option.some.injEq]
      constructor
      · intro h
        subst w
        rfl
      · intro h
        exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
    · constructor
      · intro h
        simp [tokenAt,ht] at h
      · intro h
        exact False.elim (ht (congrArg Sigma.fst (Sum.inr.inj h)))

theorem LiteralCompatible.sort_eq {x y : (fsTower eta).Carrier}
    {R : Set (Vertex eta heta x × Vertex eta heta y)}
    (hR : LiteralCompatible eta heta (bottom eta heta) x y R) (p) (hp : p ∈ R) :
    sortOf eta heta p.1 = sortOf eta heta p.2 := by
  have hh := hR.2 (.inl (sortOf eta heta p.1)) (fun _ => p) (fun _ => hp)
  change decide (sortOf eta heta p.1 = sortOf eta heta p.1) =
    decide (sortOf eta heta p.2 = sortOf eta heta p.1) at hh
  exact (of_decide_eq_true (hh.symm.trans (decide_eq_true rfl))).symm

theorem tokenAt_none_iff_sort {x : (fsTower eta).Carrier} (s : TokenSort eta)
    (u : Vertex eta heta x) :
    tokenAt eta heta s u = none ↔ sortOf eta heta u ≠ some s := by
  cases u with
  | inl n => simp [tokenAt,sortOf]
  | inr u =>
    rcases u with ⟨t,u⟩
    by_cases ht : t=s
    · subst t
      rw [tokenAt_inr]
      simp [sortOf]
    · simp [tokenAt,sortOf,ht]

def bottomAt (x : (fsTower eta).Carrier) (u : Vertex eta heta x) (n : ℕ) : Bool :=
  (tokenAt eta heta (zeroSort eta) u).elim false (fun v => bottom eta heta x v n)

theorem edgeAt_coordinate_right {x : (fsTower eta).Carrier} (s t : TokenSort eta)
    (f : Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (u : Vertex eta heta x) (n : ℕ) : edgeAt eta heta s t f u (.inl n) = false := by
  unfold edgeAt
  rw [tokenAt_inl]
  cases tokenAt eta heta s u <;> rfl

theorem diagram_coordinate_left (x : (fsTower eta).Carrier)
    (s : OrdinaryRole eta ⊕ (ColumnIndex eta ⊕ (ColumnIndex eta ⊕ Unit)))
    (n : ℕ) (u : Vertex eta heta x) :
    diagram eta heta (bottom eta heta) x (.inr s) (twoTuple (.inl n) u) = false := by
  rcases s with s | (s | (s | s)) <;> rfl

theorem coordinate_insert_compatible {x y : (fsTower eta).Carrier}
    {R : Set (Vertex eta heta x × Vertex eta heta y)}
    (hR : LiteralCompatible eta heta (bottom eta heta) x y R) (n m : ℕ)
    (hfresh : ∀ p ∈ R, (.inl n : Vertex eta heta x) ≠ p.1)
    (hfresh' : ∀ p ∈ R, (.inl m : Vertex eta heta y) ≠ p.2)
    (hbits : ∀ p ∈ R, bottomAt eta heta x p.1 n = bottomAt eta heta y p.2 m) :
    LiteralCompatible eta heta (bottom eta heta) x y (insert (.inl n,.inl m) R) := by
  apply CompatibleOn.insert_of_unary_binary hR
    (fun s => by cases s <;> simp [language,arity]) (.inl n) (.inl m)
  · intro p hp
    exact iff_of_false (hfresh p hp) (hfresh' p hp)
  · intro s hs
    cases s with
    | inl s => rfl
    | inr s => simp [language,arity] at hs
  · intro s hs
    cases s with
    | inl s => simp [language,arity] at hs
    | inr s =>
      rcases s with s | (s | (s | s)) <;> rfl
  · intro s hs p hp
    cases s with
    | inl s => simp [language,arity] at hs
    | inr s =>
      exact (diagram_coordinate_left eta heta x s n p.1).trans
        (diagram_coordinate_left eta heta y s m p.2).symm
  · intro s hs p hp
    cases s with
    | inl s => simp [language,arity] at hs
    | inr s =>
      rcases s with s | (s | (s | s))
      · change edgeAt eta heta _ _ _ p.1 (.inl n) = edgeAt eta heta _ _ _ p.2 (.inl m)
        rw [edgeAt_coordinate_right,edgeAt_coordinate_right]
      · change edgeAt eta heta _ _ _ p.1 (.inl n) = edgeAt eta heta _ _ _ p.2 (.inl m)
        rw [edgeAt_coordinate_right,edgeAt_coordinate_right]
      · change edgeAt eta heta _ _ _ p.1 (.inl n) = edgeAt eta heta _ _ _ p.2 (.inl m)
        rw [edgeAt_coordinate_right,edgeAt_coordinate_right]
      · exact hbits p hp

/-- Actual one-point extension in the coordinate sort. Every incidence
requirement is supplied by finite independence of the bottom decoder. -/
theorem coordinate_extension {x y : (fsTower eta).Carrier}
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (n : ℕ) (hfresh : ∀ p ∈ R, (.inl n : Vertex eta heta x) ≠ p.1) :
    ∃ m : ℕ, LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inl n,.inl m)]} := by
  let I := {i : Fin R.length // ∃ v : Token (raw eta heta y (zeroSort eta)),
    tokenAt eta heta (zeroSort eta) (R.get i).2 = some v}
  let old (i : I) : Token (raw eta heta y (zeroSort eta)) := i.property.choose
  have hold (i : I) : tokenAt eta heta (zeroSort eta) (R.get i.val).2 = some (old i) :=
    i.property.choose_spec
  let epsilon (i : I) : Bool := bottomAt eta heta x (R.get i.val).1 n
  have hconsistent (i j : I) (hij : old i = old j) : epsilon i = epsilon j := by
    have hi := (tokenAt_eq_some_iff eta heta _ _ _).mp (hold i)
    have hj := (tokenAt_eq_some_iff eta heta _ _ _).mp (hold j)
    have htarget : (R.get i.val).2 = (R.get j.val).2 := by rw [hi,hj,hij]
    have hsource := (hR.1 _ (List.get_mem _ i.val) _ (List.get_mem _ j.val)).mpr htarget
    exact congrArg (fun u => bottomAt eta heta x u n) hsource
  let B := Finset.univ.sup (fun i : Fin R.length =>
    (coordinateAt eta heta (R.get i).2).getD 0)
  obtain ⟨m,hm,hbits⟩ := bottom_finite_independence eta heta y old epsilon hconsistent B
  have hfresh' (p) (hp : p ∈ R) : (.inl m : Vertex eta heta y) ≠ p.2 := by
    intro heq
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
    have hi : (coordinateAt eta heta (R.get i).2).getD 0 ≤ B :=
      Finset.le_sup (f := fun i : Fin R.length =>
        (coordinateAt eta heta (R.get i).2).getD 0) (Finset.mem_univ i)
    rw [← heq] at hi
    change m ≤ B at hi
    omega
  have hmatch (p) (hp : p ∈ R) : bottomAt eta heta x p.1 n = bottomAt eta heta y p.2 m := by
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
    cases ht : tokenAt eta heta (zeroSort eta) (R.get i).2 with
    | none =>
      have hs := hR.sort_eq eta heta (R.get i) (List.get_mem _ i)
      have hn := (tokenAt_none_iff_sort eta heta (zeroSort eta) (R.get i).2).mp ht
      have hz : tokenAt eta heta (zeroSort eta) (R.get i).1 = none :=
        (tokenAt_none_iff_sort eta heta _ _).mpr (hs ▸ hn)
      simp only [bottomAt,hz,ht,Option.elim_none]
    | some v =>
      let j : I := ⟨i,⟨v,ht⟩⟩
      have hv : old j = v := Option.some.inj ((hold j).symm.trans ht)
      have hh := hbits j
      rw [hv] at hh
      change bottomAt eta heta x (R.get i).1 n =
        (tokenAt eta heta (zeroSort eta) (R.get i).2).elim false
          (fun w => bottom eta heta y w m)
      rw [ht]
      exact hh.symm
  refine ⟨m,?_⟩
  have hinsert := coordinate_insert_compatible eta heta hR n m hfresh hfresh' hmatch
  apply hinsert.mono
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact Or.inr hp
  · exact Or.inl (List.mem_singleton.mp hp)

end FSCofinality.CosetConstruction.TokenModel
