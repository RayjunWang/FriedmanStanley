import FSCofinalityProof.HierarchyEmbeddings
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality

/-- The actual disjoint union of countably many code spaces, retaining its index. -/
def countableSum (E : ℕ → CodedRelation) : CodedRelation where
  Carrier := Σ n, (E n).Carrier
  measurableSpace := inferInstance
  rel := fun x y => ∃ h : x.1 = y.1, (E y.1).rel (h ▸ x.2) y.2

theorem measurable_sigma_cases {X : ℕ → Type} [∀ n, MeasurableSpace (X n)]
    {Y : Type} [MeasurableSpace Y] (f : (Σ n, X n) → Y)
    (hf : ∀ n, Measurable (fun x => f ⟨n,x⟩)) : Measurable f := by
  intro s hs
  change @MeasurableSet _ (⨅ n, (inferInstance : MeasurableSpace (X n)).map (Sigma.mk n))
    (f ⁻¹' s)
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact hf n hs

def indexAtom (n : ℕ) : ℕ → Bool := fun k => decide (k = n)

theorem indexAtom_injective : Function.Injective indexAtom := by
  intro n m h
  have hk := congrFun h n
  simpa [indexAtom] using hk

/-- A single countable limit stage absorbs any countable disjoint sum of
relations already reducing to countable tower stages. The index is recorded
in coordinate zero; the input uses a separate cofinal coordinate. -/
theorem countableSum_reduces_fsTower (E : ℕ → CodedRelation)
    (b : ℕ → Ordinal.{0}) (hb : ∀ n, b n < Ordinal.omega 1)
    (hE : ∀ n, (E n).Reduces (fsTower (b n))) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ (countableSum E).Reduces (fsTower a) := by
  let s := ⨆ n, b n
  let a := s + Ordinal.omega0
  have hs : s < Ordinal.omega 1 := Ordinal.iSup_lt_omega_one hb
  have ha : a < Ordinal.omega 1 :=
    (Ordinal.isPrincipal_add_omega 1) hs Ordinal.omega0_lt_omega_one
  have halim : IsSuccLimit a := Ordinal.isSuccLimit_add s Ordinal.isSuccLimit_omega0
  have hba (n : ℕ) : b n < a :=
    lt_of_le_of_lt (Ordinal.le_iSup b n) (lt_add_of_pos_right s Ordinal.omega0_pos)
  have hq (n : ℕ) : ∃ k : ℕ, k ≠ 0 ∧ b n ≤ fundamentalSequence a halim k := by
    obtain ⟨k,hk⟩ := fundamentalSequence_cofinal a halim ha (b n) (hba n)
    exact ⟨k+1,by omega,hk.trans
      ((fundamentalSequence_strictMono a halim ha) (Nat.lt_succ_self k)).le⟩
  choose k hk0 hk using hq
  have hmarkTower := fsTower_reduces_mono 0 (fundamentalSequence a halim 0) zero_le
      (lt_trans (fundamentalSequence_lt a halim 0) ha)
  rw [fsTower_zero] at hmarkTower
  obtain ⟨mark,hmark,hmarkred⟩ := hmarkTower
  have hd (n : ℕ) : (E n).Reduces (fsTower (fundamentalSequence a halim (k n))) :=
    (hE n).trans (fsTower_reduces_mono _ _ (hk n)
      (lt_trans (fundamentalSequence_lt a halim (k n)) ha))
  choose data hdata hdatared using hd
  let marker (n : ℕ) := mark (indexAtom n)
  have marker_iff (n m : ℕ) :
      (fsTower (fundamentalSequence a halim 0)).rel (marker n) (marker m) ↔ n = m := by
    apply (hmarkred (indexAtom n) (indexAtom m)).symm.trans
    change indexAtom n = indexAtom m ↔ n = m
    exact ⟨fun h => indexAtom_injective h,fun h => congrArg indexAtom h⟩
  let d (i : ℕ) := Classical.choice (regular_fsTower (fundamentalSequence a halim i)).nonempty
  let f (n : ℕ) (x : (E n).Carrier) (i : ℕ) :
      (fsTower (fundamentalSequence a halim i)).Carrier :=
    if hi : i = 0 then hi.symm ▸ marker n
    else if hi : i = k n then hi.symm ▸ data n x else d i
  have f_zero (n : ℕ) (x : (E n).Carrier) : f n x 0 = marker n := by simp [f]
  have f_data (n : ℕ) (x : (E n).Carrier) : f n x (k n) = data n x := by
    simp [f,hk0 n]
  have hf (n : ℕ) : Measurable (f n) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = 0
    · subst i
      simpa only [f,dif_pos rfl] using
        (measurable_const : Measurable (fun _ : (E n).Carrier => marker n))
    · by_cases hik : i = k n
      · subst i
        simpa only [f,dif_neg hi,dif_pos rfl] using hdata n
      · simpa only [f,dif_neg hi,dif_neg hik] using
          (measurable_const : Measurable (fun _ : (E n).Carrier => d i))
  refine ⟨a,ha,?_⟩
  rw [fsTower_limit a halim]
  refine ⟨fun x => f x.1 x.2,measurable_sigma_cases _ hf,?_⟩
  rintro ⟨n,x⟩ ⟨m,y⟩
  constructor
  · rintro ⟨h,hxy⟩
    dsimp at h
    subst m
    change (E n).rel x y at hxy
    change ∀ i, (fsTower (fundamentalSequence a halim i)).rel (f n x i) (f n y i)
    intro i
    by_cases hi : i = 0
    · subst i
      rw [f_zero,f_zero]
      exact (marker_iff n n).mpr rfl
    · by_cases hik : i = k n
      · subst i
        rw [f_data,f_data]
        exact (hdatared n x y).mp hxy
      · simpa only [f,dif_neg hi,dif_neg hik] using
          (regular_fsTower (fundamentalSequence a halim i)).equivalence.refl (d i)
  · intro h
    change ∀ i, (fsTower (fundamentalSequence a halim i)).rel (f n x i) (f m y i) at h
    have hnm : n = m := (marker_iff n m).mp (by simpa only [f_zero] using h 0)
    subst m
    refine ⟨rfl,?_⟩
    apply (hdatared n x y).mpr
    simpa only [f_data] using h (k n)

theorem measurable_sigma_mk {X : ℕ → Type} [∀ n, MeasurableSpace (X n)] (n : ℕ) :
    Measurable (Sigma.mk n : X n → Σ n, X n) :=
  Measurable.of_le_map (iInf_le _ n)

/-- A sequence of invariants is represented by the set of its index-tagged
entries. Index tags force coordinatewise matching. -/
theorem countableProduct_reduces_setJump_countableSum (E : ℕ → CodedRelation) :
    (countableProduct E).Reduces (setJump (countableSum E)) := by
  refine ⟨fun x => some (fun n => (⟨n,x n⟩ : Σ n, (E n).Carrier)),?_,?_⟩
  · exact (measurable_some_setJump (countableSum E)).comp
      (measurable_pi_lambda _ (fun n => (measurable_sigma_mk n).comp (measurable_pi_apply n)))
  · intro x y
    constructor
    · intro h
      exact ⟨fun n => ⟨n,rfl,h n⟩,fun n => ⟨n,rfl,h n⟩⟩
    · intro h n
      obtain ⟨m,heq,hm⟩ := h.1 n
      dsimp at heq
      subst m
      exact hm

theorem countableProduct_reduces_fsTower (E : ℕ → CodedRelation)
    (b : ℕ → Ordinal.{0}) (hb : ∀ n, b n < Ordinal.omega 1)
    (hE : ∀ n, (E n).Reduces (fsTower (b n))) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ (countableProduct E).Reduces (fsTower a) := by
  obtain ⟨a,ha,hsum⟩ := countableSum_reduces_fsTower E b hb hE
  refine ⟨a+1,?_,?_⟩
  · simpa only [succ_eq_add_one] using (Cardinal.isSuccLimit_omega 1).succ_lt ha
  · rw [fsTower_add_one]
    exact (countableProduct_reduces_setJump_countableSum E).trans (reduces_setJump_map hsum)

end FSCofinality
