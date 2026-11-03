import FSCofinalityProof.ParameterClassMarkedLanguage
import FSCofinalityProof.MarkedCosets

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.MarkedCoding

theorem markerConditions_of_isomorphic {A B : Structures language}
    (hA : MarkerConditions A) (e : ℕ ≃ ℕ)
    (he : ∀ s a, A ⟨s,a⟩ = B ⟨s,e ∘ a⟩) : MarkerConditions B := by
  have hm := marker_preserved e he
  have hred := isomorphic_reduct e he
  have hback (j n : ℕ) : marker B j n = marker A j (e.symm n) := by
    simpa only [Equiv.apply_symm_apply] using (hm j (e.symm n)).symm
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    obtain ⟨n,hn⟩ := hA.1 j
    exact ⟨e n,(hm j n).symm.trans hn⟩
  · intro j n m hn hm'
    apply e.symm.injective
    exact hA.2.1 j _ _ ((hback j n).symm.trans hn) ((hback j m).symm.trans hm')
  · intro i j n hi hj
    exact hA.2.2.1 i j (e.symm n)
      ((hback i n).symm.trans hi) ((hback j n).symm.trans hj)
  · intro n
    have hq := distinguished_iff_of_isomorphism e hred (e.symm n)
    rw [Equiv.apply_symm_apply] at hq
    rw [← hq,hA.2.2.2]
    exact exists_congr (fun j => by rw [hback])

theorem markerChoice_preserved {A B : Structures language}
    (hA : MarkerConditions A) (hB : MarkerConditions B) (e : ℕ ≃ ℕ)
    (he : ∀ s a, A ⟨s,a⟩ = B ⟨s,e ∘ a⟩) (j : ℕ) :
    e (markerChoice A hA.1 j) = markerChoice B hB.1 j := by
  apply ((markerChoice_eq_iff B hB j _).mpr ?_).symm
  exact (marker_preserved e he j _).symm.trans (markerChoice_spec A hA.1 j)

theorem isomorphic_iff_named {A B : Structures language}
    (hA : MarkerConditions A) (hB : MarkerConditions B) (hbits : bits A = bits B) :
    Isomorphic A B ↔
      ∃ t : PermutationGroup, Carries (reduct A) (reduct B) t ∧
        ∀ j, t.toFun (markerChoice A hA.1 j) = markerChoice B hB.1 j := by
  constructor
  · rintro ⟨e,he⟩
    exact ⟨e,isomorphic_reduct e he,markerChoice_preserved hA hB e he⟩
  · rintro ⟨t,ht,hmarks⟩
    refine ⟨(show ℕ ≃ ℕ from t),?_⟩
    intro s a
    rcases s with s | (j | j)
    · exact ht s a
    · change Fin 0 → ℕ at a
      have ha : A ⟨.inr (.inl j),a⟩ = bits A j :=
        congrArg (fun b : Fin 0 → ℕ => A ⟨.inr (.inl j),b⟩)
          (funext (fun i => Fin.elim0 i))
      have hb : bits B j = B ⟨.inr (.inl j),t.toFun ∘ a⟩ :=
        congrArg (fun b : Fin 0 → ℕ => B ⟨.inr (.inl j),b⟩)
          (funext (fun i => Fin.elim0 i))
      exact ha.trans ((congrFun hbits j).trans hb)
    · change Fin 1 → ℕ at a
      have ha : a = fun _ => a 0 := funext (fun i => congrArg a (Fin.eq_zero i))
      rw [ha]
      change marker A j (a 0) = marker B j (t.toFun (a 0))
      have hmiff : marker A j (a 0) = true ↔ marker B j (t.toFun (a 0)) = true := by
        rw [← markerChoice_eq_iff A hA j (a 0),
          ← markerChoice_eq_iff B hB j (t.toFun (a 0)),← hmarks j]
        exact ⟨fun h => congrArg t.toFun h,fun h => t.injective h⟩
      cases ha' : marker A j (a 0) <;> cases hb' : marker B j (t.toFun (a 0))
      · rfl
      · exact False.elim (Bool.false_ne_true (ha' ▸ hmiff.mpr hb'))
      · exact False.elim (Bool.false_ne_true (hb' ▸ hmiff.mp ha'))
      · rfl

end FSCofinality.MarkedCoding
