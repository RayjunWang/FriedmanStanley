import FSCofinalityProof.HierarchyBasics
import FSCofinalityProof.StructuresBasics

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality

theorem measurable_some_setJump (E : CodedRelation) :
    @Measurable (ℕ → E.Carrier) (setJump E).Carrier inferInstance
      (setJump E).measurableSpace some := by
  rw [setJump_measurableSpace_eq]
  apply measurable_comap_iff.mpr
  exact measurable_inr

theorem reduces_setJump_singleton (E : CodedRelation) : E.Reduces (setJump E) := by
  refine ⟨fun x => some (fun _ => x),?_,?_⟩
  · exact (measurable_some_setJump E).comp (measurable_pi_lambda _ (fun _ => measurable_id))
  · intro x y
    change E.rel x y ↔
      (∀ _ : ℕ, ∃ _ : ℕ, E.rel x y) ∧ (∀ _ : ℕ, ∃ _ : ℕ, E.rel x y)
    exact ⟨fun h => ⟨fun _ => ⟨0,h⟩,fun _ => ⟨0,h⟩⟩,fun h => (h.1 0).choose_spec⟩

theorem reduces_countableProduct_coordinate (E : ℕ → CodedRelation)
    (hE : ∀ n, RegularRelation (E n)) (k : ℕ) :
    (E k).Reduces (countableProduct E) := by
  let f (x : (E k).Carrier) (n : ℕ) : (E n).Carrier :=
    if h : n = k then h.symm ▸ x else Classical.choice (hE n).nonempty
  refine ⟨f,?_,?_⟩
  · apply measurable_pi_lambda
    intro n
    by_cases hn : n = k
    · subst n
      simpa only [f,dif_pos rfl] using (measurable_id : Measurable (id : (E k).Carrier → _))
    · simpa only [f,dif_neg hn] using
        (measurable_const : Measurable (fun _ : (E k).Carrier => Classical.choice (hE n).nonempty))
  · intro x y
    constructor
    · intro h n
      by_cases hn : n = k
      · subst n
        simpa only [f,dif_pos rfl] using h
      · simpa only [f,dif_neg hn] using (hE n).equivalence.refl (Classical.choice (hE n).nonempty)
    · intro h
      simpa only [f,dif_pos rfl] using h k

theorem reduces_setJump_map {E F : CodedRelation} (hEF : E.Reduces F) :
    (setJump E).Reduces (setJump F) := by
  obtain ⟨f,hf,hred⟩ := hEF
  let g : Option (ℕ → E.Carrier) → Option (ℕ → F.Carrier) :=
    Option.map (fun x n => f (x n))
  refine ⟨g,?_,?_⟩
  · change @Measurable (Option (ℕ → E.Carrier)) (Option (ℕ → F.Carrier))
      (setJump E).measurableSpace (setJump F).measurableSpace g
    rw [setJump_measurableSpace_eq,setJump_measurableSpace_eq]
    apply measurable_comap_iff.mpr
    have hm : Measurable (fun u : ℕ → E.Carrier => fun n => f (u n)) :=
      measurable_pi_lambda _ (fun n => hf.comp (measurable_pi_apply n))
    have hs : Measurable (Sum.elim (fun _ : Unit => (Sum.inl () : Unit ⊕ (ℕ → F.Carrier)))
        (fun u : ℕ → E.Carrier => Sum.inr (fun n => f (u n)))) :=
      measurable_const.sumElim (measurable_inr.comp hm)
    have hc := hs.comp (comap_measurable (optionSumEquiv (ℕ → E.Carrier)))
    convert hc using 1
    funext x
    cases x <;> rfl
  · intro x y
    cases x <;> cases y
    · trivial
    · exact Iff.rfl
    · exact Iff.rfl
    · simp only [setJump,CountableSetJumpRelation,g,Option.map_some]
      exact and_congr (forall_congr' (fun i => exists_congr (fun j => hred _ _)))
        (forall_congr' (fun j => exists_congr (fun i => hred _ _)))

/-- The concrete product-limit tower is increasing under actual Borel
reductions. This statement uses its fixed cofinal sequences only below omega one. -/
theorem fsTower_reduces_mono (a b : Ordinal.{0}) (hab : a ≤ b)
    (hb : b < Ordinal.omega 1) : (fsTower a).Reduces (fsTower b) := by
  induction b using Ordinal.limitRecOn generalizing a with
  | zero =>
    have ha : a = 0 := le_antisymm hab zero_le
    subst a
    exact CodedRelation.Reduces.refl _
  | add_one b ih =>
    rcases hab.eq_or_lt with h | h
    · subst a
      exact CodedRelation.Reduces.refl _
    · have hab' : a ≤ b := lt_add_one_iff.mp h
      have hbb : b < Ordinal.omega 1 := lt_trans (lt_add_one b) hb
      have hi := ih a hab' hbb
      rw [fsTower_add_one]
      exact hi.trans (reduces_setJump_singleton _)
  | limit b hlim ih =>
    rcases hab.eq_or_lt with h | h
    · subst a
      exact CodedRelation.Reduces.refl _
    · obtain ⟨n,hn⟩ := fundamentalSequence_cofinal b hlim hb a h
      have hqn := fundamentalSequence_lt b hlim n
      have hi := ih (fundamentalSequence b hlim n) hqn a hn (lt_trans hqn hb)
      rw [fsTower_limit b hlim]
      exact hi.trans (reduces_countableProduct_coordinate _
        (fun _ => regular_fsTower _) n)

end FSCofinality
