import FSCofinalityProof.HierarchyBasics
import Mathlib.Data.Nat.Nth

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory

namespace FSCofinality

def CountableMultisetRelation {X : Type} (E : X → X → Prop) (x y : ℕ → X) : Prop :=
  ∃ σ : ℕ ≃ ℕ, ∀ i, E (x i) (y (σ i))

def multisetJump (E : CodedRelation) : CodedRelation where
  Carrier := ℕ → E.Carrier
  measurableSpace := inferInstance
  rel := CountableMultisetRelation E.rel

def naturalTagged (E : CodedRelation) : CodedRelation where
  Carrier := E.Carrier × ℕ
  measurableSpace := inferInstance
  rel := fun x y => E.rel x.1 y.1 ∧ x.2 = y.2

/-- The zero-based number of earlier occurrences in the same equivalence class. -/
def occurrenceCount {X : Type} (E : X → X → Prop) (x : ℕ → X) (i : ℕ) : ℕ :=
  Nat.count (fun j => E (x j) (x i)) i

def occurrenceCode {X : Type} (E : X → X → Prop) (x : ℕ → X) : ℕ → X × ℕ :=
  fun i => (x i,occurrenceCount E x i)

theorem sameClass_predicate {X : Type} {E : X → X → Prop} (hE : Equivalence E)
    {a b : X} (hab : E a b) (x : ℕ → X) :
    (fun j => E (x j) a) = (fun j => E (x j) b) := by
  funext j
  exact propext ⟨fun h => hE.trans h hab,fun h => hE.trans h (hE.symm hab)⟩

theorem occurrenceCount_injective_sameClass {X : Type} {E : X → X → Prop}
    (hE : Equivalence E) (x : ℕ → X) {i j : ℕ} (hij : E (x i) (x j))
    (hc : occurrenceCount E x i = occurrenceCount E x j) : i = j := by
  unfold occurrenceCount at hc
  simp only [sameClass_predicate hE hij x] at hc
  exact Nat.count_injective hij (hE.refl _) hc

theorem occurrenceCount_measurable (E : CodedRelation)
    (hE : @MeasurableSet (E.Carrier × E.Carrier)
      (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2}) (i : ℕ) :
    Measurable (fun x : ℕ → E.Carrier => occurrenceCount E.rel x i) := by
  have hcount (n : ℕ) : Measurable (fun x : ℕ → E.Carrier =>
      Nat.count (fun j => E.rel (x j) (x i)) n) := by
    induction n with
    | zero => simpa only [Nat.count_zero] using (measurable_const :
        Measurable (fun _ : ℕ → E.Carrier => (0 : ℕ)))
    | succ n ih =>
      simp only [Nat.count_succ]
      exact ih.add (Measurable.ite
        (hE.preimage (f := fun x : ℕ → E.Carrier => (x n,x i))
          ((measurable_pi_apply n).prodMk (measurable_pi_apply i)))
        measurable_const measurable_const)
  exact hcount i

theorem occurrenceCode_measurable (E : CodedRelation)
    (hE : @MeasurableSet (E.Carrier × E.Carrier)
      (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2}) :
    Measurable (occurrenceCode E.rel) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).prodMk (occurrenceCount_measurable E hE i)

/-- A permutation preserving classes supplies an occurrence of every tag
present in the input, regardless of its enumeration order. -/
theorem tagged_match_of_permutation {X : Type} {E : X → X → Prop}
    (hE : Equivalence E) {x y : ℕ → X} (σ : ℕ ≃ ℕ)
    (hσ : ∀ i, E (x i) (y (σ i))) (i : ℕ) :
    ∃ j, E (x i) (y j) ∧ occurrenceCount E x i = occurrenceCount E y j := by
  let p : ℕ → Prop := fun j => E (y j) (x i)
  let k := occurrenceCount E x i
  have hk : ∀ hf : (setOf p).Finite, k < hf.toFinset.card := by
    intro hf
    let s := (Finset.range (i+1)).filter (fun j => E (x j) (x i))
    have hsub : s.image σ ⊆ hf.toFinset := by
      intro j hj
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hj
      exact hf.mem_toFinset.mpr (hE.trans (hE.symm (hσ l)) (Finset.mem_filter.mp hl).2)
    have hcard : (s.image σ).card = s.card := Finset.card_image_iff.mpr σ.injective.injOn
    have hlt : k < s.card := by
      change Nat.count (fun j => E (x j) (x i)) i < s.card
      change Nat.count (fun j => E (x j) (x i)) i <
        ((Finset.range (i+1)).filter (fun j => E (x j) (x i))).card
      rw [← Nat.count_eq_card_filter_range]
      exact Nat.count_lt_count_succ_iff.mpr (hE.refl _)
    exact hlt.trans_le (hcard ▸ Finset.card_le_card hsub)
  let j := Nat.nth p k
  have hpj : p j := Nat.nth_mem k hk
  refine ⟨j,hE.symm hpj,?_⟩
  unfold occurrenceCount
  simp only [sameClass_predicate hE hpj y]
  exact (Nat.count_nth hk).symm

theorem occurrenceCode_reduction {X : Type} {E : X → X → Prop}
    (hE : Equivalence E) (x y : ℕ → X) :
    CountableMultisetRelation E x y ↔
      CountableSetJumpRelation (fun a b : X × ℕ => E a.1 b.1 ∧ a.2 = b.2)
        (some (occurrenceCode E x)) (some (occurrenceCode E y)) := by
  constructor
  · rintro ⟨σ,hσ⟩
    refine ⟨tagged_match_of_permutation hE σ hσ,?_⟩
    intro j
    obtain ⟨i,hi,hc⟩ := tagged_match_of_permutation hE σ.symm
      (fun j => by simpa using hE.symm (hσ (σ.symm j))) j
    exact ⟨i,hE.symm hi,hc.symm⟩
  · rintro ⟨hxy,hyx⟩
    change (∀ i, ∃ j, E (x i) (y j) ∧ occurrenceCount E x i = occurrenceCount E y j) at hxy
    change (∀ j, ∃ i, E (x i) (y j) ∧ occurrenceCount E x i = occurrenceCount E y j) at hyx
    choose f hf using hxy
    have hfinj : Function.Injective f := by
      intro i j hij
      apply occurrenceCount_injective_sameClass hE x
        (hE.trans (hf i).1 (hE.symm (by rw [hij]; exact (hf j).1)))
      exact (hf i).2.trans (by rw [hij]; exact (hf j).2.symm)
    have hfsurj : Function.Surjective f := by
      intro j
      obtain ⟨i,hi,hc⟩ := hyx j
      refine ⟨i,?_⟩
      exact occurrenceCount_injective_sameClass hE y
        (hE.trans (hE.symm (hf i).1) hi) ((hf i).2.symm.trans hc)
    exact ⟨Equiv.ofBijective f ⟨hfinj,hfsurj⟩,fun i => (hf i).1⟩

/-- Occurrence tags give the source manuscript's multiset-to-set-jump
reduction on actual sequence code spaces. -/
theorem multisetJump_reduces_setJump_naturalTagged (E : CodedRelation)
    (hE : Equivalence E.rel)
    (hgraph : @MeasurableSet (E.Carrier × E.Carrier)
      (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2}) :
    (multisetJump E).Reduces (setJump (naturalTagged E)) := by
  refine ⟨fun x => some (occurrenceCode E.rel x),?_,?_⟩
  · change @Measurable (ℕ → E.Carrier) (Option (ℕ → E.Carrier × ℕ))
      inferInstance (setJump (naturalTagged E)).measurableSpace
      (fun x => some (occurrenceCode E.rel x))
    rw [setJump_measurableSpace_eq]
    apply measurable_comap_iff.mpr
    exact measurable_inr.comp (occurrenceCode_measurable E hgraph)
  · exact occurrenceCode_reduction hE

end FSCofinality
