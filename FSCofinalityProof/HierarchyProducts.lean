import FSCofinalityProof.HierarchySums

noncomputable section
open MeasureTheory

namespace FSCofinality

def binaryProduct (E F : CodedRelation) : CodedRelation where
  Carrier := E.Carrier × F.Carrier
  measurableSpace := inferInstance
  rel := fun x y => E.rel x.1 y.1 ∧ F.rel x.2 y.2

def pairFamily (E F : CodedRelation) : ℕ → CodedRelation
  | 0 => E
  | _+1 => F

theorem binaryProduct_reduces_fsTower {E F : CodedRelation} (a b : Ordinal.{0})
    (ha : a < Ordinal.omega 1) (hb : b < Ordinal.omega 1)
    (hE : E.Reduces (fsTower a)) (hF : F.Reduces (fsTower b)) :
    ∃ c : Ordinal.{0}, c < Ordinal.omega 1 ∧ (binaryProduct E F).Reduces (fsTower c) := by
  let stage : ℕ → Ordinal.{0} | 0 => a | _+1 => b
  have hc n : stage n < Ordinal.omega 1 := by cases n <;> assumption
  have hr n : (pairFamily E F n).Reduces (fsTower (stage n)) := by cases n <;> assumption
  obtain ⟨c,hc,hprod⟩ := countableProduct_reduces_fsTower (pairFamily E F) stage hc hr
  refine ⟨c,hc,?_⟩
  apply CodedRelation.Reduces.trans (R := fsTower c) (F := countableProduct (pairFamily E F)) ?_ hprod
  let f (p : E.Carrier × F.Carrier) : ∀ n, (pairFamily E F n).Carrier
    | 0 => p.1
    | _+1 => p.2
  refine ⟨f,?_,?_⟩
  · apply measurable_pi_lambda
    intro n
    cases n
    · exact measurable_fst
    · exact measurable_snd
  · intro x y
    change (E.rel x.1 y.1 ∧ F.rel x.2 y.2) ↔ ∀ n, (pairFamily E F n).rel (f x n) (f y n)
    constructor
    · intro h n
      cases n
      · exact h.1
      · exact h.2
    · intro h
      exact ⟨h 0,h 1⟩

def boolEquality : CodedRelation where
  Carrier := Bool
  measurableSpace := inferInstance
  rel := Eq

theorem boolEquality_reduces_fsTower_zero : boolEquality.Reduces (fsTower 0) := by
  rw [fsTower_zero]
  refine ⟨fun b : Bool => fun _ : ℕ => b,measurable_pi_lambda _ (fun _ => measurable_id),?_⟩
  intro b c
  change b = c ↔ (fun _ : ℕ => b) = (fun _ : ℕ => c)
  exact ⟨fun h => congrArg (fun b : Bool => fun _ : ℕ => b) h,fun h => congrFun h 0⟩

end FSCofinality
