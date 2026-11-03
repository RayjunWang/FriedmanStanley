import Definitions.Def_FSCofinalityStructures20261102
import Mathlib.SetTheory.Ordinal.FundamentalSequence

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Order Ordinal

namespace FSCofinality

/-- Equality of represented countable sets, including a distinct empty-set
code. Repetitions and enumeration order are ignored. -/
def CountableSetJumpRelation {X : Type} (E : X → X → Prop)
    (x y : Option (ℕ → X)) : Prop :=
  match x,y with
  | none,none => True
  | some u,some v => (∀ i, ∃ j, E (u i) (v j)) ∧ (∀ j, ∃ i, E (u i) (v j))
  | _,_ => False

/-- The countable-set jump uses the actual option/sequence measurable
space, rather than a quotient space of countable sets. -/
def setJump (E : CodedRelation) : CodedRelation where
  Carrier := Option (ℕ → E.Carrier)
  measurableSpace := MeasurableSpace.comap
    (fun x : Option (ℕ → E.Carrier) => match x with
      | none => Sum.inl ()
      | some u => Sum.inr u)
    (inferInstance : MeasurableSpace (Unit ⊕ (ℕ → E.Carrier)))
  rel := CountableSetJumpRelation E.rel

/-- Coordinatewise product on the actual dependent sequence code space. -/
def countableProduct (E : ℕ → CodedRelation) : CodedRelation where
  Carrier := ∀ n, (E n).Carrier
  measurableSpace := inferInstance
  rel := fun x y => ∀ n, (E n).rel (x n) (y n)

/-- Equality on Cantor space is the bottom Friedman--Stanley benchmark. -/
def cantorEquality : CodedRelation where
  Carrier := ℕ → Bool
  measurableSpace := inferInstance
  rel := Eq

/-- A countable nonzero limit ordinal has an increasing cofinal natural
sequence. This supplies the indexing data of the concrete limit products. -/
theorem exists_nat_fundamental_sequence (a : Ordinal.{0})
    (ha : IsSuccLimit a) (hc : a < Ordinal.omega 1) :
    ∃ q : ℕ → Ordinal.{0},
      (∀ n, q n < a) ∧ StrictMono q ∧ ∀ b < a, ∃ n, b ≤ q n := by
  have hcof : a.cof.ord = Ordinal.omega0 := by
    rw [Ordinal.cof_eq_aleph0_of_isSuccLimit ha hc, Cardinal.ord_aleph0]
  obtain ⟨f,hf⟩ := Ordinal.exists_isFundamentalSeq hcof
  refine ⟨fun n => (f ⟨n,Ordinal.natCast_lt_omega0 n⟩).val,
    fun n => (f ⟨n,Ordinal.natCast_lt_omega0 n⟩).property, ?_, ?_⟩
  · intro n m hnm
    apply hf.strictMono
    change (n : Ordinal) < (m : Ordinal)
    exact_mod_cast hnm
  · intro b hb
    obtain ⟨_,⟨i,rfl⟩,hi⟩ := hf.isCofinal_range ⟨b,hb⟩
    obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp i.property
    refine ⟨n,?_⟩
    have heq : i = ⟨n,Ordinal.natCast_lt_omega0 n⟩ := Subtype.ext hn
    simpa only [heq] using hi

/-- One fixed choice of fundamental sequence at every countable nonzero
limit ordinal. Values outside the countable range are harmless defaults;
the mission's tower is used only below omega one. -/
def fundamentalSequence (a : Ordinal.{0}) (ha : IsSuccLimit a) : ℕ → Ordinal.{0} :=
  if hc : a < Ordinal.omega 1 then
    Classical.choose (exists_nat_fundamental_sequence a ha hc)
  else fun _ => 0

theorem fundamentalSequence_lt (a : Ordinal.{0}) (ha : IsSuccLimit a) (n : ℕ) :
    fundamentalSequence a ha n < a := by
  unfold fundamentalSequence
  split
  · rename_i hc
    exact (Classical.choose_spec (exists_nat_fundamental_sequence a ha hc)).1 n
  · exact bot_lt_iff_ne_bot.mpr ha.ne_bot

theorem fundamentalSequence_strictMono (a : Ordinal.{0}) (ha : IsSuccLimit a)
    (hc : a < Ordinal.omega 1) : StrictMono (fundamentalSequence a ha) := by
  unfold fundamentalSequence
  rw [dif_pos hc]
  exact (Classical.choose_spec (exists_nat_fundamental_sequence a ha hc)).2.1

theorem fundamentalSequence_cofinal (a : Ordinal.{0}) (ha : IsSuccLimit a)
    (hc : a < Ordinal.omega 1) (b : Ordinal.{0}) (hb : b < a) :
    ∃ n, b ≤ fundamentalSequence a ha n := by
  unfold fundamentalSequence
  rw [dif_pos hc]
  exact (Classical.choose_spec (exists_nat_fundamental_sequence a ha hc)).2.2 b hb

/-- The concrete product-limit Friedman--Stanley tower from the manuscript:
Cantor equality at zero, countable-set jump at successors, and coordinatewise
countable products along the fixed fundamental sequences at limits. -/
def fsTower (a : Ordinal.{0}) : CodedRelation :=
  Ordinal.limitRecOn a cantorEquality (fun _ E => setJump E)
    (fun b hb rec => countableProduct (fun n =>
      rec (fundamentalSequence b hb n) (fundamentalSequence_lt b hb n)))

@[simp] theorem fsTower_zero : fsTower 0 = cantorEquality := by
  unfold fsTower
  rw [Ordinal.limitRecOn_zero]

@[simp] theorem fsTower_add_one (a : Ordinal.{0}) : fsTower (a+1) = setJump (fsTower a) := by
  unfold fsTower
  rw [Ordinal.limitRecOn_add_one]

theorem fsTower_limit (a : Ordinal.{0}) (ha : IsSuccLimit a) :
    fsTower a = countableProduct (fun n => fsTower (fundamentalSequence a ha n)) := by
  unfold fsTower
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha]

end FSCofinality
