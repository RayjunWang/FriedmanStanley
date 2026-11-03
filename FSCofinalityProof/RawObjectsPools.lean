import FSCofinalityProof.RawObjectsLifts

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

def tag (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) (n : ℕ) :
    Ambient η hη := lift η hη 0 a (extraAtom n)

theorem tag_injective (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (ha : a ≤ Frame.top η) : Function.Injective (tag η hη a) := by
  intro n m h
  exact extraAtom_injective (lift_injective η hη 0 a zero_le ha h)

def dataColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) (v : Ambient η hη) : Ambient η hη :=
  Enc (level η (Frame.rho η lam hlam n)) (level η (Frame.delta η lam hlam n))
    (tag η hη (Frame.sigma η lam hlam n) 1) (tag η hη (Frame.sigma η lam hlam n) 3)
    (lift η hη (Frame.q η lam hlam n) (Frame.sigma η lam hlam n) v)

def markerColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) : Ambient η hη :=
  Enc (level η (Frame.rho η lam hlam n)) (level η (Frame.delta η lam hlam n))
    (tag η hη (Frame.sigma η lam hlam n) 2) (tag η hη (Frame.sigma η lam hlam n) 3)
    (tag η hη (Frame.sigma η lam hlam n) 3)

/-- The new (non-propagated) columns; all parameters come from lower layers. -/
def NewColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)) (n : ℕ) (c : Ambient η hη) : Prop :=
  (∃ v ∈ lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n),
    c = dataColumn η hη lam hlam n v) ∨
  c = markerColumn η hη lam hlam n ∨
  ∃ v ∈ lower (Frame.rho η lam hlam n) (Frame.rho_lt η lam hlam n),
    c = singleton (level η (Frame.delta η lam hlam n)) v

def SuccessorSet (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (lower : Set (Ambient η hη)) : Set (Ambient η hη) :=
  {x | ∃ u : Option (ℕ → Ambient η hη), x = collection (level η (a+1)) u ∧
    ∀ f, u = some f → ∀ i, f i ∈ lower}

def LimitSet (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)) : Set (Ambient η hη) :=
  {x | (∃ s : ℕ → Ambient η hη, x = sourceSequence (level η lam) s ∧
      ∀ n, s n ∈ lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n)) ∨
    (∃ A : Finset (ℕ × Ambient η hη), x = finiteFiller (level η lam) A ∧
      ∀ p ∈ A, NewColumn η hη lam hlam lower p.1 p.2)}

/-- Actual typed ambient layers as subsets of the small semantic universe. -/
def Valid (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) : Set (Ambient η hη) :=
  Ordinal.limitRecOn a (range sourceAtom ∪ range extraAtom)
    (SuccessorSet η hη)
    (LimitSet η hη)

abbrev W (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) :=
  {x : Ambient η hη // x ∈ Valid η hη a}

@[simp] theorem valid_zero (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) :
    Valid η hη 0 = range sourceAtom ∪ range extraAtom := by
  unfold Valid
  rw [Ordinal.limitRecOn_zero]

theorem valid_add_one (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) :
    Valid η hη (a+1) = SuccessorSet η hη a (Valid η hη a) := by
  unfold Valid
  rw [Ordinal.limitRecOn_add_one]

theorem valid_limit (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    Valid η hη lam = LimitSet η hη lam hlam (fun b _ => Valid η hη b) := by
  unfold Valid
  rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]

theorem valid_singleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) {u : Ambient η hη} (hu : u ∈ Valid η hη a) :
    singleton (level η (a+1)) u ∈ Valid η hη (a+1) := by
  rw [valid_add_one]
  refine ⟨some (fun _ => u),rfl,?_⟩
  intro f hf i
  cases hf
  exact hu

theorem valid_doubleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) {u v : Ambient η hη}
    (hu : u ∈ Valid η hη a) (hv : v ∈ Valid η hη a) :
    doubleton (level η (a+1)) u v ∈ Valid η hη (a+1) := by
  rw [valid_add_one]
  refine ⟨some (fun n => if n = 0 then u else v),rfl,?_⟩
  intro f hf i
  cases hf
  dsimp only
  split <;> assumption

theorem valid_lift (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (b a : Ordinal.{0}) (hba : b ≤ a) (ha : a ≤ Frame.top η)
    {u : Ambient η hη} (hu : u ∈ Valid η hη b) :
    lift η hη b a u ∈ Valid η hη a := by
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
      exact valid_singleton η hη a (ih b hba' haa hu)
  | limit a haLim ih =>
    by_cases h : b = a
    · subst b
      simpa only [lift_self] using hu
    · have hblt : b < a := lt_of_le_of_ne hba h
      rw [lift_limit η hη a haLim ha b hblt,valid_limit η hη a haLim]
      let n := liftIndex η hη a haLim ha b hblt
      have hlow : lift η hη b (Frame.rho η a haLim n) u ∈ Valid η hη (Frame.rho η a haLim n) :=
        ih (Frame.rho η a haLim n) (Frame.rho_lt η a haLim n) b
          (liftIndex_spec η hη a haLim ha b hblt)
          ((Frame.rho_lt η a haLim n).le.trans ha) hu
      apply Or.inr
      refine ⟨_,rfl,?_⟩
      intro p hp
      have hp' := Finset.mem_singleton.mp hp
      subst p
      exact Or.inr (Or.inr ⟨_,hlow,rfl⟩)

theorem valid_tag (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (ha : a ≤ Frame.top η) (n : ℕ) : tag η hη a n ∈ Valid η hη a := by
  apply valid_lift η hη 0 a zero_le ha
  rw [valid_zero]
  exact Or.inr (mem_range_self n)

end FSCofinality.RawObjects
