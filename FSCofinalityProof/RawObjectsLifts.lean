import FSCofinalityProof.RawObjectsUniverse
import FSCofinalityProof.RawObjectsFrame

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

abbrev Ambient (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) := Object (Frame.layerCode η hη)

/-- Outside the intended bounded range this is a harmless default layer. -/
def level (η a : Ordinal.{0}) : Frame.Layer η :=
  if h : a ≤ Frame.top η then Frame.ofOrdinal η a h else Frame.ofOrdinal η 0 zero_le

@[simp] theorem level_rank (η a : Ordinal.{0}) (h : a ≤ Frame.top η) :
    Frame.rank (level η a) = a := by simp only [level,dif_pos h,Frame.rank_ofOrdinal]

def liftIndex (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (hle : lam ≤ Frame.top η)
    (b : Ordinal.{0}) (hb : b < lam) : ℕ :=
  Nat.find (Frame.exists_le_rho η lam hlam (lt_of_le_of_lt hle (Frame.top_countable η hη)) b hb)

theorem liftIndex_spec (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (hle : lam ≤ Frame.top η)
    (b : Ordinal.{0}) (hb : b < lam) :
    b ≤ Frame.rho η lam hlam (liftIndex η hη lam hlam hle b hb) := by
  unfold liftIndex
  exact Nat.find_spec (Frame.exists_le_rho η lam hlam
    (lt_of_le_of_lt hle (Frame.top_countable η hη)) b hb)

/-- Canonical lifts recurse on the target layer. A limit lift is a finite
support at a new singleton column. No composition identity is imposed. -/
def lift (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (b a : Ordinal.{0}) :
    Ambient η hη → Ambient η hη :=
  Ordinal.limitRecOn a id
    (fun c rec => if b = c+1 then id else fun u => singleton (level η (c+1)) (rec u))
    (fun lam hlam rec =>
      if hle : lam ≤ Frame.top η then
        if hb : b < lam then
          let n := liftIndex η hη lam hlam hle b hb
          fun u => finiteFiller (level η lam)
            {(n,singleton (level η (Frame.delta η lam hlam n))
              (rec (Frame.rho η lam hlam n) (Frame.rho_lt η lam hlam n) u))}
        else id
      else id)

@[simp] theorem lift_zero (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (b : Ordinal.{0}) :
    lift η hη b 0 = id := by unfold lift; rw [Ordinal.limitRecOn_zero]

theorem lift_add_one (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (b a : Ordinal.{0}) :
    lift η hη b (a+1) =
      if b = a+1 then id else fun u => singleton (level η (a+1)) (lift η hη b a u) := by
  unfold lift
  rw [Ordinal.limitRecOn_add_one]

theorem lift_limit (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (hle : lam ≤ Frame.top η)
    (b : Ordinal.{0}) (hb : b < lam) :
    lift η hη b lam =
      let n := liftIndex η hη lam hlam hle b hb
      fun u => finiteFiller (level η lam)
        {(n,singleton (level η (Frame.delta η lam hlam n))
          (lift η hη b (Frame.rho η lam hlam n) u))} := by
  unfold lift
  rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]
  simp only [dif_pos hle,dif_pos hb]

@[simp] theorem lift_self (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) :
    lift η hη a a = id := by
  induction a using Ordinal.limitRecOn with
  | zero => exact lift_zero η hη 0
  | add_one a _ => rw [lift_add_one,if_pos rfl]
  | limit a ha _ =>
    unfold lift
    rw [Ordinal.limitRecOn_limit _ _ _ _ ha]
    split <;> simp

theorem lift_injective (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (b a : Ordinal.{0}) (hba : b ≤ a) (ha : a ≤ Frame.top η) :
    Function.Injective (lift η hη b a) := by
  induction a using Ordinal.limitRecOn generalizing b with
  | zero => simpa only [lift_zero] using Function.injective_id
  | add_one a ih =>
    by_cases h : b = a+1
    · subst b
      simpa only [lift_self] using Function.injective_id
    · have hba' : b ≤ a := lt_add_one_iff.mp (lt_of_le_of_ne hba h)
      have haa : a ≤ Frame.top η := (le_of_lt (lt_add_one a)).trans ha
      rw [lift_add_one,if_neg h]
      intro u v huv
      exact ih b hba' haa ((singleton_eq_iff _ _ _).mp huv)
  | limit a haLim ih =>
    by_cases h : b = a
    · subst b
      simpa only [lift_self] using Function.injective_id
    · have hblt : b < a := lt_of_le_of_ne hba h
      rw [lift_limit η hη a haLim ha b hblt]
      let n := liftIndex η hη a haLim ha b hblt
      intro u v huv
      have hsupport := finiteFiller_injective (level η a) huv
      have hcol : singleton (level η (Frame.delta η a haLim n))
          (lift η hη b (Frame.rho η a haLim n) u) =
          singleton (level η (Frame.delta η a haLim n))
          (lift η hη b (Frame.rho η a haLim n) v) := by
        exact congrArg Prod.snd (Finset.singleton_injective hsupport)
      exact ih (Frame.rho η a haLim n) (Frame.rho_lt η a haLim n) b
        (liftIndex_spec η hη a haLim ha b hblt)
        ((Frame.rho_lt η a haLim n).le.trans ha) ((singleton_eq_iff _ _ _).mp hcol)

end FSCofinality.RawObjects
