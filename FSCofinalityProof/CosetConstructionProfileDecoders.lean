import FSCofinalityProof.CosetConstructionColumnEnumeration
import FSCofinalityProof.CosetConstructionSeedCoordinates

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)

def freshBirthCodeValue (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) :
    Option (BirthData eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) :=
  match c with
  | .inl d => match h : (poolCodes eta heta (Frame.q eta lam hlam n)).value d x with
      | none => none
      | some u => some (.inl ⟨u,((poolCodes eta heta _).covers x u).mp ⟨d,h⟩⟩)
  | .inr (.inl _) => some (.inr (.inl ()))
  | .inr (.inr d) => match h : (poolCodes eta heta (Frame.rho eta lam hlam n)).value d x with
      | none => none
      | some u => some (.inr (.inr ⟨u,((poolCodes eta heta _).covers x u).mp ⟨d,h⟩⟩))

def columnCodeValue (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (x : (fsTower eta).Carrier) :
    Option (Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) :=
  (freshBirthCodeValue eta heta lam hlam c.val.1 c.val.2 x).map
    (fun d => ⟨⟨c.val.1,d⟩,c.property⟩)

theorem encodeNew_freshBirthCodeValue (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) :
    (freshBirthCodeValue eta heta lam hlam n c x).map
      (encodeNew eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) =
    (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x).map Prod.snd := by
  rcases c with c|⟨⟨⟩⟩|c
  · dsimp only [freshBirthCodeValue]
    split <;> simp_all [evalBirthCode,encodeNew]
  · rfl
  · dsimp only [freshBirthCodeValue]
    split <;> simp_all [evalBirthCode,encodeNew]

theorem encodeBirth_freshBirthCodeValue (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) :
    (freshBirthCodeValue eta heta lam hlam n c x).map
      (fun d => encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) ⟨n,d⟩) =
    evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x := by
  rcases c with c|⟨⟨⟩⟩|c
  · dsimp only [freshBirthCodeValue]
    split <;> simp_all [evalBirthCode,encodeBirth,encodeNew]
  · rfl
  · dsimp only [freshBirthCodeValue]
    split <;> simp_all [evalBirthCode,encodeBirth,encodeNew]

theorem encodeColumn_columnCodeValue (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (x : (fsTower eta).Carrier) :
    (columnCodeValue eta heta lam hlam n c x).map
      (encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) =
    evalColumnCode eta heta lam hlam n c x := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    have hk0 : k=0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp only [columnCodeValue,Option.map_map]
    change (freshBirthCodeValue eta heta lam hlam 0 c x).map
      (encodeNew eta heta lam hlam (TokenModel.lowerPools eta heta x lam) 0) = _
    exact encodeNew_freshBirthCodeValue eta heta lam hlam 0 c x
  | succ n ih =>
    by_cases h : c.val.1=n+1
    · rcases c with ⟨⟨k,c⟩,hk⟩
      change k=n+1 at h
      subst k
      simp only [columnCodeValue,Option.map_map,Function.comp_def,encodeColumn_fresh,evalColumnCode_fresh]
      change (freshBirthCodeValue eta heta lam hlam (n+1) c x).map
        (fun d => encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) (n+1)
          (freshColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) (n+1) d)) = _
      simp only [encodeColumn_fresh]
      exact encodeNew_freshBirthCodeValue eta heta lam hlam _ c x
    · let d : ColumnCode eta heta lam hlam n := ⟨c.val,by have hc := c.property; omega⟩
      have hval : columnCodeValue eta heta lam hlam (n+1) c x =
          (columnCodeValue eta heta lam hlam n d x).map
            (propagate eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) := by
        simp only [columnCodeValue,Option.map_map]
        rfl
      have hc : evalColumnCode eta heta lam hlam (n+1) c x =
          (evalColumnCode eta heta lam hlam n d x).map (oldColumn eta heta lam hlam n) :=
        evalColumnCode_propagate eta heta lam hlam n d x
      rw [hval,hc]
      simpa only [Option.map_map,Function.comp_def,encodeColumn_propagate] using
        congrArg (Option.map (oldColumn eta heta lam hlam n)) (ih d)

theorem encodeBirth_columnCodeValue (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (x : (fsTower eta).Carrier) :
    (columnCodeValue eta heta lam hlam n c x).map
      (fun d => encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) d.val) =
    evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x := by
  rcases c with ⟨⟨k,c⟩,hk⟩
  simp only [columnCodeValue,Option.map_map,Function.comp_def]
  exact encodeBirth_freshBirthCodeValue eta heta lam hlam k c x

end FSCofinality.CosetConstruction
