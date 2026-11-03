import FSCofinalityProof.CosetConstructionCodeRepBorel
import FSCofinalityProof.CosetConstructionTokenModels

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)

abbrev ColumnCode (n : ℕ) :=
  {c : BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) // c.1 ≤ n}

instance columnCode_countable (n : ℕ) : Countable (ColumnCode eta heta lam hlam n) := inferInstance
instance columnCode_nonempty (n : ℕ) : Nonempty (ColumnCode eta heta lam hlam n) :=
  ⟨⟨⟨0,.inr (.inl ())⟩,Nat.zero_le n⟩⟩

def evalColumnCode : (n : ℕ) → ColumnCode eta heta lam hlam n →
    (fsTower eta).Carrier → Option (Ambient eta heta)
  | 0,⟨⟨k,c⟩,hk⟩,x =>
      (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a)
        ⟨0,(Nat.eq_zero_of_le_zero hk) ▸ c⟩ x).map Prod.snd
  | n+1,c,x => if h : c.val.1 = n+1 then
      (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x).map Prod.snd
    else (evalColumnCode n ⟨c.val,by have hc := c.property; omega⟩ x).map
      (oldColumn eta heta lam hlam n)

theorem evalColumnCode_fresh (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) :
    evalColumnCode eta heta lam hlam n ⟨⟨n,c⟩,le_rfl⟩ x =
      (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x).map Prod.snd := by
  cases n <;> simp [evalColumnCode]

theorem evalColumnCode_propagate (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (x : (fsTower eta).Carrier) :
    evalColumnCode eta heta lam hlam (n+1) ⟨c.val,Nat.le_succ_of_le c.property⟩ x =
      (evalColumnCode eta heta lam hlam n c x).map (oldColumn eta heta lam hlam n) := by
  have h : c.val.1 ≠ n+1 := Nat.ne_of_lt (Nat.lt_succ_of_le c.property)
  simp only [evalColumnCode,dif_neg h]

theorem codeRep_columnCode (htop : lam ≤ Frame.top eta) (n : ℕ)
    (c : ColumnCode eta heta lam hlam n) :
    CodeRep eta heta (Frame.delta eta lam hlam n) (evalColumnCode eta heta lam hlam n c) := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    have hk0 : k=0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact codeRep_birthColumn eta heta lam hlam htop ⟨0,c⟩
  | succ n ih =>
    by_cases h : c.val.1=n+1
    · have hb := codeRep_birthColumn eta heta lam hlam htop c.val
      simpa only [evalColumnCode,dif_pos h,h] using hb
    · let d : ColumnCode eta heta lam hlam n := ⟨c.val,by have hc := c.property; omega⟩
      have hb := codeRep_oldColumn eta heta lam hlam htop n _ (ih d)
      simpa only [evalColumnCode,dif_neg h] using hb

private theorem evalBirthCode_map_snd (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) (z : Ambient eta heta) :
    (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x).map Prod.snd = some z ↔
      evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x = some (n,z) := by
  rcases c with c | ⟨⟨⟩⟩ | c
  · cases h : (poolCodes eta heta (Frame.q eta lam hlam n)).value c x <;>
      simp only [evalBirthCode,h,Option.map_none,Option.map_some,Option.some.injEq,
        reduceCtorEq,Prod.mk.injEq,true_and]
  · simp only [evalBirthCode,Option.map_some,Option.some.injEq,Prod.mk.injEq,true_and]
  · cases h : (poolCodes eta heta (Frame.rho eta lam hlam n)).value c x <;>
      simp only [evalBirthCode,h,Option.map_none,Option.map_some,Option.some.injEq,
        reduceCtorEq,Prod.mk.injEq,true_and]

theorem evalBirthCode_some_fst (c : BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a))
    (x : (fsTower eta).Carrier) (p : ℕ × Ambient eta heta)
    (h : evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c x = some p) : p.1=c.1 := by
  rcases c with ⟨n,c⟩
  rcases c with c | ⟨⟨⟩⟩ | c
  · cases hv : (poolCodes eta heta (Frame.q eta lam hlam n)).value c x with
    | none => simp only [evalBirthCode,hv,Option.map_none] at h; contradiction
    | some z =>
      have he : (n,dataColumn eta heta lam hlam n z)=p := by
        simpa only [evalBirthCode,hv,Option.map_some,Option.some.injEq] using h
      exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.fst (Option.some.inj h)).symm
  · cases hv : (poolCodes eta heta (Frame.rho eta lam hlam n)).value c x with
    | none => simp only [evalBirthCode,hv,Option.map_none] at h; contradiction
    | some z =>
      have he : (n,singleton (level eta (Frame.delta eta lam hlam n)) z)=p := by
        simpa only [evalBirthCode,hv,Option.map_some,Option.some.injEq] using h
      exact (congrArg Prod.fst he).symm

theorem evalColumnCode_covers (n : ℕ) (x : (fsTower eta).Carrier) (z : Ambient eta heta) :
    (∃ c, evalColumnCode eta heta lam hlam n c x = some z) ↔
      z ∈ ColumnSet eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n := by
  induction n generalizing z with
  | zero =>
    rw [columnSet_zero]
    constructor
    · rintro ⟨⟨⟨k,c⟩,hk⟩,hc⟩
      have hk0 : k=0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact (evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a) x (0,z)).mp
        ⟨⟨0,c⟩,(evalBirthCode_map_snd eta heta lam hlam 0 c x z).mp hc⟩
    · intro hz
      obtain ⟨⟨k,c⟩,hc⟩ :=
        (evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a) x (0,z)).mpr hz
      have hk : 0=k := evalBirthCode_some_fst eta heta lam hlam ⟨k,c⟩ x (0,z) hc
      subst k
      exact ⟨⟨⟨0,c⟩,le_rfl⟩,(evalBirthCode_map_snd eta heta lam hlam 0 c x z).mpr hc⟩
  | succ n ih =>
    rw [columnSet_succ]
    constructor
    · rintro ⟨c,hc⟩
      by_cases h : c.val.1=n+1
      · have hbc : (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x).map
            Prod.snd = some z := by simpa only [evalColumnCode,dif_pos h] using hc
        rcases c with ⟨⟨k,c⟩,hk⟩
        change k=n+1 at h
        subst k
        exact Or.inr ((evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a)
          x (n+1,z)).mp ⟨⟨n+1,c⟩,(evalBirthCode_map_snd eta heta lam hlam _ c x z).mp hbc⟩)
      · let d : ColumnCode eta heta lam hlam n := ⟨c.val,by have hd := c.property; omega⟩
        rw [evalColumnCode,dif_neg h] at hc
        change (evalColumnCode eta heta lam hlam n d x).map _ = some z at hc
        cases hv : evalColumnCode eta heta lam hlam n d x with
        | none => simp only [hv,Option.map_none] at hc; contradiction
        | some u =>
          have hu : oldColumn eta heta lam hlam n u=z := by
            simpa only [hv,Option.map_some,Option.some.injEq] using hc
          exact Or.inl ⟨u,(ih u).mp ⟨d,hv⟩,hu⟩
    · rintro (⟨u,hu,rfl⟩ | hz)
      · obtain ⟨c,hc⟩ := (ih u).mpr hu
        exact ⟨⟨c.val,Nat.le_succ_of_le c.property⟩,by rw [evalColumnCode_propagate,hc]; rfl⟩
      · obtain ⟨⟨k,c⟩,hc⟩ :=
          (evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a) x (n+1,z)).mpr hz
        have hk : n+1=k := evalBirthCode_some_fst eta heta lam hlam ⟨k,c⟩ x (n+1,z) hc
        subst k
        exact ⟨⟨⟨n+1,c⟩,le_rfl⟩,by
          rw [evalColumnCode_fresh]
          exact (evalBirthCode_map_snd eta heta lam hlam _ c x z).mpr hc⟩

end FSCofinality.CosetConstruction
