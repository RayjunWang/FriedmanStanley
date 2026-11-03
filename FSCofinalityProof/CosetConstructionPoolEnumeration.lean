import FSCofinalityProof.CosetConstructionPoolBorelLimit
import FSCofinalityProof.CosetConstructionEnumeration
import FSCofinalityProof.RawObjectsPoolRoles

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def poolCodeList (a : Ordinal.{0}) : ℕ → (poolCodes eta heta a).Code := by
  letI : Nonempty (poolCodes eta heta a).Code := ⟨(poolCodes eta heta a).seed none⟩
  exact Classical.choose (exists_surjective_nat (poolCodes eta heta a).Code)

theorem poolCodeList_surjective (a : Ordinal.{0}) :
    Function.Surjective (poolCodeList eta heta a) := by
  letI : Nonempty (poolCodes eta heta a).Code := ⟨(poolCodes eta heta a).seed none⟩
  exact Classical.choose_spec (exists_surjective_nat (poolCodes eta heta a).Code)

def poolPartialList (a : Ordinal.{0}) (n : ℕ) (x : (fsTower eta).Carrier) :
    Option (Ambient eta heta) := (poolCodes eta heta a).value (poolCodeList eta heta a n) x

theorem poolPartialList_range (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    {u | ∃ n, poolPartialList eta heta a n x = some u} =
      Pool eta heta (fun b => fullSeeds eta heta b x) a := by
  ext u
  rw [←(poolCodes eta heta a).covers x u]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨_,hn⟩
  · rintro ⟨c,hc⟩
    obtain ⟨n,rfl⟩ := poolCodeList_surjective eta heta a c
    exact ⟨n,hc⟩

theorem poolPartialList_range_infinite (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    {u | ∃ n, poolPartialList eta heta a n x = some u}.Infinite := by
  rw [poolPartialList_range]
  exact Set.infinite_coe_iff.mp (pool_infinite eta heta _ a)

def poolEnumeration (a : Ordinal.{0}) (x : (fsTower eta).Carrier) (k : ℕ) : Ambient eta heta :=
  enumerateValues (extraAtom 0) (fun n => poolPartialList eta heta a n x) k

theorem poolEnumeration_injective (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    Function.Injective (poolEnumeration eta heta a x) :=
  enumerateValues_injective _ _ (poolPartialList_range_infinite eta heta a x)

theorem poolEnumeration_range (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    Set.range (poolEnumeration eta heta a x) =
      Pool eta heta (fun b => fullSeeds eta heta b x) a :=
  (enumerateValues_range _ _ (poolPartialList_range_infinite eta heta a x)).trans
    (poolPartialList_range eta heta a x)

def poolEnumerationEquiv (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    ℕ ≃ Pool eta heta (fun b => fullSeeds eta heta b x) a :=
  Equiv.ofBijective
    (fun n => ⟨poolEnumeration eta heta a x n,(poolEnumeration_range eta heta a x).le ⟨n,rfl⟩⟩)
    ⟨fun _ _ h => poolEnumeration_injective eta heta a x (congrArg Subtype.val h),by
      intro u
      obtain ⟨n,hn⟩ := (poolEnumeration_range eta heta a x).symm.le u.property
      exact ⟨n,Subtype.ext hn⟩⟩

def poolEnumerationIndex (a : Ordinal.{0}) (x : (fsTower eta).Carrier) (k : ℕ) : ℕ :=
  Nat.nth (FirstOccurrence (fun n => poolPartialList eta heta a n x)) k

theorem measurable_poolEnumerationIndex (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) (k : ℕ) :
    Measurable (fun x => poolEnumerationIndex eta heta a x k) := by
  apply measurable_nat_nth
  · intro n
    apply measurableSet_firstOccurrence
    · intro m
      exact (poolCodes_borel eta heta a ha).absent (poolCodeList eta heta a m)
    · intro m n
      exact ((poolCodes_borel eta heta a ha).equal
        (poolCodeList eta heta a m) (poolCodeList eta heta a n)).preimage
        (measurable_id.prodMk measurable_id)
  · intro x
    exact firstOccurrence_infinite (extraAtom 0) _ (poolPartialList_range_infinite eta heta a x)

theorem poolEnumerationIndex_value (a : Ordinal.{0}) (x : (fsTower eta).Carrier) (k : ℕ) :
    poolPartialList eta heta a (poolEnumerationIndex eta heta a x k) x =
      some (poolEnumeration eta heta a x k) := by
  have hgood := Nat.nth_mem_of_infinite
    (firstOccurrence_infinite (extraAtom 0) _ (poolPartialList_range_infinite eta heta a x)) k
  cases h : poolPartialList eta heta a (poolEnumerationIndex eta heta a x k) x with
  | none => exact False.elim (hgood.1 h)
  | some z => simp only [poolEnumeration,enumerateValues,poolEnumerationIndex] at *
              simp only [h,Option.getD_some]

end FSCofinality.CosetConstruction
