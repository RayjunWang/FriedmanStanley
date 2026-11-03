import FSCofinalityProof.CosetConstructionColumnCodes

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta) (n : ℕ)

def columnCodeList : ℕ → ColumnCode eta heta lam hlam n :=
  Classical.choose (exists_surjective_nat (ColumnCode eta heta lam hlam n))

theorem columnCodeList_surjective : Function.Surjective (columnCodeList eta heta lam hlam n) :=
  Classical.choose_spec (exists_surjective_nat (ColumnCode eta heta lam hlam n))

def columnPartialList (i : ℕ) (x : (fsTower eta).Carrier) : Option (Ambient eta heta) :=
  evalColumnCode eta heta lam hlam n (columnCodeList eta heta lam hlam n i) x

theorem columnPartialList_range (x : (fsTower eta).Carrier) :
    {u | ∃ i, columnPartialList eta heta lam hlam n i x = some u} =
      ColumnSet eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n := by
  ext u
  rw [← evalColumnCode_covers]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨_,hi⟩
  · rintro ⟨c,hc⟩
    obtain ⟨i,rfl⟩ := columnCodeList_surjective eta heta lam hlam n c
    exact ⟨i,hc⟩

theorem column_infinite (x : (fsTower eta).Carrier) :
    Infinite (Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) := by
  letI : Infinite (TokenModel.mainPool eta heta x (Frame.rho eta lam hlam n)) :=
    pool_infinite eta heta (fun b => fullSeeds eta heta b x) (Frame.rho eta lam hlam n)
  let f : TokenModel.mainPool eta heta x (Frame.rho eta lam hlam n) →
      Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n :=
    fun c => freshColumn eta heta lam hlam _ n (.inr (.inr c))
  apply Infinite.of_injective f
  intro c d h
  have he := congrArg (encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) h
  simp only [f,encodeColumn_fresh,encodeNew] at he
  exact Subtype.ext ((singleton_eq_iff _ _ _).mp he)

include htop

theorem columnPartialList_range_infinite (x : (fsTower eta).Carrier) :
    {u | ∃ i, columnPartialList eta heta lam hlam n i x = some u}.Infinite := by
  rw [columnPartialList_range]
  letI := column_infinite eta heta lam hlam n x
  exact Set.infinite_range_of_injective (encodeColumn_injective eta heta lam hlam _ htop n)

def columnEnumeration (x : (fsTower eta).Carrier) (k : ℕ) : Ambient eta heta :=
  enumerateValues (extraAtom 0) (fun i => columnPartialList eta heta lam hlam n i x) k

theorem columnEnumeration_injective (x : (fsTower eta).Carrier) :
    Function.Injective (columnEnumeration eta heta lam hlam n x) :=
  enumerateValues_injective _ _ (columnPartialList_range_infinite eta heta lam hlam htop n x)

theorem columnEnumeration_range (x : (fsTower eta).Carrier) :
    range (columnEnumeration eta heta lam hlam n x) =
      ColumnSet eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n :=
  (enumerateValues_range _ _ (columnPartialList_range_infinite eta heta lam hlam htop n x)).trans
    (columnPartialList_range eta heta lam hlam n x)

def columnEnumerationRaw (x : (fsTower eta).Carrier) (k : ℕ) :
    Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n :=
  ((columnEnumeration_range eta heta lam hlam htop n x).le ⟨k,rfl⟩).choose

theorem encodeColumn_columnEnumerationRaw (x : (fsTower eta).Carrier) (k : ℕ) :
    encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n
      (columnEnumerationRaw eta heta lam hlam htop n x k) = columnEnumeration eta heta lam hlam n x k :=
  ((columnEnumeration_range eta heta lam hlam htop n x).le ⟨k,rfl⟩).choose_spec

def columnEnumerationEquiv (x : (fsTower eta).Carrier) :
    ℕ ≃ Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n :=
  Equiv.ofBijective (columnEnumerationRaw eta heta lam hlam htop n x)
    ⟨by
      intro i j hij
      apply columnEnumeration_injective eta heta lam hlam htop n x
      exact (encodeColumn_columnEnumerationRaw eta heta lam hlam htop n x i).symm.trans
        ((congrArg (encodeColumn eta heta lam hlam _ n) hij).trans
          (encodeColumn_columnEnumerationRaw eta heta lam hlam htop n x j)),by
      intro c
      obtain ⟨k,hk⟩ := (columnEnumeration_range eta heta lam hlam htop n x).symm.le ⟨c,rfl⟩
      refine ⟨k,encodeColumn_injective eta heta lam hlam _ htop n ?_⟩
      exact (encodeColumn_columnEnumerationRaw eta heta lam hlam htop n x k).trans hk⟩

def columnEnumerationIndex (x : (fsTower eta).Carrier) (k : ℕ) : ℕ :=
  Nat.nth (FirstOccurrence (fun i => columnPartialList eta heta lam hlam n i x)) k

theorem measurable_columnEnumerationIndex (k : ℕ) :
    Measurable (fun x => columnEnumerationIndex eta heta lam hlam n x k) := by
  have hd : Frame.delta eta lam hlam n ≤ Frame.top eta := (Frame.delta_lt eta lam hlam n).le.trans htop
  apply measurable_nat_nth
  · intro i
    apply measurableSet_firstOccurrence
    · intro j
      exact measurableSet_codeRep_none eta heta _ hd
        (codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n j))
    · intro j k
      exact measurableSet_codeRep_eq_diagonal eta heta _ hd
        (codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n j))
        (codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n k))
  · intro x
    exact firstOccurrence_infinite (extraAtom 0) _ (columnPartialList_range_infinite eta heta lam hlam htop n x)

theorem columnEnumerationIndex_value (x : (fsTower eta).Carrier) (k : ℕ) :
    columnPartialList eta heta lam hlam n (columnEnumerationIndex eta heta lam hlam n x k) x =
      some (columnEnumeration eta heta lam hlam n x k) := by
  have hgood := Nat.nth_mem_of_infinite
    (firstOccurrence_infinite (extraAtom 0) _ (columnPartialList_range_infinite eta heta lam hlam htop n x)) k
  cases h : columnPartialList eta heta lam hlam n (columnEnumerationIndex eta heta lam hlam n x k) x with
  | none => exact False.elim (hgood.1 h)
  | some z =>
    simp only [columnEnumeration,enumerateValues,columnEnumerationIndex] at *
    simp only [h,Option.getD_some]

theorem measurableSet_codeRep_eq_columnEnumeration
    {F : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta (Frame.delta eta lam hlam n) F) (k : ℕ) :
    MeasurableSet {x | F x = some (columnEnumeration eta heta lam hlam n x k)} := by
  have hd : Frame.delta eta lam hlam n ≤ Frame.top eta := (Frame.delta_lt eta lam hlam n).le.trans htop
  have h := measurableSet_selected (fun i x => F x = columnPartialList eta heta lam hlam n i x)
    (fun i => measurableSet_codeRep_eq_diagonal eta heta _ hd hF
      (codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n i)))
    (fun x => columnEnumerationIndex eta heta lam hlam n x k)
    (measurable_columnEnumerationIndex eta heta lam hlam htop n k)
  simpa only [columnEnumerationIndex_value eta heta lam hlam htop n] using h

end FSCofinality.CosetConstruction
