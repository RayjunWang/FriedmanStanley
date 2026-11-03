import FSCofinalityProof.GenericTablesBottom

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology

namespace FSCofinality.GenericTables.Bottom

abbrev ValidPattern := {P : Finset Request // Compatible P}

instance : Nonempty ValidPattern := ⟨⟨∅,by simp [Compatible]⟩⟩

def upperSolutions (P : ValidPattern) : Set ℕ :=
  {k | ∀ r ∈ P.val, genericTable (r.index k) = r.value}

theorem infinite_upperSolutions (P : ValidPattern) : (upperSolutions P).Infinite := by
  change ¬ (upperSolutions P).Finite
  intro hfin
  obtain ⟨N,hN⟩ := hfin.bddAbove
  obtain ⟨k,_,hk,hbits⟩ := genericTable_realizes P.val P.property (.inl ()) N
  exact not_lt_of_ge (hN hbits) hk

def patternEnumeration : ℕ → ValidPattern := Classical.choose (exists_surjective_nat ValidPattern)

theorem patternEnumeration_surjective : Function.Surjective patternEnumeration :=
  Classical.choose_spec (exists_surjective_nat ValidPattern)

def prefixTable : Table := Classical.choose
  (exists_generic (fun i => upperSolutions (patternEnumeration i))
    (fun i => infinite_upperSolutions _))

theorem prefixTable_generic : GenericOn
    (fun i => upperSolutions (patternEnumeration i)) prefixTable :=
  Classical.choose_spec (exists_generic (fun i => upperSolutions (patternEnumeration i))
    (fun i => infinite_upperSolutions _))

def zeroMatrix : BoolMatrix := ⟨0,0,fun i => Fin.elim0 i⟩

def fixedPrefix (k : ℕ) : List Bool :=
  List.ofFn (fun i : Fin k => prefixTable (0,zeroMatrix,i,k))

def bitRequest (s : List Bool) (i : Fin s.length) : Request :=
  ⟨0,zeroMatrix,true,i,s[i]⟩

def stringPattern (s : List Bool) : Finset Request := Finset.univ.image (bitRequest s)

theorem compatible_stringPattern (s : List Bool) : Compatible (stringPattern s) := by
  rintro r hr t ht hkey
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
  have hij : i = j := Fin.ext (by simpa [bitRequest,Request.key] using hkey)
  subst j
  rfl

theorem fixedPrefix_realizes (P : ValidPattern) (s : List Bool) (N : ℕ) :
    ∃ k > N, k ∈ upperSolutions P ∧ (fixedPrefix k).take s.length = s := by
  obtain ⟨i,hi⟩ := patternEnumeration_surjective P
  obtain ⟨k,hk,hN,hbits⟩ := prefixTable_generic (stringPattern s)
    (compatible_stringPattern s) i (max N s.length)
  refine ⟨k,lt_of_le_of_lt (le_max_left _ _) hN,?_,?_⟩
  · simpa only [hi] using hk
  · have hlen : s.length ≤ k := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
    apply List.ext_getElem
    · simp only [List.length_take,fixedPrefix,List.length_ofFn,Nat.min_eq_left hlen]
    · intro j hj hj'
      have hjk : j < k := lt_of_lt_of_le hj' hlen
      simp only [fixedPrefix,List.getElem_take,List.getElem_ofFn]
      have hb := hbits (bitRequest s ⟨j,hj'⟩)
        (Finset.mem_image.mpr ⟨⟨j,hj'⟩,Finset.mem_univ _,rfl⟩)
      exact hb

def coordinatedBeta (z : Cantor) (k : ℕ) : Cantor := beta fixedPrefix z k

theorem continuous_coordinatedBeta :
    Continuous (fun p : Cantor × ℕ => coordinatedBeta p.1 p.2) := continuous_beta _

theorem coordinatedBeta_injective :
    Function.Injective (fun p : Cantor × ℕ => coordinatedBeta p.1 p.2) := beta_injective _

theorem coordinatedBeta_finite_independence
    {ι : Type*} [Fintype ι] (p : ι → Cantor × ℕ) (hp : Function.Injective p)
    (epsilon : ι → Bool) (N : ℕ) :
    ∃ q > N, ∀ i, coordinatedBeta (p i).1 (p i).2 q = epsilon i :=
  beta_finite_independence _ p hp epsilon N

/-- The fixed raw context `z` is arbitrary. Every compatible upper pattern
and finite bottom bit pattern are realized by unboundedly many copy labels. -/
theorem upper_and_bottom_realization (z : Cantor) (P : ValidPattern)
    (s : List Bool) (N : ℕ) : ∃ k > N,
      k ∈ upperSolutions P ∧ bitsPrefix (coordinatedBeta z k) s.length = s := by
  obtain ⟨k,hk,hupper,hpref⟩ := fixedPrefix_realizes P s N
  refine ⟨k,hk,hupper,?_⟩
  have hlen : s.length ≤ (fixedPrefix k).length := by
    have hh := congrArg List.length hpref
    simp only [List.length_take] at hh
    omega
  apply List.ext_getElem
  · simp [bitsPrefix]
  · intro i hi hi'
    simp only [bitsPrefix,List.getElem_ofFn]
    have hh := congrArg (fun t : List Bool => t[i]?) hpref
    have hiK : i < (fixedPrefix k).length := lt_of_lt_of_le hi' hlen
    have hget : (fixedPrefix k)[i] = s[i] := by
      simpa only [List.getElem?_take,hi',if_true,List.getElem?_eq_getElem hiK,
        List.getElem?_eq_getElem hi',Option.some.injEq] using hh
    exact (beta_prefix fixedPrefix z k i hiK).trans hget

end FSCofinality.GenericTables.Bottom
