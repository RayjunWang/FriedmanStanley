import FSCofinalityProof.CosetConstructionPoolEnumeration
import FSCofinalityProof.CosetConstructionSelectionBorel

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def OptionalMember (col row : Option (Ambient eta heta)) : Prop :=
  match col,row with
  | some c,some r => Member c r
  | _,_ => False

theorem optionalMember_seed_iff (a : Ordinal.{0}) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (col : Option (Ambient eta heta)) :
    OptionalMember eta heta col (evalSeed eta heta (a+1) s x) ↔
      evalSeed eta heta (a+1) s x ≠ none ∧ col ≠ none ∧
        ∃ n, evalSeed eta heta a (childSeed s n) x = col := by
  cases hr : evalSeed eta heta (a+1) s x with
  | none => simp [OptionalMember]
  | some v =>
    cases hc : col with
    | none => simp [OptionalMember]
    | some u =>
      simpa [OptionalMember] using evalSeed_successor_member_all eta heta a s x v u hr

theorem optionalMember_finite_iff {C : Type}
    (a : Ordinal.{0}) (F : C → Option (Ambient eta heta)) (A : Finset C)
    (col : Option (Ambient eta heta)) :
    OptionalMember eta heta col
        ((liftFinite (extraAtom 0) F A).map (finiteCollection (level eta (a+1)))) ↔
      liftFinite (extraAtom 0) F A ≠ none ∧ col ≠ none ∧
        ∃ c ∈ A, F c = col := by
  cases hF : liftFinite (extraAtom 0) F A with
  | none => simp [OptionalMember]
  | some B =>
    cases hc : col with
    | none => simp [OptionalMember]
    | some u =>
      simpa [OptionalMember,member_finiteCollection] using liftFinite_mem_iff _ F A B hF u

theorem measurableSet_optionalMember_successorCodes (a : Ordinal.{0})
    (lower : PoolCodes eta heta a) (hlower : PoolCodesBorel eta heta lower)
    (row : (successorPoolCodes eta heta a lower).Code) (col : lower.Code) :
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      OptionalMember eta heta (lower.value col p.2)
        ((successorPoolCodes eta heta a lower).value row p.1)} := by
  cases row with
  | inl s =>
    simp only [successorPoolCodes,Sum.elim_inl,optionalMember_seed_iff,setOf_and,setOf_exists]
    refine ((measurableSet_evalSeed_absent eta heta (a+1) s).preimage measurable_fst).compl.inter
      (((hlower.absent col).preimage measurable_snd).compl.inter ?_)
    exact MeasurableSet.iUnion (fun n => by
      simpa only [lower.value_seed] using hlower.equal (lower.seed (childSeed s n)) col)
  | inr A =>
    simp only [successorPoolCodes,Sum.elim_inr,optionalMember_finite_iff,setOf_and]
    refine ((measurableSet_liftFinite_none (extraAtom 0) lower.value hlower.absent A).preimage
      measurable_fst).compl.inter (((hlower.absent col).preimage measurable_snd).compl.inter ?_)
    simp only [← exists_prop,setOf_exists]
    exact MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ => hlower.equal c col))

theorem measurableSet_optionalMember_poolCodes (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) :
    ∀ (row : (poolCodes eta heta (a+1)).Code) (col : (poolCodes eta heta a).Code),
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      OptionalMember eta heta ((poolCodes eta heta a).value col p.2)
        ((poolCodes eta heta (a+1)).value row p.1)} := by
  rw [poolCodes_add_one]
  exact measurableSet_optionalMember_successorCodes eta heta a _ (poolCodes_borel eta heta a ha)

theorem measurableSet_member_poolEnumeration (a : Ordinal.{0})
    (ha : a+1 ≤ Frame.top eta) (i j : ℕ) :
    MeasurableSet {x : (fsTower eta).Carrier |
      Member (poolEnumeration eta heta a x j) (poolEnumeration eta heta (a+1) x i)} := by
  have hsmall : a ≤ Frame.top eta := (show a ≤ a+1 from le_self_add).trans ha
  have hcodes (r c : ℕ) : MeasurableSet {x : (fsTower eta).Carrier |
      OptionalMember eta heta (poolPartialList eta heta a c x)
        (poolPartialList eta heta (a+1) r x)} :=
    (measurableSet_optionalMember_poolCodes eta heta a hsmall
      (poolCodeList eta heta (a+1) r) (poolCodeList eta heta a c)).preimage
      (measurable_id.prodMk measurable_id)
  have h := measurableSet_selected₂ (fun r c x =>
    OptionalMember eta heta (poolPartialList eta heta a c x) (poolPartialList eta heta (a+1) r x))
    hcodes (fun x => poolEnumerationIndex eta heta (a+1) x i)
    (fun x => poolEnumerationIndex eta heta a x j)
    (measurable_poolEnumerationIndex eta heta (a+1) ha i)
    (measurable_poolEnumerationIndex eta heta a hsmall j)
  simpa only [poolEnumerationIndex_value,OptionalMember] using h

end FSCofinality.CosetConstruction
