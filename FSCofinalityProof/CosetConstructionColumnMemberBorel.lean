import FSCofinalityProof.CosetConstructionMemberBorel
import FSCofinalityProof.CosetConstructionColumnEnumeration

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem measurableSet_member_codeRep_poolEnumeration (a : Ordinal.{0})
    (ha : a ≤ Frame.top eta) {F : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta (a+1) F) (j : ℕ) :
    MeasurableSet {x | OptionalMember eta heta (some (poolEnumeration eta heta a x j)) (F x)} := by
  obtain ⟨r,hr⟩ := hF
  have hcodes (c : ℕ) : MeasurableSet {x : (fsTower eta).Carrier |
      OptionalMember eta heta (poolPartialList eta heta a c x) (F x)} := by
    have h := (measurableSet_optionalMember_poolCodes eta heta a ha r
      (poolCodeList eta heta a c)).preimage (measurable_id.prodMk measurable_id)
    simpa only [hr] using h
  have h := measurableSet_selected (fun c x =>
    OptionalMember eta heta (poolPartialList eta heta a c x) (F x)) hcodes
    (fun x => poolEnumerationIndex eta heta a x j)
    (measurable_poolEnumerationIndex eta heta a ha j)
  simpa only [poolEnumerationIndex_value] using h

theorem measurableSet_member_column_poolEnumeration (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (n i j : ℕ) :
    MeasurableSet {x : (fsTower eta).Carrier |
      Member (poolEnumeration eta heta (Frame.rho eta lam hlam n) x j)
        (columnEnumeration eta heta lam hlam n x i)} := by
  have hr : Frame.rho eta lam hlam n ≤ Frame.top eta := (Frame.rho_lt eta lam hlam n).le.trans htop
  have hcodes (c : ℕ) : MeasurableSet {x : (fsTower eta).Carrier |
      OptionalMember eta heta (some (poolEnumeration eta heta (Frame.rho eta lam hlam n) x j))
        (columnPartialList eta heta lam hlam n c x)} := by
    apply measurableSet_member_codeRep_poolEnumeration eta heta _ hr
    have hc := codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n c)
    simpa only [Frame.rho,Frame.delta,add_assoc,one_add_one_eq_two] using hc
  have h := measurableSet_selected (fun c x =>
    OptionalMember eta heta (some (poolEnumeration eta heta (Frame.rho eta lam hlam n) x j))
      (columnPartialList eta heta lam hlam n c x)) hcodes
    (fun x => columnEnumerationIndex eta heta lam hlam n x i)
    (measurable_columnEnumerationIndex eta heta lam hlam htop n i)
  simpa only [columnEnumerationIndex_value eta heta lam hlam htop n,OptionalMember] using h

end FSCofinality.CosetConstruction
