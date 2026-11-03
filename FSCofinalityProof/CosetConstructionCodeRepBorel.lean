import FSCofinalityProof.CosetConstructionCodeOperations
import FSCofinalityProof.CosetConstructionPoolEnumeration
import FSCofinalityProof.CosetConstructionSelectionBorel

noncomputable section
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem measurableSet_codeRep_none (a : Ordinal.{0}) (ha : a ≤ Frame.top eta)
    {F : (fsTower eta).Carrier → Option (Ambient eta heta)} (hF : CodeRep eta heta a F) :
    MeasurableSet {x | F x = none} := by
  obtain ⟨c,hc⟩ := hF
  simpa only [hc] using (poolCodes_borel eta heta a ha).absent c

theorem measurableSet_codeRep_eq (a : Ordinal.{0}) (ha : a ≤ Frame.top eta)
    {F G : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta a F) (hG : CodeRep eta heta a G) :
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier | F p.1 = G p.2} := by
  obtain ⟨c,hc⟩ := hF
  obtain ⟨d,hd⟩ := hG
  simpa only [hc,hd] using (poolCodes_borel eta heta a ha).equal c d

theorem measurableSet_codeRep_eq_diagonal (a : Ordinal.{0}) (ha : a ≤ Frame.top eta)
    {F G : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta a F) (hG : CodeRep eta heta a G) :
    MeasurableSet {x : (fsTower eta).Carrier | F x = G x} :=
  (measurableSet_codeRep_eq eta heta a ha hF hG).preimage (measurable_id.prodMk measurable_id)

theorem measurableSet_codeRep_eq_poolEnumeration (a : Ordinal.{0}) (ha : a ≤ Frame.top eta)
    {F : (fsTower eta).Carrier → Option (Ambient eta heta)} (hF : CodeRep eta heta a F) (k : ℕ) :
    MeasurableSet {x : (fsTower eta).Carrier | F x = some (poolEnumeration eta heta a x k)} := by
  have h := measurableSet_selected (fun n x => F x = poolPartialList eta heta a n x)
    (fun n => measurableSet_codeRep_eq_diagonal eta heta a ha hF
      (codeRep_value eta heta a (poolCodeList eta heta a n)))
    (fun x => poolEnumerationIndex eta heta a x k)
    (measurable_poolEnumerationIndex eta heta a ha k)
  simpa only [poolEnumerationIndex_value] using h

end FSCofinality.CosetConstruction
