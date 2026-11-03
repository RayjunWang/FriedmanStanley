import FSCofinalityProof.CosetConstructionSeedFinite

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- Only tests on the source code spaces are declared measurable. There is no
measurable-space instance on the semantic quotient of raw objects. -/
structure PoolCodesBorel {a : Ordinal.{0}} (P : PoolCodes eta heta a) : Prop where
  absent : ∀ c, MeasurableSet {x | P.value c x = none}
  equal : ∀ c d, MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
    P.value c p.1 = P.value d p.2}

theorem zeroPoolCodes_borel : PoolCodesBorel eta heta (zeroPoolCodes eta heta) where
  absent := by
    intro c
    cases c with
    | inl s => exact measurableSet_evalSeed_absent eta heta 0 s
    | inr n => simp only [zeroPoolCodes,Sum.elim_inr,reduceCtorEq,setOf_false]; exact MeasurableSet.empty
  equal := by
    intro c d
    cases c with
    | inl s =>
      cases d with
      | inl t => exact measurableSet_evalSeed_eq eta heta 0 s t
      | inr n =>
        change MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          evalSeed eta heta 0 s p.1 = some (extraAtom n)}
        convert MeasurableSet.empty using 1
        ext p
        exact iff_false_intro (evalSeed_zero_ne_extra eta heta s p.1 n)
    | inr n =>
      cases d with
      | inl s =>
        change MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          some (extraAtom n) = evalSeed eta heta 0 s p.2}
        convert MeasurableSet.empty using 1
        ext p
        exact iff_false_intro (fun h => evalSeed_zero_ne_extra eta heta s p.2 n h.symm)
      | inr m =>
        change MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          some (extraAtom n) = some (extraAtom m)}
        exact MeasurableSet.const _

theorem successorPoolCodes_borel (a : Ordinal.{0}) (lower : PoolCodes eta heta a)
    (hlower : PoolCodesBorel eta heta lower) :
    PoolCodesBorel eta heta (successorPoolCodes eta heta a lower) where
  absent := by
    intro c
    cases c with
    | inl s => exact measurableSet_evalSeed_absent eta heta (a+1) s
    | inr A =>
      change MeasurableSet {x | (liftFinite (extraAtom 0) (fun c => lower.value c x) A).map
        (finiteCollection (level eta (a+1))) = none}
      simpa only [option_map_none_iff] using
        measurableSet_liftFinite_none (extraAtom 0) lower.value hlower.absent A
  equal := by
    have hseed (s : SeedIndex) (c : lower.Code) :
        MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          evalSeed eta heta a s p.1 = lower.value c p.2} := by
      simpa only [lower.value_seed] using hlower.equal (lower.seed s) c
    intro c d
    cases c with
    | inl s =>
      cases d with
      | inl t => exact measurableSet_evalSeed_eq eta heta (a+1) s t
      | inr A =>
        exact measurableSet_seed_mapFinite_eq eta heta a s lower.value hlower.absent hseed A
    | inr A =>
      cases d with
      | inl s =>
        have h := (measurableSet_seed_mapFinite_eq eta heta a s lower.value hlower.absent hseed A).preimage
          (measurable_swap : Measurable (Prod.swap :
            (fsTower eta).Carrier × (fsTower eta).Carrier →
            (fsTower eta).Carrier × (fsTower eta).Carrier))
        simpa only [successorPoolCodes,Sum.elim_inl,Sum.elim_inr,Set.preimage_setOf_eq,
          Prod.swap,eq_comm] using h
      | inr B =>
        exact measurableSet_map_liftFinite_eq (extraAtom 0) lower.value lower.value
          hlower.absent hlower.absent hlower.equal A B
          (finiteCollection (level eta (a+1))) (finiteCollection_injective _)

end FSCofinality.CosetConstruction
