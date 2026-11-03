import FSCofinalityProof.CosetConstructionPoolBorel
import FSCofinalityProof.CosetConstructionBirthBorel

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem seed_limit_eq_mapFinite_iff {C : Type}
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (f : C → Option (ℕ × Ambient eta heta)) (A : Finset C) :
    evalSeed eta heta lam s x =
        (liftFinite (0,extraAtom 0) f A).map (finiteFiller (level eta lam)) ↔
      evalSeed eta heta lam s x = none ∧ liftFinite (0,extraAtom 0) f A = none := by
  constructor
  · intro h
    cases hs : evalSeed eta heta lam s x with
    | none =>
      refine ⟨rfl,?_⟩
      cases hF : liftFinite (0,extraAtom 0) f A with
      | none => rfl
      | some B => simp only [hs,hF,Option.map_some] at h; contradiction
    | some v =>
      cases hF : liftFinite (0,extraAtom 0) f A with
      | none => simp only [hs,hF,Option.map_none] at h; contradiction
      | some B =>
        have hv : v = finiteFiller (level eta lam) B := by
          simpa only [hs,hF,Option.map_some,Option.some.injEq] using h
        exact False.elim (evalSeed_limit_ne_filler eta heta lam hlam s x B (hs.trans (congrArg some hv)))
  · rintro ⟨hs,hF⟩
    simp only [hs,hF,Option.map_none]

theorem limitPoolCodes_borel (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) (htop : lam ≤ Frame.top eta)
    (hlower : ∀ b hb, PoolCodesBorel eta heta (lower b hb)) :
    PoolCodesBorel eta heta (limitPoolCodes eta heta lam hlam lower) where
  absent := by
    intro c
    cases c with
    | inl s => exact measurableSet_evalSeed_absent eta heta lam s
    | inr A =>
      change MeasurableSet {x | (liftFinite (0,extraAtom 0)
        (fun c => evalBirthCode eta heta lam hlam lower c x) A).map
        (finiteFiller (level eta lam)) = none}
      simpa only [option_map_none_iff] using
        measurableSet_liftFinite_none (0,extraAtom 0)
          (evalBirthCode eta heta lam hlam lower)
          (measurableSet_evalBirthCode_none eta heta lam hlam lower (fun b hb => (hlower b hb).absent)) A
  equal := by
    have hnone := measurableSet_evalBirthCode_none eta heta lam hlam lower
      (fun b hb => (hlower b hb).absent)
    have heq := measurableSet_evalBirthCode_equal eta heta lam hlam lower htop
      (fun b hb => (hlower b hb).absent) (fun b hb => (hlower b hb).equal)
    have hmix (s : SeedIndex) (A : Finset (BirthCode eta heta lam hlam lower)) :
        MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          evalSeed eta heta lam s p.1 =
            (liftFinite (0,extraAtom 0) (fun c => evalBirthCode eta heta lam hlam lower c p.2) A).map
              (finiteFiller (level eta lam))} := by
      simp only [seed_limit_eq_mapFinite_iff eta heta lam hlam,setOf_and]
      exact ((measurableSet_evalSeed_absent eta heta lam s).preimage measurable_fst).inter
        ((measurableSet_liftFinite_none (0,extraAtom 0)
          (evalBirthCode eta heta lam hlam lower) hnone A).preimage measurable_snd)
    intro c d
    cases c with
    | inl s =>
      cases d with
      | inl t => exact measurableSet_evalSeed_eq eta heta lam s t
      | inr A => exact hmix s A
    | inr A =>
      cases d with
      | inl s =>
        have h := (hmix s A).preimage (measurable_swap : Measurable (Prod.swap :
          (fsTower eta).Carrier × (fsTower eta).Carrier →
          (fsTower eta).Carrier × (fsTower eta).Carrier))
        simpa only [limitPoolCodes,Sum.elim_inl,Sum.elim_inr,Set.preimage_setOf_eq,
          Prod.swap,eq_comm] using h
      | inr B =>
        exact measurableSet_map_liftFinite_eq (0,extraAtom 0)
          (evalBirthCode eta heta lam hlam lower) (evalBirthCode eta heta lam hlam lower)
          hnone hnone heq A B (finiteFiller (level eta lam)) (finiteFiller_injective _)

theorem poolCodes_borel (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) :
    PoolCodesBorel eta heta (poolCodes eta heta a) := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    unfold poolCodes
    rw [Ordinal.limitRecOn_zero]
    exact zeroPoolCodes_borel eta heta
  | add_one a ih =>
    unfold poolCodes
    rw [Ordinal.limitRecOn_add_one]
    exact successorPoolCodes_borel eta heta a _ (ih ((show a ≤ a+1 from le_self_add).trans ha))
  | limit lam hlam ih =>
    unfold poolCodes
    rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]
    exact limitPoolCodes_borel eta heta lam hlam _ ha
      (fun b hb => ih b hb (hb.le.trans ha))

end FSCofinality.CosetConstruction
