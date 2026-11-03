import FSCofinalityProof.CosetConstructionPoolCodes
import FSCofinalityProof.CosetConstructionFiniteBorel
import FSCofinalityProof.RawObjectsColumns

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

private theorem option_map_disjoint_eq_iff {A B Z : Type} (f : A → Z) (g : B → Z)
    (hfg : ∀ a b, f a ≠ g b) (u : Option A) (v : Option B) :
    u.map f = v.map g ↔ u = none ∧ v = none := by
  cases u <;> cases v <;> simp_all

private theorem option_map_ne_some {A Z : Type} (f : A → Z) (z : Z)
    (hf : ∀ a, f a ≠ z) (u : Option A) : u.map f ≠ some z := by
  cases u <;> simp_all

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b)

theorem measurableSet_evalBirthCode_none
    (hnone : ∀ b hb c, MeasurableSet {x | (lower b hb).value c x = none})
    (c : BirthCode eta heta lam hlam lower) :
    MeasurableSet {x | evalBirthCode eta heta lam hlam lower c x = none} := by
  rcases c with ⟨n,c⟩
  rcases c with c | ⟨⟨⟩⟩ | c
  · simpa only [evalBirthCode,option_map_none_iff] using hnone _ _ c
  · simp only [evalBirthCode,Option.some_ne_none,setOf_false]
    exact MeasurableSet.empty
  · simpa only [evalBirthCode,option_map_none_iff] using hnone _ _ c

private theorem evalBirthCode_some_index (c : BirthCode eta heta lam hlam lower)
    (x : (fsTower eta).Carrier) (p : ℕ × Ambient eta heta)
    (h : evalBirthCode eta heta lam hlam lower c x = some p) : p.1 = c.1 := by
  rcases c with ⟨n,c⟩
  rcases c with c | ⟨⟨⟩⟩ | c
  · change ((lower _ _).value c x).map _ = some p at h
    cases hv : (lower _ _).value c x with
    | none => simp only [hv,Option.map_none] at h; contradiction
    | some z =>
      have he : (n,dataColumn eta heta lam hlam n z) = p := by
        simpa only [hv,Option.map_some,Option.some.injEq] using h
      exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.fst (Option.some.inj h)).symm
  · change ((lower _ _).value c x).map _ = some p at h
    cases hv : (lower _ _).value c x with
    | none => simp only [hv,Option.map_none] at h; contradiction
    | some z =>
      have he : (n,singleton (level eta (Frame.delta eta lam hlam n)) z) = p := by
        simpa only [hv,Option.map_some,Option.some.injEq] using h
      exact (congrArg Prod.fst he).symm

theorem measurableSet_evalBirthCode_equal (htop : lam ≤ Frame.top eta)
    (hnone : ∀ b hb c, MeasurableSet {x | (lower b hb).value c x = none})
    (heq : ∀ b hb c d, MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      (lower b hb).value c p.1 = (lower b hb).value d p.2})
    (c d : BirthCode eta heta lam hlam lower) :
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      evalBirthCode eta heta lam hlam lower c p.1 =
        evalBirthCode eta heta lam hlam lower d p.2} := by
  rcases c with ⟨n,c⟩
  rcases d with ⟨m,d⟩
  by_cases hnm : n = m
  · subst m
    have hD : Function.Injective (fun z : Ambient eta heta =>
        (n,dataColumn eta heta lam hlam n z)) := by
      intro u v huv
      exact dataColumn_injective eta heta lam hlam htop n (congrArg Prod.snd huv)
    have hS : Function.Injective (fun z : Ambient eta heta =>
        (n,singleton (level eta (Frame.delta eta lam hlam n)) z)) := by
      intro u v huv
      exact (singleton_eq_iff _ _ _).mp (congrArg Prod.snd huv)
    have hDM (z : Ambient eta heta) :
        (n,dataColumn eta heta lam hlam n z) ≠ (n,markerColumn eta heta lam hlam n) :=
      fun h => dataColumn_ne_marker eta heta lam hlam htop n z (congrArg Prod.snd h)
    have hDS (u v : Ambient eta heta) :
        (n,dataColumn eta heta lam hlam n u) ≠
          (n,singleton (level eta (Frame.delta eta lam hlam n)) v) :=
      fun h => dataColumn_ne_singleton eta heta lam hlam htop n u v (congrArg Prod.snd h)
    have hMS (z : Ambient eta heta) :
        (n,markerColumn eta heta lam hlam n) ≠
          (n,singleton (level eta (Frame.delta eta lam hlam n)) z) :=
      fun h => markerColumn_ne_singleton eta heta lam hlam htop n z (congrArg Prod.snd h)
    rcases c with c | ⟨⟨⟩⟩ | c <;> rcases d with d | ⟨⟨⟩⟩ | d
    · simpa only [evalBirthCode,option_map_eq_iff_of_injective _ hD] using heq _ _ c d
    · simp only [evalBirthCode,option_map_ne_some _ _ hDM,setOf_false]
      exact MeasurableSet.empty
    · simpa only [evalBirthCode,option_map_disjoint_eq_iff _ _ hDS,setOf_and] using
        ((hnone _ _ c).preimage measurable_fst).inter ((hnone _ _ d).preimage measurable_snd)
    · have h : ∀ u, (n,markerColumn eta heta lam hlam n) ≠
          (n,dataColumn eta heta lam hlam n u) := fun u => (hDM u).symm
      have hfalse (p : (fsTower eta).Carrier × (fsTower eta).Carrier) :
          ¬ some (n,markerColumn eta heta lam hlam n) =
            ((lower _ _).value d p.2).map (fun z => (n,dataColumn eta heta lam hlam n z)) :=
        (option_map_ne_some _ _ hDM _).symm
      simpa only [evalBirthCode,hfalse,setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set ((fsTower eta).Carrier × (fsTower eta).Carrier)))
    · simp only [evalBirthCode,setOf_true]
      exact MeasurableSet.univ
    · have hfalse (p : (fsTower eta).Carrier × (fsTower eta).Carrier) :
          ¬ some (n,markerColumn eta heta lam hlam n) =
            ((lower _ _).value d p.2).map
              (fun z => (n,singleton (level eta (Frame.delta eta lam hlam n)) z)) :=
        (option_map_ne_some _ _ (fun z => (hMS z).symm) _).symm
      simpa only [evalBirthCode,hfalse,setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set ((fsTower eta).Carrier × (fsTower eta).Carrier)))
    · simpa only [evalBirthCode,
        option_map_disjoint_eq_iff _ _ (fun u v => (hDS v u).symm),setOf_and] using
        ((hnone _ _ c).preimage measurable_fst).inter ((hnone _ _ d).preimage measurable_snd)
    · simp only [evalBirthCode,option_map_ne_some _ _ (fun z => (hMS z).symm),setOf_false]
      exact MeasurableSet.empty
    · simpa only [evalBirthCode,option_map_eq_iff_of_injective _ hS] using heq _ _ c d
  · have hiff (p : (fsTower eta).Carrier × (fsTower eta).Carrier) :
        evalBirthCode eta heta lam hlam lower ⟨n,c⟩ p.1 =
          evalBirthCode eta heta lam hlam lower ⟨m,d⟩ p.2 ↔
        evalBirthCode eta heta lam hlam lower ⟨n,c⟩ p.1 = none ∧
          evalBirthCode eta heta lam hlam lower ⟨m,d⟩ p.2 = none := by
      constructor
      · intro h
        cases hc : evalBirthCode eta heta lam hlam lower ⟨n,c⟩ p.1 with
        | none => exact ⟨rfl,h.symm.trans hc⟩
        | some z =>
          have hd := h.symm.trans hc
          have hz := evalBirthCode_some_index eta heta lam hlam lower ⟨n,c⟩ p.1 z hc
          have hz' := evalBirthCode_some_index eta heta lam hlam lower ⟨m,d⟩ p.2 z hd
          exact False.elim (hnm (hz.symm.trans hz'))
      · rintro ⟨hc,hd⟩
        exact hc.trans hd.symm
    simpa only [hiff,setOf_and] using
      ((measurableSet_evalBirthCode_none eta heta lam hlam lower hnone ⟨n,c⟩).preimage measurable_fst).inter
        ((measurableSet_evalBirthCode_none eta heta lam hlam lower hnone ⟨m,d⟩).preimage measurable_snd)

end FSCofinality.CosetConstruction
