import FSCofinalityProof.CosetConstructionSeedShapes
import FSCofinalityProof.CosetConstructionFiniteEval

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- A concrete countable collection of partial names for the actual semantic
pool. The absence value discards failed source paths instead of adding padding
objects to the pool. -/
structure PoolCodes (a : Ordinal.{0}) where
  Code : Type
  countable : Countable Code
  value : Code → (fsTower eta).Carrier → Option (Ambient eta heta)
  seed : SeedIndex → Code
  value_seed : ∀ s x, value (seed s) x = evalSeed eta heta a s x
  covers : ∀ x u, (∃ c, value c x = some u) ↔
    u ∈ Pool eta heta (fun b => fullSeeds eta heta b x) a

attribute [instance] PoolCodes.countable

def zeroPoolCodes : PoolCodes eta heta 0 where
  Code := SeedIndex ⊕ ℕ
  countable := inferInstance
  value := Sum.elim (evalSeed eta heta 0) (fun n _ => some (extraAtom n))
  seed := Sum.inl
  value_seed := fun _ _ => rfl
  covers := by
    intro x u
    rw [pool_zero]
    constructor
    · rintro ⟨c,hc⟩
      cases c with
      | inl s => exact Or.inl ((evalSeed_covers eta heta 0 x u).mpr ⟨s,hc⟩)
      | inr n => exact Or.inr ⟨n,Option.some.inj hc⟩
    · rintro (h|⟨n,rfl⟩)
      · obtain ⟨s,hs⟩ := (evalSeed_covers eta heta 0 x u).mp h
        exact ⟨.inl s,hs⟩
      · exact ⟨.inr n,rfl⟩

def successorPoolCodes (a : Ordinal.{0}) (lower : PoolCodes eta heta a) :
    PoolCodes eta heta (a+1) where
  Code := SeedIndex ⊕ Finset lower.Code
  countable := inferInstance
  value := Sum.elim (evalSeed eta heta (a+1)) (fun A x =>
    (liftFinite (extraAtom 0) (fun c => lower.value c x) A).map
      (finiteCollection (level eta (a+1))))
  seed := Sum.inl
  value_seed := fun _ _ => rfl
  covers := by
    intro x u
    rw [pool_add_one]
    constructor
    · rintro ⟨c,hc⟩
      cases c with
      | inl s => exact Or.inl ((evalSeed_covers eta heta (a+1) x u).mpr ⟨s,hc⟩)
      | inr A =>
        change (liftFinite (extraAtom 0) (fun c => lower.value c x) A).map _ = some u at hc
        cases hv : liftFinite (extraAtom 0) (fun c => lower.value c x) A with
        | none => simp only [hv,Option.map_none] at hc; contradiction
        | some B =>
          have hu : finiteCollection (level eta (a+1)) B = u := by
            simpa only [hv,Option.map_some,Option.some.injEq] using hc
          refine Or.inr ((mem_finiteImages_iff _ _ _).mpr ⟨B,?_,hu⟩)
          intro z hz
          obtain ⟨c,_,hc⟩ := liftFinite_mem _ _ A B hv z hz
          exact (lower.covers x z).mp ⟨c,hc⟩
    · rintro (h|h)
      · obtain ⟨s,hs⟩ := (evalSeed_covers eta heta (a+1) x u).mp h
        exact ⟨.inl s,hs⟩
      · obtain ⟨B,hB,rfl⟩ := (mem_finiteImages_iff _ _ _).mp h
        obtain ⟨A,hA⟩ := liftFinite_covers (extraAtom 0) (fun c => lower.value c x) B
          (fun z hz => (lower.covers x z).mpr (hB z hz))
        exact ⟨.inr A,by simp only [Sum.elim_inr,hA,Option.map_some]⟩

def BirthCode (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) : Type :=
  Σ n : ℕ,
    (lower (Frame.q eta lam hlam n) (Frame.q_lt eta lam hlam n)).Code ⊕
      (Unit ⊕ (lower (Frame.rho eta lam hlam n) (Frame.rho_lt eta lam hlam n)).Code)

instance birthCode_countable (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) : Countable (BirthCode eta heta lam hlam lower) :=
  inferInstanceAs (Countable (Σ n : ℕ,
    (lower (Frame.q eta lam hlam n) (Frame.q_lt eta lam hlam n)).Code ⊕
      (Unit ⊕ (lower (Frame.rho eta lam hlam n) (Frame.rho_lt eta lam hlam n)).Code)))

def evalBirthCode (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b)
    (c : BirthCode eta heta lam hlam lower) (x : (fsTower eta).Carrier) :
    Option (ℕ × Ambient eta heta) :=
  match c with
  | ⟨n,.inl d⟩ =>
      ((lower _ (Frame.q_lt eta lam hlam n)).value d x).map
        (fun z => (n,dataColumn eta heta lam hlam n z))
  | ⟨n,.inr (.inl _)⟩ => some (n,markerColumn eta heta lam hlam n)
  | ⟨n,.inr (.inr d)⟩ =>
      ((lower _ (Frame.rho_lt eta lam hlam n)).value d x).map
        (fun z => (n,singleton (level eta (Frame.delta eta lam hlam n)) z))

theorem evalBirthCode_covers (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) (x : (fsTower eta).Carrier)
    (p : ℕ × Ambient eta heta) :
    (∃ c, evalBirthCode eta heta lam hlam lower c x = some p) ↔
      NewColumn eta heta lam hlam (fun b _ =>
        Pool eta heta (fun a => fullSeeds eta heta a x) b) p.1 p.2 := by
  rcases p with ⟨n,z⟩
  constructor
  · rintro ⟨⟨m,c⟩,hc⟩
    cases c with
    | inl d =>
      change ((lower _ (Frame.q_lt eta lam hlam m)).value d x).map _ = some (n,z) at hc
      cases hv : (lower _ (Frame.q_lt eta lam hlam m)).value d x with
      | none => simp only [hv,Option.map_none] at hc; contradiction
      | some u =>
        have hp : (m,dataColumn eta heta lam hlam m u) = (n,z) := by
          simpa only [hv,Option.map_some,Option.some.injEq] using hc
        cases hp
        exact Or.inl ⟨u,((lower _ _).covers x u).mp ⟨d,hv⟩,rfl⟩
    | inr c =>
      cases c with
      | inl unit =>
        have hp : (m,markerColumn eta heta lam hlam m) = (n,z) := Option.some.inj hc
        cases hp
        exact Or.inr (Or.inl rfl)
      | inr d =>
        change ((lower _ (Frame.rho_lt eta lam hlam m)).value d x).map _ = some (n,z) at hc
        cases hv : (lower _ (Frame.rho_lt eta lam hlam m)).value d x with
        | none => simp only [hv,Option.map_none] at hc; contradiction
        | some u =>
          have hp : (m,singleton (level eta (Frame.delta eta lam hlam m)) u) = (n,z) := by
            simpa only [hv,Option.map_some,Option.some.injEq] using hc
          cases hp
          exact Or.inr (Or.inr ⟨u,((lower _ _).covers x u).mp ⟨d,hv⟩,rfl⟩)
  · rintro (⟨u,hu,hz⟩|h|⟨u,hu,hz⟩)
    · change z = dataColumn eta heta lam hlam n u at hz
      obtain ⟨d,hd⟩ := ((lower _ (Frame.q_lt eta lam hlam n)).covers x u).mpr hu
      exact ⟨⟨n,.inl d⟩,by simp only [evalBirthCode,hd,Option.map_some,hz]⟩
    · change z = markerColumn eta heta lam hlam n at h
      rw [h]
      exact ⟨⟨n,.inr (.inl ())⟩,rfl⟩
    · change z = singleton (level eta (Frame.delta eta lam hlam n)) u at hz
      obtain ⟨d,hd⟩ := ((lower _ (Frame.rho_lt eta lam hlam n)).covers x u).mpr hu
      exact ⟨⟨n,.inr (.inr d)⟩,by simp only [evalBirthCode,hd,Option.map_some,hz]⟩

def limitPoolCodes (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) : PoolCodes eta heta lam where
  Code := SeedIndex ⊕ Finset (BirthCode eta heta lam hlam lower)
  countable := inferInstance
  value := Sum.elim (evalSeed eta heta lam) (fun A x =>
    (liftFinite (0,extraAtom 0) (fun c => evalBirthCode eta heta lam hlam lower c x) A).map
      (finiteFiller (level eta lam)))
  seed := Sum.inl
  value_seed := fun _ _ => rfl
  covers := by
    intro x u
    rw [pool_limit eta heta _ lam hlam]
    constructor
    · rintro ⟨c,hc⟩
      cases c with
      | inl s => exact Or.inl ((evalSeed_covers eta heta lam x u).mpr ⟨s,hc⟩)
      | inr A =>
        change (liftFinite (0,extraAtom 0) (fun c => evalBirthCode eta heta lam hlam lower c x) A).map _ = some u at hc
        cases hv : liftFinite (0,extraAtom 0) (fun c => evalBirthCode eta heta lam hlam lower c x) A with
        | none => simp only [hv,Option.map_none] at hc; contradiction
        | some B =>
          have hu : finiteFiller (level eta lam) B = u := by
            simpa only [hv,Option.map_some,Option.some.injEq] using hc
          refine Or.inr ((mem_finiteImages_iff _ _ _).mpr ⟨B,?_,hu⟩)
          intro z hz
          obtain ⟨c,_,hc⟩ := liftFinite_mem _ _ A B hv z hz
          exact (evalBirthCode_covers eta heta lam hlam lower x z).mp ⟨c,hc⟩
    · rintro (h|h)
      · obtain ⟨s,hs⟩ := (evalSeed_covers eta heta lam x u).mp h
        exact ⟨.inl s,hs⟩
      · obtain ⟨B,hB,rfl⟩ := (mem_finiteImages_iff _ _ _).mp h
        obtain ⟨A,hA⟩ := liftFinite_covers (0,extraAtom 0)
          (fun c => evalBirthCode eta heta lam hlam lower c x) B
          (fun z hz => (evalBirthCode_covers eta heta lam hlam lower x z).mpr (hB z hz))
        exact ⟨.inr A,by simp only [Sum.elim_inr,hA,Option.map_some]⟩

def poolCodes (a : Ordinal.{0}) : PoolCodes eta heta a :=
  Ordinal.limitRecOn a (zeroPoolCodes eta heta)
    (successorPoolCodes eta heta) (limitPoolCodes eta heta)

theorem poolCodes_zero : poolCodes eta heta 0 = zeroPoolCodes eta heta := by
  unfold poolCodes
  rw [Ordinal.limitRecOn_zero]

theorem poolCodes_add_one (a : Ordinal.{0}) :
    poolCodes eta heta (a+1) = successorPoolCodes eta heta a (poolCodes eta heta a) := by
  unfold poolCodes
  rw [Ordinal.limitRecOn_add_one]

theorem poolCodes_limit (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    poolCodes eta heta lam = limitPoolCodes eta heta lam hlam (fun b _ => poolCodes eta heta b) := by
  unfold poolCodes
  rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]

end FSCofinality.CosetConstruction
