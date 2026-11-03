import FSCofinalityProof.CosetConstructionPoolCodes
import FSCofinalityProof.CosetConstructionFiniteBorel

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem seed_eq_finiteCollection_iff {C : Type} (a : Ordinal.{0}) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (f : C → Option (Ambient eta heta)) (A : Finset C)
    (B : Finset (Ambient eta heta))
    (hB : liftFinite (extraAtom 0) f A = some B)
    (v : Ambient eta heta) (hv : evalSeed eta heta (a+1) s x = some v) :
    v = finiteCollection (level eta (a+1)) B ↔
      (∀ n, evalSeed eta heta a (childSeed s n) x = none ∨
        ∃ c ∈ A, evalSeed eta heta a (childSeed s n) x = f c) ∧
      (∀ c ∈ A, ∃ n, evalSeed eta heta a (childSeed s n) x = f c) := by
  have hnon (c) (hc : c ∈ A) : f c ≠ none := by
    unfold liftFinite at hB
    split_ifs at hB with h
    exact h c hc
  have hmem (u) : Member u v ↔ ∃ n, evalSeed eta heta a (childSeed s n) x = some u :=
    evalSeed_successor_member_all eta heta a s x v u hv
  constructor
  · intro heq
    constructor
    · intro n
      cases hn : evalSeed eta heta a (childSeed s n) x with
      | none => exact Or.inl rfl
      | some u =>
        have hu : Member u v := (hmem u).mpr ⟨n,hn⟩
        rw [heq,member_finiteCollection] at hu
        obtain ⟨c,hc,hfc⟩ := (liftFinite_mem_iff _ _ A B hB u).mp hu
        exact Or.inr ⟨c,hc,hfc.symm⟩
    · intro c hc
      cases hf : f c with
      | none => exact False.elim (hnon c hc hf)
      | some u =>
        have hu : u ∈ B := (liftFinite_mem_iff _ _ A B hB u).mpr ⟨c,hc,hf⟩
        have hm : Member u v := by simpa only [heq,member_finiteCollection] using hu
        exact (hmem u).mp hm
  · rintro ⟨hforward,hbackward⟩
    have hseed := (evalSeed_covers eta heta (a+1) x v).mpr ⟨s,hv⟩
    obtain ⟨z,hz⟩ := fullSeeds_successor_collection eta heta a x hseed
    obtain ⟨w,hw⟩ := finiteCollection_is_collection (level eta (a+1)) B
    rw [hz,hw]
    apply collection_ext
    intro u
    rw [←hz,←hw,member_finiteCollection,hmem,liftFinite_mem_iff _ _ A B hB u]
    constructor
    · rintro ⟨n,hn⟩
      rcases hforward n with hnnone|⟨c,hc,hfc⟩
      · rw [hn] at hnnone
        contradiction
      · exact ⟨c,hc,hfc.symm.trans hn⟩
    · rintro ⟨c,hc,hfc⟩
      obtain ⟨n,hn⟩ := hbackward c hc
      exact ⟨n,hn.trans hfc⟩

theorem seed_eq_mapFinite_iff {C : Type} (a : Ordinal.{0}) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (f : C → Option (Ambient eta heta)) (A : Finset C) :
    evalSeed eta heta (a+1) s x =
        (liftFinite (extraAtom 0) f A).map (finiteCollection (level eta (a+1))) ↔
      (evalSeed eta heta (a+1) s x = none ∧ liftFinite (extraAtom 0) f A = none) ∨
      (evalSeed eta heta (a+1) s x ≠ none ∧ liftFinite (extraAtom 0) f A ≠ none ∧
        (∀ n, evalSeed eta heta a (childSeed s n) x = none ∨
          ∃ c ∈ A, evalSeed eta heta a (childSeed s n) x = f c) ∧
        (∀ c ∈ A, ∃ n, evalSeed eta heta a (childSeed s n) x = f c)) := by
  cases hv : evalSeed eta heta (a+1) s x with
  | none => cases hB : liftFinite (extraAtom 0) f A <;> simp [hB]
  | some v =>
    cases hB : liftFinite (extraAtom 0) f A with
    | none => simp
    | some B =>
      simp only [Option.map_some,Option.some.injEq,reduceCtorEq,false_and,false_or,
        Option.some_ne_none,not_false_eq_true,true_and]
      have hh := seed_eq_finiteCollection_iff eta heta a s x f A B hB v hv
      constructor
      · intro h
        refine ⟨?_,?_,hh.mp h⟩
        · intro hn
          cases hn
        · intro hn
          cases hn
      · intro h
        exact hh.mpr h.2.2

theorem measurableSet_seed_mapFinite_eq {C : Type} [Countable C]
    (a : Ordinal.{0}) (s : SeedIndex)
    (F : C → (fsTower eta).Carrier → Option (Ambient eta heta))
    (hnone : ∀ c, MeasurableSet {x | F c x = none})
    (heq : ∀ t c, MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      evalSeed eta heta a t p.1 = F c p.2}) (A : Finset C) :
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      evalSeed eta heta (a+1) s p.1 =
        (liftFinite (extraAtom 0) (fun c => F c p.2) A).map
          (finiteCollection (level eta (a+1)))} := by
  simp only [seed_eq_mapFinite_iff,setOf_or,setOf_and]
  have hsource := (measurableSet_evalSeed_absent eta heta (a+1) s).preimage
    (measurable_fst : Measurable (fun p : (fsTower eta).Carrier × (fsTower eta).Carrier => p.1))
  have hfinite := (measurableSet_liftFinite_none (extraAtom 0) F hnone A).preimage
    (measurable_snd : Measurable (fun p : (fsTower eta).Carrier × (fsTower eta).Carrier => p.2))
  apply (hsource.inter hfinite).union
  refine hsource.compl.inter (hfinite.compl.inter ?_)
  apply MeasurableSet.inter
  · simp only [setOf_forall,setOf_or,← exists_prop,setOf_exists]
    exact MeasurableSet.iInter (fun n =>
      ((measurableSet_evalSeed_absent eta heta a (childSeed s n)).preimage
        (measurable_fst : Measurable (fun p : (fsTower eta).Carrier × (fsTower eta).Carrier => p.1))).union
        (MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ => heq (childSeed s n) c))))
  · simp only [setOf_forall,setOf_exists]
    exact MeasurableSet.iInter (fun c => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iUnion (fun n => heq (childSeed s n) c)))

end FSCofinality.CosetConstruction
