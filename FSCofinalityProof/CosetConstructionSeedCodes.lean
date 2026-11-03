import FSCofinalityProof.CosetConstructionSeeds
import FSCofinalityProof.CosetConstructionSourceBorel

noncomputable section
open Set MeasureTheory Ordinal

namespace FSCofinality.CosetConstruction
open RawObjects

abbrev SeedIndex := Option (List ℕ)
variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- A countable, input-independent code list for the actual source seeds.
The empty index denotes the one top source seed, not a missing invariant. -/
def evalSeed (a : Ordinal.{0}) (s : SeedIndex) (x : (fsTower eta).Carrier) :
    Option (Ambient eta heta) :=
  match s with
  | none => if a = Frame.top eta then some (topSource eta heta x) else none
  | some p => if (sourcePath eta p).rank = a then sourcePathValue eta heta p x else none

theorem evalSeed_covers (a : Ordinal.{0}) (x : (fsTower eta).Carrier) (u : Ambient eta heta) :
    u ∈ fullSeeds eta heta a x ↔ ∃ s : SeedIndex, evalSeed eta heta a s x = some u := by
  constructor
  · intro hu
    by_cases ha : a = Frame.top eta
    · have heq : u = topSource eta heta x := by simpa only [fullSeeds,if_pos ha,mem_singleton_iff] using hu
      exact ⟨none,by simp [evalSeed,ha,heq]⟩
    · rw [fullSeeds,if_neg ha] at hu
      obtain ⟨p,hp,hvalue⟩ := hu
      exact ⟨some p,by simp only [evalSeed,if_pos hp,hvalue]⟩
  · rintro ⟨s,hs⟩
    cases s with
    | none =>
      by_cases ha : a = Frame.top eta
      · have heq : topSource eta heta x = u := by simpa only [evalSeed,if_pos ha,Option.some.injEq] using hs
        simp [fullSeeds,ha,← heq]
      · simp [evalSeed,ha] at hs
    | some p =>
      by_cases hp : (sourcePath eta p).rank = a
      · have hv : sourcePathValue eta heta p x = some u := by simpa only [evalSeed,if_pos hp] using hs
        exact sourceSeeds_subset_fullSeeds eta heta a x ⟨p,hp,hv⟩
      · simp [evalSeed,hp] at hs

theorem measurableSet_sourcePath_absent (p : List ℕ) :
    MeasurableSet {x : (fsTower eta).Carrier | sourcePathValue eta heta p x = none} := by
  have h := (measurableSet_optionalTranslate_eq eta heta (sourcePath eta p).rank).preimage
    ((sourcePath eta p).measurable_get.prodMk
      (measurable_const : Measurable (fun _ : (fsTower eta).Carrier =>
        (Sum.inl () : Unit ⊕ (fsTower (sourcePath eta p).rank).Carrier))))
  convert h using 1

theorem measurableSet_evalSeed_absent (a : Ordinal.{0}) (s : SeedIndex) :
    MeasurableSet {x : (fsTower eta).Carrier | evalSeed eta heta a s x = none} := by
  cases s with
  | none =>
    by_cases ha : a = Frame.top eta <;> simp [evalSeed,ha]
  | some p =>
    by_cases hp : (sourcePath eta p).rank = a
    · simpa only [evalSeed,if_pos hp] using measurableSet_sourcePath_absent eta heta p
    · simp [evalSeed,hp]

theorem measurableSet_evalSeed_eq (a : Ordinal.{0}) (s t : SeedIndex) :
    MeasurableSet {xy : (fsTower eta).Carrier × (fsTower eta).Carrier |
      evalSeed eta heta a s xy.1 = evalSeed eta heta a t xy.2} := by
  cases s with
  | none =>
    cases t with
    | none =>
      by_cases ha : a = Frame.top eta
      · have h := (regular_fsTower eta).measurable_graph
        convert h using 1
        ext xy
        simp only [evalSeed,if_pos ha,Option.some.injEq,topSource_eq_iff]
      · simp [evalSeed,ha]
    | some q =>
      by_cases ha : a = Frame.top eta
      · have hq : (sourcePath eta q).rank ≠ a := by
          intro h
          have hle := (sourcePath eta q).rank_le
          rw [h,ha] at hle
          exact not_le_of_gt (Frame.lt_top eta) hle
        simp only [evalSeed,if_pos ha,if_neg hq]
        simp
      · have h := (measurableSet_evalSeed_absent eta heta a (some q)).preimage
          (measurable_snd : Measurable (fun xy : (fsTower eta).Carrier × (fsTower eta).Carrier => xy.2))
        convert h using 1
        ext xy
        simp only [Set.mem_setOf_eq,Set.mem_preimage,evalSeed,if_neg ha]
        exact eq_comm
  | some p =>
    cases t with
    | none =>
      by_cases ha : a = Frame.top eta
      · have hp : (sourcePath eta p).rank ≠ a := by
          intro h
          have hle := (sourcePath eta p).rank_le
          rw [h,ha] at hle
          exact not_le_of_gt (Frame.lt_top eta) hle
        simp only [evalSeed,if_pos ha,if_neg hp]
        simp
      · have h := (measurableSet_evalSeed_absent eta heta a (some p)).preimage
          (measurable_fst : Measurable (fun xy : (fsTower eta).Carrier × (fsTower eta).Carrier => xy.1))
        convert h using 1
        ext xy
        simp only [Set.mem_setOf_eq,Set.mem_preimage,evalSeed,if_neg ha]
    | some q =>
      by_cases hp : (sourcePath eta p).rank = a
      · by_cases hq : (sourcePath eta q).rank = a
        · simpa only [evalSeed,if_pos hp,if_pos hq] using
            measurableSet_sourcePathValue_eq eta heta p q (hp.trans hq.symm)
        · have h := (measurableSet_evalSeed_absent eta heta a (some p)).preimage
            (measurable_fst : Measurable (fun xy : (fsTower eta).Carrier × (fsTower eta).Carrier => xy.1))
          simpa only [evalSeed,if_neg hq] using h
      · have h := (measurableSet_evalSeed_absent eta heta a (some q)).preimage
          (measurable_snd : Measurable (fun xy : (fsTower eta).Carrier × (fsTower eta).Carrier => xy.2))
        convert h using 1
        ext xy
        simp only [Set.mem_setOf_eq,Set.mem_preimage,evalSeed,if_neg hp]
        exact eq_comm

end FSCofinality.CosetConstruction
