import FSCofinalityProof.CosetConstructionCodeOperations

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def seedCoordinate (lam : Ordinal.{0}) (s : SeedIndex) (n : ℕ)
    (x : (fsTower eta).Carrier) : Option (Ambient eta heta) :=
  match s with
  | none => if lam = Frame.top eta then some (topCoordinates eta heta x n) else none
  | some p => if (sourcePath eta p).rank = lam then sourcePathValue eta heta (n::p) x else none

theorem sourcePathValue_child (p : List ℕ) (x : (fsTower eta).Carrier)
    (y : (fsTower (sourcePath eta p).rank).Carrier)
    (hy : (sourcePath eta p).get x = .inr y) (n : ℕ) :
    sourcePathValue eta heta (n::p) x = codeChildValue eta heta (sourcePath eta p).rank n y := by
  simp only [sourcePathValue,sourcePath,Function.comp_apply,hy,Sum.elim_inr,codeChildValue]

theorem codeRep_seedCoordinate (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (s : SeedIndex) (n : ℕ) :
    CodeRep eta heta (Frame.q eta lam hlam n) (seedCoordinate eta heta lam s n) := by
  cases s with
  | none =>
    by_cases ha : lam = Frame.top eta
    · subst lam
      rw [Frame.q_top]
      by_cases hn : n = 0
      · subst n
        simp only [Nat.cast_zero,add_zero]
        apply codeRep_congr eta heta eta (codeRep_seed eta heta eta (some []))
        intro x
        simp [seedCoordinate,topCoordinates,evalSeed,sourcePath,sourcePathValue,optionalTranslate]
      · apply codeRep_congr eta heta (eta+n)
          (codeRep_tag eta heta (eta+n) (eta_add_nat_le_top eta n) 4)
        intro x
        simp [seedCoordinate,topCoordinates,hn]
    · apply codeRep_congr eta heta _ (codeRep_none eta heta _)
      intro x
      simp only [seedCoordinate,if_neg ha]
  | some p =>
    by_cases hp : (sourcePath eta p).rank = lam
    · have hle : lam ≤ eta := hp ▸ (sourcePath eta p).rank_le
      have hq : Frame.q eta lam hlam n = fundamentalSequence lam hlam n :=
        congrFun (Frame.q_of_le_source eta lam hlam hle) n
      have hchild : (sourcePath eta (n::p)).rank = Frame.q eta lam hlam n := by
        change (codeChildren (sourcePath eta p).rank).rank n = _
        rw [hp,codeChildren_limit_rank,hq]
      apply codeRep_congr eta heta _ (codeRep_seed eta heta _ (some (n::p)))
      intro x
      simp only [evalSeed,if_pos hchild,seedCoordinate,if_pos hp]
    · apply codeRep_congr eta heta _ (codeRep_none eta heta _)
      intro x
      simp only [seedCoordinate,if_neg hp]

theorem seedCoordinate_absent_iff (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (s : SeedIndex) (n : ℕ) (x : (fsTower eta).Carrier) :
    seedCoordinate eta heta lam s n x = none ↔ evalSeed eta heta lam s x = none := by
  cases s with
  | none => by_cases ha : lam = Frame.top eta <;> simp [seedCoordinate,evalSeed,ha]
  | some p =>
    by_cases hp : (sourcePath eta p).rank = lam
    · simp only [seedCoordinate,evalSeed,if_pos hp]
      cases hy : (sourcePath eta p).get x with
      | inl unit => simp [sourcePathValue,sourcePath,optionalTranslate,hy]
      | inr y =>
        obtain ⟨z,hz,hchildren⟩ := limit_value_children eta heta _ lam hp hlam y
        rw [sourcePathValue_child eta heta p x y hy n,(hchildren n).1]
        simp [sourcePathValue,optionalTranslate,hy]
    · simp only [seedCoordinate,evalSeed,if_neg hp]

theorem seedCoordinate_source (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (s : SeedIndex) (n : ℕ) (x : (fsTower eta).Carrier) (z : ℕ → Ambient eta heta)
    (hv : evalSeed eta heta lam s x = some (sourceSequence (level eta lam) z)) :
    seedCoordinate eta heta lam s n x = some (z n) := by
  cases s with
  | none =>
    by_cases ha : lam = Frame.top eta
    · have heq : topSource eta heta x = sourceSequence (level eta lam) z := by
        simpa only [evalSeed,if_pos ha,Option.some.injEq] using hv
      have hz : topCoordinates eta heta x = z :=
        sourceSequence_injective (level eta lam) (by simpa only [topSource,←ha] using heq)
      simp only [seedCoordinate,if_pos ha,hz]
    · simp only [evalSeed,if_neg ha] at hv
      contradiction
  | some p =>
    have hp : (sourcePath eta p).rank = lam := by
      by_contra h
      simp only [evalSeed,if_neg h] at hv
      contradiction
    have hvalue : sourcePathValue eta heta p x = some (sourceSequence (level eta lam) z) := by
      simpa only [evalSeed,if_pos hp] using hv
    unfold sourcePathValue optionalTranslate at hvalue
    split at hvalue
    · contradiction
    · rename_i y hy
      obtain ⟨w,hw,hchildren⟩ := limit_value_children eta heta _ lam hp hlam y
      have hwz : w = z := sourceSequence_injective (level eta lam)
        (hw.symm.trans (Option.some.inj hvalue))
      simp only [seedCoordinate,if_pos hp,sourcePathValue_child eta heta p x y hy n,
        (hchildren n).1,hwz]

end FSCofinality.CosetConstruction
