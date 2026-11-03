import FSCofinalityProof.CosetConstructionSeedCodes

noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem translate_zero (x : (fsTower 0).Carrier) :
    translate eta heta 0 x = sourceAtom (cast (congrArg CodedRelation.Carrier fsTower_zero) x) := by
  unfold translate sourceStage
  rw [Ordinal.limitRecOn_zero,SourceRealization.transport_value]
  rfl

theorem evalSeed_zero_source (s : SeedIndex) (x : (fsTower eta).Carrier)
    (v : Ambient eta heta) (hv : evalSeed eta heta 0 s x = some v) :
    ∃ r, v = sourceAtom r := by
  cases s with
  | none =>
    have ht : (0 : Ordinal.{0}) ≠ Frame.top eta :=
      ne_of_lt (lt_of_le_of_lt zero_le (Frame.lt_top eta))
    simp only [evalSeed,if_neg ht] at hv
    contradiction
  | some p =>
    have hp : (sourcePath eta p).rank = 0 := by
      by_contra h
      simp only [evalSeed,if_neg h] at hv
      contradiction
    have hvalue : sourcePathValue eta heta p x = some v := by
      simpa only [evalSeed,if_pos hp] using hv
    unfold sourcePathValue optionalTranslate at hvalue
    split at hvalue
    · contradiction
    · rename_i y hy
      cases hvalue
      have haux (b : Ordinal.{0}) (hb : b = 0) (y : (fsTower b).Carrier) :
          ∃ r, translate eta heta b y = sourceAtom r := by
        subst b
        exact ⟨_,translate_zero eta heta y⟩
      exact haux _ hp y

theorem evalSeed_zero_ne_extra (s : SeedIndex) (x : (fsTower eta).Carrier) (n : ℕ) :
    evalSeed eta heta 0 s x ≠ some (extraAtom n) := by
  intro hv
  obtain ⟨r,hr⟩ := evalSeed_zero_source eta heta s x _ hv
  exact sourceAtom_ne_extraAtom r n hr.symm

theorem successor_member_iff_child (b a : Ordinal.{0}) (hb : b = a+1)
    (y : (fsTower b).Carrier) (u : Ambient eta heta) :
    Member u (translate eta heta b y) ↔
      ∃ n, codeChildValue eta heta b n y = some u := by
  subst b
  rw [translate_add_one]
  cases hv : successorCode a y with
  | none => simp only [hv,Option.map_none,member_collection_none]
            simp only [codeChildValue_add_one,hv,Option.map_none,reduceCtorEq,exists_const]
  | some v =>
    simp only [hv,Option.map_some,member_collection_some,codeChildValue_add_one,
      Option.some.injEq]

theorem evalSeed_successor_none (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    evalSeed eta heta (a+1) none x = none := by
  simp only [evalSeed,if_neg (successor_ne_top eta a)]

theorem evalSeed_successor_member (a : Ordinal.{0}) (p : List ℕ)
    (x : (fsTower eta).Carrier) (v u : Ambient eta heta)
    (hv : evalSeed eta heta (a+1) (some p) x = some v) :
    Member u v ↔ ∃ n, evalSeed eta heta a (some (n::p)) x = some u := by
  have hp : (sourcePath eta p).rank = a+1 := by
    by_contra h
    simp only [evalSeed,if_neg h] at hv
    contradiction
  have hvalue : sourcePathValue eta heta p x = some v := by
    simpa only [evalSeed,if_pos hp] using hv
  unfold sourcePathValue optionalTranslate at hvalue
  split at hvalue
  · contradiction
  · rename_i y hy
    cases hvalue
    rw [successor_member_iff_child eta heta _ a hp]
    apply exists_congr
    intro n
    have hn : (sourcePath eta (n::p)).rank = a := by
      change (codeChildren (sourcePath eta p).rank).rank n = a
      rw [hp,codeChildren_add_one_rank]
    change (codeChildren (sourcePath eta p).rank).rank n = a at hn
    simp only [evalSeed,if_pos hn,sourcePathValue,sourcePath,
      Function.comp_apply,hy,Sum.elim_inr,codeChildValue]

def childSeed (s : SeedIndex) (n : ℕ) : SeedIndex := s.map (n::·)

theorem evalSeed_successor_member_all (a : Ordinal.{0}) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (v u : Ambient eta heta)
    (hv : evalSeed eta heta (a+1) s x = some v) :
    Member u v ↔ ∃ n, evalSeed eta heta a (childSeed s n) x = some u := by
  cases s with
  | none => rw [evalSeed_successor_none] at hv; contradiction
  | some p => exact evalSeed_successor_member eta heta a p x v u hv

theorem evalSeed_limit_source (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (s : SeedIndex) (x : (fsTower eta).Carrier) (v : Ambient eta heta)
    (hv : evalSeed eta heta lam s x = some v) :
    ∃ z, v = sourceSequence (level eta lam) z := by
  cases s with
  | none =>
    by_cases ha : lam = Frame.top eta
    · have heq : topSource eta heta x = v := by
        simpa only [evalSeed,if_pos ha,Option.some.injEq] using hv
      exact ⟨topCoordinates eta heta x,by simpa only [ha,topSource] using heq.symm⟩
    · simp only [evalSeed,if_neg ha] at hv
      contradiction
  | some p =>
    have hp : (sourcePath eta p).rank = lam := by
      by_contra h
      simp only [evalSeed,if_neg h] at hv
      contradiction
    have hvalue : sourcePathValue eta heta p x = some v := by
      simpa only [evalSeed,if_pos hp] using hv
    unfold sourcePathValue optionalTranslate at hvalue
    split at hvalue
    · contradiction
    · rename_i y hy
      cases hvalue
      obtain ⟨z,hz,_⟩ := limit_value_children eta heta _ lam hp hlam y
      exact ⟨z,hz⟩

theorem evalSeed_limit_ne_filler (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (s : SeedIndex) (x : (fsTower eta).Carrier) (A : Finset (ℕ × Ambient eta heta)) :
    evalSeed eta heta lam s x ≠ some (finiteFiller (level eta lam) A) := by
  intro hv
  obtain ⟨z,hz⟩ := evalSeed_limit_source eta heta lam hlam s x _ hv
  exact sourceSequence_ne_finiteFiller _ _ z A hz.symm

end FSCofinality.CosetConstruction
