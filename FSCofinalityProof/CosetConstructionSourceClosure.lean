import FSCofinalityProof.CosetConstructionSourcePaths

noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def codeChildValue (a : Ordinal.{0}) (n : ℕ) (x : (fsTower a).Carrier) :
    Option (Ambient eta heta) :=
  optionalTranslate eta heta ((codeChildren a).rank n) ((codeChildren a).get n x)

theorem codeChildren_add_one_rank (a : Ordinal.{0}) (n : ℕ) :
    (codeChildren (a+1)).rank n = a := by
  unfold codeChildren
  rw [Ordinal.limitRecOn_add_one]

theorem codeChildren_limit_rank (a : Ordinal.{0}) (ha : IsSuccLimit a) (n : ℕ) :
    (codeChildren a).rank n = fundamentalSequence a ha n := by
  unfold codeChildren
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha]

theorem codeChildValue_add_one (a : Ordinal.{0}) (n : ℕ) (x : (fsTower (a+1)).Carrier) :
    codeChildValue eta heta (a+1) n x =
      (successorCode a x).map (fun u => translate eta heta a (u n)) := by
  unfold codeChildValue codeChildren
  rw [Ordinal.limitRecOn_add_one]
  unfold successorChildCode
  dsimp only
  rw [codeCast_apply]
  change optionalTranslate eta heta a
      (Sum.map id (fun u : ℕ → (fsTower a).Carrier => u n)
        (optionSumEquiv _ (successorCode a x))) = _
  cases successorCode a x <;> rfl

theorem codeChildValue_limit (a : Ordinal.{0}) (ha : IsSuccLimit a) (n : ℕ)
    (x : (fsTower a).Carrier) : codeChildValue eta heta a n x =
      some (translate eta heta (fundamentalSequence a ha n) (limitCode a ha x n)) := by
  unfold codeChildValue codeChildren
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha]
  unfold limitChildCode
  dsimp only
  rw [codeCast_apply]
  rfl

theorem child_mem_sourceSeeds (p : List ℕ) (x : (fsTower eta).Carrier)
    (y : (fsTower (sourcePath eta p).rank).Carrier)
    (hy : (sourcePath eta p).get x = .inr y) (n : ℕ) (u : Ambient eta heta)
    (hu : codeChildValue eta heta (sourcePath eta p).rank n y = some u) :
    u ∈ sourceSeeds eta heta ((codeChildren (sourcePath eta p).rank).rank n) x := by
  refine ⟨n::p,rfl,?_⟩
  unfold sourcePathValue
  simp only [sourcePath,Function.comp_apply,hy,Sum.elim_inr]
  simpa only [codeChildValue] using hu

theorem successor_member_has_child (b a : Ordinal.{0}) (hb : b = a+1)
    (x : (fsTower b).Carrier) (u : Ambient eta heta)
    (hu : Member u (translate eta heta b x)) :
    ∃ n, codeChildValue eta heta b n x = some u ∧ (codeChildren b).rank n = a := by
  subst b
  rw [translate_add_one] at hu
  cases hv : successorCode a x with
  | none => simp only [hv,Option.map_none,member_collection_none] at hu
  | some v =>
    rw [hv] at hu
    obtain ⟨n,hn⟩ := (member_collection_some _ _ _).mp hu
    refine ⟨n,?_,codeChildren_add_one_rank a n⟩
    rw [codeChildValue_add_one,hv,Option.map_some]
    exact congrArg some hn

/-- Successor source seeds contain all members of each of their seeded sets. -/
theorem sourceSeeds_successor_downward (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {v u : Ambient eta heta} (hv : v ∈ sourceSeeds eta heta (a+1) x) (hu : Member u v) :
    u ∈ sourceSeeds eta heta a x := by
  obtain ⟨p,hrank,hp⟩ := hv
  unfold sourcePathValue optionalTranslate at hp
  split at hp
  · contradiction
  · rename_i y hy
    cases hp
    obtain ⟨n,hchild,hrank'⟩ := successor_member_has_child eta heta
      (sourcePath eta p).rank a hrank y u hu
    have hm := child_mem_sourceSeeds eta heta p x y hy n u hchild
    rwa [hrank'] at hm

theorem sourceSeeds_successor_collection (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {v : Ambient eta heta} (hv : v ∈ sourceSeeds eta heta (a+1) x) :
    ∃ z, v = collection (level eta (a+1)) z := by
  obtain ⟨p,hrank,hp⟩ := hv
  unfold sourcePathValue optionalTranslate at hp
  split at hp
  · contradiction
  · rename_i y hy
    cases hp
    have haux (b : Ordinal.{0}) (hb : b = a+1) (z : (fsTower b).Carrier) :
        ∃ u, translate eta heta b z = collection (level eta (a+1)) u := by
      subst b
      exact ⟨_,translate_add_one eta heta a z⟩
    exact haux _ hrank y

theorem sourceSeeds_rank_le (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {u : Ambient eta heta} (hu : u ∈ sourceSeeds eta heta a x) : a ≤ eta := by
  obtain ⟨p,hp,_⟩ := hu
  exact hp ▸ (sourcePath eta p).rank_le

theorem sourceSeeds_empty_of_gt (a : Ordinal.{0}) (ha : eta < a) (x : (fsTower eta).Carrier) :
    sourceSeeds eta heta a x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact not_le_of_gt ha (sourceSeeds_rank_le eta heta a x hu)

theorem limit_value_children (b lam : Ordinal.{0}) (hb : b = lam) (hlam : IsSuccLimit lam)
    (x : (fsTower b).Carrier) :
    ∃ s : ℕ → Ambient eta heta, translate eta heta b x = sourceSequence (level eta lam) s ∧
      ∀ n, codeChildValue eta heta b n x = some (s n) ∧
        (codeChildren b).rank n = fundamentalSequence lam hlam n := by
  subst b
  refine ⟨fun n => translate eta heta (fundamentalSequence lam hlam n) (limitCode lam hlam x n),
    translate_limit eta heta lam hlam x,fun n => ?_⟩
  exact ⟨codeChildValue_limit eta heta lam hlam n x,codeChildren_limit_rank lam hlam n⟩

/-- Limit source seeds contain every one of their actual typed coordinates. -/
theorem sourceSeeds_limit_representation (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (x : (fsTower eta).Carrier) {v : Ambient eta heta} (hv : v ∈ sourceSeeds eta heta lam x) :
    ∃ s : ℕ → Ambient eta heta, v = sourceSequence (level eta lam) s ∧
      ∀ n, s n ∈ sourceSeeds eta heta (Frame.q eta lam hlam n) x := by
  have hle : lam ≤ eta := sourceSeeds_rank_le eta heta lam x hv
  obtain ⟨p,hrank,hp⟩ := hv
  unfold sourcePathValue optionalTranslate at hp
  split at hp
  · contradiction
  · rename_i y hy
    cases hp
    obtain ⟨s,hs,hchildren⟩ := limit_value_children eta heta (sourcePath eta p).rank lam hrank hlam y
    refine ⟨s,hs,fun n => ?_⟩
    have hm := child_mem_sourceSeeds eta heta p x y hy n (s n) (hchildren n).1
    have hq : Frame.q eta lam hlam n = fundamentalSequence lam hlam n :=
      congrFun (Frame.q_of_le_source eta lam hlam hle) n
    rw [(hchildren n).2] at hm
    rwa [hq]

theorem sourceSeeds_limit_downward (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (x : (fsTower eta).Carrier) :
    sourceSeeds eta heta lam x ⊆ LimitSet eta heta lam hlam
      (fun b _ => sourceSeeds eta heta b x) := by
  intro v hv
  obtain ⟨s,hs,hcoord⟩ := sourceSeeds_limit_representation eta heta lam hlam x hv
  exact Or.inl ⟨s,hs,hcoord⟩

theorem seed_subset_pool (seeds : Ordinal.{0} → Set (Ambient eta heta)) (a : Ordinal.{0}) :
    seeds a ⊆ Pool eta heta seeds a := by
  induction a using Ordinal.limitRecOn with
  | zero => rw [pool_zero]; exact subset_union_left
  | add_one a IH => rw [pool_add_one]; exact subset_union_left
  | limit a ha IH => rw [pool_limit eta heta seeds a ha]; exact subset_union_left

end FSCofinality.CosetConstruction
