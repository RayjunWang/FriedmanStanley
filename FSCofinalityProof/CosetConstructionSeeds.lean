import FSCofinalityProof.CosetConstructionSourceClosure

noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def topCoordinates (x : (fsTower eta).Carrier) (n : ℕ) : Ambient eta heta :=
  if n = 0 then translate eta heta eta x else tag eta heta (eta+n) 4

def topSource (x : (fsTower eta).Carrier) : Ambient eta heta :=
  sourceSequence (level eta (Frame.top eta)) (topCoordinates eta heta x)

def fullSeeds (a : Ordinal.{0}) (x : (fsTower eta).Carrier) : Set (Ambient eta heta) :=
  if a = Frame.top eta then {topSource eta heta x} else sourceSeeds eta heta a x

theorem eta_add_nat_le_top (n : ℕ) : eta+n ≤ Frame.top eta :=
  (add_lt_add_iff_left eta).mpr (Ordinal.natCast_lt_omega0 n) |>.le

theorem topSource_typed (x : (fsTower eta).Carrier) :
    topSource eta heta x ∈ Valid eta heta (Frame.top eta) := by
  rw [valid_limit eta heta _ (Frame.top_isSuccLimit eta)]
  left
  refine ⟨topCoordinates eta heta x,rfl,fun n => ?_⟩
  change topCoordinates eta heta x n ∈ Valid eta heta
    (Frame.q eta (Frame.top eta) (Frame.top_isSuccLimit eta) n)
  rw [Frame.q_top]
  by_cases hn : n = 0
  · subst n
    simpa only [topCoordinates,if_pos rfl,Nat.cast_zero,add_zero] using
      translate_typed eta heta eta le_rfl x
  · rw [topCoordinates,if_neg hn]
    exact valid_tag eta heta (eta+n) (eta_add_nat_le_top eta n) 4

theorem sourceSeeds_subset_fullSeeds (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    sourceSeeds eta heta a x ⊆ fullSeeds eta heta a x := by
  by_cases ha : a = Frame.top eta
  · rw [ha,sourceSeeds_empty_of_gt eta heta _ (Frame.lt_top eta)]
    exact empty_subset _
  · simp only [fullSeeds,if_neg ha]
    exact Subset.rfl

theorem fullSeeds_countable (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    (fullSeeds eta heta a x).Countable := by
  by_cases ha : a = Frame.top eta
  · rw [fullSeeds,if_pos ha]
    exact countable_singleton _
  · rw [fullSeeds,if_neg ha]
    exact sourceSeeds_countable eta heta a x

theorem fullSeeds_typed (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    fullSeeds eta heta a x ⊆ Valid eta heta a := by
  by_cases ha : a = Frame.top eta
  · subst a
    intro u hu
    have heq : u = topSource eta heta x := by simpa only [fullSeeds,if_pos rfl,mem_singleton_iff] using hu
    rw [heq]
    exact topSource_typed eta heta x
  · rw [fullSeeds,if_neg ha]
    exact sourceSeeds_typed eta heta a x

theorem topCoordinates_mem_pool (x : (fsTower eta).Carrier) (n : ℕ) :
    topCoordinates eta heta x n ∈ Pool eta heta (fun a => fullSeeds eta heta a x) (eta+n) := by
  by_cases hn : n = 0
  · subst n
    simp only [topCoordinates,if_pos rfl,Nat.cast_zero,add_zero]
    apply seed_subset_pool eta heta _ eta
    exact sourceSeeds_subset_fullSeeds eta heta eta x (root_mem_sourceSeeds eta heta x)
  · rw [topCoordinates,if_neg hn]
    exact pool_tag eta heta _ (eta+n) (eta_add_nat_le_top eta n) 4

theorem successor_ne_top (a : Ordinal.{0}) : a+1 ≠ Frame.top eta := by
  intro h
  have hlt : a < Frame.top eta := by
    rw [← h]
    exact lt_add_of_pos_right a zero_lt_one
  have hsucc : a+1 < Frame.top eta := by
    simpa only [succ_eq_add_one] using (Frame.top_isSuccLimit eta).succ_lt hlt
  exact ne_of_lt hsucc h

theorem fullSeeds_successor_collection (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {v : Ambient eta heta} (hv : v ∈ fullSeeds eta heta (a+1) x) :
    ∃ z, v = collection (level eta (a+1)) z := by
  rw [fullSeeds,if_neg (successor_ne_top eta a)] at hv
  exact sourceSeeds_successor_collection eta heta a x hv

theorem fullSeeds_successor_downward (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {v u : Ambient eta heta} (hv : v ∈ fullSeeds eta heta (a+1) x) (hu : Member u v) :
    u ∈ Pool eta heta (fun b => fullSeeds eta heta b x) a := by
  rw [fullSeeds,if_neg (successor_ne_top eta a)] at hv
  apply seed_subset_pool eta heta _ a
  exact sourceSeeds_subset_fullSeeds eta heta a x (sourceSeeds_successor_downward eta heta a x hv hu)

theorem fullSeeds_limit_downward (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (x : (fsTower eta).Carrier) : fullSeeds eta heta lam x ⊆
      LimitSet eta heta lam hlam (fun b _ => Pool eta heta (fun a => fullSeeds eta heta a x) b) := by
  intro v hv
  by_cases htop : lam = Frame.top eta
  · subst lam
    have heq : v = topSource eta heta x := by simpa only [fullSeeds,if_pos rfl,mem_singleton_iff] using hv
    rw [heq]
    left
    refine ⟨topCoordinates eta heta x,rfl,fun n => ?_⟩
    change topCoordinates eta heta x n ∈ Pool eta heta _ (Frame.q eta (Frame.top eta) hlam n)
    simpa only [Frame.q_top] using topCoordinates_mem_pool eta heta x n
  · rw [fullSeeds,if_neg htop] at hv
    obtain ⟨s,hs,hcoord⟩ := sourceSeeds_limit_representation eta heta lam hlam x hv
    left
    refine ⟨s,hs,fun n => ?_⟩
    apply seed_subset_pool eta heta _ _
    exact sourceSeeds_subset_fullSeeds eta heta _ x (hcoord n)

theorem topSource_eq_iff (x y : (fsTower eta).Carrier) :
    topSource eta heta x = topSource eta heta y ↔ (fsTower eta).rel x y := by
  constructor
  · intro h
    have hseq := sourceSequence_injective (level eta (Frame.top eta)) h
    have hzero := congrFun hseq 0
    have htrans : translate eta heta eta x = translate eta heta eta y := by
      simpa only [topCoordinates,if_pos rfl] using hzero
    exact (translate_eq_iff eta heta eta x y).mp htrans
  · intro h
    apply congrArg (sourceSequence (level eta (Frame.top eta)))
    funext n
    by_cases hn : n = 0
    · simp only [topCoordinates,if_pos hn]
      exact (translate_eq_iff eta heta eta x y).mpr h
    · simp only [topCoordinates,if_neg hn]

end FSCofinality.CosetConstruction
