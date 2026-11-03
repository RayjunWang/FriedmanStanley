import FSCofinalityProof.CosetConstructionSeeds
import FSCofinalityProof.CosetConstructionSourceInvariant
import FSCofinalityProof.RawObjectsTopRecovery

noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem fullSeeds_congr (a : Ordinal.{0}) {x y : (fsTower eta).Carrier}
    (hxy : (fsTower eta).rel x y) : fullSeeds eta heta a x = fullSeeds eta heta a y := by
  by_cases ha : a = Frame.top eta
  · simp only [fullSeeds,if_pos ha,(topSource_eq_iff eta heta x y).mpr hxy]
  · simp only [fullSeeds,if_neg ha,sourceSeeds_congr eta heta a hxy]

theorem pools_congr (a : Ordinal.{0}) {x y : (fsTower eta).Carrier}
    (hxy : (fsTower eta).rel x y) :
    Pool eta heta (fun b => fullSeeds eta heta b x) a =
      Pool eta heta (fun b => fullSeeds eta heta b y) a := by
  have hseed : (fun b => fullSeeds eta heta b x) = (fun b => fullSeeds eta heta b y) :=
    funext (fun b => fullSeeds_congr eta heta b hxy)
  rw [hseed]

theorem topCoordinates_typed (x : (fsTower eta).Carrier) (n : ℕ) :
    topCoordinates eta heta x n ∈ Valid eta heta
      (Frame.q eta (Frame.top eta) (Frame.top_isSuccLimit eta) n) := by
  rw [Frame.q_top]
  by_cases hn : n = 0
  · subst n
    simpa only [topCoordinates,if_pos rfl,Nat.cast_zero,add_zero] using
      translate_typed eta heta eta le_rfl x
  · rw [topCoordinates,if_neg hn]
    exact valid_tag eta heta (eta+n) (eta_add_nat_le_top eta n) 4

theorem topSource_all_markers (x : (fsTower eta).Carrier) :
    ∀ n, ambientProfile eta heta (Frame.top eta) (Frame.top_isSuccLimit eta) le_rfl n
      (topSource eta heta x)
      ⟨markerBirth eta heta (Frame.top eta) (Frame.top_isSuccLimit eta)
        (fullLower eta heta (Frame.top eta)) n,le_rfl⟩ = true := by
  apply (ambient_all_markers_iff_source eta heta _ _ le_rfl _ (topSource_typed eta heta x)).mpr
  exact ⟨fun n => ⟨topCoordinates eta heta x n,topCoordinates_typed eta heta x n⟩,rfl⟩

theorem topSource_mem_pool (x : (fsTower eta).Carrier) :
    topSource eta heta x ∈ Pool eta heta (fun b => fullSeeds eta heta b x) (Frame.top eta) := by
  apply seed_subset_pool eta heta _ _
  simp [fullSeeds]

/-- Equality of the actual top pools already reflects the entire source
invariant: their unique all-marker source rows must be equal. -/
theorem topPool_eq_iff (x y : (fsTower eta).Carrier) :
    Pool eta heta (fun b => fullSeeds eta heta b x) (Frame.top eta) =
      Pool eta heta (fun b => fullSeeds eta heta b y) (Frame.top eta) ↔ (fsTower eta).rel x y := by
  constructor
  · intro hpool
    have hx : topSource eta heta x ∈
        Pool eta heta (fun b => fullSeeds eta heta b y) (Frame.top eta) := by
      rw [← hpool]
      exact topSource_mem_pool eta heta x
    have heq := pool_unique_all_markers eta heta (fun b => fullSeeds eta heta b y)
      (fun a => fullSeeds_typed eta heta a y) (Frame.top eta) (Frame.top_isSuccLimit eta) le_rfl
      (topCoordinates eta heta y) (by simp [fullSeeds,topSource]) hx
      (topSource_all_markers eta heta x)
    exact (topSource_eq_iff eta heta x y).mp heq
  · exact pools_congr eta heta (Frame.top eta)

end FSCofinality.CosetConstruction
