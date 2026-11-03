import FSCofinalityProof.RawObjectsPoolValidity

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem all_markers_iff_source (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))
    (r : LimitRow η hη lam hlam lower) :
    (∀ n, rowBit η hη lam hlam lower r (markerBirth η hη lam hlam lower n) = true) ↔
      ∃ s, r = Sum.inl s := by
  constructor
  · intro h
    rcases r with s | A
    · exact ⟨s,rfl⟩
    · let n := A.sup (fun b => b.1) + 1
      have hn := h n
      change decide (markerBirth η hη lam hlam lower n ∈ A) = true at hn
      have hm := of_decide_eq_true hn
      have hb : n ≤ A.sup (fun b => b.1) :=
        Finset.le_sup (f := fun b : Birth η hη lam hlam lower => b.1) hm
      omega
  · rintro ⟨s,rfl⟩ n
    rfl

theorem ambientProfile_rowObject (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (r : LimitRow η hη lam hlam (fullLower η hη lam)) (n : ℕ)
    (c : Column η hη lam hlam (fullLower η hη lam) n) :
    ambientProfile η hη lam hlam htop n (rowObject η hη lam hlam (fullLower η hη lam) htop r) c =
      profile η hη lam hlam (fullLower η hη lam) n r c := by
  have hv : rowObject η hη lam hlam (fullLower η hη lam) htop r ∈ Valid η hη lam := by
    rw [valid_limit η hη lam hlam]
    exact rowObject_mem_limitSet η hη lam hlam (fullLower η hη lam) htop r
  have hr : ambientRow η hη lam hlam htop
      (rowObject η hη lam hlam (fullLower η hη lam) htop r) hv = r :=
    rowObject_injective η hη lam hlam (fullLower η hη lam) htop
      (rowObject_ambientRow η hη lam hlam htop _ hv)
  simp only [ambientProfile,dif_pos hv,hr]

theorem ambient_all_markers_iff_source (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (x : Ambient η hη) (hx : x ∈ Valid η hη lam) :
    (∀ n, ambientProfile η hη lam hlam htop n x
      ⟨markerBirth η hη lam hlam (fullLower η hη lam) n,le_rfl⟩ = true) ↔
      ∃ s : SourceTuple η hη lam hlam (fullLower η hη lam),
        x = sourceSequence (level η lam) (fun n => (s n).val) := by
  constructor
  · intro h
    have hm : ∀ n, rowBit η hη lam hlam (fullLower η hη lam)
        (ambientRow η hη lam hlam htop x hx)
        (markerBirth η hη lam hlam (fullLower η hη lam) n) = true := by
      intro n
      simpa only [ambientProfile,dif_pos hx,profile] using h n
    obtain ⟨s,hs⟩ := (all_markers_iff_source η hη lam hlam (fullLower η hη lam) _).mp hm
    refine ⟨s,?_⟩
    have he := rowObject_ambientRow η hη lam hlam htop x hx
    rw [hs] at he
    exact he.symm
  · rintro ⟨s,rfl⟩ n
    have h := ambientProfile_rowObject η hη lam hlam htop (Sum.inl s) n
      ⟨markerBirth η hη lam hlam (fullLower η hη lam) n,le_rfl⟩
    exact h

/-- At a limit pool with one source seed, the all-marker test identifies
that seed uniquely among all of its finite-support fillers. -/
theorem pool_unique_all_markers (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (hseeds : ∀ a, seeds a ⊆ Valid η hη a)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (s : ℕ → Ambient η hη) (hseed : seeds lam = {sourceSequence (level η lam) s})
    {x : Ambient η hη} (hx : x ∈ Pool η hη seeds lam)
    (hm : ∀ n, ambientProfile η hη lam hlam htop n x
      ⟨markerBirth η hη lam hlam (fullLower η hη lam) n,le_rfl⟩ = true) :
    x = sourceSequence (level η lam) s := by
  have hv := pool_subset_valid η hη seeds hseeds lam hx
  obtain ⟨t,ht⟩ := (ambient_all_markers_iff_source η hη lam hlam htop x hv).mp hm
  rw [pool_limit η hη seeds lam hlam] at hx
  rcases hx with hx | hx
  · simpa only [hseed,mem_singleton_iff] using hx
  · obtain ⟨A,hA,hx⟩ := (mem_finiteImages_iff _ _ _).mp hx
    exact False.elim (sourceSequence_ne_finiteFiller _ _ _ _ (ht.symm.trans hx.symm))

end FSCofinality.RawObjects
