import FSCofinalityProof.CosetConstructionProfileDecoders

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta)

theorem codeRep_mem_pool (a : Ordinal.{0})
    {F : (fsTower eta).Carrier → Option (Ambient eta heta)} (hF : CodeRep eta heta a F)
    (x : (fsTower eta).Carrier) (u : Ambient eta heta) (hu : F x = some u) :
    u ∈ TokenModel.mainPool eta heta x a := by
  obtain ⟨c,hc⟩ := hF
  exact ((poolCodes eta heta a).covers x u).mp ⟨c,(hc x).trans hu⟩

def seedSourceTuple (s : SeedIndex) (x : (fsTower eta).Carrier) (z : ℕ → Ambient eta heta)
    (hv : evalSeed eta heta lam s x = some (sourceSequence (level eta lam) z)) :
    SourceTuple eta heta lam hlam (TokenModel.lowerPools eta heta x lam) :=
  fun n => ⟨z n,codeRep_mem_pool eta heta _ (codeRep_seedCoordinate eta heta lam hlam htop s n) x (z n)
    (seedCoordinate_source eta heta lam hlam s n x z hv)⟩

theorem ambientProfile_source_shape (x : (fsTower eta).Carrier)
    (s : SourceTuple eta heta lam hlam (TokenModel.lowerPools eta heta x lam))
    (n : ℕ) (c : Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) :
    ambientProfile eta heta lam hlam htop n
        (sourceSequence (level eta lam) (fun k => (s k).val))
        (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n c) =
      sourceBit eta heta lam hlam (TokenModel.lowerPools eta heta x lam) s c.val :=
  ambientProfile_restricted eta heta lam hlam htop (TokenModel.ambientLower eta heta x lam)
    n (.inl s) c

theorem ambientProfile_filler_shape (x : (fsTower eta).Carrier)
    (B : Finset (ℕ × Ambient eta heta))
    (hB : ∀ b ∈ B, NewColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) b.1 b.2)
    (n : ℕ) (c : Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) :
    ambientProfile eta heta lam hlam htop n (finiteFiller (level eta lam) B)
        (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n c) =
      decide (encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) c.val ∈ B) := by
  obtain ⟨r,hr⟩ := exists_rowObject_of_mem_limitSet eta heta lam hlam
    (TokenModel.lowerPools eta heta x lam) htop (Or.inr ⟨B,rfl,hB⟩)
  rcases r with s|A
  · exact False.elim (sourceSequence_ne_finiteFiller _ _ _ _ hr)
  · have hsupport : A.map (birthEmbedding eta heta lam hlam (TokenModel.lowerPools eta heta x lam) htop) = B :=
      finiteFiller_injective (level eta lam) hr
    have hp := ambientProfile_restricted eta heta lam hlam htop
      (TokenModel.ambientLower eta heta x lam) n (.inr A) c
    rw [hr] at hp
    rw [hp]
    change decide (c.val ∈ A) = decide (encodeBirth eta heta lam hlam
      (TokenModel.lowerPools eta heta x lam) c.val ∈ B)
    congr 1
    rw [←hsupport]
    apply propext
    constructor
    · intro hc
      exact Finset.mem_map.mpr ⟨c.val,hc,rfl⟩
    · intro hc
      obtain ⟨b,hb,heq⟩ := Finset.mem_map.mp hc
      have hbc := encodeBirth_injective eta heta lam hlam
        (TokenModel.lowerPools eta heta x lam) htop heq
      exact hbc ▸ hb

end FSCofinality.CosetConstruction
