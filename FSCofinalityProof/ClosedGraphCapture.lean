import FSCofinalityProof.TwoSortTopology

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology TopologicalSpace Filter

namespace FSCofinality.TwoSort

variable {G : Subgroup PermutationGroup}

/-- The graph representation puts the image action on the even sort and
the original faithful action on the odd sort. -/
def graphHom (π : G →* PermutationGroup) : G →* PermutationGroup :=
  combineHom.comp (π.prod G.subtype)

@[simp] theorem graphHom_apply (π : G →* PermutationGroup) (g : G) :
    graphHom π g = combine (π g) g.val := rfl

theorem graphHom_injective (π : G →* PermutationGroup) : Function.Injective (graphHom π) := by
  intro g h hgh
  apply Subtype.ext
  have he : ((π g,g.val) : PermutationGroup × PermutationGroup) = (π h,h.val) :=
    combine_injective hgh
  exact congrArg Prod.snd he

theorem isClosedEmbedding_graphPair (hG : IsClosed (G : Set PermutationGroup))
    (π : G →* PermutationGroup) (hπ : Continuous π) :
    IsClosedEmbedding (fun g : G => ((π g,g.val) : PermutationGroup × PermutationGroup)) := by
  have hgraph : IsClosedEmbedding (fun g : G => ((π g,g) : PermutationGroup × G)) := by
    have he : IsEmbedding (fun g : G => ((π g,g) : PermutationGroup × G)) :=
      IsEmbedding.of_comp (hπ.prodMk continuous_id) continuous_snd IsEmbedding.id
    have hr : range (fun g : G => ((π g,g) : PermutationGroup × G)) =
        {p : PermutationGroup × G | p.1 = π p.2} := by
      ext p
      constructor
      · rintro ⟨g,rfl⟩
        rfl
      · intro hp
        exact ⟨p.2,Prod.ext hp.symm rfl⟩
    exact ⟨he,hr ▸ isClosed_eq continuous_fst (hπ.comp continuous_snd)⟩
  have hsub : IsClosedEmbedding (Prod.map (id : PermutationGroup → PermutationGroup)
      (fun g : G => g.val)) :=
    IsClosedEmbedding.id.prodMap hG.isClosedEmbedding_subtypeVal
  exact hsub.comp hgraph

theorem isClosedEmbedding_graphHom (hG : IsClosed (G : Set PermutationGroup))
    (π : G →* PermutationGroup) (hπ : Continuous π) : IsClosedEmbedding (graphHom π) :=
  isClosedEmbedding_combine.comp (isClosedEmbedding_graphPair hG π hπ)

def graphSubgroup (π : G →* PermutationGroup) : Subgroup PermutationGroup := (graphHom π).range

theorem isClosed_graphSubgroup (hG : IsClosed (G : Set PermutationGroup))
    (π : G →* PermutationGroup) (hπ : Continuous π) :
    IsClosed (graphSubgroup π : Set PermutationGroup) :=
  (isClosedEmbedding_graphHom hG π hπ).isClosed_range

theorem graphSubgroup_preserves_evens (π : G →* PermutationGroup)
    (p : graphSubgroup π) (n : ℕ) : n ∈ Evens ↔ p.val.toFun n ∈ Evens := by
  rcases p.property with ⟨g,hg⟩
  rw [← hg]
  exact combine_preserves_evens (π g) g.val n

/-- Restriction to a preserved countable sort, written for any subgroup. -/
def restrictionHom (H : Subgroup PermutationGroup) (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : H, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q) : H →* PermutationGroup where
  toFun := fun p => DistinguishedRestriction.restrictPerm Q e p.val (hQ p)
  map_one' := by
    apply Equiv.ext
    intro n
    apply e.injective
    apply Subtype.ext
    change (e ((DistinguishedRestriction.restrictPerm Q e 1 _).toFun n)).val = (e n).val
    rw [DistinguishedRestriction.restrictPerm_apply_val]
    rfl
  map_mul' := by
    intro p q
    apply Equiv.ext
    intro n
    apply e.injective
    apply Subtype.ext
    change (e ((DistinguishedRestriction.restrictPerm Q e (p*q).val (hQ (p*q))).toFun n)).val =
      (e ((DistinguishedRestriction.restrictPerm Q e p.val (hQ p)).toFun
        ((DistinguishedRestriction.restrictPerm Q e q.val (hQ q)).toFun n))).val
    simp only [DistinguishedRestriction.restrictPerm_apply_val]
    rfl

def graphRestriction (π : G →* PermutationGroup) : graphSubgroup π →* PermutationGroup :=
  restrictionHom (graphSubgroup π) Evens evenEnumeration (graphSubgroup_preserves_evens π)

@[simp] theorem graphRestriction_graphHom (π : G →* PermutationGroup) (g : G) :
    graphRestriction π ⟨graphHom π g,⟨g,rfl⟩⟩ = π g := by
  apply Equiv.ext
  intro n
  have h := DistinguishedRestriction.restrictPerm_apply_val Evens evenEnumeration
    (graphHom π g) (graphSubgroup_preserves_evens π ⟨graphHom π g,⟨g,rfl⟩⟩) n
  change 2*((graphRestriction π ⟨graphHom π g,⟨g,rfl⟩⟩).toFun n) =
    (combine (π g) g.val).toFun (2*n) at h
  rw [combine_even] at h
  change (graphRestriction π ⟨graphHom π g,⟨g,rfl⟩⟩).toFun n = (π g).toFun n
  omega

theorem range_graphRestriction (π : G →* PermutationGroup) :
    (graphRestriction π).range = π.range := by
  ext p
  constructor
  · rintro ⟨h,hh⟩
    obtain ⟨g,hg⟩ := h.property
    have he : h = (⟨graphHom π g,⟨g,rfl⟩⟩ : graphSubgroup π) := Subtype.ext hg.symm
    rw [he,graphRestriction_graphHom] at hh
    exact ⟨g,hh⟩
  · rintro ⟨g,hg⟩
    exact ⟨⟨graphHom π g,⟨g,rfl⟩⟩,(graphRestriction_graphHom π g).trans hg⟩

end FSCofinality.TwoSort
