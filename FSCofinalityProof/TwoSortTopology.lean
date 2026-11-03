import FSCofinalityProof.TwoSortPermutations

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology TopologicalSpace Filter

namespace FSCofinality.TwoSort

@[simp] theorem combine_inv (p q : PermutationGroup) :
    (combine p q)⁻¹ = combine p⁻¹ q⁻¹ :=
  (combineHom.map_inv (p,q)).symm

theorem continuous_combine : Continuous combineHom := by
  have hf (n : ℕ) : Continuous (fun p : PermutationGroup × PermutationGroup =>
      (combine p.1 p.2).toFun n) := by
    rcases nat_even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · simp only [combine_even]
      exact (continuous_of_discreteTopology : Continuous (fun m : ℕ => 2*m)).comp
        (((continuous_apply k).comp continuous_permutationCoordinates.fst).comp continuous_fst)
    · simp only [combine_odd]
      exact (continuous_of_discreteTopology : Continuous (fun m : ℕ => 2*m+1)).comp
        (((continuous_apply k).comp continuous_permutationCoordinates.fst).comp continuous_snd)
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · exact continuous_pi hf
  · apply continuous_pi
    intro n
    have hi := (hf n).comp (continuous_inv : Continuous
      (fun p : PermutationGroup × PermutationGroup => p⁻¹))
    convert hi using 1

abbrev Coordinates := (ℕ → ℕ) × (ℕ → ℕ)

def extractCoordinates (p : PermutationGroup) : Coordinates × Coordinates :=
  ((fun n => p.toFun (2*n)/2,fun n => p.invFun (2*n)/2),
   (fun n => p.toFun (2*n+1)/2,fun n => p.invFun (2*n+1)/2))

theorem continuous_extractCoordinates : Continuous extractCoordinates := by
  have hf (b : ℕ) : Continuous (fun p : PermutationGroup => fun n => p.toFun (2*n+b)/2) := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology : Continuous (fun m : ℕ => m/2)).comp
      ((continuous_apply (2*n+b)).comp continuous_permutationCoordinates.fst)
  have hi (b : ℕ) : Continuous (fun p : PermutationGroup => fun n => p.invFun (2*n+b)/2) := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology : Continuous (fun m : ℕ => m/2)).comp
      ((continuous_apply (2*n+b)).comp continuous_permutationCoordinates.snd)
  exact ((hf 0).prodMk (hi 0)).prodMk ((hf 1).prodMk (hi 1))

theorem extractCoordinates_combine (p q : PermutationGroup) :
    extractCoordinates (combine p q) = (permutationCoordinates p,permutationCoordinates q) := by
  apply Prod.ext <;> apply Prod.ext <;> funext n
  · simp [extractCoordinates,permutationCoordinates]
  · change ((combine p q)⁻¹).toFun (2*n)/2 = p.invFun n
    rw [combine_inv,combine_even]
    change (2*p.invFun n)/2 = p.invFun n
    omega
  · change (combine p q).toFun (2*n+1)/2 = q.toFun n
    rw [combine_odd]
    omega
  · change ((combine p q)⁻¹).toFun (2*n+1)/2 = q.invFun n
    rw [combine_inv,combine_odd]
    change (2*q.invFun n+1)/2 = q.invFun n
    omega

theorem isEmbedding_combine : IsEmbedding combineHom := by
  have he : IsEmbedding (Prod.map permutationCoordinates permutationCoordinates) :=
    permutationCoordinates_injective.isEmbedding_induced.prodMap
      permutationCoordinates_injective.isEmbedding_induced
  have heq : extractCoordinates ∘ combineHom =
      Prod.map permutationCoordinates permutationCoordinates := by
    funext p
    exact extractCoordinates_combine p.1 p.2
  exact IsEmbedding.of_comp continuous_combine continuous_extractCoordinates (heq ▸ he)

def PreservesParity (p : PermutationGroup) : Prop := ∀ n, p.toFun n % 2 = n % 2

theorem preservesParity_inv (p : PermutationGroup) (hp : PreservesParity p) :
    PreservesParity p⁻¹ := by
  intro n
  change p.invFun n % 2 = n % 2
  have h := hp (p.invFun n)
  rw [p.right_inv] at h
  exact h.symm

theorem range_combine : range combineHom = {p | PreservesParity p} := by
  ext p
  constructor
  · rintro ⟨⟨a,b⟩,rfl⟩ n
    rcases nat_even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩ <;>
      simp [combineHom,PreservesParity,Nat.add_mod]
  · intro hp
    have hi := preservesParity_inv p hp
    have heven (q : PermutationGroup) (hq : PreservesParity q) (n : ℕ) :
        2*(q.toFun (2*n)/2) = q.toFun (2*n) := by
      have h := hq (2*n)
      have hm := Nat.mod_add_div (q.toFun (2*n)) 2
      omega
    have hodd (q : PermutationGroup) (hq : PreservesParity q) (n : ℕ) :
        2*(q.toFun (2*n+1)/2)+1 = q.toFun (2*n+1) := by
      have h := hq (2*n+1)
      have hm := Nat.mod_add_div (q.toFun (2*n+1)) 2
      omega
    let a : PermutationGroup :=
      { toFun := fun n => p.toFun (2*n)/2
        invFun := fun n => p.invFun (2*n)/2
        left_inv := by
          intro n
          change p.invFun (2*(p.toFun (2*n)/2))/2 = n
          rw [heven p hp]
          rw [p.left_inv]
          omega
        right_inv := by
          intro n
          change p.toFun (2*(p.invFun (2*n)/2))/2 = n
          have he : 2*(p.invFun (2*n)/2) = p.invFun (2*n) := heven p⁻¹ hi n
          rw [he,p.right_inv]
          omega }
    let b : PermutationGroup :=
      { toFun := fun n => p.toFun (2*n+1)/2
        invFun := fun n => p.invFun (2*n+1)/2
        left_inv := by
          intro n
          change p.invFun (2*(p.toFun (2*n+1)/2)+1)/2 = n
          rw [hodd p hp]
          rw [p.left_inv]
          omega
        right_inv := by
          intro n
          change p.toFun (2*(p.invFun (2*n+1)/2)+1)/2 = n
          have he : 2*(p.invFun (2*n+1)/2)+1 = p.invFun (2*n+1) := hodd p⁻¹ hi n
          rw [he,p.right_inv]
          omega }
    refine ⟨(a,b),?_⟩
    apply Equiv.ext
    intro n
    rcases nat_even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · change (combine a b).toFun (2*k) = p.toFun (2*k)
      rw [combine_even]
      exact heven p hp k
    · change (combine a b).toFun (2*k+1) = p.toFun (2*k+1)
      rw [combine_odd]
      exact hodd p hp k

theorem isClosed_preservesParity : IsClosed {p | PreservesParity p} := by
  simp only [PreservesParity,setOf_forall]
  apply isClosed_iInter
  intro n
  exact isClosed_eq
    ((continuous_of_discreteTopology : Continuous (fun m : ℕ => m%2)).comp
      ((continuous_apply n).comp continuous_permutationCoordinates.fst)) continuous_const

theorem isClosedEmbedding_combine : IsClosedEmbedding combineHom :=
  ⟨isEmbedding_combine,range_combine ▸ isClosed_preservesParity⟩

end FSCofinality.TwoSort
