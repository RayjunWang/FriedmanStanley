import FSCofinalityProof.BorelBackAndForth

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set TopologicalSpace

namespace FSCofinality

def Preserves {L : CountableRelationalLanguage} (M : Structures L)
    (p : PermutationGroup) : Prop :=
  ∀ s a, M ⟨s,a⟩ = M ⟨s,p.toFun ∘ a⟩

def automorphismGroup {L : CountableRelationalLanguage} (M : Structures L) :
    Subgroup PermutationGroup where
  carrier := {p | Preserves M p}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro p q hp hq s a
    exact (hq s a).trans (hp s (q.toFun ∘ a))
  inv_mem' := by
    intro p hp s a
    have h := hp s (p.symm.toFun ∘ a)
    have heq : p.toFun ∘ (p.symm.toFun ∘ a) = a :=
      funext (fun i => p.apply_symm_apply (a i))
    rw [heq] at h
    exact h.symm

theorem continuous_relabel_eval {L : CountableRelationalLanguage} (M : Structures L)
    (s : L.Symbol) (a : Fin (L.arity s) → ℕ) :
    Continuous (fun p : PermutationGroup => M ⟨s,p.toFun ∘ a⟩) := by
  have hc : Continuous (fun p : PermutationGroup => p.toFun ∘ a) :=
    continuous_pi (fun i => (continuous_apply (a i)).comp continuous_permutationCoordinates.fst)
  exact (continuous_of_discreteTopology : Continuous
    (fun b : Fin (L.arity s) → ℕ => M ⟨s,b⟩)).comp hc

theorem isClosed_automorphismGroup {L : CountableRelationalLanguage} (M : Structures L) :
    IsClosed (automorphismGroup M : Set PermutationGroup) := by
  change IsClosed {p : PermutationGroup | ∀ s a, M ⟨s,a⟩ = M ⟨s,p.toFun ∘ a⟩}
  simp only [setOf_forall]
  exact isClosed_iInter (fun s => isClosed_iInter (fun a =>
    isClosed_eq continuous_const (continuous_relabel_eval M s a)))

namespace DistinguishedRestriction

def restrictPerm (Q : Set ℕ) (e : ℕ ≃ Q) (p : PermutationGroup)
    (hp : ∀ n, n ∈ Q ↔ p.toFun n ∈ Q) : PermutationGroup :=
  (e.trans ((p : ℕ ≃ ℕ).subtypeEquiv hp)).trans e.symm

@[simp] theorem restrictPerm_apply_val (Q : Set ℕ) (e : ℕ ≃ Q) (p : PermutationGroup)
    (hp : ∀ n, n ∈ Q ↔ p.toFun n ∈ Q) (n : ℕ) :
    (e ((restrictPerm Q e p hp).toFun n)).val = p.toFun (e n).val := by
  simp [restrictPerm,Equiv.subtypeEquiv]

def hom {L : CountableRelationalLanguage} (M : Structures L) (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup M, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q) :
    automorphismGroup M →* PermutationGroup where
  toFun := fun p => restrictPerm Q e p.val (hQ p)
  map_one' := by
    apply Equiv.ext
    intro n
    apply e.injective
    apply Subtype.ext
    change (e ((restrictPerm Q e 1 _).toFun n)).val = (e n).val
    rw [restrictPerm_apply_val]
    rfl
  map_mul' := by
    intro p q
    apply Equiv.ext
    intro n
    apply e.injective
    apply Subtype.ext
    change (e ((restrictPerm Q e (p*q).val (hQ (p*q))).toFun n)).val =
      (e ((restrictPerm Q e p.val (hQ p)).toFun
        ((restrictPerm Q e q.val (hQ q)).toFun n))).val
    simp only [restrictPerm_apply_val]
    rfl

theorem continuous_hom {L : CountableRelationalLanguage} (M : Structures L)
    (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup M, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q) :
    Continuous (hom M Q e hQ) := by
  have hf (n : ℕ) : Continuous (fun p : automorphismGroup M =>
      (hom M Q e hQ p).toFun n) := by
    have hv : Continuous (fun p : automorphismGroup M => p.val.toFun (e n).val) :=
      ((continuous_apply (e n).val).comp continuous_permutationCoordinates.fst).comp
        continuous_subtype_val
    have hs : Continuous (fun p : automorphismGroup M =>
        (⟨p.val.toFun (e n).val,(hQ p (e n).val).mp (e n).property⟩ : Q)) :=
      hv.subtype_mk _
    exact (continuous_of_discreteTopology : Continuous e.symm).comp hs
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · exact continuous_pi hf
  · apply continuous_pi
    intro n
    have hi := (hf n).comp (continuous_inv : Continuous (fun p : automorphismGroup M => p⁻¹))
    convert hi using 1

theorem hom_injective {L : CountableRelationalLanguage} (M : Structures L)
    (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup M, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q)
    (hfaithful : ∀ p q : automorphismGroup M,
      (∀ n ∈ Q, p.val.toFun n = q.val.toFun n) → p = q) :
    Function.Injective (hom M Q e hQ) := by
  intro p q hpq
  apply hfaithful p q
  intro n hn
  obtain ⟨k,hk⟩ := e.surjective ⟨n,hn⟩
  have h := congrArg (fun g : PermutationGroup => (e (g.toFun k)).val) hpq
  simpa only [hom,MonoidHom.coe_mk,OneHom.coe_mk,restrictPerm_apply_val,hk] using h

end DistinguishedRestriction
end FSCofinality
