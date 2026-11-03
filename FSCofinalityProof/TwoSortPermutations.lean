import FSCofinalityProof.AutomorphismGroups

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology TopologicalSpace Filter

namespace FSCofinality.TwoSort

def split : ℕ ≃ ℕ ⊕ ℕ where
  toFun n := if n%2=0 then Sum.inl (n/2) else Sum.inr (n/2)
  invFun := Sum.elim (fun n => 2*n) (fun n => 2*n+1)
  left_inv n := by
    dsimp
    split_ifs with h
    · change 2*(n/2)=n
      omega
    · have hm := Nat.mod_lt n (by omega : 0<2)
      change 2*(n/2)+1=n
      omega
  right_inv n := by
    cases n <;> simp [Nat.add_mod] <;> omega

def combine (p q : PermutationGroup) : PermutationGroup :=
  (split.trans (Equiv.sumCongr (p : ℕ ≃ ℕ) (q : ℕ ≃ ℕ))).trans split.symm

@[simp] theorem combine_even (p q : PermutationGroup) (n : ℕ) :
    (combine p q).toFun (2*n) = 2*p.toFun n := by simp [combine,split]

@[simp] theorem combine_odd (p q : PermutationGroup) (n : ℕ) :
    (combine p q).toFun (2*n+1) = 2*q.toFun n+1 := by
  simp [combine,split,Nat.add_mod]
  omega

theorem nat_even_or_odd (n : ℕ) : (∃ k, n=2*k) ∨ ∃ k, n=2*k+1 := by
  have hm := Nat.mod_lt n (by omega : 0<2)
  by_cases h : n%2=0
  · exact Or.inl ⟨n/2,by omega⟩
  · exact Or.inr ⟨n/2,by omega⟩

def combineHom : PermutationGroup × PermutationGroup →* PermutationGroup where
  toFun p := combine p.1 p.2
  map_one' := by
    apply Equiv.ext
    intro n
    rcases nat_even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · change (combine 1 1).toFun (2*k) = 2*k
      rw [combine_even]
      rfl
    · change (combine 1 1).toFun (2*k+1) = 2*k+1
      rw [combine_odd]
      rfl
  map_mul' := by
    intro p q
    apply Equiv.ext
    intro n
    rcases nat_even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · change (combine (p.1*q.1) (p.2*q.2)).toFun (2*k) =
        (combine p.1 p.2).toFun ((combine q.1 q.2).toFun (2*k))
      simp only [combine_even]
      rfl
    · change (combine (p.1*q.1) (p.2*q.2)).toFun (2*k+1) =
        (combine p.1 p.2).toFun ((combine q.1 q.2).toFun (2*k+1))
      simp only [combine_odd]
      rfl

theorem combine_injective : Function.Injective combineHom := by
  intro p q hpq
  apply Prod.ext
  · apply Equiv.ext
    intro n
    have h := congrArg (fun r : PermutationGroup => r.toFun (2*n)) hpq
    change (combine p.1 p.2).toFun (2*n) = (combine q.1 q.2).toFun (2*n) at h
    simp only [combine_even] at h
    change p.1.toFun n = q.1.toFun n
    omega
  · apply Equiv.ext
    intro n
    have h := congrArg (fun r : PermutationGroup => r.toFun (2*n+1)) hpq
    change (combine p.1 p.2).toFun (2*n+1) = (combine q.1 q.2).toFun (2*n+1) at h
    simp only [combine_odd] at h
    change p.2.toFun n = q.2.toFun n
    omega

def Evens : Set ℕ := {n | n%2=0}

def evenEnumeration : ℕ ≃ Evens where
  toFun n := ⟨2*n,by simp [Evens]⟩
  invFun n := n.val/2
  left_inv n := by simp
  right_inv n := by
    apply Subtype.ext
    change 2*(n.val/2)=n.val
    have hm : n.val%2=0 := n.property
    omega

theorem combine_preserves_evens (p q : PermutationGroup) (n : ℕ) :
    n ∈ Evens ↔ (combine p q).toFun n ∈ Evens := by
  rcases nat_even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩ <;>
    simp [Evens,Nat.add_mod]

end FSCofinality.TwoSort
