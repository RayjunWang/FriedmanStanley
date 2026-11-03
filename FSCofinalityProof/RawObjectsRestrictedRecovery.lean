import FSCofinalityProof.RawObjectsNaturality
import FSCofinalityProof.TokenLimitRecovery
import FSCofinalityProof.TokenNamedRecovery

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects
open Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta)

def restrictedProfile (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb) (n : ℕ)
    (u : Ambient eta heta) (c : Column eta heta lam hlam lower n) : Bool :=
  ambientProfile eta heta lam hlam htop n u (mapColumn eta heta lam hlam hsub n c)

theorem restrictedProfile_rowObject
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb) (n : ℕ)
    (r : LimitRow eta heta lam hlam lower) (c : Column eta heta lam hlam lower n) :
    restrictedProfile eta heta lam hlam htop lower hsub n
      (rowObject eta heta lam hlam lower htop r) c = profile eta heta lam hlam lower n r c :=
  ambientProfile_restricted eta heta lam hlam htop hsub n r c

theorem restrictedFullProfile_injOn
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb) :
    (LimitSet eta heta lam hlam lower).InjOn
      (fun u => fun n => restrictedProfile eta heta lam hlam htop lower hsub n u) := by
  intro u hu v hv huv
  obtain ⟨r,rfl⟩ := exists_rowObject_of_mem_limitSet eta heta lam hlam lower htop hu
  obtain ⟨s,rfl⟩ := exists_rowObject_of_mem_limitSet eta heta lam hlam lower htop hv
  have heq : (fun n => profile eta heta lam hlam lower n r) =
      (fun n => profile eta heta lam hlam lower n s) := by
    funext n c
    have h := congrFun (congrFun huv n) c
    simpa only [restrictedProfile_rowObject] using h
  exact congrArg (rowObject eta heta lam hlam lower htop)
    (fullProfile_injective eta heta lam hlam lower heq)

theorem restrictedProfile_propagate
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb) (n : ℕ)
    (u : Ambient eta heta) (c : Column eta heta lam hlam lower n) :
    restrictedProfile eta heta lam hlam htop lower hsub (n+1) u
      (propagate eta heta lam hlam lower n c) =
        restrictedProfile eta heta lam hlam htop lower hsub n u c := by
  unfold restrictedProfile
  rw [mapColumn_propagate,ambientProfile_propagate]

theorem restricted_limit_recovery
    {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A) (e : ℕ → ℕ)
    (lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb)
    (hsub' : ∀ b hb, upper b hb ⊆ fullLower eta heta lam b hb)
    (hLU : lower=upper) (PX PY : Set (Ambient eta heta))
    (hPX : PX ⊆ LimitSet eta heta lam hlam lower)
    (hPY : PY ⊆ LimitSet eta heta lam hlam upper)
    (f : ∀ n, Token (Column eta heta lam hlam lower n) ≃ Token (Column eta heta lam hlam upper n))
    (hf : ∀ n q, mapToken (encodeColumn eta heta lam hlam upper n) (f n q) =
      mapToken (encodeColumn eta heta lam hlam lower n) q)
    (v : Token PX) (w : Token PY)
    (hedge : ∀ n q,
      branchEdge (fun n (u : PX) => restrictedProfile eta heta lam hlam htop lower hsub n u.val)
        A (e n) n v q =
      branchEdge (fun n (u : PY) => restrictedProfile eta heta lam hlam htop upper hsub' n u.val)
        A (e n) n w (f n q)) : name PX v = name PY w := by
  subst upper
  have hfId (n : ℕ) (q : Token (Column eta heta lam hlam lower n)) : f n q = q := by
    have h := hf n q
    apply Prod.ext
    · exact List.map_injective_iff.mpr (encodeColumn_injective eta heta lam hlam lower htop n)
        (congrArg Prod.fst h)
    · exact congrArg (fun p : Token (Ambient eta heta) => p.2) h
  apply limit_recovery_between_pools hA e PX PY
    (restrictedProfile eta heta lam hlam htop lower hsub)
    (propagate eta heta lam hlam lower)
  · intro n u _ c
    exact restrictedProfile_propagate eta heta lam hlam htop lower hsub n u c
  · apply (restrictedFullProfile_injOn eta heta lam hlam htop lower hsub).mono
    exact union_subset hPX hPY
  · intro n q
    simpa only [hfId] using hedge n q

end FSCofinality.RawObjects
