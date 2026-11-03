import FSCofinalityProof.RawObjectsNaturality

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

/-- Every finite birth support gives a filler row in the actual countable
pool, independently of the source seeds. -/
theorem pool_fillerRow (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient eta heta))
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta)
    (A : Finset (Birth eta heta lam hlam (fun b _ => Pool eta heta seeds b))) :
    rowObject eta heta lam hlam (fun b _ => Pool eta heta seeds b) htop (.inr A) ∈
      Pool eta heta seeds lam := by
  rw [pool_limit eta heta seeds lam hlam]
  apply Or.inr
  apply (mem_finiteImages_iff _ _ _).mpr
  refine ⟨A.map (birthEmbedding eta heta lam hlam (fun b _ => Pool eta heta seeds b) htop),?_,rfl⟩
  intro p hp
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hp
  exact encodeNew_mem eta heta lam hlam (fun b _ => Pool eta heta seeds b) b.1 b.2

/-- Restricting rows and columns to the same actual pool retains column
separation: a singleton birth-support filler distinguishes each column. -/
theorem pool_profile_column_separating (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient eta heta))
    (hseeds : ∀ a, seeds a ⊆ Valid eta heta a)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta) (n : ℕ) :
    Function.Injective (fun c : Column eta heta lam hlam (fun b _ => Pool eta heta seeds b) n =>
      fun u : Pool eta heta seeds lam => ambientProfile eta heta lam hlam htop n u.val
        (mapColumn eta heta lam hlam
          (fun b _ => pool_subset_valid eta heta seeds hseeds b) n c)) := by
  intro c d hcd
  let A : Finset (Birth eta heta lam hlam (fun b _ => Pool eta heta seeds b)) := {c.val}
  let r : LimitRow eta heta lam hlam (fun b _ => Pool eta heta seeds b) := .inr A
  have hr : rowObject eta heta lam hlam (fun b _ => Pool eta heta seeds b) htop r ∈
      Pool eta heta seeds lam := pool_fillerRow eta heta seeds lam hlam htop A
  have hquery := congrFun hcd ⟨rowObject eta heta lam hlam (fun b _ => Pool eta heta seeds b) htop r,hr⟩
  have hlocal := (ambientProfile_restricted eta heta lam hlam htop
      (fun b _ => pool_subset_valid eta heta seeds hseeds b) n r c).symm.trans
    (hquery.trans (ambientProfile_restricted eta heta lam hlam htop
      (fun b _ => pool_subset_valid eta heta seeds hseeds b) n r d))
  have hm : d.val ∈ ({c.val} : Finset (Birth eta heta lam hlam (fun b _ => Pool eta heta seeds b))) := by
    by_contra hn
    simp only [r,A,profile,rowBit,Finset.mem_singleton,decide_true] at hlocal
    simp only [Finset.mem_singleton] at hn
    simp only [decide_eq_false hn] at hlocal
    contradiction
  exact Subtype.ext (Finset.mem_singleton.mp hm).symm

end FSCofinality.RawObjects
