import FSCofinalityProof.TokenMap

noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- Limit recovery in two countable presentations of the same ambient raw
universe. Full profile injectivity is needed only on the two actual pools. -/
theorem limit_recovery_between_pools {U : Type*} {Col : ℕ → Type*}
    {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A) (e : ℕ → ℕ)
    (PX PY : Set U) (profile : ∀ n, U → Col n → Bool)
    (j : ∀ n, Col n → Col (n+1))
    (propagate : ∀ n, ∀ u ∈ PX ∪ PY, ∀ c, profile (n+1) u (j n c) = profile n u c)
    (hinj : (PX ∪ PY).InjOn (fun u => fun n => profile n u))
    (v : Token PX) (w : Token PY)
    (hsignature : ∀ n q,
      branchEdge (fun n u => profile n u.val) A (e n) n v q =
        branchEdge (fun n u => profile n u.val) A (e n) n w q) :
    name PX v = name PY w := by
  let S := PX ∪ PY
  let liftX : PX → S := fun u => ⟨u.val,Or.inl u.property⟩
  let liftY : PY → S := fun u => ⟨u.val,Or.inr u.property⟩
  let p : ∀ n, S → Col n → Bool := fun n u => profile n u.val
  have hp : Function.Injective (fun u : S => fun n => p n u) := by
    intro u v heq
    apply Subtype.ext
    exact hinj u.property v.property heq
  have hR (n : ℕ) : R p n (mapToken liftX v) (mapToken liftY w) := by
    apply (R_iff_branch_neighborhood p hA (e n) n _ _).mpr
    intro q
    rw [branchEdge_mapToken,branchEdge_mapToken]
    exact hsignature n q
  have heq := all_R_separate p j (fun n u c => propagate n u.val u.property c) hp hR
  have hn := congrArg (name S) heq
  simpa only [name,mapToken,List.map_map,Function.comp_def,liftX,liftY] using hn

end FSCofinality.Tokens
