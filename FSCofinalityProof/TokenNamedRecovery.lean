import FSCofinalityProof.TokenRecovery
import FSCofinalityProof.TokenMap
import FSCofinalityProof.GenericTablesTranspose

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.Tokens
open GenericTables

theorem contextMatrix_map {U V W Z : Type} (R : W → Z → Bool)
    (f : U → W) (g : V → Z) (s : List U) (t : List V) :
    contextMatrix (s.map (fun u v => R (f u) (g v))) t =
      contextMatrix ((s.map f).map R) (t.map g) := by
  apply BoolMatrix.ext
  · simp only [contextMatrix,List.length_map]
  · simp only [contextMatrix,List.length_map]
  · intro i j
    by_cases hi : i < s.length <;> by_cases hj : j < t.length
    all_goals simp [BoolMatrix.entry,contextMatrix,hi,hj]

theorem ordinaryEdge_map {U V W Z : Type} (A : Table) (e : ℕ) (R : W → Z → Bool)
    (f : U → W) (g : V → Z) (v : Token U) (w : Token V) :
    ordinaryEdge A e (fun u v => R (f u) (g v)) v w =
      ordinaryEdge A e R (mapToken f v) (mapToken g w) := by
  unfold ordinaryEdge
  rw [contextMatrix_map]
  rfl

theorem named_ordinary_recovery {U X Y V W : Type}
    {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A) (e : ℕ)
    (nx : X → U) (ny : Y → U) (nv : V → U) (nw : W → U) (R : U → U → Bool)
    (f : Token V ≃ Token W) (hf : ∀ q, mapToken nw (f q) = mapToken nv q)
    (hinj : (range nx ∪ range ny).InjOn (fun u => fun q : V => R u (nv q)))
    (v : Token X) (w : Token Y)
    (hedge : ∀ q, ordinaryEdge A e (fun u t => R (nx u) (nv t)) v q =
      ordinaryEdge A e (fun u t => R (ny u) (nw t)) w (f q)) :
    mapToken nx v = mapToken ny w := by
  have hsig : (v.1.map (fun u => fun q : V => R (nx u) (nv q)),v.2) =
      (w.1.map (fun u => fun q : V => R (ny u) (nv q)),w.2) := by
    apply pointed_context_injective hA e
    funext q
    have h := hedge q
    rw [ordinaryEdge_map A e R ny nw, hf] at h
    rw [← ordinaryEdge_map A e R ny nv] at h
    exact h
  have hnames : (v.1.map nx).map (fun u => fun q : V => R u (nv q)) =
      (w.1.map ny).map (fun u => fun q : V => R u (nv q)) := by
    simpa only [List.map_map,Function.comp_def] using congrArg Prod.fst hsig
  apply Prod.ext
  · apply list_eq_of_injOn _ _ hinj _ _ _ _ hnames
    · intro u hu
      obtain ⟨z,_,rfl⟩ := List.mem_map.mp hu
      exact Or.inl (mem_range_self z)
    · intro u hu
      obtain ⟨z,_,rfl⟩ := List.mem_map.mp hu
      exact Or.inr (mem_range_self z)
  · exact congrArg (fun p : List (V → Bool) × ℕ => p.2) hsig

end FSCofinality.Tokens
