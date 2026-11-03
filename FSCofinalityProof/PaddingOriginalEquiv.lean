import FSCofinalityProof.PaddingBranches
import FSCofinalityProof.PaddingTupleGraphs

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

theorem TreeIso.original_image {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) :
    ∃ t : List ℕ, e.equiv (Sum.inl s) = Sum.inl t :=
  (PaddedNode.branch_iff_original a D _).mp
    (e.map_branch (PaddedNode.branch_from_original a C s))

def TreeIso.originalMap {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) : List ℕ :=
  Classical.choose (e.original_image s)

theorem TreeIso.originalMap_spec {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) :
    e.equiv (Sum.inl s) = Sum.inl (e.originalMap s) := Classical.choose_spec (e.original_image s)

theorem TreeIso.originalMap_bijective {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) :
    Function.Bijective e.originalMap := by
  constructor
  · intro s t h
    apply Sum.inl.inj
    apply e.equiv.injective
    rw [e.originalMap_spec s,e.originalMap_spec t,h]
  · intro t
    obtain ⟨s,hs⟩ := e.symm.original_image t
    refine ⟨s,?_⟩
    apply Sum.inl.inj
    have he := congrArg e.equiv hs
    simpa only [TreeIso.symm,Equiv.apply_symm_apply,e.originalMap_spec s] using he.symm

def TreeIso.originalEquiv {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) : List ℕ ≃ List ℕ :=
  Equiv.ofBijective e.originalMap e.originalMap_bijective

theorem TreeIso.originalEquiv_colors {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) :
    D (e.originalEquiv s) = C s := by
  have h := e.colors (Sum.inl s)
  rw [e.originalMap_spec s] at h
  exact h

theorem TreeIso.originalEquiv_root {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) : e.originalEquiv [] = [] := by
  apply Sum.inl.inj
  exact (e.originalMap_spec []).symm.trans e.roots

theorem TreeIso.originalEquiv_parent {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) :
    e.originalEquiv s.dropLast = (e.originalEquiv s).dropLast := by
  have h := e.parents (Sum.inl s)
  change e.equiv (Sum.inl s.dropLast) = PaddedNode.parent (e.equiv (Sum.inl s)) at h
  rw [e.originalMap_spec s.dropLast,e.originalMap_spec s] at h
  exact Sum.inl.inj h

theorem TreeIso.originalEquiv_length {a : Ordinal.{0}} {G H : GraphSpace}
    (e : TreeIso (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H)))
    (s : List ℕ) : (e.originalEquiv s).length = s.length :=
  length_eq_of_tupleColor_eq (e.originalEquiv_colors s)

theorem TreeIso.originalEquiv_extension {a : Ordinal.{0}} {G H : GraphSpace}
    (e : TreeIso (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H)))
    (s : List ℕ) (n : ℕ) :
    ∃ m : ℕ, e.originalEquiv (s ++ [n]) = e.originalEquiv s ++ [m] := by
  let t := e.originalEquiv (s ++ [n])
  have hne : t ≠ [] := by
    intro ht
    have hlen := e.originalEquiv_length (s ++ [n])
    change t.length = (s ++ [n]).length at hlen
    rw [ht] at hlen
    simp at hlen
  refine ⟨t.getLast hne,?_⟩
  have hp : t.dropLast = e.originalEquiv s := by
    simpa only [List.dropLast_append_getLast,List.dropLast_concat] using
      (e.originalEquiv_parent (s ++ [n])).symm
  simpa only [hp] using (List.dropLast_append_getLast hne).symm

theorem TreeIso.originalEquiv_backextension {a : Ordinal.{0}} {G H : GraphSpace}
    (e : TreeIso (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H)))
    (s : List ℕ) (m : ℕ) :
    ∃ n : ℕ, e.originalEquiv (s ++ [n]) = e.originalEquiv s ++ [m] := by
  let t := e.originalEquiv.symm (e.originalEquiv s ++ [m])
  have ht : e.originalEquiv t = e.originalEquiv s ++ [m] := e.originalEquiv.apply_symm_apply _
  have hne : t ≠ [] := by
    intro hn
    rw [hn,e.originalEquiv_root] at ht
    simp at ht
  have hp : t.dropLast = s := by
    apply e.originalEquiv.injective
    rw [e.originalEquiv_parent t,ht]
    simp
  refine ⟨t.getLast hne,?_⟩
  have hst : s ++ [t.getLast hne] = t := by
    simpa only [hp] using List.dropLast_append_getLast hne
  rwa [hst]

end FSCofinality.Padding
