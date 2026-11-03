import FSCofinalityProof.TokenStructures

noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- A semantic name is the literal ambient tuple and the same full copy
label used in every incident decoding role. -/
def name {U : Type*} (P : Set U) (v : Token P) : Token U := (v.1.map Subtype.val,v.2)

theorem name_injective {U : Type*} (P : Set U) : Function.Injective (name P) := by
  intro v w h
  apply Prod.ext
  · exact (List.map_injective_iff.mpr Subtype.val_injective) (congrArg Prod.fst h)
  · exact congrArg (fun v : Token U => v.2) h

theorem list_eq_of_injOn {U V : Type*} (f : U → V) (S : Set U) (hf : S.InjOn f)
    (a b : List U) (ha : ∀ u ∈ a, u ∈ S) (hb : ∀ u ∈ b, u ∈ S)
    (h : a.map f = b.map f) : a = b := by
  have hlen : a.length = b.length := by
    simpa only [List.length_map] using congrArg List.length h
  apply List.ext_getElem hlen
  intro i hi hi'
  apply hf (ha a[i] (List.getElem_mem hi)) (hb b[i] (List.getElem_mem hi'))
  have hh := congrArg (fun l : List V => l[i]?) h
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi',Option.map_some,Option.some.injEq] using hh

/-- Shared-name successor recovery across two different raw pools. Only
the common lower pool is used as a query space; no Borel selection from
the ambient semantic quotient is involved. -/
theorem ordinary_recovery_between_pools {U V : Type*} {D : ℕ → Set ℕ} {A : Table}
    (hA : GenericOn D A) (e : ℕ) (PX PY : Set U) (Q : Set V) (raw : U → V → Bool)
    (hraw : (PX ∪ PY).InjOn (fun u => fun q : Q => raw u q.val))
    (v : Token PX) (w : Token PY)
    (hsignature : ∀ q : Token Q,
      ordinaryEdge A e (fun u : PX => fun q : Q => raw u.val q.val) v q =
        ordinaryEdge A e (fun u : PY => fun q : Q => raw u.val q.val) w q) :
    name PX v = name PY w := by
  have h : (v.1.map (fun u : PX => fun q : Q => raw u.val q.val),v.2) =
      (w.1.map (fun u : PY => fun q : Q => raw u.val q.val),w.2) := by
    apply pointed_context_injective hA e
    funext q
    exact hsignature q
  have hm : (name PX v).1.map (fun u => fun q : Q => raw u q.val) =
      (name PY w).1.map (fun u => fun q : Q => raw u q.val) := by
    simpa only [name,List.map_map,Function.comp_def] using congrArg Prod.fst h
  apply Prod.ext
  · apply list_eq_of_injOn _ _ hraw _ _ ?_ ?_ hm
    · intro u hu
      obtain ⟨u',_,rfl⟩ := List.mem_map.mp hu
      exact Or.inl u'.property
    · intro u hu
      obtain ⟨u',_,rfl⟩ := List.mem_map.mp hu
      exact Or.inr u'.property
  · exact congrArg (fun p : List (Q → Bool) × ℕ => p.2) h

/-- Every raw object appears in a singleton token. A bijection preserving
literal token names therefore identifies the entire two raw pools. -/
theorem pools_eq_of_named_bijection {U : Type*} (P Q : Set U)
    (f : Token P ≃ Token Q) (hname : ∀ v, name Q (f v) = name P v) : P = Q := by
  have hsubset : P ⊆ Q := by
    intro u hu
    let v : Token P := ([⟨u,hu⟩],0)
    have hh := congrArg Prod.fst (hname v)
    change (f v).1.map Subtype.val = [u] at hh
    have hmem : u ∈ (f v).1.map Subtype.val := by
      rw [hh]
      simp [name,v]
    obtain ⟨q,_,hq⟩ := List.mem_map.mp hmem
    simpa only [hq] using q.property
  have hreverse : Q ⊆ P := by
    intro u hu
    let w : Token Q := ([⟨u,hu⟩],0)
    have hh := congrArg Prod.fst (hname (f.symm w))
    rw [f.apply_symm_apply] at hh
    change [u] = (f.symm w).1.map Subtype.val at hh
    have hmem : u ∈ (f.symm w).1.map Subtype.val := by
      rw [← hh]
      simp [name,w]
    obtain ⟨p,_,hp⟩ := List.mem_map.mp hmem
    simpa only [hp] using p.property
  exact Set.Subset.antisymm hsubset hreverse

end FSCofinality.Tokens
