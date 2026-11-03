import FSCofinalityProof.GenericTablesPointed

noncomputable section
open Set

namespace FSCofinality.GenericTables

/-- A finite subset of any separated family is separated by finitely many
actual tests. No choice of semantic quotient representatives occurs here. -/
theorem finite_separating_tests {X T Y : Type*} (f : T → X → Y)
    (hsep : ∀ x y, x ≠ y → ∃ t, f t x ≠ f t y) (F : Finset X) :
    ∃ S : Finset T, ∀ x ∈ F, ∀ y ∈ F,
      (∀ t ∈ S, f t x = f t y) → x = y := by
  classical
  let S : Finset T := F.biUnion (fun x => F.biUnion (fun y =>
    if h : x ≠ y then {Classical.choose (hsep x y h)} else ∅))
  refine ⟨S,fun x hx y hy htests => ?_⟩
  by_contra hxy
  have ht : Classical.choose (hsep x y hxy) ∈ S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,Finset.mem_biUnion.mpr ⟨y,hy,?_⟩⟩
    simp only [dif_pos hxy,Finset.mem_singleton]
  exact (Classical.choose_spec (hsep x y hxy)) (htests _ ht)

theorem context_ext_of_all_rows {U V : Type*} [Nonempty U] (R : U → V → Bool)
    (hcol : Function.Injective (fun v => fun u => R u v)) (s t : List V)
    (h : ∀ u, s.map (R u) = t.map (R u)) : s = t := by
  have hlen : s.length = t.length := by
    have hh := congrArg List.length (h (Classical.arbitrary U))
    simpa only [List.length_map] using hh
  apply List.ext_getElem hlen
  intro i hi hi'
  apply hcol
  funext u
  have hh := congrArg (fun l : List Bool => l[i]?) (h u)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi',Option.map_some,Option.some.injEq] using hh

theorem matrix_eq_implies_row_eq {U V : Type*} (R : U → V → Bool)
    (rows : List U) (u : U) (hu : u ∈ rows) (s t : List V)
    (hm : contextMatrix (rows.map R) s = contextMatrix (rows.map R) t) :
    s.map (R u) = t.map (R u) := by
  obtain ⟨i,hi,hu⟩ := List.mem_iff_getElem.mp hu
  have hlen : s.length = t.length := congrArg (fun M : BoolMatrix => M.2.1) hm
  apply List.ext_getElem (by simpa only [List.length_map] using hlen)
  intro j hj hj'
  have hs : j < s.length := by simpa only [List.length_map] using hj
  have ht : j < t.length := by simpa only [List.length_map] using hj'
  have hrow : i < (rows.map R).length := by simpa only [List.length_map] using hi
  have hh := congrArg (fun M : BoolMatrix => M.entry i j) hm
  simpa only [contextMatrix_entry _ _ i j hrow hs,contextMatrix_entry _ _ i j hrow ht,
    List.getElem_map,hu] using hh

/-- The witnesses may be appended to an already fixed context and combined
with witnesses for other roles: only their membership in the final tuple matters. -/
theorem finite_context_witnesses {U V ι : Type*} [Nonempty U] [Fintype ι]
    (R : U → V → Bool) (hcol : Function.Injective (fun v => fun u => R u v))
    (s : ι → List V) :
    ∃ S : Finset U, ∀ rows : List U, (∀ u ∈ S, u ∈ rows) → ∀ i j,
      contextMatrix (rows.map R) (s i) = contextMatrix (rows.map R) (s j) → s i = s j := by
  classical
  have hsep (a b : List V) (hab : a ≠ b) : ∃ u : U, a.map (R u) ≠ b.map (R u) := by
    by_contra! h
    exact hab (context_ext_of_all_rows R hcol a b h)
  obtain ⟨S,hS⟩ := finite_separating_tests (fun u a => a.map (R u)) hsep
    (Finset.univ.image s)
  refine ⟨S,fun rows hrows i j hm => ?_⟩
  apply hS (s i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    (s j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  intro u hu
  exact matrix_eq_implies_row_eq R rows u (hrows u hu) _ _ hm

end FSCofinality.GenericTables
