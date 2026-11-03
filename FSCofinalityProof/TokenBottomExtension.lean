import FSCofinalityProof.TokenOrdinaryExtension
import FSCofinalityProof.TokenBottomRecovery

noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- The bottom map may be evaluated after an actual semantic decoder into
a standard Borel space; the raw witness pool itself needs no measurable structure. -/
theorem ordinary_bottom_extension_mapped {U V ι : Type} [Nonempty U]
    [MeasurableSpace V] [StandardBorelSpace V] [Fintype ι]
    (f : U → V) (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (initial : List U) (s : List Bool) (N : ℕ) :
    ∃ rows : List U, ∃ k > N, (∃ extra, rows = initial ++ extra) ∧
      (∀ i j, genericTable (((r i).request rows j).index k) = (r i).bit j) ∧
      Bottom.bitsPrefix (bottomListMap (rows.map f) k) s.length = s := by
  classical
  have hw (i : ι) : ∃ S : Finset U, ∀ rows : List U, (∀ u ∈ S, u ∈ rows) → ∀ a b,
      contextMatrix (rows.map (r i).raw) ((r i).context a) =
        contextMatrix (rows.map (r i).raw) ((r i).context b) →
          (r i).context a = (r i).context b :=
    finite_context_witnesses (r i).raw (r i).separated (r i).context
  choose S hS using hw
  let allS : Finset U := Finset.univ.biUnion S
  let rows := initial ++ allS.toList
  have hrows (i : ι) (u : U) (hu : u ∈ S i) : u ∈ rows := by
    apply List.mem_append_right
    apply Finset.mem_toList.mpr
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hu⟩
  let P : Finset Request := Finset.univ.image (fun q : Σ i, Fin (r i).count =>
    (r q.1).request rows q.2)
  have hP : Compatible P := by
    rintro a ha b hb heq
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨i',j'⟩,_,rfl⟩ := Finset.mem_image.mp hb
    have hii : i = i' := hr (congrArg Prod.fst heq)
    subst i'
    have hdata :
        orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j)) =
          orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j')) ∧
        (r i).label j = (r i).label j' := by
      simpa only [Request.key,FiniteRole.request,Prod.mk.injEq,true_and,and_true] using heq
    exact (r i).consistent j j'
      (hS i rows (hrows i) j j' (orientMatrix_injective _ hdata.1)) hdata.2
  obtain ⟨k,hk,hbits,hbottom⟩ :=
    Bottom.bottomMap_realization (contextOfList (rows.map f)) ⟨P,hP⟩ s N
  refine ⟨rows,k,hk,⟨allS.toList,rfl⟩,?_,hbottom⟩
  intro i j
  exact hbits ((r i).request rows j)
    (Finset.mem_image.mpr ⟨⟨i,j⟩,Finset.mem_univ _,rfl⟩)

/-- Simultaneous ordinary extension can prescribe a finite bottom prefix
while preserving every previously chosen entry of the raw context. -/
theorem ordinary_bottom_extension {U ι : Type} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
    [Fintype ι] (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (initial : List U) (s : List Bool) (N : ℕ) :
    ∃ rows : List U, ∃ k > N, (∃ extra, rows = initial ++ extra) ∧
      (∀ i j, genericTable (((r i).request rows j).index k) = (r i).bit j) ∧
      Bottom.bitsPrefix (bottomListMap rows k) s.length = s := by
  classical
  have hw (i : ι) : ∃ S : Finset U, ∀ rows : List U, (∀ u ∈ S, u ∈ rows) → ∀ a b,
      contextMatrix (rows.map (r i).raw) ((r i).context a) =
        contextMatrix (rows.map (r i).raw) ((r i).context b) →
          (r i).context a = (r i).context b :=
    finite_context_witnesses (r i).raw (r i).separated (r i).context
  choose S hS using hw
  let allS : Finset U := Finset.univ.biUnion S
  let rows := initial ++ allS.toList
  have hrows (i : ι) (u : U) (hu : u ∈ S i) : u ∈ rows := by
    apply List.mem_append_right
    apply Finset.mem_toList.mpr
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hu⟩
  let P : Finset Request := Finset.univ.image (fun q : Σ i, Fin (r i).count =>
    (r q.1).request rows q.2)
  have hP : Compatible P := by
    rintro a ha b hb heq
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨i',j'⟩,_,rfl⟩ := Finset.mem_image.mp hb
    have hrole : (r i).role = (r i').role := congrArg Prod.fst heq
    have hii : i = i' := hr hrole
    subst i'
    have hdata :
        orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j)) =
          orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j')) ∧
        (r i).label j = (r i).label j' := by
      simpa only [Request.key,FiniteRole.request,Prod.mk.injEq,true_and,and_true] using heq
    apply (r i).consistent j j' ?_ hdata.2
    exact hS i rows (hrows i) j j' (orientMatrix_injective _ hdata.1)
  obtain ⟨k,hk,hbits,hbottom⟩ :=
    Bottom.bottomMap_realization (contextOfList rows) ⟨P,hP⟩ s N
  refine ⟨rows,k,hk,⟨allS.toList,rfl⟩,?_,hbottom⟩
  intro i j
  exact hbits ((r i).request rows j)
    (Finset.mem_image.mpr ⟨⟨i,j⟩,Finset.mem_univ _,rfl⟩)

/-- The bottom requirements may instead be presented at arbitrary finitely
many natural-number coordinates, including repeated coordinates. -/
theorem ordinary_bottom_coordinates_extension {U ι J : Type}
    [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U] [Fintype ι] [Fintype J]
    (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (initial : List U) (coordinate : J → ℕ) (epsilon : J → Bool)
    (hconsistent : ∀ i j, coordinate i = coordinate j → epsilon i = epsilon j)
    (N : ℕ) :
    ∃ rows : List U, ∃ k > N, (∃ extra, rows = initial ++ extra) ∧
      (∀ i j, genericTable (((r i).request rows j).index k) = (r i).bit j) ∧
      ∀ j, bottomListMap rows k (coordinate j) = epsilon j := by
  classical
  let f : ℕ → Bool := fun n => if h : ∃ j, coordinate j = n then epsilon h.choose else false
  have hf (j : J) : f (coordinate j) = epsilon j := by
    dsimp [f]
    split_ifs with h
    · exact hconsistent h.choose j h.choose_spec
    · exact False.elim (h ⟨j,rfl⟩)
  let m := Finset.univ.sup coordinate + 1
  let s := Bottom.bitsPrefix f m
  obtain ⟨rows,k,hk,hrows,hreq,hbottom⟩ := ordinary_bottom_extension r hr initial s N
  refine ⟨rows,k,hk,hrows,hreq,fun j => ?_⟩
  have hj : coordinate j < m := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j))
  have he := congrArg (fun t : List Bool => t[coordinate j]?.getD false) hbottom
  have he' : bottomListMap rows k (coordinate j) = f (coordinate j) := by
    simpa only [s,Bottom.bitsPrefix,List.length_ofFn,List.getElem?_ofFn,
      dif_pos hj,Option.getD_some] using he
  exact he'.trans (hf j)

end FSCofinality.Tokens
