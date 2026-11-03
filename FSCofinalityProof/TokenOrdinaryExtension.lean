import FSCofinalityProof.GenericTablesTranspose
import FSCofinalityProof.GenericTablesHistories

noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- Finite incidence requirements from one decoding role, viewed from the
new point. Different roles may place it on different sides of their tables. -/
structure FiniteRole (U : Type) where
  Opposite : Type
  count : ℕ
  context : Fin count → List Opposite
  label : Fin count → ℕ
  bit : Fin count → Bool
  raw : U → Opposite → Bool
  separated : Function.Injective (fun v => fun u => raw u v)
  direction : Bool
  role : ℕ
  consistent : ∀ i j, context i = context j → label i = label j → bit i = bit j

def orientMatrix (direction : Bool) (M : BoolMatrix) : BoolMatrix :=
  if direction then M else M.transpose

theorem orientMatrix_injective (direction : Bool) : Function.Injective (orientMatrix direction) := by
  intro M N h
  cases direction
  · have hh := congrArg BoolMatrix.transpose h
    simpa only [orientMatrix,Bool.false_eq_true,if_false,BoolMatrix.transpose_transpose] using hh
  · exact h

def FiniteRole.request {U : Type} (r : FiniteRole U) (rows : List U) (j : Fin r.count) : Request :=
  ⟨r.role,orientMatrix r.direction (contextMatrix (rows.map r.raw) (r.context j)),
    r.direction,r.label j,r.bit j⟩

/-- Simultaneous ordinary one-point extension in finitely many incident
roles, preserving an arbitrary already chosen raw context. -/
theorem ordinary_extension {U ι : Type} [Nonempty U] [Fintype ι]
    (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (initial : List U) (N : ℕ) :
    ∃ rows : List U, ∃ k > N, (∃ extra, rows = initial ++ extra) ∧
      ∀ i j, genericTable (((r i).request rows j).index k) = (r i).bit j := by
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
  obtain ⟨k,_,hk,hbits⟩ := genericTable_realizes P hP (.inl ()) N
  refine ⟨rows,k,hk,⟨allS.toList,rfl⟩,fun i j => ?_⟩
  exact hbits ((r i).request rows j)
    (Finset.mem_image.mpr ⟨⟨i,j⟩,Finset.mem_univ _,rfl⟩)

end FSCofinality.Tokens
