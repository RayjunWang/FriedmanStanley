import FSCofinalityProof.GenericTablesFiniteContexts

noncomputable section

namespace FSCofinality.GenericTables

def BoolMatrix.transpose (M : BoolMatrix) : BoolMatrix :=
  ⟨M.2.1,M.1,fun j i => M.2.2 i j⟩

@[simp] theorem BoolMatrix.transpose_transpose (M : BoolMatrix) : M.transpose.transpose = M := by
  cases M with | mk l rest => cases rest; rfl

theorem BoolMatrix.ext (M N : BoolMatrix) (hl : M.1 = N.1) (hm : M.2.1 = N.2.1)
    (he : ∀ i j, M.entry i j = N.entry i j) : M = N := by
  cases M with | mk l rest =>
    cases rest with | mk m f =>
      cases N with | mk l' rest' =>
        cases rest' with | mk m' g =>
          dsimp at hl hm
          subst l'
          subst m'
          have hfg : f = g := by
            funext i j
            have hh := he i j
            simpa only [BoolMatrix.entry,dif_pos i.isLt,dif_pos j.isLt] using hh
          rw [hfg]

theorem transpose_contextMatrix {U V : Type*} (R : U → V → Bool) (t : List U) (s : List V) :
    (contextMatrix (t.map R) s).transpose = contextMatrix (s.map (fun v u => R u v)) t := by
  apply BoolMatrix.ext
  · simp only [BoolMatrix.transpose,contextMatrix,List.length_map]
  · simp only [BoolMatrix.transpose,contextMatrix,List.length_map]
  · intro i j
    by_cases hi : i < s.length <;> by_cases hj : j < t.length
    all_goals simp [BoolMatrix.entry,BoolMatrix.transpose,contextMatrix,hi,hj]

/-- The dual witness lemma supplies columns distinguishing every finite
family of upper tuples. These are the same new raw context entries used
in the lower roles, so finite witness sets can be combined. -/
theorem finite_column_witnesses {U V ι : Type*} [Nonempty V] [Fintype ι]
    (R : U → V → Bool) (hrow : Function.Injective R) (t : ι → List U) :
    ∃ S : Finset V, ∀ columns : List V, (∀ v ∈ S, v ∈ columns) → ∀ i j,
      contextMatrix ((t i).map R) columns = contextMatrix ((t j).map R) columns → t i = t j := by
  obtain ⟨S,hS⟩ := finite_context_witnesses (fun v u => R u v) hrow t
  refine ⟨S,fun columns hcols i j hm => ?_⟩
  apply hS columns hcols i j
  have hh := congrArg BoolMatrix.transpose hm
  simpa only [transpose_contextMatrix] using hh

end FSCofinality.GenericTables
