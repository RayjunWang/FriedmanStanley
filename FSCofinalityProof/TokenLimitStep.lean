import FSCofinalityProof.TokenHistoryOperations
import FSCofinalityProof.GenericTablesFiniteContexts

noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- One constrained branch level: append the actual raw witnesses at that
level, choose a local history label in its genuine infinite fiber, and
preserve every earlier active tuple and local history. -/
theorem limit_branch_step {U : Type} [Nonempty U] {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool) (e n : ℕ)
    (hcol : Function.Injective (fun c : Col n => fun u => profile n u c))
    (v : Token U) (hbound : ∀ a ∈ (history v).val.activation, a ≤ n)
    {ι : Type} [Fintype ι] (c : ι → Token (Col n)) (epsilon : ι → Bool)
    (hconsistent : ∀ i j, c i = c j → epsilon i = epsilon j) (labelBound : ℕ) :
    ∃ w : Token U, ∃ extra : List U,
      w.1 = v.1 ++ extra ∧ labelBound < localCode w n ∧
      (∀ a ∈ (history w).val.activation, a ≤ n) ∧
      (∀ m < n, localCode w m = localCode v m ∧ activeTuple w m = activeTuple v m) ∧
      ∀ i, branchEdge profile genericTable e n w (c i) = epsilon i := by
  classical
  obtain ⟨S,hS⟩ := finite_context_witnesses (profile n) hcol (fun i => (c i).1)
  let extra := S.toList
  let rows := v.1 ++ extra
  let v0 := extendAt v n extra hbound
  have hrows (u : U) (hu : u ∈ S) : u ∈ rows :=
    List.mem_append_right _ (Finset.mem_toList.mpr hu)
  let req : ι → Request := fun i =>
    ⟨e,contextMatrix (rows.map (profile n)) (c i).1,true,(c i).2,epsilon i⟩
  let P := Finset.univ.image req
  have hP : Compatible P := by
    rintro a ha b hb heq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    have hdata : contextMatrix (rows.map (profile n)) (c i).1 =
        contextMatrix (rows.map (profile n)) (c j).1 ∧ (c i).2 = (c j).2 := by
      simpa only [Request.key,req,Prod.mk.injEq,true_and,and_true] using heq
    exact hconsistent i j (Prod.ext (hS rows hrows i j hdata.1) hdata.2)
  have hbound0 : ∀ a ∈ (history v0).val.activation, a ≤ n := by
    intro a ha
    rw [show v0 = extendAt v n extra hbound from rfl,extendAt_history] at ha
    rcases List.mem_append.mp ha with hold | hnew
    · exact hbound a hold
    · exact le_of_eq (List.eq_of_mem_replicate hnew)
  obtain ⟨z,hz,hzN,hbits⟩ := genericTable_realizes P hP
    (.inr (.inl ((history v0).val.activation,(history v0).val.noiseBefore n))) labelBound
  change z ∈ localLabelSet (history v0).val.activation ((history v0).val.noiseBefore n) at hz
  obtain ⟨k,hk⟩ := hz
  let w := withNoiseAt v0 n k
  have hcode : localCode w n = z := by
    rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_localCode_at,
      activeTimes_eq_self _ _ hbound0]
    exact hk
  have hfull : activeTuple w n = rows := by
    rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_activeTuple,
      activeTuple_eq_full v0 n hbound0]
    rfl
  have hboundw : ∀ a ∈ (history w).val.activation, a ≤ n := by
    intro a ha
    rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_history] at ha
    exact hbound0 a ha
  refine ⟨w,extra,rfl,by rwa [hcode],hboundw,?_,?_⟩
  · intro m hm
    refine ⟨?_,?_⟩
    · rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_localCode_earlier _ _ _ _ hm]
      exact extendAt_localCode v n extra hbound m hm
    · rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_activeTuple]
      exact extendAt_activeTuple v n extra hbound m hm
  · intro i
    change genericTable (e,contextMatrix ((activeTuple w n).map (profile n)) (c i).1,
      (c i).2,localCode w n) = epsilon i
    rw [hfull,hcode]
    exact hbits (req i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

end FSCofinality.Tokens
