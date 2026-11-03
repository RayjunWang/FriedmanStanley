import FSCofinalityProof.TokenHistoryOperations

noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

theorem fullLabelFiber_snapshot {U : Type*} (v : Token U) (M z : ℕ)
    (hz : z ∈ fullLabelSet (history v).val M) :
    ∀ n ≤ M, localCode (v.1,z) n = localCode v n ∧
      activeTuple (v.1,z) n = activeTuple v n := by
  have hpres := fullLabelSet_preserves_prefix (history v).val M z hz
  dsimp only at hpres
  rw [(history v).property] at hpres
  have ha : (history (v.1,z)).val.activation = (history v).val.activation := by
    simpa only [history] using hpres.1
  intro n hn
  refine ⟨?_,?_⟩
  · simpa only [localCode,history] using hpres.2 n hn
  · unfold activeTuple activeLength History.activeTimes
    rw [ha]

/-- Once the actual full raw tuple and activation list are fixed, the
eventually-zero tail realizes any compatible finite upper-table pattern
without changing any previously fixed branch snapshot. -/
theorem limit_tail_realization {U : Type*} (v : Token U) (M : ℕ)
    (P : Finset Request) (hP : Compatible P) (labelBound : ℕ) :
    ∃ w : Token U, w.1 = v.1 ∧ labelBound < w.2 ∧
      (∀ n ≤ M, localCode w n = localCode v n ∧ activeTuple w n = activeTuple v n) ∧
      ∀ r ∈ P, genericTable (r.index w.2) = r.value := by
  obtain ⟨z,hz,hN,hbits⟩ := genericTable_realizes P hP
    (.inr (.inr ((history v).val,M))) labelBound
  exact ⟨(v.1,z),rfl,hN,fullLabelFiber_snapshot v M z hz,hbits⟩

/-- Late raw witnesses for ordinary upper roles preserve the complete
already fixed branch snapshots, including the active profile tuples. -/
theorem late_witnesses_preserve {U : Type*} (v : Token U) (M : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ M) :
    ∃ w : Token U, w.1 = v.1 ++ extra ∧
      ∀ n ≤ M, localCode w n = localCode v n ∧ activeTuple w n = activeTuple v n := by
  let hb : ∀ a ∈ (history v).val.activation, a ≤ M+1 :=
    fun a ha => (hbound a ha).trans (Nat.le_succ M)
  refine ⟨extendAt v (M+1) extra hb,rfl,fun n hn => ?_⟩
  exact ⟨extendAt_localCode v (M+1) extra hb n (by omega),
    extendAt_activeTuple v (M+1) extra hb n (by omega)⟩

end FSCofinality.Tokens
