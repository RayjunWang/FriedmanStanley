import FSCofinalityProof.HierarchyBasics

noncomputable section
open Set MeasureTheory TopologicalSpace

namespace FSCofinality

/-- The coinduced measurable structure on a countable dependent sum is
standard Borel when every summand is standard Borel. -/
theorem standardBorel_sigma {X : ℕ → Type} [∀ n, MeasurableSpace (X n)]
    [∀ n, StandardBorelSpace (X n)] : StandardBorelSpace (Σ n, X n) := by
  choose t hb hp using (fun n => StandardBorelSpace.polish (α := X n))
  letI : ∀ n, TopologicalSpace (X n) := t
  letI : ∀ n, BorelSpace (X n) := hb
  letI : ∀ n, PolishSpace (X n) := hp
  have hB : (inferInstance : MeasurableSpace (Σ n, X n)) = borel (Σ n, X n) := by
    apply le_antisymm
    · intro s hs
      have hslice (n : ℕ) : MeasurableSet (Sigma.mk n ⁻¹' s) :=
        MeasurableSpace.measurableSet_iInf.mp hs n
      letI : MeasurableSpace (Σ n, X n) := borel (Σ n, X n)
      letI : BorelSpace (Σ n, X n) := ⟨rfl⟩
      have himage (n : ℕ) : MeasurableSet (Sigma.mk n '' (Sigma.mk n ⁻¹' s)) :=
        (Topology.IsOpenEmbedding.sigmaMk (i := n)).measurableEmbedding.measurableSet_image' (hslice n)
      have heq : s = ⋃ n, Sigma.mk n '' (Sigma.mk n ⁻¹' s) := by
        apply le_antisymm
        · rintro ⟨n,x⟩ hx
          exact mem_iUnion.mpr ⟨n,⟨x,hx,rfl⟩⟩
        · intro z hz
          obtain ⟨n,x,hx,rfl⟩ := mem_iUnion.mp hz
          exact hx
      rw [heq]
      exact MeasurableSet.iUnion himage
    · change MeasurableSpace.generateFrom {s : Set (Σ n, X n) | IsOpen s} ≤ _
      apply MeasurableSpace.generateFrom_le
      intro s hs
      apply MeasurableSpace.measurableSet_iInf.mpr
      intro n
      change MeasurableSet (Sigma.mk n ⁻¹' s)
      exact (hs.preimage (continuous_sigmaMk (i := n))).measurableSet
  letI : BorelSpace (Σ n, X n) := ⟨hB⟩
  letI : PolishSpace (Σ n, X n) :=
    { toSecondCountableTopology := inferInstance
      toIsCompletelyMetrizableSpace := inferInstance }
  infer_instance

end FSCofinality
