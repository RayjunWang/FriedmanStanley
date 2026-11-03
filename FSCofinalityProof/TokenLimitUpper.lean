import FSCofinalityProof.TokenOrdinaryExtension
import FSCofinalityProof.TokenLimitTail

noncomputable section

namespace FSCofinality.Tokens
open GenericTables

/-- Ordinary upper roles are met after all branch levels have been fixed.
Their actual raw witnesses activate later than `M`; the final tail varies
inside the full-history prefix fiber and retains every earlier snapshot. -/
theorem limit_upper_extension {U ι : Type} [Nonempty U] [Fintype ι]
    (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (v : Token U) (M : ℕ) (hbound : ∀ a ∈ (history v).val.activation, a ≤ M)
    (labelBound : ℕ) :
    ∃ w : Token U, labelBound < w.2 ∧
      (∀ n ≤ M, localCode w n = localCode v n ∧ activeTuple w n = activeTuple v n) ∧
      ∀ i j, genericTable (((r i).request w.1 j).index w.2) = (r i).bit j := by
  classical
  obtain ⟨rows,k,_,⟨extra,hrows⟩,hreq⟩ := ordinary_extension r hr v.1 0
  let P : Finset Request := Finset.univ.image (fun q : Σ i, Fin (r i).count =>
    (r q.1).request rows q.2)
  have hP : Compatible P := by
    apply compatible_of_realization genericTable P k
    intro a ha
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp ha
    exact hreq i j
  obtain ⟨v0,hv0,hprefix⟩ := late_witnesses_preserve v M extra hbound
  have htuple : v0.1 = rows := hv0.trans hrows.symm
  obtain ⟨w,hwt,hlabel,hsnap,hbits⟩ := limit_tail_realization v0 M P hP labelBound
  refine ⟨w,hlabel,?_,?_⟩
  · intro n hn
    have hs := hsnap n hn
    have hp := hprefix n hn
    exact ⟨hs.1.trans hp.1,hs.2.trans hp.2⟩
  · intro i j
    rw [hwt,htuple]
    exact hbits ((r i).request rows j)
      (Finset.mem_image.mpr ⟨⟨i,j⟩,Finset.mem_univ _,rfl⟩)

end FSCofinality.Tokens
