import FSCofinalityProof.TokenFiniteTypes
import FSCofinalityProof.TokenStructures

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.Tokens
open GenericTables

theorem branchEdge_eq_of_R {U : Type} {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool) (A : Table) (e n : ℕ)
    {v w : Token U} (h : R profile n v w) (c : Token (Col n)) :
    branchEdge profile A e n v c = branchEdge profile A e n w c := by
  simp only [branchEdge,h.1,h.2]

/-- Transfer of the full nested-equivalence type together with every finite
branch requirement and all ordinary roles. The old correspondence supplies
only its actual atomic agreements, rather than an extension assumption. -/
theorem limit_finite_type_extension
    {U V : Type} [Nonempty V] {ColX ColY : ℕ → Type}
    (PX : ∀ n, U → ColX n → Bool) (PY : ∀ n, V → ColY n → Bool)
    (jx : ∀ n, ColX n → ColX (n+1))
    (hxprop : ∀ n u c, PX (n+1) u (jx n c) = PX n u c)
    (hxinj : Function.Injective (fun u => fun n => PX n u))
    (hycol : ∀ n, Function.Injective (fun c => fun u => PY n u c))
    (e count : ℕ → ℕ) (cx : ∀ n, Fin (count n) → Token (ColX n))
    (cy : ∀ n, Fin (count n) → Token (ColY n))
    {Old Upper : Type} [Fintype Old] [Fintype Upper]
    (oldX : Old → Token U) (oldY : Old → Token V)
    (hOldR : ∀ n i j, R PX n (oldX i) (oldX j) ↔ R PY n (oldY i) (oldY j))
    (hOldBranch : ∀ n i j,
      branchEdge PX genericTable (e n) n (oldX i) (cx n j) =
      branchEdge PY genericTable (e n) n (oldY i) (cy n j))
    (upper : Upper → FiniteRole V) (hupper : Function.Injective (fun i => (upper i).role))
    (v : Token U) (hfresh : ∀ i, v ≠ oldX i)
    (hconsistent : ∀ n i j, cy n i = cy n j →
      branchEdge PX genericTable (e n) n v (cx n i) =
      branchEdge PX genericTable (e n) n v (cx n j))
    (bound : ℕ) (hbound : ∀ n, bound < n → count n = 0) (copyBound : ℕ) :
    ∃ w : Token V, copyBound < w.2 ∧
      (∀ n i, R PY n w (oldY i) ↔ R PX n v (oldX i)) ∧
      (∀ n j, branchEdge PY genericTable (e n) n w (cy n j) =
        branchEdge PX genericTable (e n) n v (cx n j)) ∧
      ∀ i j, genericTable (((upper i).request w.1 j).index w.2) = (upper i).bit j := by
  let r (n : ℕ) (i : Old) : Prop := R PX n v (oldX i)
  have hdown (n : ℕ) (i : Old) : r (n+1) i → r n i :=
    R_refines PX jx hxprop n
  have hsep (i : Old) : ∃ N, ∀ n ≥ N, ¬r n i := by
    have hnot : ¬∀ n, r n i := fun hall =>
      hfresh i (all_R_separate PX jx hxprop hxinj hall)
    push_neg at hnot
    obtain ⟨N,hN⟩ := hnot
    exact ⟨N,fun n hn hr => hN (finite_type_down r hdown hn i hr)⟩
  have hcoherent (n : ℕ) (i : Old) (hi : r n i) (j : Old) :
      r n j ↔ R PY n (oldY i) (oldY j) := by
    rw [← hOldR n i j]
    exact ⟨fun hj => (R_equivalence PX n).trans ((R_equivalence PX n).symm hi) hj,
      fun hij => (R_equivalence PX n).trans hi hij⟩
  let epsilon (n : ℕ) (j : Fin (count n)) : Bool :=
    branchEdge PX genericTable (e n) n v (cx n j)
  obtain hnone | ⟨N,i,hi,hthrough,htail⟩ :=
    classify_finite_limit_type (fun n i j => R PY n (oldY i) (oldY j)) r hdown hsep hcoherent
  · let v₀ : Token V := ofHistory [] (basicHistory 0 0)
    have hactivation : ∀ a ∈ (history v₀).val.activation, a ≤ 0 := by
      intro a ha
      simp [v₀,basicHistory,history_ofHistory] at ha
    obtain ⟨w,hw,_,hseparate,hbranch,hordinary⟩ := limit_extension_core PY hycol e count cy
      epsilon hconsistent oldY upper hupper v₀ 0 (bound+1) (by omega) hactivation copyBound
    refine ⟨w,hw,?_,?_,hordinary⟩
    · intro n j
      exact iff_of_false (hseparate n (by omega) j) (hnone n j)
    · intro n j
      have hn : n ≤ bound := by
        by_contra hn
        have hz := hbound n (by omega)
        have := j.isLt
        omega
      let matched (k : ℕ) : Prop := ∀ j : Fin (count k),
        branchEdge PY genericTable (e k) k w (cy k j) = epsilon k j
      have hh : matched (0+n) := hbranch n (by omega)
      have hh' : matched n := (Nat.zero_add n) ▸ hh
      exact hh' j
  · obtain ⟨w,hw,hthroughW,hseparate,hbranch,hordinary⟩ := anchored_limit_extension PY hycol
      e count cy epsilon hconsistent oldY upper hupper (oldY i) N (bound+1) (by omega) copyBound
    refine ⟨w,hw,?_,?_,hordinary⟩
    · intro n j
      by_cases hn : n ≤ N
      · have hwanchor := hthroughW n hn
        have heq : R PY n w (oldY j) ↔ R PY n (oldY i) (oldY j) :=
          ⟨fun h => (R_equivalence PY n).trans ((R_equivalence PY n).symm hwanchor) h,
            fun h => (R_equivalence PY n).trans hwanchor h⟩
        exact heq.trans (hthrough n hn j).symm
      · exact iff_of_false (hseparate n (by omega) j) (htail n (by omega) j)
    · intro n j
      by_cases hn : n ≤ N
      · have hvanchor := finite_type_down r hdown hn i hi
        exact (branchEdge_eq_of_R PY genericTable (e n) n (hthroughW n hn) (cy n j)).trans
          ((hOldBranch n i j).symm.trans
            (branchEdge_eq_of_R PX genericTable (e n) n hvanchor (cx n j)).symm)
      · have hnb : n ≤ bound := by
          by_contra hnb
          have hz := hbound n (by omega)
          have := j.isLt
          omega
        have hnrewrite : N+1+(n-(N+1)) = n := by omega
        have hh := hbranch (n-(N+1)) (by omega)
        rw [hnrewrite] at hh
        exact hh j

end FSCofinality.Tokens
