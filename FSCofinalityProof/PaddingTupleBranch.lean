import FSCofinalityProof.PaddingTupleGraphs
import Mathlib.Data.List.GetD

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

def sourceTuple (s : List ℕ) : List ℕ := (PartialIso.pairsFrom 0 s).map Prod.fst
def targetTuple (s : List ℕ) : List ℕ := (PartialIso.pairsFrom 0 s).map Prod.snd

@[simp] theorem sourceTuple_length (s : List ℕ) : (sourceTuple s).length = s.length := by
  have hp : ∀ (k : ℕ) (s : List ℕ), (PartialIso.pairsFrom k s).length = s.length := by
    intro k s
    induction s generalizing k <;> simp_all [PartialIso.pairsFrom]
  simpa only [sourceTuple,List.length_map] using hp 0 s

@[simp] theorem targetTuple_length (s : List ℕ) : (targetTuple s).length = s.length := by
  have hp : ∀ (k : ℕ) (s : List ℕ), (PartialIso.pairsFrom k s).length = s.length := by
    intro k s
    induction s generalizing k <;> simp_all [PartialIso.pairsFrom]
  simpa only [targetTuple,List.length_map] using hp 0 s

theorem sourceTuple_append (s : List ℕ) (n : ℕ) :
    sourceTuple (s ++ [n]) = sourceTuple s ++ [(PartialIso.scheduledPair s.length n).1] := by
  simp [sourceTuple,PartialIso.pairsFrom_append,PartialIso.pairsFrom]

theorem targetTuple_append (s : List ℕ) (n : ℕ) :
    targetTuple (s ++ [n]) = targetTuple s ++ [(PartialIso.scheduledPair s.length n).2] := by
  simp [targetTuple,PartialIso.pairsFrom_append,PartialIso.pairsFrom]

theorem sourceTuple_getD_prefix (b : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    (sourceTuple (PartialIso.initialSegment b n)).getD i 0 = (PartialIso.scheduledPair i (b i)).1 := by
  simp only [sourceTuple,PartialIso.initialSegment,PartialIso.pairsFrom_ofFn,List.map_ofFn,Nat.zero_add]
  rw [List.getD_eq_getElem _ _ (by simpa)]
  simp only [List.getElem_ofFn,Function.comp_apply]

theorem targetTuple_getD_prefix (b : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    (targetTuple (PartialIso.initialSegment b n)).getD i 0 = (PartialIso.scheduledPair i (b i)).2 := by
  simp only [targetTuple,PartialIso.initialSegment,PartialIso.pairsFrom_ofFn,List.map_ofFn,Nat.zero_add]
  rw [List.getD_eq_getElem _ _ (by simpa)]
  simp only [List.getElem_ofFn,Function.comp_apply]

/-- Scheduled tuple correspondences with identical finite graph diagrams
along every prefix recover one actual graph isomorphism. -/
theorem graphIsomorphic_of_tuple_branch (G H : GraphSpace) (b : ℕ → ℕ)
    (hb : ∀ n, tupleColor G (sourceTuple (PartialIso.initialSegment b n)) =
      tupleColor H (targetTuple (PartialIso.initialSegment b n))) : GraphIsomorphic G H := by
  have hdiagram (n i j : ℕ) (hi : i < n) (hj : j < n) :
      ((PartialIso.scheduledPair i (b i)).1 = (PartialIso.scheduledPair j (b j)).1 ↔
        (PartialIso.scheduledPair i (b i)).2 = (PartialIso.scheduledPair j (b j)).2) ∧
      G.val ((PartialIso.scheduledPair i (b i)).1,(PartialIso.scheduledPair j (b j)).1) =
        H.val ((PartialIso.scheduledPair i (b i)).2,(PartialIso.scheduledPair j (b j)).2) := by
    have h := atomic_of_tupleColor_eq (hb n) i j (by simpa [PartialIso.initialSegment] using hi)
      (by simpa [PartialIso.initialSegment] using hj)
    simpa only [sourceTuple_getD_prefix b n i hi,sourceTuple_getD_prefix b n j hj,
      targetTuple_getD_prefix b n i hi,targetTuple_getD_prefix b n j hj] using h
  let f : ℕ → ℕ := fun i => b (2*i)
  let g : ℕ → ℕ := fun i => b (2*i+1)
  have hgf (i : ℕ) : g (f i) = i := by
    have h := (hdiagram (max (2*i) (2*(f i)+1)+1) (2*i) (2*(f i)+1) (by omega) (by omega)).1
    simp only [PartialIso.scheduledPair_even,PartialIso.scheduledPair_odd] at h
    exact (h.mpr rfl).symm
  have hfg (i : ℕ) : f (g i) = i := by
    have h := (hdiagram (max (2*(g i)) (2*i+1)+1) (2*(g i)) (2*i+1) (by omega) (by omega)).1
    simp only [PartialIso.scheduledPair_even,PartialIso.scheduledPair_odd] at h
    exact h.mp rfl
  let e : ℕ ≃ ℕ := ⟨f,g,hgf,hfg⟩
  refine ⟨e,fun m n => ?_⟩
  simpa only [PartialIso.scheduledPair_even] using
    (hdiagram (max (2*m) (2*n)+1) (2*m) (2*n) (by omega) (by omega)).2

end FSCofinality.Padding
