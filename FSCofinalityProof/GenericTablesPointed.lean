import FSCofinalityProof.GenericTables
import Mathlib.Data.List.GetD

noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.GenericTables

theorem compatible_pair {r s : Request} (hrs : r.key ≠ s.key) : Compatible {r,s} := by
  classical
  intro u hu v hv huv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · rfl
  · exact False.elim (hrs huv)
  · exact False.elim (hrs huv.symm)
  · rfl

theorem separates_rows {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A)
    (e : ℕ) (M M' : BoolMatrix) (k k' : ℕ) (hne : (M,k) ≠ (M',k')) :
    ∃ d, A (e,M,d,k) = false ∧ A (e,M',d,k') = true := by
  let r : Request := ⟨e,M,false,k,false⟩
  let s : Request := ⟨e,M',false,k',true⟩
  have hrs : r.key ≠ s.key := by
    intro h
    apply hne
    have hh : M = M' ∧ k = k' := by simpa [r,s,Request.key] using h
    exact Prod.ext hh.1 hh.2
  obtain ⟨d,_,_,hd⟩ := hA {r,s} (compatible_pair hrs) 0 0
  exact ⟨d,hd r (by simp),hd s (by simp)⟩

theorem row_signature_injective {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A) (e : ℕ) :
    Function.Injective (fun p : BoolMatrix × ℕ => fun d : ℕ => A (e,p.1,d,p.2)) := by
  intro p q h
  by_contra hne
  obtain ⟨d,hd,hd'⟩ := separates_rows hA e p.1 q.1 p.2 q.2 hne
  have hh := congrFun h d
  change A (e,p.1,d,p.2) = A (e,q.1,d,q.2) at hh
  rw [hd,hd'] at hh
  contradiction

def BoolMatrix.entry (M : BoolMatrix) (i j : ℕ) : Bool :=
  if hi : i < M.1 then if hj : j < M.2.1 then M.2.2 ⟨i,hi⟩ ⟨j,hj⟩ else false else false

/-- The finite raw-incidence matrix, retaining the tuple lengths. -/
def contextMatrix {V : Type*} (C : List (V → Bool)) (s : List V) : BoolMatrix :=
  ⟨C.length,s.length,fun i j => C[i] (s[j])⟩

theorem contextMatrix_length {V : Type*} (C : List (V → Bool)) (s : List V) :
    (contextMatrix C s).1 = C.length := rfl

theorem contextMatrix_entry {V : Type*} (C : List (V → Bool)) (s : List V)
    (i j : ℕ) (hi : i < C.length) (hj : j < s.length) :
    (contextMatrix C s).entry i j = C[i] s[j] := by
  simp [BoolMatrix.entry,contextMatrix,hi,hj]

theorem contextMatrix_entry_singleton {V : Type*} (C : List (V → Bool))
    (i : ℕ) (hi : i < C.length) (v : V) :
    (contextMatrix C [v]).entry i 0 = C[i] v := by
  simp [BoolMatrix.entry,contextMatrix,hi]

theorem contextMatrix_injective {V : Type*} (C C' : List (V → Bool))
    (h : ∀ s : List V, contextMatrix C s = contextMatrix C' s) : C = C' := by
  have hlen : C.length = C'.length := congrArg Sigma.fst (h [])
  apply List.ext_getElem hlen
  intro i hi hi'
  apply funext
  intro v
  have hh := congrArg (fun M : BoolMatrix => M.entry i 0) (h [v])
  simpa only [contextMatrix_entry_singleton C i hi v,
    contextMatrix_entry_singleton C' i hi' v] using hh

/-- Pointed-context injectivity: all finite lower contexts and natural copy
labels determine the ordered row-profile tuple and its row copy label. -/
theorem pointed_context_injective {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A)
    (e : ℕ) {V : Type*} :
    Function.Injective (fun p : List (V → Bool) × ℕ =>
      fun q : List V × ℕ => A (e,contextMatrix p.1 q.1,q.2,p.2)) := by
  intro p q hpq
  have hlocal (s : List V) : (contextMatrix p.1 s,p.2) = (contextMatrix q.1 s,q.2) := by
    apply row_signature_injective hA e
    funext d
    exact congrFun hpq (s,d)
  exact Prod.ext (contextMatrix_injective p.1 q.1 (fun s => congrArg Prod.fst (hlocal s)))
    (show p.2 = q.2 from congrArg (fun r : BoolMatrix × ℕ => r.2) (hlocal []))

end FSCofinality.GenericTables
