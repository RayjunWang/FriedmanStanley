import FSCofinalityProof.TokenHistoryOperations
import FSCofinalityProof.GenericTablesHistorySorting
import Mathlib.Data.Finsupp.Basic

noncomputable section
open Set

namespace FSCofinality.GenericTables

theorem activeTimes_restrict (h : History) {m n : ℕ} (hmn : m ≤ n) :
    h.activeTimes m = (h.activeTimes n).filter (fun a => decide (a ≤ m)) := by
  simp only [History.activeTimes,List.filter_filter]
  congr 1
  funext a
  by_cases ha : a ≤ m
  · have hb : a ≤ n := ha.trans hmn
    simp [ha,hb]
  · simp [ha]

def History.truncate (h : History) (N : ℕ) : History where
  activation := h.activeTimes N
  ordered := h.ordered.filter _
  noise := h.noise.filter (fun i => i ≤ N)

theorem truncate_activeTimes (h : History) (N m : ℕ) (hm : m ≤ N) :
    (h.truncate N).activeTimes m = h.activeTimes m := (activeTimes_restrict h hm).symm

theorem truncate_bound (h : History) (N : ℕ) :
    ∀ a ∈ (h.truncate N).activation, a ≤ N := by
  intro a ha
  exact of_decide_eq_true (List.mem_filter.mp ha).2

theorem truncate_localCode (h : History) (N m : ℕ) (hm : m ≤ N) :
    (h.truncate N).localCode m = h.localCode m := by
  apply (localCode_eq_iff _ _ m).mpr
  apply Prod.ext
  · exact truncate_activeTimes h N m hm
  · change List.ofFn (fun i : Fin (m+1) => (h.truncate N).noise i) =
      List.ofFn (fun i : Fin (m+1) => h.noise i)
    congr 1
    funext i
    change h.noise.filter (fun j => j ≤ N) i = h.noise i
    rw [Finsupp.filter_apply,if_pos (by omega : (i : ℕ) ≤ N)]

end FSCofinality.GenericTables

namespace FSCofinality.Tokens
open GenericTables

theorem activeLength_le_of_level {U : Type*} (v : Token U) {m n : ℕ} (hmn : m ≤ n) :
    activeLength v m ≤ activeLength v n := by
  unfold activeLength
  rw [activeTimes_restrict _ hmn]
  exact List.length_filter_le _ _

/-- Copy precisely the anchor's existing active slots and history prefix;
its future slots and noise are not copied into the new point. -/
def truncate {U : Type*} (v : Token U) (N : ℕ) : Token U :=
  ofHistory (activeTuple v N) ⟨(history v).val.truncate N,by
    change activeLength v N = (v.1.take (activeLength v N)).length
    simp only [List.length_take,Nat.min_eq_left (activeLength_le_length v N)]⟩

theorem truncate_history {U : Type*} (v : Token U) (N : ℕ) :
    (history (truncate v N)).val = (history v).val.truncate N := by
  simp only [truncate,history_ofHistory]

theorem truncate_activation_bound {U : Type*} (v : Token U) (N : ℕ) :
    ∀ a ∈ (history (truncate v N)).val.activation, a ≤ N := by
  rw [truncate_history]
  exact truncate_bound _ _

theorem truncate_snapshot {U : Type*} (v : Token U) (N m : ℕ) (hm : m ≤ N) :
    localCode (truncate v N) m = localCode v m ∧ activeTuple (truncate v N) m = activeTuple v m := by
  refine ⟨?_,?_⟩
  · unfold localCode
    rw [truncate_history]
    exact truncate_localCode _ _ _ hm
  · have hl : activeLength (truncate v N) m = activeLength v m := by
      unfold activeLength
      rw [truncate_history,truncate_activeTimes _ _ _ hm]
    change ((v.1.take (activeLength v N)).take (activeLength (truncate v N) m)) = _
    rw [hl,List.take_take,Nat.min_eq_left (activeLength_le_of_level v hm)]
    rfl

end FSCofinality.Tokens
