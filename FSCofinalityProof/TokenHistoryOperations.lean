import FSCofinalityProof.TokenStructures
import FSCofinalityProof.GenericTablesHistoryExtensions

noncomputable section

namespace FSCofinality.Tokens
open GenericTables

theorem activeLength_le_length {U : Type*} (v : Token U) (n : ℕ) :
    activeLength v n ≤ v.1.length := by
  unfold activeLength History.activeTimes
  exact (List.length_filter_le _ _).trans_eq (history v).property

def extendAt {U : Type*} (v : Token U) (time : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ time) : Token U :=
  ofHistory (v.1 ++ extra) ⟨(history v).val.appendAt time extra.length hbound,by
    simp only [History.appendAt,List.length_append,List.length_replicate,(history v).property]⟩

theorem extendAt_history {U : Type*} (v : Token U) (time : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ time) :
    (history (extendAt v time extra hbound)).val =
      (history v).val.appendAt time extra.length hbound := by
  simp only [extendAt,history_ofHistory]

theorem extendAt_localCode {U : Type*} (v : Token U) (time : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ time) (n : ℕ) (hn : n < time) :
    localCode (extendAt v time extra hbound) n = localCode v n := by
  unfold localCode
  rw [extendAt_history]
  exact appendAt_localCode _ _ _ _ _ hn

theorem extendAt_activeTuple {U : Type*} (v : Token U) (time : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ time) (n : ℕ) (hn : n < time) :
    activeTuple (extendAt v time extra hbound) n = activeTuple v n := by
  have hv := (localCode_eq_iff _ _ n).mp (extendAt_localCode v time extra hbound n hn)
  have hl : activeLength (extendAt v time extra hbound) n = activeLength v n :=
    congrArg (fun p : List ℕ × List ℕ => p.1.length) hv
  change (v.1 ++ extra).take _ = v.1.take _
  rw [hl,List.take_append_of_le_length (activeLength_le_length v n)]

def withNoiseAt {U : Type*} (v : Token U) (n k : ℕ) : Token U :=
  ofHistory v.1 ⟨(history v).val.updateNoise n k,(history v).property⟩

theorem withNoiseAt_history {U : Type*} (v : Token U) (n k : ℕ) :
    (history (withNoiseAt v n k)).val = (history v).val.updateNoise n k := by
  simp only [withNoiseAt,history_ofHistory]

theorem withNoiseAt_localCode_at {U : Type*} (v : Token U) (n k : ℕ) :
    localCode (withNoiseAt v n k) n = Encodable.encode
      ((history v).val.activeTimes n,(history v).val.noiseBefore n ++ [k]) := by
  unfold localCode
  rw [withNoiseAt_history]
  exact updateNoise_localCode_at _ _ _

theorem withNoiseAt_localCode_earlier {U : Type*} (v : Token U) (n k m : ℕ) (hm : m < n) :
    localCode (withNoiseAt v n k) m = localCode v m := by
  unfold localCode
  rw [withNoiseAt_history]
  exact updateNoise_localCode_earlier _ _ _ _ hm

theorem withNoiseAt_activeTuple {U : Type*} (v : Token U) (n k m : ℕ) :
    activeTuple (withNoiseAt v n k) m = activeTuple v m := by
  unfold activeTuple activeLength
  rw [withNoiseAt_history]
  rfl

end FSCofinality.Tokens
