import FSCofinalityProof.GenericTablesHistories

noncomputable section
open Set

namespace FSCofinality.GenericTables

theorem localCode_eq_of_le (h k : History) {m n : ℕ} (hmn : m ≤ n)
    (heq : h.localCode n = k.localCode n) : h.localCode m = k.localCode m := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact heq
  | succ n IH =>
    by_cases hm : m = n+1
    · rw [hm]
      exact heq
    · exact IH (by omega) (localCode_refines h k n heq)

/-- A fresh local code continues to separate the two histories at every
later level; choosing a later tail cannot erase the separation. -/
theorem localCode_ne_of_le (h k : History) {m n : ℕ} (hmn : m ≤ n)
    (hne : h.localCode m ≠ k.localCode m) : h.localCode n ≠ k.localCode n :=
  fun heq => hne (localCode_eq_of_le h k hmn heq)

theorem localCode_eq_of_same_prefix (h k : History) (M n : ℕ)
    (hn : n ≤ M) (ha : h.activation = k.activation)
    (hk : ∀ i ≤ M, h.noise i = k.noise i) : h.localCode n = k.localCode n := by
  apply (localCode_eq_iff h k n).mpr
  apply Prod.ext
  · change h.activation.filter _ = k.activation.filter _
    rw [ha]
  · change List.ofFn (fun i : Fin (n+1) => h.noise i) =
      List.ofFn (fun i : Fin (n+1) => k.noise i)
    congr 1
    funext i
    exact hk i (by omega)

/-- Every full label in a fixed-history-prefix fiber preserves all previously
fixed local history codes, not just one finite code coordinate. -/
theorem fullLabelSet_preserves_prefix (h : History) (M z : ℕ) (hz : z ∈ fullLabelSet h M) :
    let k := (fullLabelEquiv h.activation.length).symm z
    k.val.activation = h.activation ∧ ∀ n ≤ M, k.val.localCode n = h.localCode n := by
  obtain ⟨k,hk,ha,hnoise⟩ := hz
  have heq : (fullLabelEquiv h.activation.length).symm z = k := by
    rw [← hk,Equiv.symm_apply_apply]
  dsimp
  rw [heq]
  exact ⟨ha,fun n hn => localCode_eq_of_same_prefix k.val h M n hn ha hnoise⟩

def History.appendLate (h : History) (M count : ℕ)
    (hbound : ∀ a ∈ h.activation, a ≤ M) : History where
  activation := h.activation ++ List.replicate count (M+1)
  ordered := by
    apply List.pairwise_append.mpr
    refine ⟨h.ordered,by simp,?_⟩
    intro a ha b hb
    rw [List.eq_of_mem_replicate hb]
    exact (hbound a ha).trans (Nat.le_succ M)
  noise := h.noise

theorem appendLate_localCode (h : History) (M count : ℕ)
    (hbound : ∀ a ∈ h.activation, a ≤ M) (n : ℕ) (hn : n ≤ M) :
    (h.appendLate M count hbound).localCode n = h.localCode n := by
  apply (localCode_eq_iff _ _ n).mpr
  apply Prod.ext
  · change (h.activation ++ List.replicate count (M+1)).filter _ = h.activeTimes n
    apply activeTimes_append_late
    intro a ha
    have heq : a = M+1 := List.eq_of_mem_replicate ha
    omega
  · rfl

theorem bump_localCode (h : History) (M k n : ℕ) (hn : n ≤ M) :
    (h.bump M k).localCode n = h.localCode n :=
  localCode_eq_of_same_prefix _ _ M n hn rfl (fun i hi => bump_noise_prefix h M k i hi)

def History.appendAt (h : History) (time count : ℕ)
    (hbound : ∀ a ∈ h.activation, a ≤ time) : History where
  activation := h.activation ++ List.replicate count time
  ordered := by
    apply List.pairwise_append.mpr
    refine ⟨h.ordered,by simp,?_⟩
    intro a ha b hb
    rw [List.eq_of_mem_replicate hb]
    exact hbound a ha
  noise := h.noise

theorem appendAt_localCode (h : History) (time count : ℕ)
    (hbound : ∀ a ∈ h.activation, a ≤ time) (n : ℕ) (hn : n < time) :
    (h.appendAt time count hbound).localCode n = h.localCode n := by
  apply (localCode_eq_iff _ _ n).mpr
  apply Prod.ext
  · change (h.activation ++ List.replicate count time).filter _ = h.activeTimes n
    apply activeTimes_append_late
    intro a ha
    simpa only [List.eq_of_mem_replicate ha] using hn
  · rfl

def History.noiseBefore (h : History) (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => h.noise i)

def History.updateNoise (h : History) (n k : ℕ) : History :=
  ⟨h.activation,h.ordered,h.noise.update n k⟩

theorem updateNoise_prefix (h : History) (n k : ℕ) :
    (h.updateNoise n k).noisePrefix n = h.noiseBefore n ++ [k] := by
  unfold History.noisePrefix
  rw [List.ofFn_succ',List.concat_eq_append]
  congr 1
  · apply congrArg List.ofFn
    funext i
    change h.noise.update n k i = h.noise i
    rw [Finsupp.update_apply,if_neg (by omega : (i : ℕ) ≠ n)]
  · simp [History.updateNoise,Finsupp.update_apply]

theorem updateNoise_localCode_at (h : History) (n k : ℕ) :
    (h.updateNoise n k).localCode n = Encodable.encode (h.activeTimes n,h.noiseBefore n ++ [k]) := by
  unfold History.localCode History.localView
  rw [updateNoise_prefix]
  rfl

theorem updateNoise_localCode_earlier (h : History) (n k m : ℕ) (hm : m < n) :
    (h.updateNoise n k).localCode m = h.localCode m := by
  apply localCode_eq_of_same_prefix (h.updateNoise n k) h m m le_rfl rfl
  intro i hi
  change h.noise.update n k i = h.noise i
  rw [Finsupp.update_apply,if_neg (by omega : i ≠ n)]

end FSCofinality.GenericTables
