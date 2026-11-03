import FSCofinalityProof.GenericTablesPointed
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Logic.Denumerable

noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.GenericTables

/-- A full finite activation list and an eventually-zero natural sequence. -/
structure History where
  activation : List ℕ
  ordered : activation.Pairwise (· ≤ ·)
  noise : ℕ →₀ ℕ

instance : Countable History := by
  apply Function.Injective.countable (f := fun h : History => (h.activation,h.noise))
  intro h k heq
  cases h
  cases k
  simpa only [Prod.mk.injEq,History.mk.injEq] using heq

def FullHistory (l : ℕ) := {h : History // h.activation.length = l}

instance (l : ℕ) : Countable (FullHistory l) := inferInstanceAs (Countable {h : History // _})

def basicHistory (l k : ℕ) : FullHistory l :=
  ⟨⟨List.replicate l 0,by simp,Finsupp.single 0 k⟩,by simp⟩

theorem basicHistory_injective (l : ℕ) : Function.Injective (basicHistory l) := by
  intro k k' h
  have heq := congrArg (fun h : FullHistory l => h.val.noise 0) h
  simpa [basicHistory] using heq

instance (l : ℕ) : Infinite (FullHistory l) := Infinite.of_injective _ (basicHistory_injective l)

/-- Every natural full label denotes a legitimate history of the given length. -/
def fullLabelEquiv (l : ℕ) : FullHistory l ≃ ℕ := Classical.choice inferInstance

def History.fullLabel (h : History) : ℕ := fullLabelEquiv h.activation.length ⟨h,rfl⟩

def History.activeTimes (h : History) (n : ℕ) : List ℕ :=
  h.activation.filter (fun a => decide (a ≤ n))

def History.noisePrefix (h : History) (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (n+1) => h.noise i)

def History.localView (h : History) (n : ℕ) : List ℕ × List ℕ :=
  (h.activeTimes n,h.noisePrefix n)

def History.localCode (h : History) (n : ℕ) : ℕ := Encodable.encode (h.localView n)

theorem localCode_eq_iff (h k : History) (n : ℕ) :
    h.localCode n = k.localCode n ↔ h.localView n = k.localView n :=
  Encodable.encode_injective.eq_iff

theorem activeTimes_previous (h : History) (n : ℕ) :
    h.activeTimes n = (h.activeTimes (n+1)).filter (fun a => decide (a ≤ n)) := by
  simp only [History.activeTimes,List.filter_filter]
  congr 1
  funext a
  by_cases ha : a ≤ n
  · have hb : a ≤ n+1 := by omega
    simp [ha,hb]
  · simp [ha]

theorem noisePrefix_previous (h : History) (n : ℕ) :
    h.noisePrefix n = (h.noisePrefix (n+1)).take (n+1) := by
  apply List.ext_getElem
  · simp [History.noisePrefix]
  · intro i hi hi'
    simp only [History.noisePrefix,List.getElem_take,List.getElem_ofFn]

theorem localCode_refines (h k : History) (n : ℕ)
    (heq : h.localCode (n+1) = k.localCode (n+1)) : h.localCode n = k.localCode n := by
  apply (localCode_eq_iff h k n).mpr
  have hv := (localCode_eq_iff h k (n+1)).mp heq
  apply Prod.ext
  · change h.activeTimes n = k.activeTimes n
    have hh : h.activeTimes (n+1) = k.activeTimes (n+1) := congrArg Prod.fst hv
    rw [activeTimes_previous h n,activeTimes_previous k n,hh]
  · change h.noisePrefix n = k.noisePrefix n
    have hh : h.noisePrefix (n+1) = k.noisePrefix (n+1) := congrArg Prod.snd hv
    rw [noisePrefix_previous h n,noisePrefix_previous k n,hh]

/-- Future activation slots are invisible to a local view. -/
theorem activeTimes_append_late (h : History) (extra : List ℕ) (n : ℕ)
    (hlate : ∀ a ∈ extra, n < a) :
    (h.activation ++ extra).filter (fun a => decide (a ≤ n)) = h.activeTimes n := by
  rw [List.filter_append]
  have he : extra.filter (fun a => decide (a ≤ n)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    simpa only [decide_eq_true_eq] using not_le.mpr (hlate a ha)
  simp [he,History.activeTimes]

/-- Labels obtained by varying only the newest noise entry in a local code. -/
def localLabelSet (active pref : List ℕ) : Set ℕ :=
  range (fun k : ℕ => Encodable.encode (active,pref ++ [k]))

theorem infinite_localLabelSet (active pref : List ℕ) : (localLabelSet active pref).Infinite := by
  apply Set.infinite_range_of_injective
  intro k k' h
  have heq := Encodable.encode_injective h
  have hh : pref ++ [k] = pref ++ [k'] := congrArg Prod.snd heq
  simpa only [List.append_cancel_left_eq,List.cons.injEq,and_true] using hh

def History.bump (h : History) (M k : ℕ) : History :=
  ⟨h.activation,h.ordered,h.noise + Finsupp.single (M+1) k⟩

@[simp] theorem bump_activation (h : History) (M k : ℕ) :
    (h.bump M k).activation = h.activation := rfl

theorem bump_noise_prefix (h : History) (M k i : ℕ) (hi : i ≤ M) :
    (h.bump M k).noise i = h.noise i := by
  simp only [History.bump,Finsupp.add_apply]
  rw [Finsupp.single_eq_of_ne (by omega : i ≠ M+1),add_zero]

theorem bump_injective (h : History) (M : ℕ) : Function.Injective (h.bump M) := by
  intro k k' heq
  have hh := congrArg (fun g : History => g.noise (M+1)) heq
  simpa [History.bump] using hh

/-- Full labels with an entire activation list fixed and a noise prefix fixed. -/
def fullLabelSet (h : History) (M : ℕ) : Set ℕ :=
  {z | ∃ k : FullHistory h.activation.length,
    fullLabelEquiv _ k = z ∧ k.val.activation = h.activation ∧
      ∀ i ≤ M, k.val.noise i = h.noise i}

theorem infinite_fullLabelSet (h : History) (M : ℕ) : (fullLabelSet h M).Infinite := by
  let f : ℕ → ℕ := fun k => fullLabelEquiv h.activation.length ⟨h.bump M k,rfl⟩
  have hf : Function.Injective f := by
    intro k k' heq
    have hh := (fullLabelEquiv h.activation.length).injective heq
    exact bump_injective h M (congrArg Subtype.val hh)
  apply (Set.infinite_range_of_injective hf).mono
  rintro z ⟨k,rfl⟩
  exact ⟨⟨h.bump M k,rfl⟩,rfl,rfl,fun i hi => bump_noise_prefix h M k i hi⟩

theorem activeTimes_eq_self (h : History) (n : ℕ)
    (hn : ∀ a ∈ h.activation, a ≤ n) : h.activeTimes n = h.activation := by
  apply List.filter_eq_self.mpr
  intro a ha
  exact decide_eq_true (hn a ha)

/-- All local histories determine the actual entire finite activation
list and the eventually-zero noise sequence. -/
theorem all_localCodes_injective : Function.Injective (fun h : History => h.localCode) := by
  intro h k heq
  have hv (n : ℕ) : h.localView n = k.localView n :=
    (localCode_eq_iff h k n).mp (congrFun heq n)
  let N := h.activation.sum + k.activation.sum
  have hact : h.activation = k.activation := by
    have hh : h.activeTimes N = k.activeTimes N := congrArg Prod.fst (hv N)
    rw [activeTimes_eq_self h N (fun a ha => (List.le_sum_of_mem ha).trans (Nat.le_add_right _ _)),
      activeTimes_eq_self k N (fun a ha => (List.le_sum_of_mem ha).trans (Nat.le_add_left _ _))] at hh
    exact hh
  have hnoise : h.noise = k.noise := by
    ext i
    have hh := congrArg (fun p : List ℕ × List ℕ => p.2[i]?) (hv i)
    simpa only [History.localView,History.noisePrefix,List.getElem?_ofFn,
      dif_pos (Nat.lt_succ_self i),Option.some.injEq] using hh
  cases h
  cases k
  simp_all only [History.mk.injEq,true_and,and_self]

abbrev AllowedIndex := Unit ⊕ (List ℕ × List ℕ) ⊕ (History × ℕ)

def allowedSet : AllowedIndex → Set ℕ
  | .inl _ => univ
  | .inr (.inl (active,pref)) => localLabelSet active pref
  | .inr (.inr (h,M)) => fullLabelSet h M

theorem infinite_allowedSet (i : AllowedIndex) : (allowedSet i).Infinite := by
  rcases i with _ | (⟨active,pref⟩ | ⟨h,M⟩)
  · exact Set.infinite_univ
  · exact infinite_localLabelSet active pref
  · exact infinite_fullLabelSet h M

def allowedEnumeration : ℕ → AllowedIndex := Classical.choose (exists_surjective_nat AllowedIndex)

theorem allowedEnumeration_surjective : Function.Surjective allowedEnumeration :=
  Classical.choose_spec (exists_surjective_nat AllowedIndex)

def allowedSets (n : ℕ) : Set ℕ := allowedSet (allowedEnumeration n)

/-- A fixed actual family of independent Boolean tables meeting every local
history and full-history-tail requirement of the construction. -/
def genericTable : Table := Classical.choose (exists_generic allowedSets (fun i => infinite_allowedSet _))

theorem genericTable_generic : GenericOn allowedSets genericTable :=
  Classical.choose_spec (exists_generic allowedSets (fun i => infinite_allowedSet _))

theorem genericTable_realizes (P : Finset Request) (hP : Compatible P)
    (i : AllowedIndex) (N : ℕ) : ∃ z ∈ allowedSet i,
      N < z ∧ ∀ r ∈ P, genericTable (r.index z) = r.value := by
  obtain ⟨n,hn⟩ := allowedEnumeration_surjective i
  obtain ⟨z,hz,hN,hbits⟩ := genericTable_generic P hP n N
  exact ⟨z,by simpa only [allowedSets,hn] using hz,hN,hbits⟩

end FSCofinality.GenericTables
