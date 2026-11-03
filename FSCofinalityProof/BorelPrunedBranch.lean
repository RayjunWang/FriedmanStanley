import FSCofinalityProof.TreeBranches
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology TopologicalSpace

namespace FSCofinality.RootedTrees

local instance : MeasurableSpace Node := borel Node
local instance : BorelSpace Node := ⟨rfl⟩

def Pruned (T : TreeSpace) : Prop :=
  ∀ s : Node, T s = true → ∃ n : ℕ, T (s ++ [n]) = true

theorem continuous_child_bit (n : ℕ) :
    Continuous (fun p : TreeSpace × Node => p.1 (p.2 ++ [n])) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have heq : ∀ᶠ q : TreeSpace × Node in 𝓝 p, q.2 = p.2 :=
    (continuous_snd.tendsto p).eventually ((isOpen_discrete {p.2}).mem_nhds rfl)
  have hc : ContinuousAt (fun q : TreeSpace × Node => q.1 (p.2 ++ [n])) p :=
    ((continuous_eval (p.2 ++ [n])).comp continuous_fst).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [heq] with q hq
  rw [hq]

private theorem exists_child_candidate (T : TreeSpace) (s : Node) :
    ∃ n, T (s ++ [n]) = true ∨ ¬ ∃ k, T (s ++ [k]) = true := by
  by_cases h : ∃ k, T (s ++ [k]) = true
  · obtain ⟨k,hk⟩ := h
    exact ⟨k,Or.inl hk⟩
  · exact ⟨0,Or.inr h⟩

def childIndex (T : TreeSpace) (s : Node) : ℕ := Nat.find (exists_child_candidate T s)

theorem childIndex_spec (T : TreeSpace) (s : Node) (h : ∃ k, T (s ++ [k]) = true) :
    T (s ++ [childIndex T s]) = true :=
  (Nat.find_spec (exists_child_candidate T s)).resolve_right (not_not.mpr h)

theorem measurable_childIndex : Measurable (fun p : TreeSpace × Node => childIndex p.1 p.2) := by
  have hc (n : ℕ) : MeasurableSet {p : TreeSpace × Node | p.1 (p.2 ++ [n]) = true} :=
    (measurableSet_singleton true).preimage (continuous_child_bit n).measurable
  have he : MeasurableSet {p : TreeSpace × Node | ∃ n, p.1 (p.2 ++ [n]) = true} := by
    simpa only [setOf_exists] using MeasurableSet.iUnion hc
  exact measurable_find (fun p : TreeSpace × Node => exists_child_candidate p.1 p.2)
    (fun n => (hc n).union he.compl)

def chosenPrefix (T : TreeSpace) : ℕ → Node
  | 0 => []
  | n+1 => chosenPrefix T n ++ [childIndex T (chosenPrefix T n)]

theorem measurable_chosenPrefix (n : ℕ) : Measurable (fun T => chosenPrefix T n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hstep : Measurable (fun T => childIndex T (chosenPrefix T n)) :=
      measurable_childIndex.comp (measurable_id.prodMk ih)
    exact (measurable_of_countable (fun p : Node × ℕ => p.1 ++ [p.2])).comp (ih.prodMk hstep)

def branchChoice (T : TreeSpace) : Baire := fun n => childIndex T (chosenPrefix T n)

theorem measurable_branchChoice : Measurable branchChoice := by
  apply measurable_pi_lambda
  intro n
  exact measurable_childIndex.comp (measurable_id.prodMk (measurable_chosenPrefix n))

theorem chosenPrefix_eq_branchPrefix (T : TreeSpace) (n : ℕ) :
    chosenPrefix T n = branchPrefix (branchChoice T) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change chosenPrefix T n ++ [branchChoice T n] = branchPrefix (branchChoice T) (n+1)
    rw [branchPrefix_succ,ih]

theorem chosenPrefix_mem (T : TreeSpace) (hroot : T [] = true) (hpruned : Pruned T)
    (n : ℕ) : T (chosenPrefix T n) = true := by
  induction n with
  | zero => exact hroot
  | succ n ih => exact childIndex_spec T _ (hpruned _ ih)

/-- The total Borel choice function is a branch on rooted pruned trees.
No branch-selection assertion is made for arbitrary ill-founded trees. -/
theorem branchChoice_spec (T : TreeSpace) (hroot : T [] = true) (hpruned : Pruned T) :
    ∀ n, T (branchPrefix (branchChoice T) n) = true := by
  intro n
  rw [← chosenPrefix_eq_branchPrefix]
  exact chosenPrefix_mem T hroot hpruned n

end FSCofinality.RootedTrees
