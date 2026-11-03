import FSCofinalityProof.TreeRanks
import Mathlib.Data.List.Indexes
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace FSCofinality.RootedTrees

def firstNode (s : Node) : Node := s.map (fun n => (Nat.unpair n).1)
def secondNode (s : Node) : Node := s.map (fun n => (Nat.unpair n).2)

/-- A countable tree records simultaneous finite approximations to a
parameter and to a node of its continuously parametrized tree. -/
def parameterTree (f : Baire → TreeSpace) : TreeSpace :=
  ⟨fun s => decide (∃ x : Baire, branchPrefix x s.length = firstNode s ∧
      f x (secondNode s) = true), by
    intro s k hs
    obtain ⟨x,hx,ht⟩ := of_decide_eq_true hs
    apply decide_eq_true
    refine ⟨x,?_,?_⟩
    · have h := congrArg (fun l : Node => l.take s.length) hx
      simpa [firstNode,List.map_append] using h
    · have ht' : f x (secondNode s ++ [(Nat.unpair k).2]) = true := by
        simpa [secondNode,List.map_append] using ht
      exact mem_parent (f x) (secondNode s) (Nat.unpair k).2 ht'⟩

theorem parameterTree_mem_iff (f : Baire → TreeSpace) (s : Node) :
    parameterTree f s = true ↔ ∃ x : Baire,
      branchPrefix x s.length = firstNode s ∧ f x (secondNode s) = true := by
  simp only [parameterTree,decide_eq_true_eq]

@[simp] theorem firstNode_branchPrefix (z : Baire) (n : ℕ) :
    firstNode (branchPrefix z n) = branchPrefix (fun i => (Nat.unpair (z i)).1) n := by
  simp [firstNode,branchPrefix,List.map_ofFn,Function.comp_def]

@[simp] theorem secondNode_branchPrefix (z : Baire) (n : ℕ) :
    secondNode (branchPrefix z n) = branchPrefix (fun i => (Nat.unpair (z i)).2) n := by
  simp [secondNode,branchPrefix,List.map_ofFn,Function.comp_def]

theorem branch_of_parameterTree (f : Baire → TreeSpace) (hf : Continuous f)
    (h : HasBranch (parameterTree f)) : ∃ x : Baire, HasBranch (f x) := by
  obtain ⟨z,hz⟩ := h
  let x : Baire := fun n => (Nat.unpair (z n)).1
  let y : Baire := fun n => (Nat.unpair (z n)).2
  have hex (n : ℕ) : ∃ u : Baire,
      branchPrefix u n = branchPrefix x n ∧ f u (branchPrefix y n) = true := by
    simpa only [parameterTree_mem_iff,length_branchPrefix,firstNode_branchPrefix,
      secondNode_branchPrefix] using hz n
  choose u hu ht using hex
  have hlim := tendsto_of_prefix_agreement u x hu
  refine ⟨x,y,fun k => ?_⟩
  have htrue : ∀ᶠ n in atTop, f (u n) (branchPrefix y k) = true := by
    filter_upwards [eventually_ge_atTop k] with n hn
    exact mem_branchPrefix_of_le (f (u n)) y hn (ht n)
  have hc := ((continuous_eval (branchPrefix y k)).comp hf).tendsto x |>.comp hlim
  have hconst : Tendsto (fun n => f (u n) (branchPrefix y k)) atTop (𝓝 true) :=
    tendsto_const_nhds.congr' (htrue.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hc hconst

def zipNode (x : Baire) (s : Node) : Node :=
  s.mapIdx (fun i n => Nat.pair (x i) n)

@[simp] theorem length_zipNode (x : Baire) (s : Node) : (zipNode x s).length = s.length := by
  simp [zipNode]

@[simp] theorem firstNode_zipNode (x : Baire) (s : Node) :
    firstNode (zipNode x s) = branchPrefix x s.length := by
  simp [firstNode,zipNode,List.mapIdx_eq_ofFn,branchPrefix,List.map_ofFn,Function.comp_def]

@[simp] theorem secondNode_zipNode (x : Baire) (s : Node) :
    secondNode (zipNode x s) = s := by
  apply List.ext_getElem
  · simp [secondNode,zipNode]
  · intro i hi hi'
    simp [secondNode,zipNode,List.mapIdx_eq_ofFn]

theorem zipNode_append (x : Baire) (s : Node) (n : ℕ) :
    zipNode x (s ++ [n]) = zipNode x s ++ [Nat.pair (x s.length) n] := by
  simp only [zipNode,List.mapIdx_append_one]

def nodeIntoParameter (f : Baire → TreeSpace) (x : Baire)
    (s : Nodes (f x)) : Nodes (parameterTree f) :=
  ⟨zipNode x s.val,(parameterTree_mem_iff f _).mpr
    ⟨x,by simp,by simpa using s.property⟩⟩

theorem child_nodeIntoParameter (f : Baire → TreeSpace) (x : Baire)
    {s t : Nodes (f x)} (hst : Child s t) :
    Child (nodeIntoParameter f x s) (nodeIntoParameter f x t) := by
  obtain ⟨n,hn⟩ := hst
  refine ⟨Nat.pair (x t.val.length) n,?_⟩
  change zipNode x s.val = zipNode x t.val ++ [Nat.pair (x t.val.length) n]
  rw [hn,zipNode_append]

theorem bounded_of_parameterTree (f : Baire → TreeSpace) {a : Ordinal.{0}}
    (h : BoundedTree (parameterTree f) a) (x : Baire) : BoundedTree (f x) a := by
  obtain ⟨ρ,hρ,hchild⟩ := h
  exact ⟨fun s => ρ (nodeIntoParameter f x s),fun s => hρ _,
    fun s t hst => hchild _ _ (child_nodeIntoParameter f x hst)⟩

/-- Analytic boundedness for the exact native tree code and global height
bound used in the mission. No ordinal rank theorem is assumed here. -/
theorem analytic_wellFoundedTree_bounded (A : Set TreeSpace)
    (hA : AnalyticSet A) (hWF : ∀ T ∈ A, ¬ HasBranch T) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ ∀ T ∈ A, BoundedTree T a := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f,hf,hfA⟩
  · exact ⟨0,by exact (Cardinal.isSuccLimit_omega 1).bot_lt,fun T hT => False.elim hT⟩
  · have hnb : ¬ HasBranch (parameterTree f) := by
      intro h
      obtain ⟨x,hx⟩ := branch_of_parameterTree f hf h
      exact hWF (f x) (by rw [← hfA]; exact mem_range_self x) hx
    obtain ⟨a,ha,hab⟩ := exists_countable_bound_of_wellFounded (parameterTree f)
      ((wellFounded_child_iff_no_branch _).mpr hnb)
    refine ⟨a,ha,?_⟩
    intro T hT
    rw [← hfA] at hT
    obtain ⟨x,rfl⟩ := hT
    exact bounded_of_parameterTree f hab x

end FSCofinality.RootedTrees
