import FSCofinalityProof.TreeBranches
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Cardinal.Regular

noncomputable section
open Set Order Ordinal

namespace FSCofinality.RootedTrees

instance (T : TreeSpace) : Countable (Nodes T) :=
  inferInstanceAs (Countable {s : List ℕ // T s = true})

theorem BoundedTree.wellFounded {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T a) : WellFounded (@Child T) := by
  obtain ⟨ρ,_,hρ⟩ := h
  exact (InvImage.wf ρ Ordinal.lt_wf).mono (fun s t hst => hρ s t hst)

theorem BoundedTree.no_branch {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T a) : ¬ HasBranch T :=
  (wellFounded_child_iff_no_branch T).mp h.wellFounded

/-- Every well-founded countable tree admits a countable ordinal bound on
its whole reverse-tree height, with the exact fixed mission definition. -/
theorem exists_countable_bound_of_wellFounded (T : TreeSpace)
    (hwf : WellFounded (@Child T)) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ BoundedTree T a := by
  letI : IsWellFounded (Nodes T) (@Child T) := ⟨hwf⟩
  let ρ : Nodes T → Ordinal.{0} := IsWellFounded.rank (@Child T)
  have hc : ∀ s : Nodes T, ρ s < Ordinal.omega 1 := by
    intro s
    induction s using hwf.induction with
    | h s ih =>
      change IsWellFounded.rank (@Child T) s < Ordinal.omega 1
      rw [IsWellFounded.rank_eq]
      apply Ordinal.iSup_lt_omega_one
      intro t
      exact (Cardinal.isSuccLimit_omega 1).succ_lt (ih t.val t.property)
  let a : Ordinal.{0} := ⨆ s : Nodes T, Order.succ (ρ s)
  refine ⟨a,Ordinal.iSup_lt_omega_one (fun s =>
    (Cardinal.isSuccLimit_omega 1).succ_lt (hc s)),ρ,?_,?_⟩
  · intro s
    exact (Order.lt_succ (ρ s)).trans_le (Ordinal.le_iSup _ s)
  · intro s t hst
    exact IsWellFounded.rank_lt_of_rel hst

theorem no_branch_iff_countable_bound (T : TreeSpace) :
    ¬ HasBranch T ↔ ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ BoundedTree T a := by
  constructor
  · intro h
    exact exists_countable_bound_of_wellFounded T
      ((wellFounded_child_iff_no_branch T).mpr h)
  · rintro ⟨a,_,ha⟩
    exact ha.no_branch

end FSCofinality.RootedTrees
