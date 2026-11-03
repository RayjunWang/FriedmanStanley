import FSCofinalityProof.TreeAssembly

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RootedTrees

/-- Infinitely many empty padding entries make absent child labels irrelevant. -/
def paddedChildren (T : TreeSpace) (i : ℕ) : TreeSpace :=
  if i % 2 = 0 then childTree T (i/2) else emptyTree

@[simp] theorem paddedChildren_even (T : TreeSpace) (n : ℕ) :
    paddedChildren T (2*n) = childTree T n := by simp [paddedChildren]

@[simp] theorem paddedChildren_odd (T : TreeSpace) (n : ℕ) :
    paddedChildren T (2*n+1) = emptyTree := by simp [paddedChildren,Nat.add_mod]

theorem continuous_paddedChildren : Continuous paddedChildren := by
  apply continuous_pi
  intro i
  by_cases hi : i%2=0
  · simpa only [paddedChildren,if_pos hi] using continuous_childTree (i/2)
  · simpa only [paddedChildren,if_neg hi] using
      (continuous_const : Continuous (fun _ : TreeSpace => emptyTree))

theorem measurable_paddedChildren : Measurable paddedChildren := continuous_paddedChildren.measurable

theorem BoundedTree.paddedChildren_of_succ {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T (a+1)) (i : ℕ) : BoundedTree (paddedChildren T i) a := by
  by_cases hi : i%2=0
  · simpa only [paddedChildren,if_pos hi] using h.child_of_succ (i/2)
  · simpa only [paddedChildren,if_neg hi] using bounded_emptyTree a

abbrev PresentChildren (T : TreeSpace) := {i : ℕ // paddedChildren T i [] = true}
abbrev AbsentChildren (T : TreeSpace) := {i : ℕ // ¬ paddedChildren T i [] = true}

theorem present_even {T : TreeSpace} (i : PresentChildren T) : i.val % 2 = 0 := by
  by_contra h
  have hp := i.property
  simp only [paddedChildren,if_neg h,emptyTree] at hp
  contradiction

def labelPresentEquiv (T : TreeSpace) : ChildLabels T ≃ PresentChildren T where
  toFun n := ⟨2*n.val,by simpa using n.property⟩
  invFun i := ⟨i.val/2,by
    have h := i.property
    simpa only [paddedChildren,if_pos (present_even i)] using h⟩
  left_inv n := by apply Subtype.ext; simp
  right_inv i := by
    apply Subtype.ext
    change 2*(i.val/2) = i.val
    have h := present_even i
    omega

@[simp] theorem labelPresentEquiv_val (T : TreeSpace) (n : ChildLabels T) :
    (labelPresentEquiv T n).val = 2*n.val := rfl

theorem labelPresentEquiv_tree (T : TreeSpace) (n : ChildLabels T) :
    paddedChildren T (labelPresentEquiv T n).val = childTree T n.val := by simp

instance absentChildren_infinite (T : TreeSpace) : Infinite (AbsentChildren T) := by
  let f : ℕ → AbsentChildren T := fun n => ⟨2*n+1,by simp [emptyTree]⟩
  apply Infinite.of_injective f
  intro n m h
  have hv := congrArg Subtype.val h
  dsimp only [f] at hv
  omega

def absentEquiv (T U : TreeSpace) : AbsentChildren T ≃ AbsentChildren U :=
  (Classical.choice (inferInstance : Nonempty (ℕ ≃ AbsentChildren T))).symm.trans
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ AbsentChildren U)))

end FSCofinality.RootedTrees
