import Definitions.Def_FSCofinalityStructures20261102
import Mathlib.SetTheory.Ordinal.Basic

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace

namespace FSCofinality.RootedTrees

abbrev Node := List ℕ

def PrefixClosed (t : Node → Bool) : Prop :=
  ∀ s n, t (s ++ [n]) = true → t s = true

/-- Prefix-closed trees, including the empty tree and finite trees. -/
def TreeSpace := {t : Node → Bool // PrefixClosed t}

instance : TopologicalSpace TreeSpace :=
  inferInstanceAs (TopologicalSpace {t : Node → Bool // PrefixClosed t})

instance : CoeFun TreeSpace (fun _ => Node → Bool) := ⟨fun t => t.val⟩

theorem isClosed_prefixClosed : IsClosed {t : Node → Bool | PrefixClosed t} := by
  unfold PrefixClosed
  simp only [setOf_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro n
  have heq : {t : Node → Bool | t (s ++ [n]) = true → t s = true} =
      {t | t (s ++ [n]) = false} ∪ {t | t s = true} := by
    ext t
    cases h : t (s ++ [n]) <;> simp [h]
  rw [heq]
  exact (isClosed_eq (continuous_apply (s ++ [n])) continuous_const).union
    (isClosed_eq (continuous_apply s) continuous_const)

instance : PolishSpace TreeSpace := by
  letI : PolishSpace (Node → Bool) := {
    toSecondCountableTopology := inferInstance
    toIsCompletelyMetrizableSpace := inferInstance }
  exact isClosed_prefixClosed.polishSpace

instance : MeasurableSpace TreeSpace := borel TreeSpace
instance : BorelSpace TreeSpace := ⟨rfl⟩

def Nodes (T : TreeSpace) := {s : Node // T s = true}

/-- The first argument is an immediate child of the second. -/
def Child {T : TreeSpace} (s t : Nodes T) : Prop :=
  ∃ n : ℕ, s.val = t.val ++ [n]

/-- One actual node bijection preserves and reflects the parent relation.
In particular, empty trees cannot be isomorphic to nonempty trees. -/
def Isomorphic (T U : TreeSpace) : Prop :=
  ∃ e : Nodes T ≃ Nodes U, ∀ s t, Child s t ↔ Child (e s) (e t)

/-- A global bound for the reverse-tree well-founded height. Every node is
assigned an ordinal below `a`, and immediate children receive strictly
smaller ordinals. The empty tree has height zero and a one-node tree has
height one. This bounds the whole tree, rather than declaring its root
to have leaf-rank zero and then silently identifying ordinal indices. -/
def BoundedTree (T : TreeSpace) (a : Ordinal.{0}) : Prop :=
  ∃ ρ : Nodes T → Ordinal.{0},
    (∀ s, ρ s < a) ∧ ∀ s t, Child s t → ρ s < ρ t

def treeRelation (a : Ordinal.{0}) : CodedRelation where
  Carrier := {T : TreeSpace // BoundedTree T a}
  measurableSpace := inferInstance
  rel := fun T U => Isomorphic T.val U.val

def emptyTree : TreeSpace := ⟨fun _ => false, by simp [PrefixClosed]⟩

def oneNodeTree : TreeSpace := ⟨fun s => decide (s = []), by simp [PrefixClosed]⟩

theorem bounded_emptyTree (a : Ordinal.{0}) : BoundedTree emptyTree a := by
  have he (s : Nodes emptyTree) : False := by
    have h := s.property
    simp [emptyTree] at h
  exact ⟨fun s => False.elim (he s), fun s => False.elim (he s),
    fun s _ _ => False.elim (he s)⟩

theorem bounded_oneNodeTree : BoundedTree oneNodeTree 1 := by
  refine ⟨fun _ => 0, fun _ => zero_lt_one, ?_⟩
  intro s t h
  obtain ⟨n, hn⟩ := h
  have hs : s.val = [] := of_decide_eq_true s.property
  have ht : t.val = [] := of_decide_eq_true t.property
  simp [hs, ht] at hn

end FSCofinality.RootedTrees
