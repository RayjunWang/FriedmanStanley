import FSCofinalityProof.PaddingAncestors
import Mathlib.SetTheory.Cardinal.Aleph

set_option autoImplicit false
noncomputable section
open Set

namespace FSCofinality.Padding

/-- A vertex of the canonical fat tree. Each descent chooses a smaller
ordinal rank, a color, and an independent multiplicity index. -/
inductive FatNode : Ordinal.{0} → Type 1
  | root {a : Ordinal.{0}} : FatNode a
  | descend {a : Ordinal.{0}} (r : a.ToType) (color copy : ℕ)
      (sub : FatNode (r : Ordinal.{0})) : FatNode a

namespace FatNode

def rank {a : Ordinal.{0}} : FatNode a → Ordinal.{0}
  | root => a
  | descend _ _ _ sub => rank sub

def height {a : Ordinal.{0}} : FatNode a → ℕ
  | root => 0
  | descend _ _ _ sub => height sub+1

def color {a : Ordinal.{0}} (rootColor : ℕ) : FatNode a → ℕ
  | root => rootColor
  | descend _ c _ sub => color c sub

def parent {a : Ordinal.{0}} : FatNode a → FatNode a
  | root => root
  | descend _ _ _ root => root
  | descend r c k (descend s d l sub) => descend r c k (parent (descend s d l sub))

theorem rank_le {a : Ordinal.{0}} (v : FatNode a) : rank v ≤ a := by
  induction v with
  | root => exact le_rfl
  | @descend a r c k sub IH => exact IH.trans r.toOrd.property.le

theorem rank_lt_of_ne_root {a : Ordinal.{0}} (v : FatNode a) (hv : v ≠ root) :
    rank v < a := by
  cases v with
  | root => exact False.elim (hv rfl)
  | descend r c k sub => exact (rank_le sub).trans_lt r.toOrd.property

theorem height_pos_of_ne_root {a : Ordinal.{0}} (v : FatNode a) (hv : v ≠ root) :
    0 < height v := by
  cases v with
  | root => exact False.elim (hv rfl)
  | descend r c k sub => exact Nat.zero_lt_succ _

theorem height_zero {a : Ordinal.{0}} (v : FatNode a) (hv : height v = 0) : v = root := by
  cases v with
  | root => rfl
  | descend r c k sub => simp [height] at hv

theorem parent_height {a : Ordinal.{0}} (v : FatNode a) (hv : v ≠ root) :
    height (parent v)+1 = height v := by
  induction v with
  | root => exact False.elim (hv rfl)
  | @descend a r c k sub IH =>
      cases sub with
      | root => rfl
      | descend s d l sub =>
          have hsub : (descend s d l sub : FatNode (r : Ordinal.{0})) ≠ root := by
            intro h; cases h
          simpa only [parent,height] using congrArg (fun n : ℕ => n+1) (IH hsub)

theorem rank_parent_lt {a : Ordinal.{0}} (v : FatNode a) (hv : v ≠ root) :
    rank v < rank (parent v) := by
  induction v with
  | root => exact False.elim (hv rfl)
  | @descend a r c k sub IH =>
      cases sub with
      | root => exact r.toOrd.property
      | descend s d l sub =>
          have hsub : (descend s d l sub : FatNode (r : Ordinal.{0})) ≠ root := by
            intro h; cases h
          exact IH hsub

def tree (a : Ordinal.{0}) (rootColor : ℕ) : RankedTree where
  Vertex := FatNode a
  root := root
  parent := parent
  color := color rootColor
  height := height
  rank := fun v => (rank v : WithTop Ordinal.{0})
  parent_root := rfl
  height_root := rfl
  height_zero := height_zero
  parent_height := parent_height
  rank_parent := by
    intro v
    by_cases hv : v = root
    · subst v; exact le_rfl
    · exact (WithTop.coe_lt_coe.mpr (rank_parent_lt v hv)).le
  finite_rank_strict := by
    intro v hv _
    exact WithTop.coe_lt_coe.mpr (rank_parent_lt v hv)

/-- Append a new reservoir child at the current vertex. -/
def child {a : Ordinal.{0}} : (v : FatNode a) →
    (r : Ordinal.{0}) → r < rank v → ℕ → ℕ → FatNode a
  | root, r, hr, c, k => descend (Ordinal.ToType.mk ⟨r,hr⟩) c k root
  | descend s d l sub, r, hr, c, k => descend s d l (child sub r hr c k)

theorem child_ne_root {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c k : ℕ) : child v r hr c k ≠ root := by
  cases v <;> simp only [child] <;> intro h <;> cases h

theorem parent_descend {a : Ordinal.{0}} (s : a.ToType) (c k : ℕ)
    (v : FatNode (s : Ordinal.{0})) (hv : v ≠ root) :
    parent (descend s c k v) = descend s c k (parent v) := by
  cases v with
  | root => exact False.elim (hv rfl)
  | descend t d l sub => rfl

theorem parent_child {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c k : ℕ) : parent (child v r hr c k) = v := by
  induction v with
  | root => rfl
  | descend s d l sub IH =>
      rw [child,parent_descend s d l _ (child_ne_root sub r hr c k),IH]

theorem rank_child {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c k : ℕ) : rank (child v r hr c k) = r := by
  induction v with
  | root => simp [child,rank,Ordinal.ToType.toOrd]
  | descend s d l sub IH => exact IH hr

theorem color_child {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c k rootColor : ℕ) :
    color rootColor (child v r hr c k) = c := by
  induction v generalizing rootColor with
  | root => rfl
  | descend s d l sub IH => exact IH hr d

theorem child_copy_injective {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c : ℕ) :
    Function.Injective (fun k : ℕ => child v r hr c k) := by
  induction v with
  | root => intro k l h; simpa [child,descend.injEq] using h
  | descend s d l sub IH =>
      intro k l h
      apply IH hr
      simpa [child,descend.injEq] using h

/-- Every canonical fat tree has all the reservoirs used by the
finite-path extension argument. -/
theorem hasFatReservoirs (a : Ordinal.{0}) (rootColor : ℕ) :
    HasFatReservoirs (tree a rootColor) a := by
  intro v r _ hr c
  have hrv : r < rank v := WithTop.coe_lt_coe.mp hr
  have hinf : Set.Infinite (Set.range (fun k : ℕ => child v r hrv c k)) :=
    Set.infinite_range_of_injective (child_copy_injective v r hrv c)
  apply hinf.mono
  rintro w ⟨k,rfl⟩
  exact ⟨child_ne_root v r hrv c k,parent_child v r hrv c k,
    by simp only [tree,rank_child],color_child v r hrv c k rootColor⟩

def split {a : Ordinal.{0}} : FatNode a →
    Unit ⊕ (Σ r : a.ToType, ℕ × ℕ × FatNode (r : Ordinal.{0}))
  | root => Sum.inl ()
  | descend r c k sub => Sum.inr ⟨r,c,k,sub⟩

def join {a : Ordinal.{0}} :
    Unit ⊕ (Σ r : a.ToType, ℕ × ℕ × FatNode (r : Ordinal.{0})) → FatNode a
  | Sum.inl _ => root
  | Sum.inr ⟨r,c,k,sub⟩ => descend r c k sub

theorem join_split {a : Ordinal.{0}} (v : FatNode a) : join (split v) = v := by
  cases v <;> rfl

/-- Each canonical fat tree at a countable ordinal has countably many
vertices, despite its ordinal-indexed semantic presentation. -/
theorem countable (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) : Countable (FatNode a) := by
  revert ha
  induction a using WellFoundedLT.induction with
  | ind a IH =>
      intro ha
      haveI : Countable a.ToType := Cardinal.mk_le_aleph0_iff.mp (by
        rw [Cardinal.mk_toType]
        exact Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp ha))
      letI : ∀ r : a.ToType, Countable (FatNode (r : Ordinal.{0})) := fun r =>
        IH (r : Ordinal.{0}) r.toOrd.property (r.toOrd.property.trans ha)
      have hi : Function.Injective (@split a) :=
        Function.LeftInverse.injective (fun v => join_split v)
      exact hi.countable

end FatNode
end FSCofinality.Padding
