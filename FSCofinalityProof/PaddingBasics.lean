import FSCofinalityProof.PartialIsomorphismRank
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.WithBot

set_option autoImplicit false
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq α
open Set Order

namespace FSCofinality.Padding

/-- The cutoff used in the fat-tree back-and-forth argument. -/
def cutoff (b : Ordinal.{0}) : Ordinal.{0} := Ordinal.omega0 * b

/-- Below the cutoff ranks must agree exactly; above it they may differ.
The top rank denotes an original vertex on an infinite branch. -/
def RankAgrees (b : Ordinal.{0}) (r s : WithTop Ordinal.{0}) : Prop :=
  r = s ∨ ((cutoff b : WithTop Ordinal.{0}) ≤ r ∧ (cutoff b : WithTop Ordinal.{0}) ≤ s)

theorem cutoff_mono {b d : Ordinal.{0}} (h : d ≤ b) : cutoff d ≤ cutoff b :=
  mul_le_mul_left' h Ordinal.omega0

theorem RankAgrees.mono {b d : Ordinal.{0}} {r s : WithTop Ordinal.{0}}
    (h : RankAgrees b r s) (hdb : d ≤ b) : RankAgrees d r s := by
  rcases h with h | ⟨hr,hs⟩
  · exact Or.inl h
  · have hcut : (cutoff d : WithTop Ordinal.{0}) ≤ (cutoff b : WithTop Ordinal.{0}) :=
      WithTop.coe_le_coe.mpr (cutoff_mono hdb)
    exact Or.inr ⟨hcut.trans hr,hcut.trans hs⟩

/-- The underlying rooted colored tree, with finite depth to the root
and an ordinal or infinite rank at each vertex. -/
structure RankedTree where
  Vertex : Type 1
  root : Vertex
  parent : Vertex → Vertex
  color : Vertex → ℕ
  height : Vertex → ℕ
  rank : Vertex → WithTop Ordinal.{0}
  parent_root : parent root = root
  height_root : height root = 0
  height_zero : ∀ v, height v = 0 → v = root
  parent_height : ∀ v, v ≠ root → height (parent v)+1 = height v
  rank_parent : ∀ v, rank v ≤ rank (parent v)
  finite_rank_strict : ∀ v, v ≠ root → rank v ≠ ⊤ → rank v < rank (parent v)

/-- The reservoirs supply infinitely many fresh children of every
available smaller ordinal rank and color. This property will be proved
for the explicit canonical and padded trees. -/
def HasFatReservoirs (T : RankedTree) (a : Ordinal.{0}) : Prop :=
  ∀ (v : T.Vertex) (r : Ordinal.{0}), r < a →
    (r : WithTop Ordinal.{0}) < T.rank v → ∀ c : ℕ,
      Set.Infinite {w : T.Vertex | w ≠ T.root ∧ T.parent w = v ∧
        T.rank w = (r : WithTop Ordinal.{0}) ∧ T.color w = c}

/-- A finite ancestor-closed partial tree isomorphism with the required
rank comparison. The root pair is always present. -/
structure GoodPartial (T U : RankedTree) (b : Ordinal.{0}) where
  pairs : Finset (T.Vertex × U.Vertex)
  roots : (T.root,U.root) ∈ pairs
  bijective : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 = q.1 ↔ p.2 = q.2
  parents : ∀ p ∈ pairs, (T.parent p.1,U.parent p.2) ∈ pairs
  colors : ∀ p ∈ pairs, T.color p.1 = U.color p.2
  ranks : ∀ p ∈ pairs, RankAgrees b (T.rank p.1) (U.rank p.2)

def GoodPartial.source {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : Finset T.Vertex := f.pairs.image Prod.fst

def GoodPartial.target {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : Finset U.Vertex := f.pairs.image Prod.snd

def GoodPartial.lower {T U : RankedTree} {b d : Ordinal.{0}}
    (f : GoodPartial T U b) (hdb : d ≤ b) : GoodPartial T U d where
  pairs := f.pairs
  roots := f.roots
  bijective := f.bijective
  parents := f.parents
  colors := f.colors
  ranks := fun p hp => (f.ranks p hp).mono hdb

theorem GoodPartial.root_mem_source {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : T.root ∈ f.source :=
  Finset.mem_image.mpr ⟨(T.root,U.root),f.roots,rfl⟩

theorem GoodPartial.root_mem_target {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : U.root ∈ f.target :=
  Finset.mem_image.mpr ⟨(T.root,U.root),f.roots,rfl⟩

theorem GoodPartial.parent_mem_source {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) {v : T.Vertex} (hv : v ∈ f.source) :
    T.parent v ∈ f.source := by
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨(T.parent x,U.parent y),f.parents (x,y) hxy,rfl⟩

theorem GoodPartial.parent_mem_target {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) {v : U.Vertex} (hv : v ∈ f.target) :
    U.parent v ∈ f.target := by
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨(T.parent x,U.parent y),f.parents (x,y) hxy,rfl⟩

/-- Adding a fresh child pair preserves the complete finite tree
matching. Its parents must already be matched. -/
def GoodPartial.extend {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) (y : U.Vertex)
    (hx : x ∉ f.source) (hy : y ∉ f.target)
    (hparent : (T.parent x,U.parent y) ∈ f.pairs)
    (hcolor : T.color x = U.color y)
    (hrank : RankAgrees b (T.rank x) (U.rank y)) : GoodPartial T U b where
  pairs := insert (x,y) f.pairs
  roots := Finset.mem_insert_of_mem f.roots
  bijective := by
    intro p hp q hq
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ⟨fun _ => rfl,fun _ => rfl⟩
      · have hxq : x ≠ q.1 := fun h => hx (h.symm ▸ Finset.mem_image.mpr ⟨q,hq,rfl⟩)
        have hyq : y ≠ q.2 := fun h => hy (h.symm ▸ Finset.mem_image.mpr ⟨q,hq,rfl⟩)
        exact ⟨fun h => False.elim (hxq h),fun h => False.elim (hyq h)⟩
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · have hpx : p.1 ≠ x := fun h => hx (h ▸ Finset.mem_image.mpr ⟨p,hp,rfl⟩)
        have hpy : p.2 ≠ y := fun h => hy (h ▸ Finset.mem_image.mpr ⟨p,hp,rfl⟩)
        exact ⟨fun h => False.elim (hpx h),fun h => False.elim (hpy h)⟩
      · exact f.bijective p hp q hq
  parents := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_insert_of_mem hparent
    · exact Finset.mem_insert_of_mem (f.parents p hp)
  colors := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hcolor
    · exact f.colors p hp
  ranks := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hrank
    · exact f.ranks p hp

/-- An explicit fresh reservoir point exists outside every finite
forbidden range. -/
theorem exists_fresh_child {U : RankedTree} {a : Ordinal.{0}}
    (hU : HasFatReservoirs U a) (v : U.Vertex) (r : Ordinal.{0})
    (hra : r < a) (hrv : (r : WithTop Ordinal.{0}) < U.rank v)
    (c : ℕ) (forbidden : Finset U.Vertex) :
    ∃ w : U.Vertex, w ∉ forbidden ∧ w ≠ U.root ∧ U.parent w = v ∧
      U.rank w = (r : WithTop Ordinal.{0}) ∧ U.color w = c := by
  obtain ⟨w,hw,hwf⟩ := (hU v r hra hrv c).exists_notMem_finset forbidden
  exact ⟨w,hwf,hw⟩

end FSCofinality.Padding
