import FSCofinalityProof.PaddingExtension
import FSCofinalityProof.PaddingBackAndForth
import FSCofinalityProof.PaddingPaddedTree
import Mathlib.Logic.Denumerable

set_option autoImplicit false
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq α

namespace FSCofinality.Padding

theorem RankAgrees.symm {b : Ordinal.{0}} {r s : WithTop Ordinal.{0}}
    (h : RankAgrees b r s) : RankAgrees b s r := by
  rcases h with h | ⟨hr,hs⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨hs,hr⟩

def GoodPartial.swap {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : GoodPartial U T b where
  pairs := f.pairs.image Prod.swap
  roots := Finset.mem_image.mpr ⟨(T.root,U.root),f.roots,rfl⟩
  bijective := by
    rintro p hp q hq
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q₀,hq₀,rfl⟩ := Finset.mem_image.mp hq
    exact (f.bijective p₀ hp₀ q₀ hq₀).symm
  parents := by
    intro p hp
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨(T.parent p₀.1,U.parent p₀.2),f.parents p₀ hp₀,rfl⟩
  colors := by
    intro p hp
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
    exact (f.colors p₀ hp₀).symm
  ranks := by
    intro p hp
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
    exact (f.ranks p₀ hp₀).symm

theorem GoodPartial.mem_swap_iff {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (p : U.Vertex × T.Vertex) :
    p ∈ f.swap.pairs ↔ p.swap ∈ f.pairs := by
  constructor
  · intro hp
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hp
    subst p
    exact hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p.swap,hp,by cases p; rfl⟩

theorem GoodPartial.target_swap {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : f.swap.target = f.source := by
  simp only [GoodPartial.target,GoodPartial.source,GoodPartial.swap,Finset.image_image,
    Function.comp_def]
  rfl

def rootPartial (T U : RankedTree) (b : Ordinal.{0})
    (hc : T.color T.root = U.color U.root)
    (hr : RankAgrees b (T.rank T.root) (U.rank U.root)) : GoodPartial T U b where
  pairs := {(T.root,U.root)}
  roots := Finset.mem_singleton_self _
  bijective := by
    intro p hp q hq
    obtain rfl := Finset.mem_singleton.mp hp
    obtain rfl := Finset.mem_singleton.mp hq
    exact ⟨fun _ => rfl,fun _ => rfl⟩
  parents := by
    intro p hp
    obtain rfl := Finset.mem_singleton.mp hp
    simpa only [T.parent_root,U.parent_root] using Finset.mem_singleton_self (T.root,U.root)
  colors := by
    intro p hp
    obtain rfl := Finset.mem_singleton.mp hp
    exact hc
  ranks := by
    intro p hp
    obtain rfl := Finset.mem_singleton.mp hp
    exact hr

/-- The genuine fat-padding back-and-forth lemma, in the fixed native
relational tree language. The vertex enumerations can be any bijections. -/
theorem fat_padding_backAndForth
    (a b : Ordinal.{0}) (hba : cutoff b ≤ a) (C : List ℕ → ℕ)
    (eP : ℕ ≃ PaddedNode a) (eF : ℕ ≃ FatNode a) :
    PartialIso.BackAndForth
      (code (PaddedNode.tree a C) eP) (code (FatNode.tree a (C [])) eF) b [] := by
  let T := PaddedNode.tree a C
  let U := FatNode.tree a (C [])
  have hforth : ∀ c ≤ b, ∀ d < c, ∀ f : GoodPartial T U c, ∀ x : T.Vertex,
      ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ x ∈ g.source := by
    intro c hcb d hdc f x
    exact exists_good_extension (FatNode.hasFatReservoirs a (C [])) f hdc
      ((cutoff_mono hcb).trans hba) x
  have hback : ∀ c ≤ b, ∀ d < c, ∀ f : GoodPartial T U c, ∀ y : U.Vertex,
      ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ y ∈ g.target := by
    intro c hcb d hdc f y
    obtain ⟨g,hg,hy⟩ := exists_good_extension (PaddedNode.hasFatReservoirs a C) f.swap hdc
      ((cutoff_mono hcb).trans hba) y
    refine ⟨g.swap,?_,?_⟩
    · intro p hp
      apply (g.mem_swap_iff p).mpr
      exact hg ((f.mem_swap_iff p.swap).mpr hp)
    · rwa [g.target_swap]
  have hrank : RankAgrees b (T.rank T.root) (U.rank U.root) :=
    Or.inr ⟨le_top,WithTop.coe_le_coe.mpr hba⟩
  let f := rootPartial T U b rfl hrank
  exact backAndForth_of_goodPartial T U eP eF b hforth hback b le_rfl f []
    (fun _ h => False.elim (List.not_mem_nil h))

end FSCofinality.Padding
