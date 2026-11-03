import FSCofinalityProof.PaddingCanonical

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.Padding

/-- The fixed domain of a padded tuple tree: original finite tuples,
and nonroot canonical-fat vertices attached below each tuple. -/
def PaddedNode (a : Ordinal.{0}) :=
  List ℕ ⊕ (List ℕ × {v : FatNode a // v ≠ FatNode.root})

namespace PaddedNode

def root (a : Ordinal.{0}) : PaddedNode a := Sum.inl []

def parent {a : Ordinal.{0}} : PaddedNode a → PaddedNode a
  | Sum.inl s => Sum.inl s.dropLast
  | Sum.inr (s,v) => if h : FatNode.parent v.val = FatNode.root then Sum.inl s
      else Sum.inr (s,⟨FatNode.parent v.val,h⟩)

def height {a : Ordinal.{0}} : PaddedNode a → ℕ
  | Sum.inl s => s.length
  | Sum.inr (s,v) => s.length+FatNode.height v.val

def rank {a : Ordinal.{0}} : PaddedNode a → WithTop Ordinal.{0}
  | Sum.inl _ => ⊤
  | Sum.inr (_,v) => (FatNode.rank v.val : WithTop Ordinal.{0})

def color {a : Ordinal.{0}} (originalColor : List ℕ → ℕ) : PaddedNode a → ℕ
  | Sum.inl s => originalColor s
  | Sum.inr (_,v) => FatNode.color 0 v.val

theorem height_zero {a : Ordinal.{0}} (v : PaddedNode a) (hv : height v = 0) : v = root a := by
  cases v with
  | inl s =>
      have hs : s = [] := List.length_eq_zero_iff.mp hv
      rw [hs]
      rfl
  | inr v =>
      have hp := FatNode.height_pos_of_ne_root v.2.val v.2.property
      simp only [height] at hv
      omega

theorem parent_height {a : Ordinal.{0}} (v : PaddedNode a) (hv : v ≠ root a) :
    height (parent v)+1 = height v := by
  cases v with
  | inl s =>
      have hs : s ≠ [] := fun hs => hv (by rw [hs]; rfl)
      have hlen : 0 < s.length := List.length_pos_iff.mpr hs
      simp only [parent,height,List.length_dropLast]
      omega
  | inr v =>
      have hp := FatNode.parent_height v.2.val v.2.property
      dsimp only [parent]
      split_ifs with h
      · rw [h] at hp
        simp only [FatNode.height] at hp
        simp only [height]
        omega
      · simp only [height]
        omega

theorem rank_parent {a : Ordinal.{0}} (v : PaddedNode a) : rank v ≤ rank (parent v) := by
  cases v with
  | inl s => exact le_rfl
  | inr v =>
      have hp := FatNode.rank_parent_lt v.2.val v.2.property
      dsimp only [parent]
      split_ifs
      · exact le_top
      · exact (WithTop.coe_lt_coe.mpr hp).le

theorem finite_rank_strict {a : Ordinal.{0}} (v : PaddedNode a)
    (_ : v ≠ root a) (hv : rank v ≠ ⊤) : rank v < rank (parent v) := by
  cases v with
  | inl s => exact False.elim (hv rfl)
  | inr v =>
      have hp := FatNode.rank_parent_lt v.2.val v.2.property
      dsimp only [parent]
      split_ifs
      · exact WithTop.coe_lt_top _
      · exact WithTop.coe_lt_coe.mpr hp

def tree (a : Ordinal.{0}) (originalColor : List ℕ → ℕ) : RankedTree where
  Vertex := PaddedNode a
  root := root a
  parent := parent
  color := color originalColor
  height := height
  rank := rank
  parent_root := rfl
  height_root := rfl
  height_zero := height_zero
  parent_height := parent_height
  rank_parent := rank_parent
  finite_rank_strict := finite_rank_strict

def embed {a : Ordinal.{0}} (s : List ℕ) (v : FatNode a) : PaddedNode a :=
  if h : v = FatNode.root then Sum.inl s else Sum.inr (s,⟨v,h⟩)

@[simp] theorem embed_root {a : Ordinal.{0}} (s : List ℕ) :
    embed s (FatNode.root : FatNode a) = Sum.inl s := by simp [embed]

theorem embed_injective {a : Ordinal.{0}} (s : List ℕ) :
    Function.Injective (embed (a := a) s) := by
  intro v w h
  by_cases hv : v = FatNode.root <;> by_cases hw : w = FatNode.root
  · exact hv.trans hw.symm
  · simp [embed,hv,hw] at h
  · simp [embed,hv,hw] at h
  · simp only [embed,dif_neg hv,dif_neg hw] at h
    exact congrArg Subtype.val (congrArg Prod.snd (Sum.inr.inj h))

theorem embed_ne_root {a : Ordinal.{0}} (s : List ℕ) (v : FatNode a)
    (hv : v ≠ FatNode.root) : embed s v ≠ root a := by simp [embed,hv,root]

theorem parent_embed {a : Ordinal.{0}} (s : List ℕ) (v : FatNode a)
    (hv : v ≠ FatNode.root) : parent (embed s v) = embed s (FatNode.parent v) := by
  simp only [embed,dif_neg hv,parent]

theorem rank_embed {a : Ordinal.{0}} (s : List ℕ) (v : FatNode a)
    (hv : v ≠ FatNode.root) : rank (embed s v) = (FatNode.rank v : WithTop Ordinal.{0}) := by
  simp [embed,hv,rank]

theorem color_embed {a : Ordinal.{0}} (C : List ℕ → ℕ) (s : List ℕ) (v : FatNode a)
    (hv : v ≠ FatNode.root) : color C (embed s v) = FatNode.color 0 v := by
  simp [embed,hv,color]

/-- Padding adds the same fat reservoirs below every original vertex
and retains them below every attached canonical vertex. -/
theorem hasFatReservoirs (a : Ordinal.{0}) (C : List ℕ → ℕ) :
    HasFatReservoirs (tree a C) a := by
  intro v r hra hr c
  cases v with
  | inl s =>
      let child := fun k : ℕ => FatNode.child (FatNode.root : FatNode a) r hra c k
      have hne (k : ℕ) : child k ≠ FatNode.root := FatNode.child_ne_root _ _ _ _ _
      have hinf : Set.Infinite (Set.range (fun k : ℕ => embed s (child k))) :=
        Set.infinite_range_of_injective ((embed_injective s).comp
          (FatNode.child_copy_injective (FatNode.root : FatNode a) r hra c))
      apply hinf.mono
      rintro w ⟨k,rfl⟩
      refine ⟨embed_ne_root s _ (hne k),?_,?_,?_⟩
      · exact (parent_embed s _ (hne k)).trans (by simp [child,FatNode.parent_child])
      · rw [show (tree a C).rank = rank from rfl,rank_embed s _ (hne k)]
        rw [FatNode.rank_child]
      · rw [show (tree a C).color = color C from rfl,color_embed C s _ (hne k)]
        exact FatNode.color_child (FatNode.root : FatNode a) r hra c k 0
  | inr v =>
      have hrv : r < FatNode.rank v.2.val := WithTop.coe_lt_coe.mp hr
      let child := fun k : ℕ => FatNode.child v.2.val r hrv c k
      have hne (k : ℕ) : child k ≠ FatNode.root := FatNode.child_ne_root _ _ _ _ _
      have hinf : Set.Infinite (Set.range (fun k : ℕ => embed v.1 (child k))) :=
        Set.infinite_range_of_injective ((embed_injective v.1).comp
          (FatNode.child_copy_injective _ r hrv c))
      apply hinf.mono
      rintro w ⟨k,rfl⟩
      refine ⟨embed_ne_root v.1 _ (hne k),?_,?_,?_⟩
      · exact (parent_embed v.1 _ (hne k)).trans
          (by simp [child,FatNode.parent_child,embed,v.2.property])
      · rw [show (tree a C).rank = rank from rfl,rank_embed v.1 _ (hne k)]
        rw [FatNode.rank_child]
      · rw [show (tree a C).color = color C from rfl,color_embed C v.1 _ (hne k)]
        exact FatNode.color_child _ r hrv c k 0

theorem countable (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) : Countable (PaddedNode a) := by
  letI := FatNode.countable a ha
  unfold PaddedNode
  infer_instance

end PaddedNode
end FSCofinality.Padding
