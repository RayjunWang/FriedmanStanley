import FSCofinalityProof.PaddingAncestors

set_option autoImplicit false
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq α
open Set

namespace FSCofinality.Padding

/-- A finite downward path with explicit target ranks. -/
def PathTemplate (T : RankedTree) (a d : Ordinal.{0}) :
    T.Vertex → WithTop Ordinal.{0} → List (T.Vertex × Ordinal.{0}) → Prop
  | _, _, [] => True
  | anchor, anchorRank, (v,r) :: rest =>
      T.parent v = anchor ∧ r < a ∧ (r : WithTop Ordinal.{0}) < anchorRank ∧
      RankAgrees d (T.rank v) (r : WithTop Ordinal.{0}) ∧
      PathTemplate T a d v (r : WithTop Ordinal.{0}) rest

theorem GoodPartial.source_extend {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) (y : U.Vertex)
    (hx : x ∉ f.source) (hy : y ∉ f.target)
    (hp : (T.parent x,U.parent y) ∈ f.pairs)
    (hc : T.color x = U.color y) (hr : RankAgrees b (T.rank x) (U.rank y)) :
    (f.extend x y hx hy hp hc hr).source = insert x f.source := by
  classical
  exact Finset.image_insert (Prod.fst : T.Vertex × U.Vertex → T.Vertex) (x,y) f.pairs

/-- A whole fresh ancestor path can be realized, preserving all old
pairs, once its decreasing rank template is specified. Infinitely many
copies provide fresh vertices at each step. -/
theorem extend_path
    {T U : RankedTree} {a d : Ordinal.{0}}
    (hU : HasFatReservoirs U a) (f : GoodPartial T U d)
    (anchor : T.Vertex) (targetAnchor : U.Vertex)
    (hanchor : (anchor,targetAnchor) ∈ f.pairs)
    (path : List (T.Vertex × Ordinal.{0}))
    (ht : PathTemplate T a d anchor (U.rank targetAnchor) path)
    (hfresh : ∀ p ∈ path, p.1 ∉ f.source)
    (hnodup : (path.map Prod.fst).Nodup) :
    ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧
      ∀ p ∈ path, ∃ y : U.Vertex, (p.1,y) ∈ g.pairs ∧ U.rank y = (p.2 : WithTop Ordinal.{0}) := by
  classical
  induction path generalizing f anchor targetAnchor with
  | nil => exact ⟨f,(fun _ h => h),fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons p rest IH =>
      obtain ⟨v,r⟩ := p
      obtain ⟨hp,hra,hra',hr,htail⟩ := ht
      obtain ⟨w,hwfresh,_,hwparent,hwrank,hwcolor⟩ :=
        exists_fresh_child hU targetAnchor r hra hra' (T.color v) f.target
      have hvfresh : v ∉ f.source := hfresh (v,r) (List.mem_cons_self)
      have hparent : (T.parent v,U.parent w) ∈ f.pairs := by
        simpa only [hp,hwparent] using hanchor
      have hrank : RankAgrees d (T.rank v) (U.rank w) := by rwa [hwrank]
      let f' := f.extend v w hvfresh hwfresh hparent hwcolor.symm hrank
      have hfsub : f.pairs ⊆ f'.pairs := Finset.subset_insert (v,w) f.pairs
      have hnew : (v,w) ∈ f'.pairs := Finset.mem_insert_self _ _
      have htail' : PathTemplate T a d v (U.rank w) rest := by rwa [hwrank]
      have hfresh' : ∀ p ∈ rest, p.1 ∉ f'.source := by
        intro p hpRest hpSource
        rw [GoodPartial.source_extend] at hpSource
        rcases Finset.mem_insert.mp hpSource with hpEq | hpOld
        · have hvnot : v ∉ rest.map Prod.fst := (List.nodup_cons.mp hnodup).1
          exact hvnot (hpEq ▸ List.mem_map.mpr ⟨p,hpRest,rfl⟩)
        · exact hfresh p (List.mem_cons_of_mem _ hpRest) hpOld
      have hnrest : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hnodup).2
      obtain ⟨g,hg,hrg⟩ := IH f' v w hnew htail' hfresh' hnrest
      refine ⟨g,hfsub.trans hg,fun p hpMem => ?_⟩
      rcases List.mem_cons.mp hpMem with rfl | hpMem
      · exact ⟨w,hg hnew,hwrank⟩
      · exact hrg p hpMem

end FSCofinality.Padding
