import FSCofinalityProof.TreeRanks
import FSCofinalityProof.HierarchySums

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RootedTrees

def childTree (T : TreeSpace) (n : ℕ) : TreeSpace :=
  ⟨fun s => T (n::s),fun s k h => T.property (n::s) k h⟩

theorem continuous_childTree (n : ℕ) : Continuous (fun T => childTree T n) :=
  (continuous_pi (fun s => continuous_eval (n::s))).subtype_mk _

def childNode (T : TreeSpace) (n : ℕ) (s : Nodes (childTree T n)) : Nodes T :=
  ⟨n::s.val,s.property⟩

theorem childNode_child {T : TreeSpace} (n : ℕ) (s t : Nodes (childTree T n)) :
    Child s t ↔ Child (childNode T n s) (childNode T n t) := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,congrArg (List.cons n) hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,List.cons.inj hk |>.2⟩

theorem BoundedTree.mono {T : TreeSpace} {a b : Ordinal.{0}}
    (h : BoundedTree T a) (hab : a ≤ b) : BoundedTree T b := by
  obtain ⟨rho,hrho,hdec⟩ := h
  exact ⟨rho,fun s => (hrho s).trans_le hab,hdec⟩

theorem rank_le_prefix {T : TreeSpace} (rho : Nodes T → Ordinal.{0})
    (hdec : ∀ s t, Child s t → rho s < rho t) (s t : Node)
    (hst : T (s++t) = true) :
    rho ⟨s++t,hst⟩ ≤ rho ⟨s,mem_of_append T s t hst⟩ := by
  induction t using List.reverseRecOn with
  | nil => simp only [List.append_nil]; exact le_refl _
  | append_singleton t n ih =>
    have hp : T (s++t) = true := mem_parent T (s++t) n (by simpa using hst)
    have hd : rho ⟨s++(t++[n]),hst⟩ < rho ⟨s++t,hp⟩ :=
      hdec _ _ ⟨n,by simp only [List.append_assoc]⟩
    exact hd.le.trans (ih hp)

theorem BoundedTree.child_of_succ {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T (a+1)) (n : ℕ) : BoundedTree (childTree T n) a := by
  obtain ⟨rho,hrho,hdec⟩ := h
  refine ⟨fun s => rho (childNode T n s),?_,?_⟩
  · intro s
    have hn : T [n] = true := mem_of_append T [n] s.val s.property
    have hroot : T [] = true := mem_parent T [] n hn
    have hd : rho ⟨[n],hn⟩ < rho ⟨[],hroot⟩ := hdec _ _ ⟨n,rfl⟩
    have hle := rank_le_prefix rho hdec [n] s.val s.property
    exact hle.trans_lt (hd.trans_le (Order.lt_succ_iff.mp (hrho ⟨[],hroot⟩)))
  · intro s t hst
    exact hdec _ _ ((childNode_child n s t).mp hst)

theorem BoundedTree.exists_smaller_of_limit {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T a) (ha : IsSuccLimit a) :
    ∃ b < a, BoundedTree T b := by
  by_cases hroot : T [] = true
  · obtain ⟨rho,hrho,hdec⟩ := h
    refine ⟨rho ⟨[],hroot⟩+1,ha.succ_lt (hrho _),rho,?_,hdec⟩
    intro s
    have hle := rank_le_prefix rho hdec [] s.val s.property
    exact Order.lt_succ_iff.mpr hle
  · have he : T = emptyTree := by
      apply Subtype.ext
      funext s
      have hn : T s ≠ true := fun hs => hroot (mem_of_append T [] s hs)
      exact Bool.eq_false_iff.mpr hn
    exact ⟨0,ha.pos,he ▸ bounded_emptyTree 0⟩

end FSCofinality.RootedTrees
