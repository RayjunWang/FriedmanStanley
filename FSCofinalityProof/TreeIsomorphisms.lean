import FSCofinalityProof.TreeSubtrees
import FSCofinalityProof.MultisetClosure

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RootedTrees

theorem isomorphic_refl (T : TreeSpace) : Isomorphic T T := ⟨Equiv.refl _,fun _ _ => Iff.rfl⟩

theorem isomorphic_symm {T U : TreeSpace} (h : Isomorphic T U) : Isomorphic U T := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,fun s t => ?_⟩
  simpa only [Equiv.apply_symm_apply] using (he (e.symm s) (e.symm t)).symm

theorem isomorphic_trans {T U V : TreeSpace} (h : Isomorphic T U) (k : Isomorphic U V) :
    Isomorphic T V := by
  obtain ⟨e,he⟩ := h
  obtain ⟨f,hf⟩ := k
  exact ⟨e.trans f,fun s t => (he s t).trans (hf (e s) (e t))⟩

theorem isomorphic_equivalence : Equivalence Isomorphic :=
  ⟨isomorphic_refl,fun h => isomorphic_symm h,fun h k => isomorphic_trans h k⟩

theorem noRoot_iff_eq_empty (T : TreeSpace) : T [] ≠ true ↔ T = emptyTree := by
  constructor
  · intro h
    apply Subtype.ext
    funext s
    apply Bool.eq_false_iff.mpr
    intro hs
    exact h (mem_of_append T [] s hs)
  · rintro rfl
    decide

theorem isomorphic_root_iff {T U : TreeSpace} (h : Isomorphic T U) :
    T [] = true ↔ U [] = true := by
  obtain ⟨e,he⟩ := h
  constructor
  · intro ht
    exact mem_of_append U [] (e ⟨[],ht⟩).val (e ⟨[],ht⟩).property
  · intro hu
    exact mem_of_append T [] (e.symm ⟨[],hu⟩).val (e.symm ⟨[],hu⟩).property

theorem map_prefix {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (s : Nodes T)
    (v : Node) (hv : T (s.val++v) = true) :
    ∃ w, (e ⟨s.val++v,hv⟩).val = (e s).val ++ w := by
  induction v using List.reverseRecOn with
  | nil => exact ⟨[],by simp only [List.append_nil]; rfl⟩
  | append_singleton v n ih =>
    have hp : T (s.val++v) = true := mem_parent T (s.val++v) n (by simpa using hv)
    obtain ⟨w,hw⟩ := ih hp
    obtain ⟨k,hk⟩ := (he ⟨s.val++(v++[n]),hv⟩ ⟨s.val++v,hp⟩).mp
      ⟨n,by simp only [List.append_assoc]⟩
    exact ⟨w++[k],by rw [hk,hw,List.append_assoc]⟩

theorem root_image {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t))
    (ht : T [] = true) (hu : U [] = true) : (e ⟨[],ht⟩).val = [] := by
  let s := e.symm ⟨[],hu⟩
  obtain ⟨w,hw⟩ := map_prefix e he ⟨[],ht⟩ s.val s.property
  have hs : (e ⟨s.val,s.property⟩).val = [] := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨[],hu⟩)
  change (e ⟨s.val,s.property⟩).val = (e ⟨[],ht⟩).val ++ w at hw
  rw [hs] at hw
  exact (List.append_eq_nil_iff.mp hw.symm).1

abbrev ChildLabels (T : TreeSpace) := {n : ℕ // T [n] = true}

theorem child_image {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) :
    ∃ m : ChildLabels U, (e ⟨[n.val],n.property⟩).val = [m.val] := by
  have ht : T [] = true := mem_parent T [] n.val n.property
  have hu : U [] = true := (isomorphic_root_iff ⟨e,he⟩).mp ht
  obtain ⟨m,hm⟩ := (he ⟨[n.val],n.property⟩ ⟨[],ht⟩).mp ⟨n.val,rfl⟩
  rw [root_image e he ht hu] at hm
  exact ⟨⟨m,by simpa only [hm,List.nil_append] using (e ⟨[n.val],n.property⟩).property⟩,
    by simpa only [List.nil_append] using hm⟩

def childLabelMap {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) : ChildLabels T → ChildLabels U :=
  fun n => (child_image e he n).choose

theorem childLabelMap_spec {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) :
    (e ⟨[n.val],n.property⟩).val = [(childLabelMap e he n).val] :=
  (child_image e he n).choose_spec

theorem childLabelMap_leftInverse {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) :
    Function.LeftInverse
      (childLabelMap e.symm (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm))
      (childLabelMap e he) := by
  intro n
  apply Subtype.ext
  have h := childLabelMap_spec e.symm
    (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm) (childLabelMap e he n)
  have hn : e ⟨[n.val],n.property⟩ =
      ⟨[(childLabelMap e he n).val],(childLabelMap e he n).property⟩ :=
    Subtype.ext (childLabelMap_spec e he n)
  rw [← hn,e.symm_apply_apply] at h
  exact List.singleton_injective h.symm

def childLabelEquiv {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) : ChildLabels T ≃ ChildLabels U where
  toFun := childLabelMap e he
  invFun := childLabelMap e.symm (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm)
  left_inv := childLabelMap_leftInverse e he
  right_inv := by
    intro n
    exact childLabelMap_leftInverse e.symm
      (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm) n

theorem map_prefix_iff {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (s t : Nodes T) :
    (∃ v, t.val = s.val ++ v) ↔ ∃ v, (e t).val = (e s).val ++ v := by
  constructor
  · rintro ⟨v,hv⟩
    have hmem : T (s.val++v) = true := hv ▸ t.property
    have ht : (⟨s.val++v,hmem⟩ : Nodes T) = t := Subtype.ext hv.symm
    simpa only [ht] using map_prefix e he s v hmem
  · rintro ⟨v,hv⟩
    have hmem : U ((e s).val++v) = true := hv ▸ (e t).property
    have ht : (⟨(e s).val++v,hmem⟩ : Nodes U) = e t := Subtype.ext hv.symm
    have h := map_prefix e.symm
      (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm) (e s) v hmem
    simpa only [ht,Equiv.symm_apply_apply] using h

abbrev Descendants (T : TreeSpace) (n : ℕ) :=
  {s : Nodes T // ∃ v, s.val = n::v}

theorem descendant_eq_cons_tail {T : TreeSpace} {n : ℕ} (s : Descendants T n) :
    s.val.val = n::s.val.val.tail := by
  obtain ⟨v,hv⟩ := s.property
  rw [hv]
  rfl

def childDescendantEquiv (T : TreeSpace) (n : ℕ) :
    Nodes (childTree T n) ≃ Descendants T n where
  toFun s := ⟨childNode T n s,s.val,rfl⟩
  invFun s := ⟨s.val.val.tail,by
    change T (n::s.val.val.tail) = true
    rw [← descendant_eq_cons_tail s]
    exact s.val.property⟩
  left_inv s := rfl
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    exact (descendant_eq_cons_tail s).symm

theorem map_descendants_iff {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) (s : Nodes T) :
    (∃ v, s.val = n.val::v) ↔
      ∃ v, (e s).val = (childLabelEquiv e he n).val::v := by
  have h := map_prefix_iff e he ⟨[n.val],n.property⟩ s
  rw [childLabelMap_spec e he n] at h
  simpa only [List.singleton_append] using h

def childSubtreeEquiv {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) :
    Nodes (childTree T n.val) ≃ Nodes (childTree U (childLabelEquiv e he n).val) :=
  ((childDescendantEquiv T n.val).trans
    (e.subtypeEquiv (map_descendants_iff e he n))).trans
      (childDescendantEquiv U (childLabelEquiv e he n).val).symm

theorem childSubtreeEquiv_lift {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T)
    (s : Nodes (childTree T n.val)) :
    childNode U (childLabelEquiv e he n).val (childSubtreeEquiv e he n s) =
      e (childNode T n.val s) := by
  apply Subtype.ext
  exact (descendant_eq_cons_tail
    ((e.subtypeEquiv (map_descendants_iff e he n)) (childDescendantEquiv T n.val s))).symm

theorem child_isomorphic {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) :
    Isomorphic (childTree T n.val) (childTree U (childLabelEquiv e he n).val) := by
  refine ⟨childSubtreeEquiv e he n,fun s t => ?_⟩
  rw [childNode_child n.val s t,he,
    childNode_child (childLabelEquiv e he n).val,
    childSubtreeEquiv_lift,childSubtreeEquiv_lift]

end FSCofinality.RootedTrees
