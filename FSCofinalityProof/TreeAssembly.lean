import FSCofinalityProof.TreeIsomorphisms

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RootedTrees

abbrev TreeParts (T : TreeSpace) := Unit ⊕ Σ n : ChildLabels T, Nodes (childTree T n.val)

def joinParts (T : TreeSpace) (hroot : T [] = true) : TreeParts T → Nodes T
  | Sum.inl _ => ⟨[],hroot⟩
  | Sum.inr ⟨n,s⟩ => childNode T n.val s

theorem joinParts_injective (T : TreeSpace) (hroot : T [] = true) :
    Function.Injective (joinParts T hroot) := by
  rintro (u | ⟨n,s⟩) (v | ⟨m,t⟩) h
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · have hv := congrArg Subtype.val h
    simp [joinParts,childNode] at hv
  · have hv := congrArg Subtype.val h
    simp [joinParts,childNode] at hv
  · have hv := List.cons.inj (congrArg Subtype.val h)
    have hnm : n = m := Subtype.ext hv.1
    subst m
    have hst : s = t := Subtype.ext hv.2
    subst t
    rfl

theorem joinParts_surjective (T : TreeSpace) (hroot : T [] = true) :
    Function.Surjective (joinParts T hroot) := by
  rintro ⟨s,hs⟩
  cases s with
  | nil => exact ⟨Sum.inl (),rfl⟩
  | cons n s =>
    have hn : T [n] = true := mem_of_append T [n] s hs
    exact ⟨Sum.inr ⟨⟨n,hn⟩,⟨s,hs⟩⟩,rfl⟩

def partsEquiv (T : TreeSpace) (hroot : T [] = true) : TreeParts T ≃ Nodes T :=
  Equiv.ofBijective (joinParts T hroot) ⟨joinParts_injective T hroot,joinParts_surjective T hroot⟩

def PartsChild (T : TreeSpace) : TreeParts T → TreeParts T → Prop
  | Sum.inl _, _ => False
  | Sum.inr ⟨_,s⟩, Sum.inl _ => s.val = []
  | Sum.inr ⟨n,s⟩, Sum.inr ⟨m,t⟩ => ∃ h : n=m, Child (h ▸ s) t

theorem joinParts_child (T : TreeSpace) (hroot : T [] = true) (s t : TreeParts T) :
    PartsChild T s t ↔ Child (joinParts T hroot s) (joinParts T hroot t) := by
  cases s with
  | inl u =>
    cases t with
    | inl v => simp [PartsChild,Child,joinParts]
    | inr v =>
      rcases v with ⟨m,t⟩
      simp [PartsChild,Child,joinParts,childNode]
  | inr u =>
    rcases u with ⟨n,s⟩
    cases t with
    | inl v =>
      simp only [PartsChild,Child,joinParts,childNode,List.nil_append]
      constructor
      · intro hs
        exact ⟨n.val,by simp [hs]⟩
      · rintro ⟨k,hk⟩
        exact (List.cons.inj hk).2
    | inr v =>
      rcases v with ⟨m,t⟩
      constructor
      · rintro ⟨h,hchild⟩
        subst m
        exact (childNode_child n.val s t).mp hchild
      · rintro ⟨k,hk⟩
        have hnm : n = m := Subtype.ext (List.cons.inj hk).1
        subst m
        exact ⟨rfl,k,(List.cons.inj hk).2⟩

def assembleParts {T U : TreeSpace} (e : ChildLabels T ≃ ChildLabels U)
    (f : ∀ n, Nodes (childTree T n.val) ≃ Nodes (childTree U (e n).val)) :
    TreeParts T ≃ TreeParts U :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sigmaCongr e f)

theorem assembleParts_child {T U : TreeSpace} (e : ChildLabels T ≃ ChildLabels U)
    (f : ∀ n, Nodes (childTree T n.val) ≃ Nodes (childTree U (e n).val))
    (hf : ∀ n s t, Child s t ↔ Child (f n s) (f n t))
    (s t : TreeParts T) :
    PartsChild T s t ↔ PartsChild U (assembleParts e f s) (assembleParts e f t) := by
  cases s with
  | inl u => cases t <;> exact Iff.rfl
  | inr u =>
    rcases u with ⟨n,s⟩
    cases t with
    | inl v =>
      change s.val = [] ↔ (f n s).val = []
      have hs := isomorphic_root_iff (show Isomorphic (childTree T n.val)
        (childTree U (e n).val) from ⟨f n,hf n⟩)
      constructor
      · intro hsroot
        have htroot : childTree T n.val [] = true := n.property
        have huroot := hs.mp htroot
        have hsn : s = ⟨[],htroot⟩ := Subtype.ext hsroot
        rw [hsn]
        exact root_image (f n) (hf n) htroot huroot
      · intro hsroot
        have huroot : childTree U (e n).val [] = true := (e n).property
        have htroot := hs.mpr huroot
        have hsn : f n s = ⟨[],huroot⟩ := Subtype.ext hsroot
        have h := root_image (f n).symm
          (fun s t => by simpa using (hf n ((f n).symm s) ((f n).symm t)).symm)
          huroot htroot
        rw [← hsn,Equiv.symm_apply_apply] at h
        exact h
    | inr v =>
      rcases v with ⟨m,t⟩
      change (∃ h : n=m, Child (h ▸ s) t) ↔
        ∃ h : e n = e m, Child (h ▸ f n s) (f m t)
      constructor
      · rintro ⟨h,hst⟩
        subst m
        exact ⟨rfl,(hf n s t).mp hst⟩
      · rintro ⟨h,hst⟩
        have hnm := e.injective h
        subst m
        exact ⟨rfl,(hf n s t).mpr hst⟩

theorem isomorphic_of_child_equiv {T U : TreeSpace}
    (ht : T [] = true) (hu : U [] = true) (e : ChildLabels T ≃ ChildLabels U)
    (hchildren : ∀ n, Isomorphic (childTree T n.val) (childTree U (e n).val)) :
    Isomorphic T U := by
  choose f hf using hchildren
  let q := ((partsEquiv T ht).symm.trans (assembleParts e f)).trans (partsEquiv U hu)
  refine ⟨q,fun s t => ?_⟩
  have hs : joinParts T ht ((partsEquiv T ht).symm s) = s := (partsEquiv T ht).apply_symm_apply s
  have ht' : joinParts T ht ((partsEquiv T ht).symm t) = t := (partsEquiv T ht).apply_symm_apply t
  have h1 := joinParts_child T ht ((partsEquiv T ht).symm s) ((partsEquiv T ht).symm t)
  rw [hs,ht'] at h1
  exact h1.symm.trans ((assembleParts_child e f hf _ _).trans (joinParts_child U hu _ _))

end FSCofinality.RootedTrees
