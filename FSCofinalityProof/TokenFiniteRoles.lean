import FSCofinalityProof.TokenFiniteCorrespondence
import FSCofinalityProof.CosetConstructionRawProperties
import FSCofinalityProof.TokenBottomExtension

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem rowSort_injective : Function.Injective (rowSort eta) := by
  intro e f hef
  rcases e with e | e <;> rcases f with f | f
  · apply congrArg Sum.inl
    apply Subtype.ext
    have hr := congrArg (fun s : TokenSort eta => match s with
      | .inl a => Frame.rank a
      | .inr _ => 0) hef
    simp only [rowSort,mainSort,Frame.rank_ofOrdinal] at hr
    have heq : Frame.rank e.val = Frame.rank f.val :=
      (Ordinal.add_right_cancel 1).mp (by simpa only [Nat.cast_one] using hr)
    have hinj : Function.Injective (Frame.rank (η := eta)) := by
      intro a b hab
      exact Ordinal.ToType.mk.symm.injective (Subtype.ext hab)
    exact hinj heq
  · cases hef
  · cases hef
  · exact congrArg Sum.inr (Sum.inr.inj hef)

theorem rowSort_ne_colSort (e : OrdinaryRole eta) : rowSort eta e ≠ colSort eta e := by
  rcases e with e | e
  · intro h
    have hr := congrArg (fun s : TokenSort eta => match s with
      | .inl a => Frame.rank a
      | .inr _ => 0) h
    simp only [rowSort,colSort,mainSort,Frame.rank_ofOrdinal] at hr
    exact (ne_of_gt (lt_add_one (Frame.rank e.val))) hr
  · intro h
    cases h

theorem rowSort_ne_limit (e : OrdinaryRole eta) (lam : LimitIndex eta) :
    rowSort eta e ≠ .inl lam.val := by
  rcases e with e | e
  · intro h
    have hr := congrArg (fun s : TokenSort eta => match s with
      | .inl a => Frame.rank a
      | .inr _ => 0) h
    simp only [rowSort,mainSort,Frame.rank_ofOrdinal] at hr
    have hlt : Frame.rank e.val < Frame.rank lam.val := by rw [← hr]; exact lt_add_one _
    have hs := lam.property.succ_lt hlt
    rw [Order.succ_eq_add_one,hr] at hs
    exact (lt_irrefl _) hs
  · intro h
    cases h

def rowRole (s : TokenSort eta) : Option (OrdinaryRole eta) :=
  if h : ∃ e, rowSort eta e = s then some h.choose else none

@[simp] theorem rowRole_rowSort (e : OrdinaryRole eta) : rowRole eta (rowSort eta e) = some e := by
  rw [rowRole,dif_pos ⟨e,rfl⟩]
  apply congrArg some
  exact rowSort_injective eta (Exists.choose_spec (show ∃ f, rowSort eta f = rowSort eta e from ⟨e,rfl⟩))

def finiteOrdinaryRoles (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta) :
    Finset (OrdinaryRole eta) :=
  ((s :: R.filterMap (fun p => sortOf eta heta p.2)).filterMap (rowRole eta)).toFinset

theorem mem_finiteOrdinaryRoles_row (R : List (Vertex eta heta x × Vertex eta heta y))
    (s : TokenSort eta) (e : OrdinaryRole eta) (he : rowSort eta e = s) :
    e ∈ finiteOrdinaryRoles eta heta R s := by
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  exact ⟨s,List.mem_cons_self,(he ▸ rowRole_rowSort eta e)⟩

theorem mem_finiteOrdinaryRoles_oldRow (R : List (Vertex eta heta x × Vertex eta heta y))
    (s : TokenSort eta) (e : OrdinaryRole eta) (p) (hp : p ∈ R)
    (hs : sortOf eta heta p.2 = some (rowSort eta e)) :
    e ∈ finiteOrdinaryRoles eta heta R s := by
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  refine ⟨rowSort eta e,List.mem_cons_of_mem _ ?_,rowRole_rowSort eta e⟩
  exact List.mem_filterMap.mpr ⟨p,hp,hs⟩

def rowRequirement (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (e : OrdinaryRole eta)
    (hs : rowSort eta e=s) : FiniteRole (raw eta heta y s) := by
  subst s
  let I := SortEntries eta heta R (colSort eta e)
  let idx := (Fintype.equivFin I).symm
  exact {
    Opposite := raw eta heta y (colSort eta e)
    count := Fintype.card I
    context := fun j => (targetEntry eta heta R _ (idx j)).1
    label := fun j => (targetEntry eta heta R _ (idx j)).2
    bit := fun j => ordinary eta heta x e v (sourceEntry eta heta R hR _ (idx j))
    raw := ordinaryMatrix eta heta y e
    separated := ordinaryMatrix_column_separating eta heta y e
    direction := true
    role := roleNumber eta heta (.inl e)
    consistent := by
      intro i j hc hl
      have he : targetEntry eta heta R _ (idx i) = targetEntry eta heta R _ (idx j) := Prod.ext hc hl
      have hsrc := (sourceEntry_eq_iff_targetEntry_eq eta heta R hR _ (idx i) (idx j)).mpr he
      exact congrArg (ordinary eta heta x e v) hsrc }

def colRequirement (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (e : OrdinaryRole eta)
    (hs : colSort eta e=s) : FiniteRole (raw eta heta y s) := by
  subst s
  let I := SortEntries eta heta R (rowSort eta e)
  let idx := (Fintype.equivFin I).symm
  exact {
    Opposite := raw eta heta y (rowSort eta e)
    count := Fintype.card I
    context := fun j => (targetEntry eta heta R _ (idx j)).1
    label := fun j => (targetEntry eta heta R _ (idx j)).2
    bit := fun j => ordinary eta heta x e (sourceEntry eta heta R hR _ (idx j)) v
    raw := fun u z => ordinaryMatrix eta heta y e z u
    separated := ordinaryMatrix_row_injective eta heta y e
    direction := false
    role := roleNumber eta heta (.inl e)
    consistent := by
      intro i j hc hl
      have he : targetEntry eta heta R _ (idx i) = targetEntry eta heta R _ (idx j) := Prod.ext hc hl
      have hsrc := (sourceEntry_eq_iff_targetEntry_eq eta heta R hR _ (idx i) (idx j)).mpr he
      exact congrArg (fun w => ordinary eta heta x e w v) hsrc }

def ordinaryRequirement (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (e : OrdinaryRole eta) :
    FiniteRole (raw eta heta y s) :=
  if h : rowSort eta e=s then rowRequirement eta heta R hR s v e h
  else if h : colSort eta e=s then colRequirement eta heta R hR s v e h
  else {
    Opposite := Unit
    count := 0
    context := Fin.elim0
    label := Fin.elim0
    bit := Fin.elim0
    raw := fun _ _ => false
    separated := fun a b _ => Subsingleton.elim a b
    direction := true
    role := roleNumber eta heta (.inl e)
    consistent := fun i => Fin.elim0 i }

theorem ordinaryRequirement_role (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (e : OrdinaryRole eta) :
    (ordinaryRequirement eta heta R hR s v e).role = roleNumber eta heta (.inl e) := by
  unfold ordinaryRequirement
  split_ifs with hr hc
  · cases hr
    rfl
  · cases hc
    rfl
  · rfl

def ordinaryRequirements (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s))
    (e : finiteOrdinaryRoles eta heta R s) : FiniteRole (raw eta heta y s) :=
  ordinaryRequirement eta heta R hR s v e.val

theorem ordinaryRequirements_roles_injective (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) :
    Function.Injective (fun e => (ordinaryRequirements eta heta R hR s v e).role) := by
  intro e f hef
  apply Subtype.ext
  simp only [ordinaryRequirements,ordinaryRequirement_role] at hef
  exact Sum.inl.inj ((roleNumber eta heta).injective hef)

def OrdinaryRequestsRealized (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s)) : Prop :=
  ∀ e j, genericTable (((ordinaryRequirements eta heta R hR s v e).request w.1 j).index w.2) =
    (ordinaryRequirements eta heta R hR s v e).bit j

theorem ordinaryRequirements_row_realizes
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hw : OrdinaryRequestsRealized eta heta R hR s v w)
    (e : OrdinaryRole eta) (hs : rowSort eta e=s)
    (i : SortEntries eta heta R (colSort eta e)) :
    ordinary eta heta x e (hs.symm ▸ v) (sourceEntry eta heta R hR _ i) =
      ordinary eta heta y e (hs.symm ▸ w) (targetEntry eta heta R _ i) := by
  subst s
  have he := mem_finiteOrdinaryRoles_row eta heta R (rowSort eta e) e rfl
  have h := hw ⟨e,he⟩
  change ∀ j, genericTable (((ordinaryRequirement eta heta R hR (rowSort eta e) v e).request w.1 j).index w.2) =
    (ordinaryRequirement eta heta R hR (rowSort eta e) v e).bit j at h
  rw [ordinaryRequirement,dif_pos rfl] at h
  have hh := h ((Fintype.equivFin (SortEntries eta heta R (colSort eta e))) i)
  simpa only [rowRequirement,FiniteRole.request,orientMatrix,if_true,Request.index,
    Equiv.symm_apply_apply,ordinary,ordinaryEdge] using hh.symm

theorem ordinaryRequirements_col_realizes
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hw : OrdinaryRequestsRealized eta heta R hR s v w)
    (e : OrdinaryRole eta) (hs : colSort eta e=s)
    (i : SortEntries eta heta R (rowSort eta e)) :
    ordinary eta heta x e (sourceEntry eta heta R hR _ i) (hs.symm ▸ v) =
      ordinary eta heta y e (targetEntry eta heta R _ i) (hs.symm ▸ w) := by
  subst s
  have he := mem_finiteOrdinaryRoles_oldRow eta heta R (colSort eta e) e
    (R.get i.val) (List.get_mem _ i.val) i.property
  have h := hw ⟨e,he⟩
  change ∀ j, genericTable (((ordinaryRequirement eta heta R hR (colSort eta e) v e).request w.1 j).index w.2) =
    (ordinaryRequirement eta heta R hR (colSort eta e) v e).bit j at h
  rw [ordinaryRequirement,dif_neg (rowSort_ne_colSort eta e),dif_pos rfl] at h
  have hh := h ((Fintype.equivFin (SortEntries eta heta R (rowSort eta e))) i)
  simpa only [colRequirement,FiniteRole.request,orientMatrix,Bool.false_eq_true,if_false,
    Request.index,Equiv.symm_apply_apply,transpose_contextMatrix,ordinary,ordinaryEdge] using hh.symm

theorem ordinaryRequests_forward (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hw : OrdinaryRequestsRealized eta heta R hR s v w) (e : OrdinaryRole eta)
    (p : Vertex eta heta x × Vertex eta heta y) (hp : p ∈ R) :
    edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta x e) (.inr ⟨s,v⟩) p.1 =
      edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta y e) (.inr ⟨s,w⟩) p.2 := by
  by_cases hs : rowSort eta e=s
  · subst s
    by_cases ht : sortOf eta heta p.2 = some (colSort eta e)
    · let u := (tokenFiberEquiv eta heta y (colSort eta e)).symm ⟨p.2,ht⟩
      have hu : (.inr ⟨colSort eta e,u⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (colSort eta e)).apply_symm_apply _)
      obtain ⟨i,hi,_⟩ := targetEntry_covers eta heta R (colSort eta e) p hp u hu.symm
      have h := ordinaryRequirements_row_realizes eta heta R hR _ v w hw e rfl i
      have he : edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta x e)
          (.inr ⟨rowSort eta e,v⟩) (R.get i.val).1 =
          edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta y e)
            (.inr ⟨rowSort eta e,w⟩) (R.get i.val).2 := by
        rw [← sourceEntry_vertex eta heta R hR (colSort eta e) i,← targetEntry_vertex eta heta R (colSort eta e) i]
        simpa only [edgeAt_inr] using h
      simpa only [hi] using he
    · have hyt := (tokenAt_none_iff_sort eta heta (colSort eta e) p.2).mpr ht
      have hxt := (tokenAt_none_iff_sort eta heta (colSort eta e) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      unfold edgeAt
      rw [tokenAt_inr,tokenAt_inr,hxt,hyt]
      rfl
  · have hxt : tokenAt eta heta (rowSort eta e) (.inr ⟨s,v⟩) = none := by simp [tokenAt,Ne.symm hs]
    have hyt : tokenAt eta heta (rowSort eta e) (.inr ⟨s,w⟩) = none := by simp [tokenAt,Ne.symm hs]
    simp only [edgeAt,hxt,hyt,Option.elim_none]

theorem ordinaryRequests_backward (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hw : OrdinaryRequestsRealized eta heta R hR s v w) (e : OrdinaryRole eta)
    (p : Vertex eta heta x × Vertex eta heta y) (hp : p ∈ R) :
    edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta x e) p.1 (.inr ⟨s,v⟩) =
      edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta y e) p.2 (.inr ⟨s,w⟩) := by
  by_cases hs : colSort eta e=s
  · subst s
    by_cases ht : sortOf eta heta p.2 = some (rowSort eta e)
    · let u := (tokenFiberEquiv eta heta y (rowSort eta e)).symm ⟨p.2,ht⟩
      have hu : (.inr ⟨rowSort eta e,u⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (rowSort eta e)).apply_symm_apply _)
      obtain ⟨i,hi,_⟩ := targetEntry_covers eta heta R (rowSort eta e) p hp u hu.symm
      have h := ordinaryRequirements_col_realizes eta heta R hR _ v w hw e rfl i
      have he : edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta x e)
          (R.get i.val).1 (.inr ⟨colSort eta e,v⟩) =
          edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta y e)
            (R.get i.val).2 (.inr ⟨colSort eta e,w⟩) := by
        rw [← sourceEntry_vertex eta heta R hR (rowSort eta e) i,← targetEntry_vertex eta heta R (rowSort eta e) i]
        simpa only [edgeAt_inr] using h
      simpa only [hi] using he
    · have hyt := (tokenAt_none_iff_sort eta heta (rowSort eta e) p.2).mpr ht
      have hxt := (tokenAt_none_iff_sort eta heta (rowSort eta e) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      simp only [edgeAt,hxt,hyt,Option.elim_none]
  · have hxt : tokenAt eta heta (colSort eta e) (.inr ⟨s,v⟩) = none := by simp [tokenAt,Ne.symm hs]
    have hyt : tokenAt eta heta (colSort eta e) (.inr ⟨s,w⟩) = none := by simp [tokenAt,Ne.symm hs]
    unfold edgeAt
    rw [hxt,hyt]
    cases tokenAt eta heta (rowSort eta e) p.1 <;> cases tokenAt eta heta (rowSort eta e) p.2 <;> rfl

end FSCofinality.CosetConstruction.TokenModel
