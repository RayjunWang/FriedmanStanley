import FSCofinalityProof.TokenFiniteRoles

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

def oldLabelBound (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta) : ℕ :=
  Finset.univ.sup (fun i : Fin R.length =>
    (tokenAt eta heta s (R.get i).2).elim 0 (fun v => v.2))

theorem token_fresh_of_labelBound (R : List (Vertex eta heta x × Vertex eta heta y))
    (s : TokenSort eta) (w : Token (raw eta heta y s)) (hw : oldLabelBound eta heta R s < w.2) :
    ∀ p ∈ R, (.inr ⟨s,w⟩ : Vertex eta heta y) ≠ p.2 := by
  intro p hp heq
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
  have hi : (tokenAt eta heta s (R.get i).2).elim 0 (fun v => v.2) ≤ oldLabelBound eta heta R s :=
    Finset.le_sup (f := fun i : Fin R.length =>
      (tokenAt eta heta s (R.get i).2).elim 0 (fun v => v.2)) (Finset.mem_univ i)
  rw [← heq,tokenAt_inr] at hi
  exact not_lt_of_ge hi hw

def localRelationAt (z : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (u v : Vertex eta heta z) : Bool :=
  edgeAt eta heta (.inl lam.val) (.inl lam.val)
    (fun r t => decide (Tokens.R (limitProfile eta heta z lam) n r t)) u v

def bottomEdge (z : (fsTower eta).Carrier) (u v : Vertex eta heta z) : Bool :=
  (tokenAt eta heta (zeroSort eta) u).elim false (fun r =>
    (coordinateAt eta heta v).elim false (bottom eta heta z r))

theorem localRelationAt_symm (z : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (u v : Vertex eta heta z) : localRelationAt eta heta z lam n u v =
      localRelationAt eta heta z lam n v u := by
  unfold localRelationAt edgeAt
  cases tokenAt eta heta (.inl lam.val) u <;> cases tokenAt eta heta (.inl lam.val) v
    <;> simp only [Option.elim_none,Option.elim_some]
  apply decide_eq_decide.mpr
  exact ⟨(Tokens.R_equivalence _ _).symm,(Tokens.R_equivalence _ _).symm⟩

theorem bottomEdge_token_right (z : (fsTower eta).Carrier) (u : Vertex eta heta z)
    (s : TokenSort eta) (v : Token (raw eta heta z s)) :
    bottomEdge eta heta z u (.inr ⟨s,v⟩) = false := by
  unfold bottomEdge
  cases tokenAt eta heta (zeroSort eta) u <;> rfl

theorem edgeAt_self_of_ne (z : (fsTower eta).Carrier) (s t : TokenSort eta) (hst : s ≠ t)
    (f : Token (raw eta heta z s) → Token (raw eta heta z t) → Bool)
    (u : Vertex eta heta z) : edgeAt eta heta s t f u u = false := by
  unfold edgeAt
  cases hs : tokenAt eta heta s u with
  | none => rfl
  | some r =>
    have hu := (tokenAt_eq_some_iff eta heta s u r).mp hs
    have ht : tokenAt eta heta t u = none :=
      (tokenAt_none_iff_sort eta heta t u).mpr (by
        rw [hu]
        exact fun h => hst (Option.some.inj h))
    simp only [Option.elim_some,ht,Option.elim_none]

theorem token_diagonal_agrees (s : TokenSort eta) (v : Token (raw eta heta x s))
    (w : Token (raw eta heta y s)) (r : (language eta heta).Symbol) :
    diagram eta heta (bottom eta heta) x r (fun _ => .inr ⟨s,v⟩) =
      diagram eta heta (bottom eta heta) y r (fun _ => .inr ⟨s,w⟩) := by
  rcases r with r | (e | (⟨lam,n⟩ | (⟨lam,n⟩ | r)))
  · rfl
  · exact (edgeAt_self_of_ne eta heta x _ _ (rowSort_ne_colSort eta e) _ _).trans
      (edgeAt_self_of_ne eta heta y _ _ (rowSort_ne_colSort eta e) _ _).symm
  · exact (edgeAt_self_of_ne eta heta x _ _ (by intro h; cases h) _ _).trans
      (edgeAt_self_of_ne eta heta y _ _ (by intro h; cases h) _ _).symm
  · by_cases hs : s = .inl lam.val
    · subst s
      change edgeAt eta heta _ _ _ (.inr ⟨.inl lam.val,v⟩) (.inr ⟨.inl lam.val,v⟩) =
        edgeAt eta heta _ _ _ (.inr ⟨.inl lam.val,w⟩) (.inr ⟨.inl lam.val,w⟩)
      rw [edgeAt_inr,edgeAt_inr]
      simp [Tokens.R]
    · have hx : tokenAt eta heta (.inl lam.val) (.inr ⟨s,v⟩ : Vertex eta heta x) = none :=
        (tokenAt_none_iff_sort eta heta _ _).mpr (fun h => hs (Option.some.inj h))
      have hy : tokenAt eta heta (.inl lam.val) (.inr ⟨s,w⟩ : Vertex eta heta y) = none :=
        (tokenAt_none_iff_sort eta heta _ _).mpr (fun h => hs (Option.some.inj h))
      change edgeAt eta heta _ _ _ _ _ = edgeAt eta heta _ _ _ _ _
      simp only [edgeAt,hx,hy,Option.elim_none]
  · exact (bottomEdge_token_right eta heta x _ s v).trans
      (bottomEdge_token_right eta heta y _ s w).symm

theorem token_insert_compatible
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hfresh : ∀ p ∈ R, (.inr ⟨s,v⟩ : Vertex eta heta x) ≠ p.1)
    (hfresh' : ∀ p ∈ R, (.inr ⟨s,w⟩ : Vertex eta heta y) ≠ p.2)
    (hOrdF : ∀ e p, p ∈ R → edgeAt eta heta _ _ (ordinary eta heta x e) (.inr ⟨s,v⟩) p.1 =
      edgeAt eta heta _ _ (ordinary eta heta y e) (.inr ⟨s,w⟩) p.2)
    (hOrdB : ∀ e p, p ∈ R → edgeAt eta heta _ _ (ordinary eta heta x e) p.1 (.inr ⟨s,v⟩) =
      edgeAt eta heta _ _ (ordinary eta heta y e) p.2 (.inr ⟨s,w⟩))
    (hBrF : ∀ lam n p, p ∈ R → edgeAt eta heta _ _ (branch eta heta x lam n) (.inr ⟨s,v⟩) p.1 =
      edgeAt eta heta _ _ (branch eta heta y lam n) (.inr ⟨s,w⟩) p.2)
    (hBrB : ∀ lam n p, p ∈ R → edgeAt eta heta _ _ (branch eta heta x lam n) p.1 (.inr ⟨s,v⟩) =
      edgeAt eta heta _ _ (branch eta heta y lam n) p.2 (.inr ⟨s,w⟩))
    (hRF : ∀ lam n p, p ∈ R → localRelationAt eta heta x lam n (.inr ⟨s,v⟩) p.1 =
      localRelationAt eta heta y lam n (.inr ⟨s,w⟩) p.2)
    (hBottomF : ∀ p, p ∈ R → bottomEdge eta heta x (.inr ⟨s,v⟩) p.1 =
      bottomEdge eta heta y (.inr ⟨s,w⟩) p.2) :
    LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨s,v⟩,.inr ⟨s,w⟩)]} := by
  have hcompat : CompatibleOn (L := language eta heta) (diagram eta heta (bottom eta heta) x)
      (diagram eta heta (bottom eta heta) y) (insert (.inr ⟨s,v⟩,.inr ⟨s,w⟩) {p | p ∈ R}) := by
    apply CompatibleOn.insert_of_unary_binary hR (fun r => by cases r <;> simp [language,arity])
    · intro p hp
      exact iff_of_false (hfresh p hp) (hfresh' p hp)
    · intro r hr
      cases r with
      | inl r => rfl
      | inr r => simp [language,arity] at hr
    · intro r _
      exact token_diagonal_agrees eta heta s v w r
    · intro r hr p hp
      rcases r with r | (e | (⟨lam,n⟩ | (⟨lam,n⟩ | r)))
      · simp [language,arity] at hr
      · exact hOrdF e p hp
      · exact hBrF lam n p hp
      · exact hRF lam n p hp
      · exact hBottomF p hp
    · intro r hr p hp
      rcases r with r | (e | (⟨lam,n⟩ | (⟨lam,n⟩ | r)))
      · simp [language,arity] at hr
      · exact hOrdB e p hp
      · exact hBrB lam n p hp
      · exact (localRelationAt_symm eta heta x lam n p.1 _).trans
          ((hRF lam n p hp).trans (localRelationAt_symm eta heta y lam n p.2 _).symm)
      · exact (bottomEdge_token_right eta heta x p.1 s v).trans
          (bottomEdge_token_right eta heta y p.2 s w).symm
  apply hcompat.mono
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact Or.inr hp
  · exact Or.inl (List.mem_singleton.mp hp)

end FSCofinality.CosetConstruction.TokenModel
