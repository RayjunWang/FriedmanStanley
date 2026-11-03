import FSCofinalityProof.TokenCoordinateExtension

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

def SortEntries (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta) :=
  {i : Fin R.length // sortOf eta heta (R.get i).2 = some s}

instance (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta) :
    Fintype (SortEntries eta heta R s) := inferInstanceAs (Fintype {i : Fin R.length // _})

def targetEntry (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta)
    (i : SortEntries eta heta R s) : Token (raw eta heta y s) :=
  (tokenFiberEquiv eta heta y s).symm ⟨(R.get i.val).2,i.property⟩

def sourceEntry (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R}) (s : TokenSort eta)
    (i : SortEntries eta heta R s) : Token (raw eta heta x s) :=
  (tokenFiberEquiv eta heta x s).symm ⟨(R.get i.val).1,
    (hR.sort_eq eta heta _ (List.get_mem _ i.val)).trans i.property⟩

theorem targetEntry_vertex (R : List (Vertex eta heta x × Vertex eta heta y))
    (s : TokenSort eta) (i : SortEntries eta heta R s) :
    (.inr ⟨s,targetEntry eta heta R s i⟩ : Vertex eta heta y) = (R.get i.val).2 :=
  congrArg Subtype.val ((tokenFiberEquiv eta heta y s).apply_symm_apply _)

theorem sourceEntry_vertex (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (i : SortEntries eta heta R s) :
    (.inr ⟨s,sourceEntry eta heta R hR s i⟩ : Vertex eta heta x) = (R.get i.val).1 :=
  congrArg Subtype.val ((tokenFiberEquiv eta heta x s).apply_symm_apply _)

theorem tokenVertex_injective (z : (fsTower eta).Carrier) (s : TokenSort eta) :
    Function.Injective (fun v : Token (raw eta heta z s) => (.inr ⟨s,v⟩ : Vertex eta heta z)) := by
  intro v w h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2

theorem sourceEntry_eq_iff_targetEntry_eq
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (i j : SortEntries eta heta R s) :
    sourceEntry eta heta R hR s i = sourceEntry eta heta R hR s j ↔
      targetEntry eta heta R s i = targetEntry eta heta R s j := by
  have h := hR.1 (R.get i.val) (List.get_mem _ i.val) (R.get j.val) (List.get_mem _ j.val)
  constructor
  · intro hij
    apply tokenVertex_injective eta heta y s
    dsimp only
    rw [targetEntry_vertex,targetEntry_vertex]
    apply h.mp
    rw [← sourceEntry_vertex eta heta R hR s i,← sourceEntry_vertex eta heta R hR s j,hij]
  · intro hij
    apply tokenVertex_injective eta heta x s
    dsimp only
    rw [sourceEntry_vertex,sourceEntry_vertex]
    apply h.mpr
    rw [← targetEntry_vertex eta heta R s i,← targetEntry_vertex eta heta R s j,hij]

theorem entries_preserve_limit_R
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ)
    (i j : SortEntries eta heta R (.inl lam.val)) :
    Tokens.R (limitProfile eta heta x lam) n (sourceEntry eta heta R hR _ i)
      (sourceEntry eta heta R hR _ j) ↔
    Tokens.R (limitProfile eta heta y lam) n (targetEntry eta heta R _ i)
      (targetEntry eta heta R _ j) := by
  have h := hR.pair_diagram (.inr (.inr (.inr (.inl (lam,n)))))
    (R.get i.val) (List.get_mem _ i.val) (R.get j.val) (List.get_mem _ j.val)
  rw [← sourceEntry_vertex eta heta R hR (.inl lam.val) i,
    ← sourceEntry_vertex eta heta R hR (.inl lam.val) j,
    ← targetEntry_vertex eta heta R (.inl lam.val) i,
    ← targetEntry_vertex eta heta R (.inl lam.val) j] at h
  change edgeAt eta heta _ _ _ (.inr ⟨_,_⟩) (.inr ⟨_,_⟩) =
    edgeAt eta heta _ _ _ (.inr ⟨_,_⟩) (.inr ⟨_,_⟩) at h
  exact decide_eq_decide.mp (by simpa only [edgeAt_inr] using h)

theorem entries_preserve_branch
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ)
    (i : SortEntries eta heta R (.inl lam.val))
    (j : SortEntries eta heta R (.inr (lam,n))) :
    branch eta heta x lam n (sourceEntry eta heta R hR _ i) (sourceEntry eta heta R hR _ j) =
      branch eta heta y lam n (targetEntry eta heta R _ i) (targetEntry eta heta R _ j) := by
  have h := hR.pair_diagram (.inr (.inr (.inl (lam,n))))
    (R.get i.val) (List.get_mem _ i.val) (R.get j.val) (List.get_mem _ j.val)
  rw [← sourceEntry_vertex eta heta R hR (.inl lam.val) i,
    ← sourceEntry_vertex eta heta R hR (.inr (lam,n)) j,
    ← targetEntry_vertex eta heta R (.inl lam.val) i,
    ← targetEntry_vertex eta heta R (.inr (lam,n)) j] at h
  change edgeAt eta heta _ _ _ (.inr ⟨_,_⟩) (.inr ⟨_,_⟩) =
    edgeAt eta heta _ _ _ (.inr ⟨_,_⟩) (.inr ⟨_,_⟩) at h
  simpa only [edgeAt_inr] using h

theorem targetEntry_covers
    (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta)
    (p : Vertex eta heta x × Vertex eta heta y) (hp : p ∈ R)
    (v : Token (raw eta heta y s)) (hv : p.2 = .inr ⟨s,v⟩) :
    ∃ i : SortEntries eta heta R s, R.get i.val = p ∧ targetEntry eta heta R s i = v := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
  let j : SortEntries eta heta R s := ⟨i,by rw [hi,hv]; rfl⟩
  refine ⟨j,hi,?_⟩
  apply tokenVertex_injective eta heta y s
  dsimp only
  exact (targetEntry_vertex eta heta R s j).trans ((congrArg Prod.snd hi).trans hv)

end FSCofinality.CosetConstruction.TokenModel
