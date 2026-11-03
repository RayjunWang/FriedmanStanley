import FSCofinalityProof.CosetConstructionTokenModels
import FSCofinalityProof.CosetConstructionBottomValues

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem bottom_raw_valid (x : (fsTower eta).Carrier) (u : raw eta heta x (zeroSort eta)) :
    u.val ∈ Valid eta heta 0 := by
  have h := pool_subset_valid eta heta _ (fun a => fullSeeds_typed eta heta a x)
    (Frame.rank (Frame.ofOrdinal eta 0 zero_le)) u.property
  simpa only [Frame.rank_ofOrdinal] using h

def decodedBottom (x : (fsTower eta).Carrier) (v : Token (raw eta heta x (zeroSort eta))) :
    Token BottomValueSpace := (v.1.map (fun u => decodeAtom eta heta u.val),v.2)

def bottom (x : (fsTower eta).Carrier) (v : Token (raw eta heta x (zeroSort eta))) : ℕ → Bool :=
  bottomListMap (decodedBottom eta heta x v).1 v.2

def rawName (x : (fsTower eta).Carrier) : (s : TokenSort eta) → raw eta heta x s → Ambient eta heta
  | .inl _,u => u.val
  | .inr (lam,n),u => encodeColumn eta heta _ lam.property (lowerPools eta heta x _) n u

def tokenName (x : (fsTower eta).Carrier) (s : TokenSort eta) (v : Token (raw eta heta x s)) :
    Token (Ambient eta heta) := mapToken (rawName eta heta x s) v

theorem rawName_injective (x : (fsTower eta).Carrier) (s : TokenSort eta) :
    Function.Injective (rawName eta heta x s) := by
  cases s with
  | inl a => exact Subtype.val_injective
  | inr c => exact encodeColumn_injective eta heta _ c.1.property _ (Frame.rank_le_top c.1.val) c.2

theorem tokenName_injective (x : (fsTower eta).Carrier) (s : TokenSort eta) :
    Function.Injective (tokenName eta heta x s) := by
  intro v w h
  apply Prod.ext
  · exact List.map_injective_iff.mpr (rawName_injective eta heta x s) (congrArg Prod.fst h)
  · exact congrArg (fun z : Token (Ambient eta heta) => z.2) h

theorem decodedBottom_reencode (x : (fsTower eta).Carrier)
    (v : Token (raw eta heta x (zeroSort eta))) :
    mapToken (atomObject eta heta) (decodedBottom eta heta x v) =
      tokenName eta heta x (zeroSort eta) v := by
  apply Prod.ext
  · simp only [mapToken,decodedBottom,tokenName,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro u _
    exact atomObject_decodeAtom_of_valid eta heta u.val (bottom_raw_valid eta heta x u)
  · rfl

theorem bottom_recovers_name (x y : (fsTower eta).Carrier)
    (v : Token (raw eta heta x (zeroSort eta))) (w : Token (raw eta heta y (zeroSort eta)))
    (h : bottom eta heta x v = bottom eta heta y w) :
    tokenName eta heta x (zeroSort eta) v = tokenName eta heta y (zeroSort eta) w := by
  have hd : decodedBottom eta heta x v = decodedBottom eta heta y w := bottomListMap_injective h
  exact (decodedBottom_reencode eta heta x v).symm.trans
    ((congrArg (mapToken (atomObject eta heta)) hd).trans (decodedBottom_reencode eta heta y w))

@[simp] theorem tokenAt_inr (x : (fsTower eta).Carrier) (s : TokenSort eta)
    (v : Token (raw eta heta x s)) : tokenAt eta heta s (.inr ⟨s,v⟩) = some v := by
  simp [tokenAt]

@[simp] theorem tokenAt_inl (x : (fsTower eta).Carrier) (s : TokenSort eta) (n : ℕ) :
    tokenAt eta heta s (.inl n : Vertex eta heta x) = none := rfl

@[simp] theorem edgeAt_inr (x : (fsTower eta).Carrier) (s t : TokenSort eta)
    (f : Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (v : Token (raw eta heta x s)) (w : Token (raw eta heta x t)) :
    edgeAt eta heta s t f (.inr ⟨s,v⟩) (.inr ⟨t,w⟩) = f v w := by simp [edgeAt]

def tokenFiberEquiv (x : (fsTower eta).Carrier) (s : TokenSort eta) :
    Token (raw eta heta x s) ≃ {v : Vertex eta heta x // sortOf eta heta v = some s} :=
  Equiv.ofBijective (fun v => ⟨.inr ⟨s,v⟩,rfl⟩) ⟨by
    intro v w h
    have h' := Sum.inr.inj (congrArg Subtype.val h)
    exact eq_of_heq (Sigma.mk.inj_iff.mp h').2,by
    rintro ⟨v,hv⟩
    cases v with
    | inl n => simp [sortOf] at hv
    | inr v =>
      rcases v with ⟨t,v⟩
      have ht : t=s := Option.some.inj hv
      subst t
      exact ⟨v,rfl⟩⟩

def sortedTokenEquiv {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y)
    (hsort : ∀ v, sortOf eta heta (e v) = sortOf eta heta v) (s : TokenSort eta) :
    Token (raw eta heta x s) ≃ Token (raw eta heta y s) :=
  ((tokenFiberEquiv eta heta x s).trans
    (e.subtypeEquiv (fun v => by rw [hsort v]))).trans (tokenFiberEquiv eta heta y s).symm

theorem sortedTokenEquiv_commutes {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (hsort : ∀ v, sortOf eta heta (e v) = sortOf eta heta v) (s : TokenSort eta)
    (v : Token (raw eta heta x s)) :
    e (.inr ⟨s,v⟩) = .inr ⟨s,sortedTokenEquiv eta heta e hsort s v⟩ := by
  have h := (tokenFiberEquiv eta heta y s).apply_symm_apply
    ((e.subtypeEquiv (fun v => by rw [hsort v])) (tokenFiberEquiv eta heta x s v))
  exact (congrArg Subtype.val h).symm

theorem preserves_sort {x y : (fsTower eta).Carrier}
    (b : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta b x s a = diagram eta heta b y s (e ∘ a))
    (v : Vertex eta heta x) : sortOf eta heta (e v) = sortOf eta heta v := by
  have h := he (.inl (sortOf eta heta v)) (fun _ => v)
  change decide (sortOf eta heta v = sortOf eta heta v) =
    decide (sortOf eta heta (e v) = sortOf eta heta v) at h
  exact of_decide_eq_true (h.symm.trans (decide_eq_true rfl))

theorem preserves_ordinary {x y : (fsTower eta).Carrier}
    (b : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta b x s a = diagram eta heta b y s (e ∘ a))
    (r : OrdinaryRole eta) (v : Token (raw eta heta x (rowSort eta r)))
    (w : Token (raw eta heta x (colSort eta r))) :
    ordinary eta heta x r v w = ordinary eta heta y r
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (rowSort eta r) v)
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (colSort eta r) w) := by
  have h := he (.inr (.inl r)) ![.inr ⟨rowSort eta r,v⟩,.inr ⟨colSort eta r,w⟩]
  change edgeAt eta heta _ _ (ordinary eta heta x r) (.inr ⟨_,v⟩) (.inr ⟨_,w⟩) =
    edgeAt eta heta _ _ (ordinary eta heta y r) (e (.inr ⟨_,v⟩)) (e (.inr ⟨_,w⟩)) at h
  rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he),
    sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he)] at h
  simpa only [edgeAt_inr] using h

theorem preserves_branch {x y : (fsTower eta).Carrier}
    (b : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta b x s a = diagram eta heta b y s (e ∘ a))
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inl lam.val)))
    (w : Token (raw eta heta x (.inr (lam,n)))) :
    branch eta heta x lam n v w = branch eta heta y lam n
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (.inl lam.val) v)
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (.inr (lam,n)) w) := by
  have h := he (.inr (.inr (.inl (lam,n)))) ![.inr ⟨.inl lam.val,v⟩,.inr ⟨.inr (lam,n),w⟩]
  change edgeAt eta heta _ _ (branch eta heta x lam n) (.inr ⟨_,v⟩) (.inr ⟨_,w⟩) =
    edgeAt eta heta _ _ (branch eta heta y lam n) (e (.inr ⟨_,v⟩)) (e (.inr ⟨_,w⟩)) at h
  rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he),
    sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he)] at h
  simpa only [edgeAt_inr] using h

theorem preserves_limit_R {x y : (fsTower eta).Carrier}
    (b : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta b x s a = diagram eta heta b y s (e ∘ a))
    (lam : LimitIndex eta) (n : ℕ) (v w : Token (raw eta heta x (.inl lam.val))) :
    R (limitProfile eta heta x lam) n v w ↔ R (limitProfile eta heta y lam) n
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (.inl lam.val) v)
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (.inl lam.val) w) := by
  have h := he (.inr (.inr (.inr (.inl (lam,n))))) ![.inr ⟨.inl lam.val,v⟩,.inr ⟨.inl lam.val,w⟩]
  change edgeAt eta heta _ _ (fun r t => decide (R (limitProfile eta heta x lam) n r t))
      (.inr ⟨_,v⟩) (.inr ⟨_,w⟩) =
    edgeAt eta heta _ _ (fun r t => decide (R (limitProfile eta heta y lam) n r t))
      (e (.inr ⟨_,v⟩)) (e (.inr ⟨_,w⟩)) at h
  rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he),
    sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he)] at h
  exact decide_eq_decide.mp (by simpa only [edgeAt_inr] using h)

theorem qFixed_bottom_name {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta (bottom eta heta) x s a =
      diagram eta heta (bottom eta heta) y s (e ∘ a))
    (hQ : ∀ n, e (.inl n) = .inl n)
    (v : Token (raw eta heta x (zeroSort eta))) :
    tokenName eta heta x (zeroSort eta) v = tokenName eta heta y (zeroSort eta)
      (sortedTokenEquiv eta heta e (preserves_sort eta heta (bottom eta heta) e he) (zeroSort eta) v) := by
  apply bottom_recovers_name
  funext n
  have h := he (.inr (.inr (.inr (.inr ())))) ![.inr ⟨zeroSort eta,v⟩,.inl n]
  change (tokenAt eta heta (zeroSort eta) (.inr ⟨_,v⟩)).elim false
      (fun r => (coordinateAt eta heta (.inl n)).elim false (bottom eta heta x r)) =
    (tokenAt eta heta (zeroSort eta) (e (.inr ⟨_,v⟩))).elim false
      (fun r => (coordinateAt eta heta (e (.inl n))).elim false (bottom eta heta y r)) at h
  rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta (bottom eta heta) e he),hQ] at h
  simpa only [tokenAt_inr,coordinateAt,Option.elim_some] using h

end FSCofinality.CosetConstruction.TokenModel
