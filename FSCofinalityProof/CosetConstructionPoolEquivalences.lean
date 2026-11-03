import FSCofinalityProof.CosetConstructionTokenModelProperties
import FSCofinalityProof.CosetConstructionRawProperties
import FSCofinalityProof.CosetConstructionSemanticRecovery
import FSCofinalityProof.TokenEquivalences

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def columnCongr (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta)}
    (h : lower=upper) (n : ℕ) : Column eta heta lam hlam lower n ≃ Column eta heta lam hlam upper n :=
  Equiv.cast (congrArg (fun L => Column eta heta lam hlam L n) h)

theorem columnCongr_encode (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta)}
    (h : lower=upper) (n : ℕ) (c : Column eta heta lam hlam lower n) :
    encodeColumn eta heta lam hlam upper n (columnCongr eta heta lam hlam h n c) =
      encodeColumn eta heta lam hlam lower n c := by subst upper; rfl

def rawEquiv {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y) :
    (s : TokenSort eta) → raw eta heta x s ≃ raw eta heta y s
  | .inl a => Equiv.setCongr (pools_congr eta heta (Frame.rank a) h)
  | .inr (lam,n) => columnCongr eta heta _ lam.property
      (funext (fun b => funext (fun _ => pools_congr eta heta b h))) n

theorem rawEquiv_names {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y)
    (s : TokenSort eta) (u : raw eta heta x s) :
    rawName eta heta y s (rawEquiv eta heta h s u) = rawName eta heta x s u := by
  cases s with
  | inl a => rfl
  | inr c =>
    exact columnCongr_encode eta heta _ c.1.property
      (funext (fun b => funext (fun _ => pools_congr eta heta b h))) c.2 u

theorem limitProfile_semantic_congr (x y : (fsTower eta).Carrier)
    (lam : LimitIndex eta) (n : ℕ)
    (r : raw eta heta x (.inl lam.val)) (s : raw eta heta y (.inl lam.val))
    (c : raw eta heta x (.inr (lam,n))) (d : raw eta heta y (.inr (lam,n)))
    (hrow : r.val=s.val)
    (hcol : rawName eta heta x (.inr (lam,n)) c = rawName eta heta y (.inr (lam,n)) d) :
    limitProfile eta heta x lam n r c = limitProfile eta heta y lam n s d := by
  rw [limitProfile_local,limitProfile_local]
  apply profile_semantic_congr eta heta _ lam.property (Frame.rank_le_top lam.val) n
  · exact (rowObject_localLimitRow eta heta x lam r).trans
      (hrow.trans (rowObject_localLimitRow eta heta y lam s).symm)
  · exact hcol

theorem rawEquiv_profile {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y)
    (lam : LimitIndex eta) (n : ℕ) (r : raw eta heta x (.inl lam.val))
    (c : raw eta heta x (.inr (lam,n))) :
    limitProfile eta heta x lam n r c = limitProfile eta heta y lam n
      (rawEquiv eta heta h (.inl lam.val) r) (rawEquiv eta heta h (.inr (lam,n)) c) := by
  apply limitProfile_semantic_congr eta heta x y lam n
  · exact (rawEquiv_names eta heta h (.inl lam.val) r).symm
  · exact (rawEquiv_names eta heta h (.inr (lam,n)) c).symm

theorem rawEquiv_bottom {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y)
    (v : Token (raw eta heta x (zeroSort eta))) :
    bottom eta heta x v = bottom eta heta y (mapToken (rawEquiv eta heta h (zeroSort eta)) v) := by
  have hn : tokenName eta heta y (zeroSort eta) (mapToken (rawEquiv eta heta h (zeroSort eta)) v) =
      tokenName eta heta x (zeroSort eta) v := by
    apply Prod.ext
    · simp only [tokenName,mapToken,List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro u _
      exact rawEquiv_names eta heta h (zeroSort eta) u
    · rfl
  have hd : decodedBottom eta heta y (mapToken (rawEquiv eta heta h (zeroSort eta)) v) =
      decodedBottom eta heta x v := by
    apply Prod.ext
    · have hh := congrArg Prod.fst hn
      have hm := congrArg (List.map (decodeAtom eta heta)) hh
      simpa only [tokenName,mapToken,decodedBottom,List.map_map,Function.comp_def,rawName,zeroSort,mainSort] using hm
    · rfl
  exact congrArg (fun t : Token BottomValueSpace => bottomListMap t.1 t.2) hd.symm

def vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) : Vertex eta heta x ≃ Vertex eta heta y :=
  Equiv.sumCongr (Equiv.refl ℕ) (Equiv.sigmaCongrRight (fun s => tokenCongr (f s)))

@[simp] theorem vertexCongr_coordinate {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (n : ℕ) :
    vertexCongr eta heta f (.inl n) = .inl n := rfl

@[simp] theorem vertexCongr_token {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (s : TokenSort eta) (v : Token (raw eta heta x s)) :
    vertexCongr eta heta f (.inr ⟨s,v⟩) = .inr ⟨s,mapToken (f s) v⟩ := rfl

@[simp] theorem sortOf_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (v : Vertex eta heta x) :
    sortOf eta heta (vertexCongr eta heta f v) = sortOf eta heta v := by
  cases v <;> rfl

theorem tokenAt_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (s : TokenSort eta) (v : Vertex eta heta x) :
    tokenAt eta heta s (vertexCongr eta heta f v) =
      (tokenAt eta heta s v).map (mapToken (f s)) := by
  cases v with
  | inl n => rfl
  | inr v =>
    rcases v with ⟨t,v⟩
    by_cases ht : t=s
    · subst t
      simp only [vertexCongr_token,tokenAt_inr,Option.map_some]
    · simp only [vertexCongr_token,tokenAt,dif_neg ht,Option.map_none]

@[simp] theorem coordinateAt_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (v : Vertex eta heta x) :
    coordinateAt eta heta (vertexCongr eta heta f v) = coordinateAt eta heta v := by
  cases v <;> rfl

theorem edgeAt_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (s t : TokenSort eta)
    (R : Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (R' : Token (raw eta heta y s) → Token (raw eta heta y t) → Bool)
    (hR : ∀ v w, R v w = R' (mapToken (f s) v) (mapToken (f t) w))
    (u v : Vertex eta heta x) : edgeAt eta heta s t R u v =
      edgeAt eta heta s t R' (vertexCongr eta heta f u) (vertexCongr eta heta f v) := by
  unfold edgeAt
  rw [tokenAt_vertexCongr,tokenAt_vertexCongr]
  cases hu : tokenAt eta heta s u <;> cases hv : tokenAt eta heta t v <;>
    simp only [Option.map_none,Option.map_some,Option.elim_none,Option.elim_some]
  exact hR _ _

theorem diagram_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s)
    (hO : ∀ r u v, ordinaryMatrix eta heta x r u v =
      ordinaryMatrix eta heta y r (f (rowSort eta r) u) (f (colSort eta r) v))
    (hP : ∀ lam n u c, limitProfile eta heta x lam n u c =
      limitProfile eta heta y lam n (f (.inl lam.val) u) (f (.inr (lam,n)) c))
    (hB : ∀ v, bottom eta heta x v = bottom eta heta y (mapToken (f (zeroSort eta)) v)) :
    ∀ s a, diagram eta heta (bottom eta heta) x s a =
      diagram eta heta (bottom eta heta) y s (vertexCongr eta heta f ∘ a) := by
  intro s a
  rcases s with s | r | c | c | u
  · simp only [diagram,Function.comp_def,sortOf_vertexCongr]
  · apply edgeAt_vertexCongr eta heta f
    intro v w
    exact ordinaryEdge_congr _ _ _ _ (hO r) genericTable (roleNumber eta heta (.inl r)) v w
  · rcases c with ⟨lam,n⟩
    apply edgeAt_vertexCongr eta heta f
    intro v w
    exact branchEdge_congr _ _ _ _ (hP lam) genericTable (roleNumber eta heta (.inr (lam,n))) n v w
  · rcases c with ⟨lam,n⟩
    apply edgeAt_vertexCongr eta heta f
    intro v w
    exact decide_eq_decide.mpr (limit_R_congr _ _ (f (.inl lam.val))
      (fun n => f (.inr (lam,n))) (hP lam) v w n)
  · change (tokenAt eta heta (zeroSort eta) (a (0 : Fin 2))).elim false
      (fun r => (coordinateAt eta heta (a (1 : Fin 2))).elim false (bottom eta heta x r)) =
      (tokenAt eta heta (zeroSort eta) (vertexCongr eta heta f (a (0 : Fin 2)))).elim false
      (fun r => (coordinateAt eta heta (vertexCongr eta heta f (a (1 : Fin 2)))).elim false
        (bottom eta heta y r))
    rw [tokenAt_vertexCongr,coordinateAt_vertexCongr]
    cases ht : tokenAt eta heta (zeroSort eta) (a (0 : Fin 2)) <;>
      cases hq : coordinateAt eta heta (a (1 : Fin 2)) <;>
      simp only [Option.map_none,Option.map_some,Option.elim_none,Option.elim_some]
    exact congrFun (hB _) _

theorem source_equivalent_qFixed {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y) :
    ∃ e : Vertex eta heta x ≃ Vertex eta heta y,
      (∀ s a, diagram eta heta (bottom eta heta) x s a =
        diagram eta heta (bottom eta heta) y s (e ∘ a)) ∧ ∀ n, e (.inl n) = .inl n := by
  refine ⟨vertexCongr eta heta (rawEquiv eta heta h),?_,fun _ => rfl⟩
  apply diagram_vertexCongr eta heta (rawEquiv eta heta h)
  · intro r u v
    rw [ordinaryMatrix_eq_names,ordinaryMatrix_eq_names,rawEquiv_names,rawEquiv_names]
  · exact rawEquiv_profile eta heta h
  · exact rawEquiv_bottom eta heta h

end FSCofinality.CosetConstruction.TokenModel
