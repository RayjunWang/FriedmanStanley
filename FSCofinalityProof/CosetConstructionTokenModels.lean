import FSCofinalityProof.CosetConstructionPoolInvariant
import FSCofinalityProof.RawObjectsNaturality
import FSCofinalityProof.RawObjectsPoolRoles
import FSCofinalityProof.TokenBottomRecovery
import FSCofinalityProof.TokenLimitRecovery

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

abbrev MainIndex := Frame.Layer eta
abbrev LimitIndex := {a : MainIndex eta // IsSuccLimit (Frame.rank a)}
abbrev ColumnIndex := LimitIndex eta × ℕ
abbrev SuccessorIndex := {a : MainIndex eta // Frame.rank a + 1 ≤ Frame.top eta}
abbrev TokenSort := MainIndex eta ⊕ ColumnIndex eta
abbrev OrdinaryRole := SuccessorIndex eta ⊕ ColumnIndex eta

instance mainIndex_countable : Countable (MainIndex eta) := Frame.layer_countable eta heta
instance limitIndex_countable : Countable (LimitIndex eta) := by
  letI := mainIndex_countable eta heta
  exact inferInstanceAs (Countable {a : MainIndex eta // _})
instance columnIndex_countable : Countable (ColumnIndex eta) := by
  letI := limitIndex_countable eta heta
  infer_instance
instance sort_countable : Countable (TokenSort eta) := by
  letI := mainIndex_countable eta heta
  letI := columnIndex_countable eta heta
  infer_instance
instance ordinaryRole_countable : Countable (OrdinaryRole eta) := by
  letI := mainIndex_countable eta heta
  letI := columnIndex_countable eta heta
  infer_instance

def mainPool (x : (fsTower eta).Carrier) (a : Ordinal.{0}) : Set (Ambient eta heta) :=
  Pool eta heta (fun b => fullSeeds eta heta b x) a

def lowerPools (x : (fsTower eta).Carrier) (lam : Ordinal.{0}) :
    ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta) := fun b _ => mainPool eta heta x b

def raw (x : (fsTower eta).Carrier) : TokenSort eta → Type
  | .inl a => mainPool eta heta x (Frame.rank a)
  | .inr (lam,n) => Column eta heta (Frame.rank lam.val) lam.property
      (lowerPools eta heta x (Frame.rank lam.val)) n

instance mainPool_countable (x : (fsTower eta).Carrier) (a : Ordinal.{0}) :
    Countable (mainPool eta heta x a) :=
  (pool_countable eta heta _ (fun b => fullSeeds_countable eta heta b x) a).to_subtype

instance columnRaw_countable (x : (fsTower eta).Carrier) (c : ColumnIndex eta) :
    Countable (raw eta heta x (.inr c)) := by
  rcases c with ⟨lam,n⟩
  let f : raw eta heta x (.inr (lam,n)) → mainPool eta heta x
      (Frame.delta eta (Frame.rank lam.val) lam.property n) := fun c =>
    ⟨encodeColumn eta heta (Frame.rank lam.val) lam.property
      (lowerPools eta heta x (Frame.rank lam.val)) n c,
      (pool_encodeColumn eta heta _ _ _ (Frame.rank_le_top lam.val) n c).1⟩
  apply Function.Injective.countable (f := f)
  intro c d h
  exact encodeColumn_injective eta heta _ _ _ (Frame.rank_le_top lam.val) n
    (congrArg Subtype.val h)

instance raw_countable (x : (fsTower eta).Carrier) (s : TokenSort eta) : Countable (raw eta heta x s) := by
  cases s with
  | inl a => exact mainPool_countable eta heta x _
  | inr c => exact columnRaw_countable eta heta x c

def Vertex (x : (fsTower eta).Carrier) := ℕ ⊕ Σ s : TokenSort eta, Token (raw eta heta x s)

instance vertex_countable (x : (fsTower eta).Carrier) : Countable (Vertex eta heta x) := by
  letI := sort_countable eta heta
  exact inferInstanceAs (Countable (ℕ ⊕ Σ s : TokenSort eta, List (raw eta heta x s) × ℕ))

instance vertex_infinite (x : (fsTower eta).Carrier) : Infinite (Vertex eta heta x) :=
  Infinite.of_injective (Sum.inl : ℕ → Vertex eta heta x) Sum.inl_injective

def sortOf {x : (fsTower eta).Carrier} : Vertex eta heta x → Option (TokenSort eta)
  | .inl _ => none
  | .inr ⟨s,_⟩ => some s

def mainSort (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) : TokenSort eta :=
  .inl (Frame.ofOrdinal eta a ha)

def rowSort : OrdinaryRole eta → TokenSort eta
  | .inl a => mainSort eta (Frame.rank a.val+1) a.property
  | .inr c => .inr c

def colSort : OrdinaryRole eta → TokenSort eta
  | .inl a => .inl a.val
  | .inr (lam,n) => mainSort eta (Frame.rho eta (Frame.rank lam.val) lam.property n)
      ((Frame.rho_lt eta _ lam.property n).le.trans (Frame.rank_le_top lam.val))

def ordinaryMatrix (x : (fsTower eta).Carrier) (e : OrdinaryRole eta) :
    raw eta heta x (rowSort eta e) → raw eta heta x (colSort eta e) → Bool := by
  cases e with
  | inl a =>
    intro r c
    exact ordinaryRaw r.val c.val
  | inr c =>
    rcases c with ⟨lam,n⟩
    intro r c
    exact ordinaryRaw
      (encodeColumn eta heta _ lam.property (lowerPools eta heta x _) n r) c.val

def roleNumber : OrdinaryRole eta ⊕ ColumnIndex eta ↪ ℕ := by
  letI := ordinaryRole_countable eta heta
  letI := columnIndex_countable eta heta
  letI := Encodable.ofCountable (OrdinaryRole eta ⊕ ColumnIndex eta)
  exact ⟨Encodable.encode,Encodable.encode_injective⟩

def ambientLower (x : (fsTower eta).Carrier) (lam : Ordinal.{0}) :
    ∀ b hb, lowerPools eta heta x lam b hb ⊆ fullLower eta heta lam b hb :=
  fun b _ => pool_subset_valid eta heta _ (fun a => fullSeeds_typed eta heta a x) b

def limitProfile (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (r : raw eta heta x (.inl lam.val))
    (c : raw eta heta x (.inr (lam,n))) : Bool :=
  ambientProfile eta heta (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val) n r.val
    (mapColumn eta heta _ lam.property (ambientLower eta heta x _) n c)

def ordinary (x : (fsTower eta).Carrier) (e : OrdinaryRole eta)
    (r : Token (raw eta heta x (rowSort eta e)))
    (c : Token (raw eta heta x (colSort eta e))) : Bool :=
  ordinaryEdge genericTable (roleNumber eta heta (.inl e)) (ordinaryMatrix eta heta x e) r c

def branch (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (r : Token (raw eta heta x (.inl lam.val)))
    (c : Token (raw eta heta x (.inr (lam,n)))) : Bool :=
  branchEdge (limitProfile eta heta x lam) genericTable (roleNumber eta heta (.inr (lam,n))) n r c

abbrev Symbol := Option (TokenSort eta) ⊕
  (OrdinaryRole eta ⊕ (ColumnIndex eta ⊕ (ColumnIndex eta ⊕ Unit)))

def arity : Symbol eta → ℕ
  | .inl _ => 1
  | .inr _ => 2

def language : CountableRelationalLanguage where
  Symbol := Symbol eta
  arity := arity eta
  countable := by
    letI := sort_countable eta heta
    letI := ordinaryRole_countable eta heta
    letI := columnIndex_countable eta heta
    infer_instance

def tokenAt {x : (fsTower eta).Carrier} (s : TokenSort eta) :
    Vertex eta heta x → Option (Token (raw eta heta x s))
  | .inl _ => none
  | .inr ⟨t,v⟩ => if h : t=s then some (h ▸ v) else none

def coordinateAt {x : (fsTower eta).Carrier} : Vertex eta heta x → Option ℕ
  | .inl n => some n
  | .inr _ => none

def edgeAt {x : (fsTower eta).Carrier} (s t : TokenSort eta)
    (f : Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (u v : Vertex eta heta x) : Bool :=
  (tokenAt eta heta s u).elim false (fun r => (tokenAt eta heta t v).elim false (f r))

def zeroSort : TokenSort eta := mainSort eta 0 zero_le

/-- All non-sort symbols are binary. Bottom neighborhoods are supplied by
the actual atom decoder; no sigma algebra on the raw semantic universe is used. -/
def diagram (bottom : ∀ x : (fsTower eta).Carrier,
    Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x : (fsTower eta).Carrier) :
    (s : Symbol eta) → (Fin (arity eta s) → Vertex eta heta x) → Bool
  | .inl s,a => decide (sortOf eta heta (a (0 : Fin 1)) = s)
  | .inr (.inl e),a => edgeAt eta heta (rowSort eta e) (colSort eta e)
      (ordinary eta heta x e) (a (0 : Fin 2)) (a (1 : Fin 2))
  | .inr (.inr (.inl (lam,n))),a => edgeAt eta heta (.inl lam.val) (.inr (lam,n))
      (branch eta heta x lam n) (a (0 : Fin 2)) (a (1 : Fin 2))
  | .inr (.inr (.inr (.inl (lam,n)))),a =>
      edgeAt eta heta (.inl lam.val) (.inl lam.val)
        (fun r t => decide (R (limitProfile eta heta x lam) n r t)) (a (0 : Fin 2)) (a (1 : Fin 2))
  | .inr (.inr (.inr (.inr _))),a =>
      (tokenAt eta heta (zeroSort eta) (a (0 : Fin 2))).elim false (fun r =>
        (coordinateAt eta heta (a (1 : Fin 2))).elim false (bottom x r))

def modelWithEnumeration (bottom : ∀ x : (fsTower eta).Carrier,
    Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x : (fsTower eta).Carrier) (e : ℕ ≃ Vertex eta heta x) :
    Structures (language eta heta) :=
  fun c => diagram eta heta bottom x c.1 (e ∘ c.2)

def LiteralIsomorphic (bottom : ∀ x : (fsTower eta).Carrier,
    Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x y : (fsTower eta).Carrier) : Prop :=
  ∃ e : Vertex eta heta x ≃ Vertex eta heta y,
    ∀ s a, diagram eta heta bottom x s a = diagram eta heta bottom y s (e ∘ a)

theorem isomorphic_modelWithEnumeration_iff
    (bottom : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x y : (fsTower eta).Carrier)
    (e : ℕ ≃ Vertex eta heta x) (f : ℕ ≃ Vertex eta heta y) :
    Isomorphic (modelWithEnumeration eta heta bottom x e) (modelWithEnumeration eta heta bottom y f) ↔
      LiteralIsomorphic eta heta bottom x y := by
  constructor
  · rintro ⟨p,hp⟩
    let q := (e.symm.trans p).trans f
    refine ⟨q,fun s a => ?_⟩
    have h := hp s (e.symm ∘ a)
    simpa only [modelWithEnumeration,q,Equiv.trans_apply,Function.comp_def,
      Equiv.apply_symm_apply] using h
  · rintro ⟨q,hq⟩
    let p := (e.trans q).trans f.symm
    refine ⟨p,fun s a => ?_⟩
    have h := hq s (e ∘ a)
    simpa only [modelWithEnumeration,p,Equiv.trans_apply,Function.comp_def,
      Equiv.apply_symm_apply] using h

end FSCofinality.CosetConstruction.TokenModel
