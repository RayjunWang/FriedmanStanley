import FSCofinalityProof.CosetConstructionTokenModelProperties
import FSCofinalityProof.CosetConstructionRawProperties
import FSCofinalityProof.RawObjectsRestrictedRecovery

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def PreservesDiagram {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y) : Prop :=
  ∀ s a, diagram eta heta (bottom eta heta) x s a = diagram eta heta (bottom eta heta) y s (e ∘ a)

def inducedTokenEquiv {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : PreservesDiagram eta heta e) (s : TokenSort eta) :
    Token (raw eta heta x s) ≃ Token (raw eta heta y s) :=
  sortedTokenEquiv eta heta e (preserves_sort eta heta (bottom eta heta) e he) s

def Recovers {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : PreservesDiagram eta heta e) (s : TokenSort eta) : Prop :=
  ∀ v, tokenName eta heta y s (inducedTokenEquiv eta heta e he s v) = tokenName eta heta x s v

theorem recovers_zero {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : PreservesDiagram eta heta e) (hQ : ∀ n, e (.inl n) = .inl n) :
    Recovers eta heta e he (zeroSort eta) := fun v => (qFixed_bottom_name eta heta e he hQ v).symm

theorem mainPool_eq_of_recovers {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (a : MainIndex eta) (hrec : Recovers eta heta e he (.inl a)) :
    mainPool eta heta x (Frame.rank a) = mainPool eta heta y (Frame.rank a) := by
  apply pools_eq_of_named_bijection _ _ (inducedTokenEquiv eta heta e he (.inl a))
  exact hrec

def sortRank : TokenSort eta → Ordinal.{0}
  | .inl a => Frame.rank a
  | .inr (lam,n) => Frame.delta eta (Frame.rank lam.val) lam.property n

theorem ordinary_rank_lt (r : OrdinaryRole eta) :
    sortRank eta (colSort eta r) < sortRank eta (rowSort eta r) := by
  cases r with
  | inl a =>
    simp only [sortRank,rowSort,colSort,mainSort,Frame.rank_ofOrdinal]
    exact lt_add_one _
  | inr c =>
    rcases c with ⟨lam,n⟩
    simp only [sortRank,rowSort,colSort,mainSort,Frame.rank_ofOrdinal]
    simpa only [Frame.rho,Frame.delta,add_assoc,one_add_one_eq_two] using
      lt_add_one (Frame.sigma eta (Frame.rank lam.val) lam.property n + 1)

theorem branch_rank_lt (lam : LimitIndex eta) (n : ℕ) :
    sortRank eta (.inr (lam,n)) < sortRank eta (.inl lam.val) := Frame.delta_lt eta _ lam.property n

theorem ordinaryMatrix_eq_names (x : (fsTower eta).Carrier) (r : OrdinaryRole eta)
    (u : raw eta heta x (rowSort eta r)) (v : raw eta heta x (colSort eta r)) :
    ordinaryMatrix eta heta x r u v =
      ordinaryRaw (rawName eta heta x (rowSort eta r) u) (rawName eta heta x (colSort eta r) v) := by
  cases r <;> rfl

theorem recovers_ordinary_row {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (r : OrdinaryRole eta) (hcol : Recovers eta heta e he (colSort eta r))
    (hinj : (range (rawName eta heta x (rowSort eta r)) ∪
      range (rawName eta heta y (rowSort eta r))).InjOn
        (fun u => fun q : raw eta heta x (colSort eta r) =>
          ordinaryRaw u (rawName eta heta x (colSort eta r) q))) :
    Recovers eta heta e he (rowSort eta r) := by
  intro v
  apply Eq.symm
  apply named_ordinary_recovery genericTable_generic (roleNumber eta heta (.inl r))
    (rawName eta heta x (rowSort eta r)) (rawName eta heta y (rowSort eta r))
    (rawName eta heta x (colSort eta r)) (rawName eta heta y (colSort eta r)) ordinaryRaw
    (inducedTokenEquiv eta heta e he (colSort eta r)) hcol hinj v
  intro q
  have hx : ordinaryMatrix eta heta x r = fun u v =>
      ordinaryRaw (rawName eta heta x (rowSort eta r) u) (rawName eta heta x (colSort eta r) v) :=
    funext (fun u => funext (ordinaryMatrix_eq_names eta heta x r u))
  have hy : ordinaryMatrix eta heta y r = fun u v =>
      ordinaryRaw (rawName eta heta y (rowSort eta r) u) (rawName eta heta y (colSort eta r) v) :=
    funext (fun u => funext (ordinaryMatrix_eq_names eta heta y r u))
  simpa only [ordinary,hx,hy] using
    preserves_ordinary eta heta (bottom eta heta) e he r v q

theorem ordinary_names_injOn {X Y V : Type} (l : Frame.Layer eta)
    (nx : X → Ambient eta heta) (ny : Y → Ambient eta heta) (nv : V → Ambient eta heta)
    (hcollection : ∀ u ∈ range nx ∪ range ny, ∃ z, u = collection l z)
    (hdown : ∀ u ∈ range nx ∪ range ny, ∀ c, Member c u → ∃ q, nv q = c) :
    (range nx ∪ range ny).InjOn (fun u => fun q => ordinaryRaw u (nv q)) := by
  intro u hu v hv huv
  obtain ⟨s,rfl⟩ := hcollection u hu
  obtain ⟨t,rfl⟩ := hcollection v hv
  apply collection_ext
  intro c
  constructor
  · intro hc
    obtain ⟨q,hq⟩ := hdown _ hu c hc
    have h := decide_eq_decide.mp (congrFun huv q)
    exact hq ▸ h.mp (hq.symm ▸ hc)
  · intro hc
    obtain ⟨q,hq⟩ := hdown _ hv c hc
    have h := decide_eq_decide.mp (congrFun huv q)
    exact hq ▸ h.mpr (hq.symm ▸ hc)

def colMainIndex : OrdinaryRole eta → MainIndex eta
  | .inl a => a.val
  | .inr (lam,n) => Frame.ofOrdinal eta (Frame.rho eta (Frame.rank lam.val) lam.property n)
      ((Frame.rho_lt eta _ lam.property n).le.trans (Frame.rank_le_top lam.val))

theorem colSort_eq (r : OrdinaryRole eta) : colSort eta r = .inl (colMainIndex eta r) := by
  cases r <;> rfl

theorem colMainIndex_rank (r : OrdinaryRole eta) :
    Frame.rank (colMainIndex eta r) = sortRank eta (colSort eta r) := by rw [colSort_eq]; rfl

theorem ordinary_rank_succ (r : OrdinaryRole eta) :
    sortRank eta (rowSort eta r) = sortRank eta (colSort eta r)+1 := by
  cases r with
  | inl a => simp only [rowSort,colSort,sortRank,mainSort,Frame.rank_ofOrdinal]
  | inr c =>
    simp only [rowSort,colSort,sortRank,mainSort,Frame.rank_ofOrdinal,
      Frame.delta,Frame.rho,add_assoc,one_add_one_eq_two]

theorem rawName_ordinary_row_mem (x : (fsTower eta).Carrier) (r : OrdinaryRole eta)
    (u : raw eta heta x (rowSort eta r)) :
    rawName eta heta x (rowSort eta r) u ∈ mainPool eta heta x (sortRank eta (rowSort eta r)) := by
  cases r with
  | inl a => simpa only [rowSort,rawName,sortRank,mainSort,Frame.rank_ofOrdinal] using u.property
  | inr c => exact (pool_encodeColumn eta heta _ _ c.1.property (Frame.rank_le_top c.1.val) c.2 u).1

theorem rawName_ordinary_member_lower (x : (fsTower eta).Carrier) (r : OrdinaryRole eta)
    (u : raw eta heta x (rowSort eta r)) {c : Ambient eta heta}
    (hc : Member c (rawName eta heta x (rowSort eta r) u)) :
    c ∈ mainPool eta heta x (sortRank eta (colSort eta r)) := by
  cases r with
  | inl a =>
    apply pool_member_lower eta heta _ (Frame.rank a.val)
      (fun _ h _ hm => fullSeeds_successor_downward eta heta (Frame.rank a.val) x h hm) ?_ hc
    simpa only [rowSort,raw,mainSort,Frame.rank_ofOrdinal] using u.property
  | inr q =>
    have h := (pool_encodeColumn eta heta _ _ q.1.property (Frame.rank_le_top q.1.val) q.2 u).2 c hc
    simpa only [colSort,sortRank,mainSort,Frame.rank_ofOrdinal] using h

theorem rawName_col_surjective (x : (fsTower eta).Carrier) (r : OrdinaryRole eta)
    {c : Ambient eta heta} (hc : c ∈ mainPool eta heta x (sortRank eta (colSort eta r))) :
    ∃ q : raw eta heta x (colSort eta r), rawName eta heta x (colSort eta r) q = c := by
  rw [colSort_eq] at hc ⊢
  exact ⟨⟨c,hc⟩,rfl⟩

theorem recovers_ordinary {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (r : OrdinaryRole eta) (hcol : Recovers eta heta e he (colSort eta r)) :
    Recovers eta heta e he (rowSort eta r) := by
  have hpool : mainPool eta heta x (sortRank eta (colSort eta r)) =
      mainPool eta heta y (sortRank eta (colSort eta r)) := by
    rw [colSort_eq] at hcol ⊢
    exact mainPool_eq_of_recovers eta heta e he _ hcol
  apply recovers_ordinary_row eta heta e he r hcol
  apply ordinary_names_injOn eta heta (level eta (sortRank eta (rowSort eta r)))
  · rintro u (⟨u,rfl⟩ | ⟨u,rfl⟩)
    · have hu := rawName_ordinary_row_mem eta heta x r u
      rw [ordinary_rank_succ] at hu
      have h := pool_successor_collection eta heta _ (fun b => fullSeeds_typed eta heta b x)
        (sortRank eta (colSort eta r)) hu
      simpa only [ordinary_rank_succ] using h
    · have hu := rawName_ordinary_row_mem eta heta y r u
      rw [ordinary_rank_succ] at hu
      have h := pool_successor_collection eta heta _ (fun b => fullSeeds_typed eta heta b y)
        (sortRank eta (colSort eta r)) hu
      simpa only [ordinary_rank_succ] using h
  · rintro u (⟨u,rfl⟩ | ⟨u,rfl⟩) c hc
    · exact rawName_col_surjective eta heta x r (rawName_ordinary_member_lower eta heta x r u hc)
    · apply rawName_col_surjective eta heta x r
      rw [hpool]
      exact rawName_ordinary_member_lower eta heta y r u hc

theorem recovers_limit {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (lam : LimitIndex eta)
    (hpool : ∀ b < Frame.rank lam.val, mainPool eta heta x b = mainPool eta heta y b)
    (hcols : ∀ n, Recovers eta heta e he (.inr (lam,n))) :
    Recovers eta heta e he (.inl lam.val) := by
  have hLU : lowerPools eta heta x (Frame.rank lam.val) =
      lowerPools eta heta y (Frame.rank lam.val) := funext (fun b => funext (hpool b))
  intro v
  apply Eq.symm
  apply restricted_limit_recovery eta heta (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val)
    genericTable_generic (fun n => roleNumber eta heta (.inr (lam,n)))
    (lowerPools eta heta x _) (lowerPools eta heta y _)
    (ambientLower eta heta x _) (ambientLower eta heta y _) hLU
    (mainPool eta heta x _) (mainPool eta heta y _)
    (mainPool_limit_subset_limitSet eta heta x _ lam.property)
    (mainPool_limit_subset_limitSet eta heta y _ lam.property)
    (fun n => inducedTokenEquiv eta heta e he (.inr (lam,n))) hcols v
  intro n q
  exact preserves_branch eta heta (bottom eta heta) e he lam n v q

theorem mainIndex_rank_injective : Function.Injective (Frame.rank : MainIndex eta → Ordinal.{0}) := by
  intro a b hab
  have ha := Frame.ofOrdinal_rank a
  have hb := Frame.ofOrdinal_rank b
  rw [← ha,← hb]
  congr 1

/-- Simultaneous recovery follows the actual semantic decoding ranks.
Dedicated column sorts are recovered at their own successor rank, before
the higher limit main sort can query them. -/
theorem recovers_all {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (hQ : ∀ n, e (.inl n) = .inl n) : ∀ s, Recovers eta heta e he s := by
  have hall (a : Ordinal.{0}) : ∀ s, sortRank eta s = a → Recovers eta heta e he s := by
    refine Ordinal.induction (p := fun a => ∀ s, sortRank eta s = a → Recovers eta heta e he s)
      a (fun gamma ih s hs => ?_)
    cases s with
    | inr c =>
      apply recovers_ordinary eta heta e he (.inr c)
      apply ih (sortRank eta (colSort eta (.inr c))) ?_ _ rfl
      rw [← hs]
      exact ordinary_rank_lt eta (.inr c)
    | inl l =>
      rcases Ordinal.zero_or_succ_or_isSuccLimit (Frame.rank l) with hzero | ⟨b,hb⟩ | hlim
      · have hl : l = Frame.ofOrdinal eta 0 zero_le :=
          mainIndex_rank_injective eta (hzero.trans (Frame.rank_ofOrdinal eta 0 zero_le).symm)
        subst l
        exact recovers_zero eta heta e he hQ
      · have hbl : Frame.rank l = b+1 := by simpa only [succ_eq_add_one] using hb.symm
        have hbtop : b+1 ≤ Frame.top eta := hbl ▸ Frame.rank_le_top l
        have hb' : b ≤ Frame.top eta := (le_self_add : b ≤ b+1).trans hbtop
        let r : SuccessorIndex eta := ⟨Frame.ofOrdinal eta b hb',by simpa using hbtop⟩
        have hrow : rowSort eta (.inl r) = .inl l := by
          apply congrArg Sum.inl
          apply mainIndex_rank_injective eta
          simp only [rowSort,mainSort,Frame.rank_ofOrdinal,r,hbl]
        rw [← hrow]
        apply recovers_ordinary eta heta e he (.inl r)
        apply ih (sortRank eta (colSort eta (.inl r))) ?_ _ rfl
        rw [← hs,← hrow]
        exact ordinary_rank_lt eta (.inl r)
      · let lam : LimitIndex eta := ⟨l,hlim⟩
        apply recovers_limit eta heta e he lam
        · intro b hb
          have hbtop : b ≤ Frame.top eta := hb.le.trans (Frame.rank_le_top l)
          let k := Frame.ofOrdinal eta b hbtop
          have hk : Recovers eta heta e he (.inl k) :=
            ih b (by rw [← hs]; exact hb) (.inl k) (Frame.rank_ofOrdinal eta b hbtop)
          simpa only [k,Frame.rank_ofOrdinal] using mainPool_eq_of_recovers eta heta e he k hk
        · intro n
          exact ih (sortRank eta (.inr (lam,n)))
            (by rw [← hs]; exact branch_rank_lt eta lam n) (.inr (lam,n)) rfl
  intro s
  exact hall (sortRank eta s) s rfl

theorem qFixed_reflects {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (hQ : ∀ n, e (.inl n) = .inl n) : (fsTower eta).rel x y := by
  apply (topPool_eq_iff eta heta x y).mp
  let t := Frame.ofOrdinal eta (Frame.top eta) le_rfl
  have h := mainPool_eq_of_recovers eta heta e he t (recovers_all eta heta e he hQ (.inl t))
  simpa only [t,Frame.rank_ofOrdinal] using h

theorem qFixed_rigid {x : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta x) (he : PreservesDiagram eta heta e)
    (hQ : ∀ n, e (.inl n) = .inl n) : e = Equiv.refl _ := by
  apply Equiv.ext
  intro v
  cases v with
  | inl n => exact hQ n
  | inr v =>
    rcases v with ⟨s,v⟩
    rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta (bottom eta heta) e he)]
    have hv := (tokenName_injective eta heta x s) (recovers_all eta heta e he hQ s v)
    exact congrArg (fun w : Token (raw eta heta x s) => (Sum.inr ⟨s,w⟩ : Vertex eta heta x)) hv

end FSCofinality.CosetConstruction.TokenModel
