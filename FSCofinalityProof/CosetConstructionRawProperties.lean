import FSCofinalityProof.CosetConstructionTokenModels
import FSCofinalityProof.RawObjectsPoolProfileSeparation

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem mainPool_ordinary_union_injOn (x y : (fsTower eta).Carrier) (a : Ordinal.{0}) :
    InjOn (fun r => fun c : (mainPool eta heta x a ∪ mainPool eta heta y a : Set (Ambient eta heta)) =>
      ordinaryRaw r c.val) (mainPool eta heta x (a+1) ∪ mainPool eta heta y (a+1)) :=
  ordinary_pool_union_injOn eta heta _ _
    (fun b => fullSeeds_typed eta heta b x) (fun b => fullSeeds_typed eta heta b y) a
    (fun _ h _ hm => fullSeeds_successor_downward eta heta a x h hm)
    (fun _ h _ hm => fullSeeds_successor_downward eta heta a y h hm)

theorem mainPool_ordinary_injective (x : (fsTower eta).Carrier) (a : Ordinal.{0}) :
    Function.Injective (fun r : mainPool eta heta x (a+1) =>
      fun c : mainPool eta heta x a => ordinaryRaw r.val c.val) := by
  intro r s hrs
  apply Subtype.ext
  apply ordinary_role_injOn (level eta (a+1)) (mainPool eta heta x (a+1))
    (mainPool eta heta x a) ?_ ?_ r.property s.property hrs
  · intro u hu
    exact pool_successor_collection eta heta _ (fun b => fullSeeds_typed eta heta b x) a hu
  · intro u hu c hc
    exact pool_member_lower eta heta _ a
      (fun _ h _ hm => fullSeeds_successor_downward eta heta a x h hm) hu hc

theorem column_ordinary_injective (x : (fsTower eta).Carrier)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta) (n : ℕ) :
    Function.Injective (fun r : Column eta heta lam hlam (lowerPools eta heta x lam) n =>
      fun c : mainPool eta heta x (Frame.rho eta lam hlam n) =>
        ordinaryRaw (encodeColumn eta heta lam hlam (lowerPools eta heta x lam) n r) c.val) := by
  intro r s hrs
  apply encodeColumn_injective eta heta lam hlam _ htop n
  let P := range (encodeColumn eta heta lam hlam (lowerPools eta heta x lam) n)
  have hdelta : Frame.delta eta lam hlam n = Frame.rho eta lam hlam n + 1 := by
    simp only [Frame.delta,Frame.rho,add_assoc,one_add_one_eq_two]
  apply ordinary_role_injOn (level eta (Frame.delta eta lam hlam n)) P
    (mainPool eta heta x (Frame.rho eta lam hlam n)) ?_ ?_ (mem_range_self r) (mem_range_self s) hrs
  · rintro u ⟨c,rfl⟩
    have hu := (pool_encodeColumn eta heta (fun b => fullSeeds eta heta b x) lam hlam htop n c).1
    have hm := pool_successor_collection eta heta (fun b => fullSeeds eta heta b x)
      (fun b => fullSeeds_typed eta heta b x) (Frame.rho eta lam hlam n) (by simpa only [hdelta] using hu)
    simpa only [hdelta] using hm
  · rintro u ⟨c,rfl⟩ v hv
    exact (pool_encodeColumn eta heta (fun b => fullSeeds eta heta b x) lam hlam htop n c).2 v hv

theorem column_ordinary_column_separating (x : (fsTower eta).Carrier)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta) (n : ℕ) :
    Function.Injective (fun c : mainPool eta heta x (Frame.rho eta lam hlam n) =>
      fun r : Column eta heta lam hlam (lowerPools eta heta x lam) n =>
        ordinaryRaw (encodeColumn eta heta lam hlam (lowerPools eta heta x lam) n r) c.val) := by
  intro c d hcd
  let r := freshColumn eta heta lam hlam (lowerPools eta heta x lam) n (.inr (.inr c))
  have hquery := congrFun hcd r
  have heq : d.val = c.val := by
    by_contra hne
    simp only [r,encodeColumn_fresh,encodeNew,ordinaryRaw,member_singleton,
      decide_true,decide_eq_false hne] at hquery
    contradiction
  exact Subtype.ext heq.symm

theorem ordinaryMatrix_row_injective (x : (fsTower eta).Carrier) (e : OrdinaryRole eta) :
    Function.Injective (ordinaryMatrix eta heta x e) := by
  cases e with
  | inl a =>
    intro r s hrs
    have hr : r.val ∈ mainPool eta heta x (Frame.rank a.val+1) := by
      simpa only [rowSort,raw,mainSort,Frame.rank_ofOrdinal] using r.property
    have hs : s.val ∈ mainPool eta heta x (Frame.rank a.val+1) := by
      simpa only [rowSort,raw,mainSort,Frame.rank_ofOrdinal] using s.property
    have he := mainPool_ordinary_injective eta heta x (Frame.rank a.val)
      (a₁ := ⟨r.val,hr⟩) (a₂ := ⟨s.val,hs⟩) hrs
    exact Subtype.ext (congrArg
      (fun u : mainPool eta heta x (Frame.rank a.val+1) => u.val) he)
  | inr c =>
    rcases c with ⟨lam,n⟩
    intro r s hrs
    apply column_ordinary_injective eta heta x (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val) n
    funext c
    let c' : raw eta heta x (colSort eta (.inr (lam,n))) := ⟨c.val,by
      simpa only [colSort,raw,mainSort,Frame.rank_ofOrdinal] using c.property⟩
    exact congrFun hrs c'

theorem ordinaryMatrix_column_separating (x : (fsTower eta).Carrier) (e : OrdinaryRole eta) :
    Function.Injective (fun c => fun r => ordinaryMatrix eta heta x e r c) := by
  cases e with
  | inl a =>
    intro c d hcd
    apply ordinary_pool_column_separating eta heta (fun b => fullSeeds eta heta b x) (Frame.rank a.val)
    funext r
    let r' : raw eta heta x (rowSort eta (.inl a)) := ⟨r.val,by
      simpa only [rowSort,raw,mainSort,Frame.rank_ofOrdinal,mainPool] using r.property⟩
    exact congrFun hcd r'
  | inr c =>
    rcases c with ⟨lam,n⟩
    intro c d hcd
    have hc : c.val ∈ mainPool eta heta x (Frame.rho eta (Frame.rank lam.val) lam.property n) := by
      simpa only [colSort,raw,mainSort,Frame.rank_ofOrdinal] using c.property
    have hd : d.val ∈ mainPool eta heta x (Frame.rho eta (Frame.rank lam.val) lam.property n) := by
      simpa only [colSort,raw,mainSort,Frame.rank_ofOrdinal] using d.property
    have he := column_ordinary_column_separating eta heta x (Frame.rank lam.val) lam.property
      (Frame.rank_le_top lam.val) n (a₁ := ⟨c.val,hc⟩) (a₂ := ⟨d.val,hd⟩) hcd
    exact Subtype.ext (congrArg
      (fun u : mainPool eta heta x (Frame.rho eta (Frame.rank lam.val) lam.property n) => u.val) he)

theorem mainPool_limit_subset_limitSet (x : (fsTower eta).Carrier)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    mainPool eta heta x lam ⊆ LimitSet eta heta lam hlam (lowerPools eta heta x lam) := by
  intro u hu
  rw [mainPool,pool_limit eta heta _ lam hlam] at hu
  rcases hu with hs | hf
  · exact fullSeeds_limit_downward eta heta lam hlam x hs
  · obtain ⟨A,hA,rfl⟩ := (mem_finiteImages_iff _ _ _).mp hf
    exact Or.inr ⟨A,rfl,hA⟩

def localLimitRow (x : (fsTower eta).Carrier) (lam : LimitIndex eta)
    (r : raw eta heta x (.inl lam.val)) :
    LimitRow eta heta (Frame.rank lam.val) lam.property (lowerPools eta heta x (Frame.rank lam.val)) :=
  (exists_rowObject_of_mem_limitSet eta heta _ lam.property _ (Frame.rank_le_top lam.val)
    (mainPool_limit_subset_limitSet eta heta x _ lam.property r.property)).choose

theorem rowObject_localLimitRow (x : (fsTower eta).Carrier) (lam : LimitIndex eta)
    (r : raw eta heta x (.inl lam.val)) :
    rowObject eta heta _ lam.property _ (Frame.rank_le_top lam.val) (localLimitRow eta heta x lam r) = r.val :=
  (exists_rowObject_of_mem_limitSet eta heta _ lam.property _ (Frame.rank_le_top lam.val)
    (mainPool_limit_subset_limitSet eta heta x _ lam.property r.property)).choose_spec

theorem limitProfile_local (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (r : raw eta heta x (.inl lam.val)) (c : raw eta heta x (.inr (lam,n))) :
    limitProfile eta heta x lam n r c =
      profile eta heta _ lam.property _ n (localLimitRow eta heta x lam r) c := by
  have h := ambientProfile_restricted eta heta _ lam.property (Frame.rank_le_top lam.val)
    (ambientLower eta heta x _) n (localLimitRow eta heta x lam r) c
  rw [rowObject_localLimitRow] at h
  exact h

theorem limitProfile_full_injective (x : (fsTower eta).Carrier) (lam : LimitIndex eta) :
    Function.Injective (fun r => fun n => limitProfile eta heta x lam n r) := by
  intro r s hrs
  have hl : (fun n => profile eta heta _ lam.property _ n (localLimitRow eta heta x lam r)) =
      (fun n => profile eta heta _ lam.property _ n (localLimitRow eta heta x lam s)) := by
    funext n c
    exact (limitProfile_local eta heta x lam n r c).symm.trans
      ((congrFun (congrFun hrs n) c).trans (limitProfile_local eta heta x lam n s c))
  have he := fullProfile_injective eta heta _ lam.property _ hl
  apply Subtype.ext
  exact (rowObject_localLimitRow eta heta x lam r).symm.trans
    ((congrArg (rowObject eta heta _ lam.property _ (Frame.rank_le_top lam.val)) he).trans
      (rowObject_localLimitRow eta heta x lam s))

def limitPropagate (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ) :
    raw eta heta x (.inr (lam,n)) → raw eta heta x (.inr (lam,n+1)) :=
  propagate eta heta _ lam.property (lowerPools eta heta x _) n

theorem limitProfile_propagate (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (r : raw eta heta x (.inl lam.val)) (c : raw eta heta x (.inr (lam,n))) :
    limitProfile eta heta x lam (n+1) r (limitPropagate eta heta x lam n c) =
      limitProfile eta heta x lam n r c := by
  rw [limitProfile_local,limitProfile_local]
  exact profile_propagate eta heta _ lam.property _ n _ c

theorem limitProfile_column_separating (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ) :
    Function.Injective (fun c => fun r => limitProfile eta heta x lam n r c) :=
  pool_profile_column_separating eta heta (fun b => fullSeeds eta heta b x)
    (fun b => fullSeeds_typed eta heta b x) _ lam.property (Frame.rank_le_top lam.val) n

end FSCofinality.CosetConstruction.TokenModel
