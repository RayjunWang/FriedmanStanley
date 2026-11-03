import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.W.Basic
import Mathlib.Tactic

noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RawObjects

/-- Small, distinct set-theoretic tags. These need not be von Neumann ordinals. -/
def natTag : ℕ → ZFSet.{0}
  | 0 => ∅
  | n+1 => {natTag n}

theorem natTag_injective : Function.Injective natTag := by
  intro n
  induction n with
  | zero =>
    intro m h
    cases m with
    | zero => rfl
    | succ m =>
      have hm : natTag m ∈ (∅ : ZFSet.{0}) := by
        change natTag m ∈ natTag 0
        rw [h]
        exact ZFSet.mem_singleton.mpr rfl
      exact False.elim (ZFSet.notMem_empty _ hm)
  | succ n ih =>
    intro m h
    cases m with
    | zero =>
      have hn : natTag n ∈ (∅ : ZFSet.{0}) := by
        change natTag n ∈ natTag 0
        rw [← h]
        exact ZFSet.mem_singleton.mpr rfl
      exact False.elim (ZFSet.notMem_empty _ hn)
    | succ m => exact congrArg Nat.succ (ih (ZFSet.singleton_inj.mp h))

def graph (f : ℕ → ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.range (fun n => ZFSet.pair (natTag n) (f n))

theorem graph_injective : Function.Injective graph := by
  intro f g h
  funext n
  have hn : ZFSet.pair (natTag n) (f n) ∈ graph g := by
    rw [← h]
    exact ZFSet.mem_range_self n
  obtain ⟨m,hm⟩ := ZFSet.mem_range.mp hn
  obtain ⟨hidx,hval⟩ := ZFSet.pair_injective hm
  have hmn : m = n := natTag_injective hidx
  subst m
  exact hval.symm

def boolTag (b : Bool) : ZFSet.{0} := natTag (if b then 1 else 0)

theorem boolTag_injective : Function.Injective boolTag := by
  intro b c h
  have hnat := natTag_injective h
  cases b <;> cases c <;> simp_all [boolTag]

def record (kind layer : ℕ) (payload : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.pair (natTag kind) (ZFSet.pair (natTag layer) payload)

@[simp] theorem record_eq_iff {k l k' l' : ℕ} {x y : ZFSet.{0}} :
    record k l x = record k' l' y ↔ k = k' ∧ l = l' ∧ x = y := by
  simp only [record,ZFSet.pair_inj,natTag_injective.eq_iff]

/-- The branching positions are always finite or countably infinite.
Thus raw codes, unlike the auxiliary ZFC semantic universe, live in Type 0. -/
inductive Shape (Layer : Type) where
  | sourceAtom : (ℕ → Bool) → Shape Layer
  | extraAtom : ℕ → Shape Layer
  | empty : Layer → Shape Layer
  | collection : Layer → Shape Layer
  | source : Layer → Shape Layer
  | filler : Layer → (n : ℕ) → (Fin n → ℕ) → Shape Layer

def Positions {Layer : Type} : Shape Layer → Type
  | .sourceAtom _ => Empty
  | .extraAtom _ => Empty
  | .empty _ => Empty
  | .collection _ => ℕ
  | .source _ => ℕ
  | .filler _ n _ => Fin n

abbrev RawCode (Layer : Type) := WType (@Positions Layer)

def semanticAlgebra {Layer : Type} (layerCode : Layer ↪ ℕ)
    (s : Σ a : Shape Layer, Positions a → ZFSet.{0}) : ZFSet.{0} :=
  match s with
  | ⟨.sourceAtom r,_⟩ => record 0 0 (graph (fun n => boolTag (r n)))
  | ⟨.extraAtom n,_⟩ => record 1 0 (natTag n)
  | ⟨.empty l,_⟩ => record 2 (layerCode l) ∅
  | ⟨.collection l,f⟩ => record 2 (layerCode l) (ZFSet.range f)
  | ⟨.source l,f⟩ => record 3 (layerCode l) (graph f)
  | ⟨.filler l n tags,f⟩ => record 4 (layerCode l)
      (ZFSet.range (fun i : Fin n => ZFSet.pair (natTag (tags i)) (f i)))

def evalCode {Layer : Type} (layerCode : Layer ↪ ℕ) : RawCode Layer → ZFSet.{0} :=
  WType.elim _ (semanticAlgebra layerCode)

def codeSetoid {Layer : Type} (layerCode : Layer ↪ ℕ) : Setoid (RawCode Layer) :=
  Setoid.ker (evalCode layerCode)

/-- Semantic names are quotients of actual small codes. No standard Borel
structure is asserted on this semantic quotient. -/
def Object {Layer : Type} (layerCode : Layer ↪ ℕ) := Quotient (codeSetoid layerCode)

def eval {Layer : Type} {layerCode : Layer ↪ ℕ} : Object layerCode → ZFSet.{0} :=
  Quotient.lift (evalCode layerCode) (fun _ _ h => h)

theorem eval_injective {Layer : Type} {layerCode : Layer ↪ ℕ} :
    Function.Injective (eval (layerCode := layerCode)) := by
  intro x y h
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound h

@[simp] theorem eval_out {Layer : Type} {layerCode : Layer ↪ ℕ} (x : Object layerCode) :
    evalCode layerCode (Quotient.out x) = eval x := by
  exact congrArg eval (Quotient.out_eq x)

def make {Layer : Type} {layerCode : Layer ↪ ℕ} (a : Shape Layer)
    (f : Positions a → Object layerCode) : Object layerCode :=
  Quotient.mk _ (WType.mk a (fun i => Quotient.out (f i)))

theorem eval_make {Layer : Type} {layerCode : Layer ↪ ℕ} (a : Shape Layer)
    (f : Positions a → Object layerCode) :
    eval (make a f) = semanticAlgebra layerCode ⟨a,fun i => eval (f i)⟩ := by
  change semanticAlgebra layerCode ⟨a,fun i => evalCode layerCode (Quotient.out (f i))⟩ = _
  simp only [eval_out]

section Constructors
variable {Layer : Type} {layerCode : Layer ↪ ℕ}

def sourceAtom (r : ℕ → Bool) : Object layerCode := make (.sourceAtom r) Empty.elim
def extraAtom (n : ℕ) : Object layerCode := make (.extraAtom n) Empty.elim

def collection (l : Layer) (x : Option (ℕ → Object layerCode)) : Object layerCode :=
  match x with | none => make (.empty l) Empty.elim | some f => make (.collection l) f

def sourceSequence (l : Layer) (x : ℕ → Object layerCode) : Object layerCode :=
  make (.source l) x

def finiteFiller (l : Layer) (A : Finset (ℕ × Object layerCode)) : Object layerCode := by
  classical
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  exact make (.filler l (Fintype.card A) (fun i => (e i).val.1))
    (fun i => (e i).val.2)

@[simp] theorem eval_sourceAtom (r : ℕ → Bool) :
    eval (sourceAtom (layerCode := layerCode) r) = record 0 0 (graph (fun n => boolTag (r n))) := by
  exact eval_make _ _

@[simp] theorem eval_extraAtom (n : ℕ) :
    eval (extraAtom (layerCode := layerCode) n) = record 1 0 (natTag n) := by
  exact eval_make _ _

@[simp] theorem eval_collection_none (l : Layer) :
    eval (collection (layerCode := layerCode) l none) = record 2 (layerCode l) ∅ := by
  exact eval_make _ _

@[simp] theorem eval_collection_some (l : Layer) (f : ℕ → Object layerCode) :
    eval (collection l (some f)) = record 2 (layerCode l) (ZFSet.range (fun i => eval (f i))) := by
  exact eval_make _ _

@[simp] theorem eval_sourceSequence (l : Layer) (f : ℕ → Object layerCode) :
    eval (sourceSequence l f) = record 3 (layerCode l) (graph (fun i => eval (f i))) := by
  exact eval_make _ _

@[simp] theorem eval_finiteFiller (l : Layer) (A : Finset (ℕ × Object layerCode)) :
    eval (finiteFiller l A) = record 4 (layerCode l)
      (ZFSet.range (fun p : A => ZFSet.pair (natTag p.val.1) (eval p.val.2))) := by
  classical
  unfold finiteFiller
  rw [eval_make]
  change record 4 (layerCode l) (ZFSet.range _) = _
  congr 1
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨(Fintype.equivFin A).symm i,rfl⟩
  · rintro ⟨p,rfl⟩
    exact ⟨Fintype.equivFin A p,by simp⟩

theorem sourceAtom_injective : Function.Injective (sourceAtom (layerCode := layerCode)) := by
  intro r s h
  have hp := congrArg eval h
  simp only [eval_sourceAtom,record_eq_iff,true_and] at hp
  have hfun := graph_injective hp
  funext n
  exact boolTag_injective (congrFun hfun n)

theorem extraAtom_injective : Function.Injective (extraAtom (layerCode := layerCode)) := by
  intro n m h
  have hp := congrArg eval h
  simp only [eval_extraAtom,record_eq_iff,true_and] at hp
  exact natTag_injective hp

theorem sourceAtom_ne_extraAtom (r : ℕ → Bool) (n : ℕ) :
    sourceAtom (layerCode := layerCode) r ≠ extraAtom n := by
  intro h
  have hp := congrArg eval h
  simp only [eval_sourceAtom,eval_extraAtom,record_eq_iff] at hp
  exact Nat.zero_ne_add_one 0 hp.1

theorem sourceSequence_injective (l : Layer) :
    Function.Injective (sourceSequence (layerCode := layerCode) l) := by
  intro f g h
  have hp := congrArg eval h
  simp only [eval_sourceSequence,record_eq_iff,true_and] at hp
  have hfun := graph_injective hp
  funext n
  exact eval_injective (congrFun hfun n)

theorem finiteFiller_injective (l : Layer) :
    Function.Injective (finiteFiller (layerCode := layerCode) l) := by
  intro A B h
  have hp := congrArg eval h
  simp only [eval_finiteFiller,record_eq_iff,true_and] at hp
  ext p
  constructor
  · intro hpA
    have hm : ZFSet.pair (natTag p.1) (eval p.2) ∈
        ZFSet.range (fun q : B => ZFSet.pair (natTag q.val.1) (eval q.val.2)) := by
      rw [← hp]
      exact ZFSet.mem_range_self (⟨p,hpA⟩ : A)
    obtain ⟨q,hq⟩ := ZFSet.mem_range.mp hm
    obtain ⟨hidx,hobj⟩ := ZFSet.pair_injective hq
    have hqp : q.val = p := Prod.ext (natTag_injective hidx) (eval_injective hobj)
    exact hqp ▸ q.property
  · intro hpB
    have hm : ZFSet.pair (natTag p.1) (eval p.2) ∈
        ZFSet.range (fun q : A => ZFSet.pair (natTag q.val.1) (eval q.val.2)) := by
      rw [hp]
      exact ZFSet.mem_range_self (⟨p,hpB⟩ : B)
    obtain ⟨q,hq⟩ := ZFSet.mem_range.mp hm
    obtain ⟨hidx,hobj⟩ := ZFSet.pair_injective hq
    have hqp : q.val = p := Prod.ext (natTag_injective hidx) (eval_injective hobj)
    exact hqp ▸ q.property

theorem sourceSequence_ne_finiteFiller (l m : Layer)
    (f : ℕ → Object layerCode) (A : Finset (ℕ × Object layerCode)) :
    sourceSequence l f ≠ finiteFiller m A := by
  intro h
  have hp := congrArg eval h
  simp only [eval_sourceSequence,eval_finiteFiller,record_eq_iff] at hp
  exact (by decide : (3 : ℕ) ≠ 4) hp.1

/-- Ordinary membership in the countable-set payload of a successor object. -/
def Member (u x : Object layerCode) : Prop :=
  ∃ l : Layer, ∃ p : ZFSet.{0}, eval x = record 2 (layerCode l) p ∧ eval u ∈ p

@[simp] theorem member_collection_none (l : Layer) (u : Object layerCode) :
    ¬ Member u (collection l none) := by
  rintro ⟨m,p,hp,hm⟩
  rw [eval_collection_none] at hp
  have he : (∅ : ZFSet.{0}) = p := (record_eq_iff.mp hp).2.2
  exact ZFSet.notMem_empty _ (he ▸ hm)

@[simp] theorem member_collection_some (l : Layer) (f : ℕ → Object layerCode)
    (u : Object layerCode) : Member u (collection l (some f)) ↔ ∃ i, f i = u := by
  constructor
  · rintro ⟨m,p,hp,hm⟩
    rw [eval_collection_some] at hp
    have he := (record_eq_iff.mp hp).2.2
    rw [← he] at hm
    obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hm
    exact ⟨i,eval_injective hi⟩
  · rintro ⟨i,rfl⟩
    exact ⟨l,_,eval_collection_some l f,ZFSet.mem_range_self i⟩

def singleton (l : Layer) (u : Object layerCode) : Object layerCode :=
  collection l (some (fun _ => u))

def doubleton (l : Layer) (u v : Object layerCode) : Object layerCode :=
  collection l (some (fun n => if n = 0 then u else v))

def finiteCollection (l : Layer) (A : Finset (Object layerCode)) : Object layerCode := by
  classical
  exact if h : A.Nonempty then
    letI : Nonempty A := ⟨⟨h.choose,h.choose_spec⟩⟩
    collection l (some (fun n => ((exists_surjective_nat A).choose n).val))
  else collection l none

@[simp] theorem member_finiteCollection (l : Layer) (A : Finset (Object layerCode))
    (u : Object layerCode) : Member u (finiteCollection l A) ↔ u ∈ A := by
  classical
  by_cases h : A.Nonempty
  · letI : Nonempty A := ⟨⟨h.choose,h.choose_spec⟩⟩
    rw [finiteCollection,dif_pos h,member_collection_some]
    constructor
    · rintro ⟨i,rfl⟩
      exact ((exists_surjective_nat A).choose i).property
    · intro hu
      obtain ⟨i,hi⟩ := (exists_surjective_nat A).choose_spec (⟨u,hu⟩ : A)
      exact ⟨i,congrArg Subtype.val hi⟩
  · rw [finiteCollection,dif_neg h]
    simp only [member_collection_none,false_iff]
    intro hu
    exact h ⟨u,hu⟩

theorem finiteCollection_injective (l : Layer) :
    Function.Injective (finiteCollection (layerCode := layerCode) l) := by
  intro A B h
  ext u
  have hm : Member u (finiteCollection l A) ↔ Member u (finiteCollection l B) := by rw [h]
  simpa only [member_finiteCollection] using hm

theorem finiteCollection_is_collection (l : Layer) (A : Finset (Object layerCode)) :
    ∃ x, finiteCollection l A = collection l x := by
  classical
  unfold finiteCollection
  split <;> exact ⟨_,rfl⟩

@[simp] theorem member_singleton (l : Layer) (u v : Object layerCode) :
    Member u (singleton l v) ↔ u = v := by
  simp only [singleton,member_collection_some,exists_const,eq_comm]

@[simp] theorem member_doubleton (l : Layer) (u v w : Object layerCode) :
    Member u (doubleton l v w) ↔ u = v ∨ u = w := by
  rw [doubleton,member_collection_some]
  constructor
  · rintro ⟨n,hn⟩
    by_cases h : n = 0
    · exact Or.inl (by simpa only [if_pos h] using hn.symm)
    · exact Or.inr (by simpa only [if_neg h] using hn.symm)
  · rintro (h | h)
    · exact ⟨0,by simpa only [if_pos rfl] using h.symm⟩
    · exact ⟨1,by simpa using h.symm⟩

@[simp] theorem eval_singleton (l : Layer) (u : Object layerCode) :
    eval (singleton l u) = record 2 (layerCode l) {eval u} := by
  rw [singleton,eval_collection_some]
  apply congrArg (record 2 (layerCode l))
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_range,ZFSet.mem_singleton,exists_const,eq_comm]

@[simp] theorem eval_doubleton (l : Layer) (u v : Object layerCode) :
    eval (doubleton l u v) = record 2 (layerCode l) {eval u,eval v} := by
  rw [doubleton,eval_collection_some]
  apply congrArg (record 2 (layerCode l))
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_range,ZFSet.mem_pair]
  constructor
  · rintro ⟨n,rfl⟩
    by_cases h : n = 0 <;> simp [h]
  · rintro (h | h)
    · exact ⟨0,by simpa only [if_pos rfl] using h.symm⟩
    · exact ⟨1,by simpa using h.symm⟩

@[simp] theorem singleton_eq_iff (l : Layer) (u v : Object layerCode) :
    singleton l u = singleton l v ↔ u = v := by
  constructor
  · intro h
    have hp := congrArg eval h
    simp only [eval_singleton,record_eq_iff,true_and,ZFSet.singleton_inj] at hp
    exact eval_injective hp
  · exact congrArg (singleton l)

theorem doubleton_comm (l : Layer) (u v : Object layerCode) :
    doubleton l u v = doubleton l v u := by
  apply eval_injective
  rw [eval_doubleton,eval_doubleton]
  apply congrArg (record 2 (layerCode l))
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_pair,or_comm]

theorem doubleton_eq_iff (l : Layer) (a b c d : Object layerCode) :
    doubleton l a b = doubleton l c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a = c ∨ a = d := (member_doubleton l a c d).mp (by rw [← h]; simp)
    have hb : b = c ∨ b = d := (member_doubleton l b c d).mp (by rw [← h]; simp)
    have hc : c = a ∨ c = b := (member_doubleton l c a b).mp (by rw [h]; simp)
    have hd : d = a ∨ d = b := (member_doubleton l d a b).mp (by rw [h]; simp)
    aesop
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact doubleton_comm l _ _

theorem singleton_ne_doubleton (l : Layer) (a b u : Object layerCode) (hab : a ≠ b) :
    singleton l a ≠ doubleton l b u := by
  intro h
  have hm : Member b (singleton l a) := by rw [h]; simp
  exact hab ((member_singleton l b a).mp hm).symm

/-- The manuscript's two-member tag code, using the next two successor layers. -/
def Enc (inner outer : Layer) (tag base u : Object layerCode) : Object layerCode :=
  doubleton outer (singleton inner tag) (doubleton inner base u)

theorem Enc_injective (inner outer : Layer) (tag base : Object layerCode) (ht : tag ≠ base) :
    Function.Injective (Enc inner outer tag base) := by
  intro u v h
  rcases (doubleton_eq_iff outer _ _ _ _).mp h with ⟨hs,hp⟩ | ⟨hcross,_⟩
  · rcases (doubleton_eq_iff inner _ _ _ _).mp hp with ⟨_,huv⟩ | ⟨hbv,hub⟩
    · exact huv
    · exact hub.trans hbv
  · exact False.elim (singleton_ne_doubleton inner tag base v ht hcross)

theorem Enc_ne (inner outer : Layer) (tag tag' base u v : Object layerCode)
    (ht : tag ≠ base) (htt : tag ≠ tag') :
    Enc inner outer tag base u ≠ Enc inner outer tag' base v := by
  intro h
  rcases (doubleton_eq_iff outer _ _ _ _).mp h with ⟨hs,_⟩ | ⟨hcross,_⟩
  · exact htt ((singleton_eq_iff inner tag tag').mp hs)
  · exact singleton_ne_doubleton inner tag base v ht hcross

theorem Enc_member_iff (inner outer : Layer) (tag base u c : Object layerCode) :
    Member c (Enc inner outer tag base u) ↔
      c = singleton inner tag ∨ c = doubleton inner base u := member_doubleton _ _ _ _

theorem collection_ext (l : Layer) (x y : Option (ℕ → Object layerCode))
    (h : ∀ u, Member u (collection l x) ↔ Member u (collection l y)) :
    collection l x = collection l y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some g =>
      have hg : Member (g 0) (collection l (some g)) := (member_collection_some _ _ _).mpr ⟨0,rfl⟩
      exact False.elim (member_collection_none _ _ ((h _).mpr hg))
  | some f =>
    cases y with
    | none =>
      have hf : Member (f 0) (collection l (some f)) := (member_collection_some _ _ _).mpr ⟨0,rfl⟩
      exact False.elim (member_collection_none _ _ ((h _).mp hf))
    | some g =>
      apply eval_injective
      rw [eval_collection_some,eval_collection_some]
      apply congrArg (record 2 (layerCode l))
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_range]
      constructor
      · rintro ⟨i,rfl⟩
        have hf : Member (f i) (collection l (some f)) := (member_collection_some _ _ _).mpr ⟨i,rfl⟩
        obtain ⟨j,hj⟩ := (member_collection_some _ _ _).mp ((h _).mp hf)
        exact ⟨j,congrArg eval hj⟩
      · rintro ⟨j,rfl⟩
        have hg : Member (g j) (collection l (some g)) := (member_collection_some _ _ _).mpr ⟨j,rfl⟩
        obtain ⟨i,hi⟩ := (member_collection_some _ _ _).mp ((h _).mpr hg)
        exact ⟨i,congrArg eval hi⟩

theorem collection_some_eq_iff (l : Layer) (f g : ℕ → Object layerCode) :
    collection l (some f) = collection l (some g) ↔
      (∀ i, ∃ j, f i = g j) ∧ (∀ j, ∃ i, f i = g j) := by
  constructor
  · intro h
    constructor
    · intro i
      have hm : Member (f i) (collection l (some g)) := by rw [← h]; simp
      obtain ⟨j,hj⟩ := (member_collection_some _ _ _).mp hm
      exact ⟨j,hj.symm⟩
    · intro j
      have hm : Member (g j) (collection l (some f)) := by rw [h]; simp
      exact (member_collection_some _ _ _).mp hm
  · rintro ⟨hfg,hgf⟩
    apply collection_ext
    intro u
    simp only [member_collection_some]
    constructor
    · rintro ⟨i,rfl⟩
      obtain ⟨j,hj⟩ := hfg i
      exact ⟨j,hj.symm⟩
    · rintro ⟨j,rfl⟩
      exact hgf j

theorem Enc_ne_singleton (inner outer : Layer) (tag base u v : Object layerCode)
    (ht : tag ≠ base) : Enc inner outer tag base u ≠ singleton outer v := by
  intro h
  have hs : singleton inner tag = v := (member_singleton _ _ _).mp (by rw [← h]; simp [Enc])
  have hp : doubleton inner base u = v := (member_singleton _ _ _).mp (by rw [← h]; simp [Enc])
  exact singleton_ne_doubleton inner tag base u ht (hs.trans hp.symm)

@[simp] theorem finiteCollection_singleton (l : Layer) (u : Object layerCode) :
    finiteCollection l {u} = singleton l u := by
  classical
  obtain ⟨x,hx⟩ := finiteCollection_is_collection l {u}
  rw [hx]
  apply collection_ext
  intro z
  rw [← hx,member_finiteCollection]
  simp only [singleton,member_collection_some,Finset.mem_singleton,exists_const,eq_comm]

@[simp] theorem finiteCollection_doubleton (l : Layer) (u v : Object layerCode) :
    finiteCollection l {u,v} = doubleton l u v := by
  classical
  obtain ⟨x,hx⟩ := finiteCollection_is_collection l {u,v}
  rw [hx]
  apply collection_ext
  intro z
  rw [← hx,member_finiteCollection]
  change z ∈ ({u,v} : Finset (Object layerCode)) ↔ Member z (doubleton l u v)
  rw [member_doubleton]
  simp only [Finset.mem_insert,Finset.mem_singleton]

end Constructors

end FSCofinality.RawObjects
