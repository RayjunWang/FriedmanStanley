import FSCofinalityProof.GenericTablesHistories

noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

abbrev Token (U : Type*) := List U × ℕ

def history {U : Type*} (v : Token U) : FullHistory v.1.length :=
  (fullLabelEquiv v.1.length).symm v.2

def ofHistory {U : Type*} (t : List U) (h : FullHistory t.length) : Token U :=
  (t,fullLabelEquiv t.length h)

@[simp] theorem history_ofHistory {U : Type*} (t : List U) (h : FullHistory t.length) :
    history (ofHistory t h) = h := (fullLabelEquiv t.length).symm_apply_apply h

def activeLength {U : Type*} (v : Token U) (n : ℕ) : ℕ :=
  ((history v).val.activeTimes n).length

def activeTuple {U : Type*} (v : Token U) (n : ℕ) : List U := v.1.take (activeLength v n)

def localCode {U : Type*} (v : Token U) (n : ℕ) : ℕ := (history v).val.localCode n

theorem activeLength_mono {U : Type*} (v : Token U) (n : ℕ) :
    activeLength v n ≤ activeLength v (n+1) := by
  unfold activeLength
  rw [activeTimes_previous (history v).val n]
  exact List.length_filter_le _ _

theorem activeTuple_eq_full {U : Type*} (v : Token U) (n : ℕ)
    (hn : ∀ a ∈ (history v).val.activation, a ≤ n) : activeTuple v n = v.1 := by
  unfold activeTuple activeLength
  rw [activeTimes_eq_self _ _ hn,(history v).property,List.take_length]

def ordinaryEdge {U V : Type*} (A : Table) (e : ℕ) (R : U → V → Bool)
    (v : Token U) (w : Token V) : Bool :=
  A (e,contextMatrix (v.1.map R) w.1,w.2,v.2)

/-- A lower pool with every finite context present decodes ordinary tokens
exactly whenever the actual raw rows are distinct. -/
theorem ordinary_neighborhood_injective {U V : Type*} {D : ℕ → Set ℕ} {A : Table}
    (hA : GenericOn D A) (e : ℕ) (R : U → V → Bool) (hR : Function.Injective R) :
    Function.Injective (fun v : Token U => fun w : Token V => ordinaryEdge A e R v w) := by
  intro v w heq
  have h : (v.1.map R,v.2) = (w.1.map R,w.2) := by
    apply pointed_context_injective hA e
    exact heq
  apply Prod.ext
  · exact (List.map_injective_iff.mpr hR) (congrArg Prod.fst h)
  · exact congrArg (fun p : List (V → Bool) × ℕ => p.2) h

section Limit
variable {U : Type*} {Col : ℕ → Type*}
variable (profile : ∀ n, U → Col n → Bool)

def activeProfiles (v : Token U) (n : ℕ) : List (Col n → Bool) :=
  (activeTuple v n).map (profile n)

def R (n : ℕ) (v w : Token U) : Prop :=
  localCode v n = localCode w n ∧ activeProfiles profile v n = activeProfiles profile w n

theorem R_equivalence (n : ℕ) : Equivalence (R profile n) := by
  refine ⟨fun v => ⟨rfl,rfl⟩,fun h => ⟨h.1.symm,h.2.symm⟩,
    fun h h' => ⟨h.1.trans h'.1,h.2.trans h'.2⟩⟩

def branchEdge (A : Table) (e n : ℕ) (v : Token U) (w : Token (Col n)) : Bool :=
  A (e,contextMatrix (activeProfiles profile v n) w.1,w.2,localCode v n)

theorem R_iff_branch_neighborhood {D : ℕ → Set ℕ} {A : Table}
    (hA : GenericOn D A) (e n : ℕ) (v w : Token U) :
    R profile n v w ↔ ∀ c : Token (Col n),
      branchEdge profile A e n v c = branchEdge profile A e n w c := by
  constructor
  · rintro ⟨hl,hp⟩ c
    simp only [branchEdge,hl,hp]
  · intro h
    have heq : (activeProfiles profile v n,localCode v n) =
        (activeProfiles profile w n,localCode w n) := by
      apply pointed_context_injective hA e
      funext c
      exact h c
    exact ⟨congrArg Prod.snd heq,congrArg Prod.fst heq⟩

variable (j : ∀ n, Col n → Col (n+1))
variable (propagate : ∀ n u c, profile (n+1) u (j n c) = profile n u c)
include j propagate

theorem activeProfiles_previous (v : Token U) (n : ℕ) :
    activeProfiles profile v n =
      ((activeProfiles profile v (n+1)).map (fun f c => f (j n c))).take (activeLength v n) := by
  have hp : (fun u c => profile (n+1) u (j n c)) = profile n := by
    funext u c
    exact propagate n u c
  simp only [activeProfiles,activeTuple,List.map_take,List.map_map,Function.comp_def]
  rw [hp,List.take_take,Nat.min_eq_left (activeLength_mono v n)]

theorem R_refines (n : ℕ) {v w : Token U} (h : R profile (n+1) v w) : R profile n v w := by
  have hl : localCode v n = localCode w n :=
    localCode_refines (history v).val (history w).val n h.1
  have hlen : activeLength v n = activeLength w n := by
    have hh := (localCode_eq_iff (history v).val (history w).val n).mp hl
    exact congrArg (fun p : List ℕ × List ℕ => p.1.length) hh
  refine ⟨hl,?_⟩
  rw [activeProfiles_previous profile j propagate v n,
    activeProfiles_previous profile j propagate w n,h.2,hlen]

theorem profile_eq_of_later (u v : U) {m n : ℕ} (hmn : m ≤ n)
    (h : profile n u = profile n v) : profile m u = profile m v := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact h
  | succ n IH =>
    by_cases hm : m = n+1
    · rw [hm]
      exact h
    · apply IH (by omega)
      funext c
      have hh := congrFun h (j n c)
      simpa only [propagate] using hh

/-- Finite activation does not lose earlier profile information: propagation
recovers all levels before a slot's activation. -/
theorem all_R_separate (hinj : Function.Injective (fun u : U => fun n => profile n u))
    {v w : Token U} (h : ∀ n, R profile n v w) : v = w := by
  have hhist : (history v).val = (history w).val :=
    all_localCodes_injective (funext (fun n => (h n).1))
  let N := (history v).val.activation.sum + (history w).val.activation.sum
  have hfullv (n : ℕ) (hn : N ≤ n) : activeTuple v n = v.1 := by
    apply activeTuple_eq_full
    intro a ha
    exact (List.le_sum_of_mem ha).trans ((Nat.le_add_right _ _).trans hn)
  have hfullw (n : ℕ) (hn : N ≤ n) : activeTuple w n = w.1 := by
    apply activeTuple_eq_full
    intro a ha
    exact (List.le_sum_of_mem ha).trans ((Nat.le_add_left _ _).trans hn)
  have hp (n : ℕ) (hn : N ≤ n) : v.1.map (profile n) = w.1.map (profile n) := by
    simpa only [activeProfiles,hfullv n hn,hfullw n hn] using (h n).2
  have hlen : v.1.length = w.1.length := by
    have hh := congrArg List.length (hp N le_rfl)
    simpa only [List.length_map] using hh
  have htuple : v.1 = w.1 := by
    apply List.ext_getElem hlen
    intro i hi hi'
    apply hinj
    funext n
    let m := max N n
    apply profile_eq_of_later profile j propagate _ _ (show n ≤ m from le_max_right _ _)
    have hh := congrArg (fun t : List (Col m → Bool) => t[i]?) (hp m (le_max_left _ _))
    simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi',Option.map_some,Option.some.injEq] using hh
  apply Prod.ext htuple
  cases v with | mk tv kv =>
    cases w with | mk tw kw =>
      change tv = tw at htuple
      subst tw
      have hh : history (tv,kv) = history (tv,kw) := Subtype.ext hhist
      have hh' := congrArg (fullLabelEquiv tv.length) hh
      simpa only [history,Equiv.apply_symm_apply] using hh'

end Limit
end FSCofinality.Tokens
