import Definitions.Def_FSCofinalityTrees20261102
import FSCofinalityProof.StructuresBasics
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory TopologicalSpace

namespace FSCofinality.PartialIso

/-- Agreement of complete atomic diagrams on a finite correspondence.
Repeated entries are permitted; equality agreement makes the induced
correspondence a partial bijection. Nullary symbols are included. -/
def AtomicCompatible {L : CountableRelationalLanguage} (M N : Structures L)
    (R : Set (ℕ × ℕ)) : Prop :=
  (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 ↔ p.2 = q.2) ∧
  ∀ (s : L.Symbol) (a : Fin (L.arity s) → ℕ × ℕ),
    (∀ i, a i ∈ R) → M ⟨s,fun i => (a i).1⟩ = N ⟨s,fun i => (a i).2⟩

theorem AtomicCompatible.mono {L : CountableRelationalLanguage} {M N : Structures L}
    {R S : Set (ℕ × ℕ)} (h : AtomicCompatible M N S) (hRS : R ⊆ S) :
    AtomicCompatible M N R :=
  ⟨fun p hp q hq => h.1 p (hRS hp) q (hRS hq),
    fun s a ha => h.2 s a (fun i => hRS (ha i))⟩

/-- Even stages ensure domain coverage, odd stages ensure range coverage. -/
def scheduledPair (k a : ℕ) : ℕ × ℕ :=
  if k % 2 = 0 then (k/2,a) else (a,k/2)

@[simp] theorem scheduledPair_even (i a : ℕ) : scheduledPair (2*i) a = (i,a) := by
  simp [scheduledPair]

@[simp] theorem scheduledPair_odd (i a : ℕ) : scheduledPair (2*i+1) a = (a,i) := by
  simp [scheduledPair]
  omega

def pairsFrom : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | k, a :: s => scheduledPair k a :: pairsFrom (k+1) s

theorem pairsFrom_append (k : ℕ) (s t : List ℕ) :
    pairsFrom k (s ++ t) = pairsFrom k s ++ pairsFrom (k+s.length) t := by
  induction s generalizing k with
  | nil => simp [pairsFrom]
  | cons a s IH =>
      simp only [List.cons_append,pairsFrom,List.length_cons]
      rw [IH]
      simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem pairsFrom_ofFn {n : ℕ} (k : ℕ) (f : Fin n → ℕ) :
    pairsFrom k (List.ofFn f) = List.ofFn (fun i : Fin n => scheduledPair (k+i.val) (f i)) := by
  induction n generalizing k with
  | zero => simp [pairsFrom]
  | succ n IH =>
      rw [List.ofFn_succ,pairsFrom,IH,List.ofFn_succ]
      congr 1
      apply congrArg List.ofFn
      funext i
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def attemptTree {L : CountableRelationalLanguage} (M N : Structures L) :
    RootedTrees.TreeSpace where
  val := fun s => decide (AtomicCompatible M N {p | p ∈ pairsFrom 0 s})
  property := by
    intro s n hs
    apply of_decide_eq_true at hs
    apply decide_eq_true
    apply hs.mono
    intro p hp
    simpa only [pairsFrom_append,List.mem_append,mem_setOf_eq] using Or.inl hp

def initialSegment (b : ℕ → ℕ) (n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => b i.val)

theorem scheduledPair_mem_prefix (b : ℕ → ℕ) {k n : ℕ} (hk : k < n) :
    scheduledPair k (b k) ∈ pairsFrom 0 (initialSegment b n) := by
  rw [initialSegment,pairsFrom_ofFn]
  exact List.mem_ofFn.mpr ⟨⟨k,hk⟩,by simp⟩

theorem compatible_of_branch {L : CountableRelationalLanguage} {M N : Structures L}
    {b : ℕ → ℕ} (hb : ∀ n, attemptTree M N (initialSegment b n) = true) (n : ℕ) :
    AtomicCompatible M N {p | p ∈ pairsFrom 0 (initialSegment b n)} :=
  of_decide_eq_true (hb n)

theorem isomorphic_of_branch {L : CountableRelationalLanguage} {M N : Structures L}
    (b : ℕ → ℕ) (hb : ∀ n, attemptTree M N (initialSegment b n) = true) : Isomorphic M N := by
  let f : ℕ → ℕ := fun i => b (2*i)
  let g : ℕ → ℕ := fun i => b (2*i+1)
  have hpair (i : ℕ) {n : ℕ} (hn : 2*i < n) :
      (i,f i) ∈ pairsFrom 0 (initialSegment b n) := by
    simpa only [scheduledPair_even,f] using scheduledPair_mem_prefix b hn
  have hipair (i : ℕ) {n : ℕ} (hn : 2*i+1 < n) :
      (g i,i) ∈ pairsFrom 0 (initialSegment b n) := by
    simpa only [scheduledPair_odd,g] using scheduledPair_mem_prefix b hn
  have hgf (i : ℕ) : g (f i) = i := by
    let n := max (2*i) (2*(f i)+1)+1
    exact ((compatible_of_branch hb n).1 (i,f i) (hpair i (by omega))
      (g (f i),f i) (hipair (f i) (by omega))).mpr rfl |>.symm
  have hfg (i : ℕ) : f (g i) = i := by
    let n := max (2*(g i)) (2*i+1)+1
    exact ((compatible_of_branch hb n).1 (g i,f (g i)) (hpair (g i) (by omega))
      (g i,i) (hipair i (by omega))).mp rfl
  let e : ℕ ≃ ℕ := ⟨f,g,hgf,hfg⟩
  refine ⟨e,fun s a => ?_⟩
  let n : ℕ := (Finset.univ.sup (fun i : Fin (L.arity s) => 2*(a i)))+1
  exact (compatible_of_branch hb n).2 s (fun i => (a i,f (a i)))
    (fun i => hpair (a i) (by
      exact Nat.lt_succ_of_le (Finset.le_sup
        (f := fun i : Fin (L.arity s) => 2*(a i)) (Finset.mem_univ i))))

theorem compatible_graph {L : CountableRelationalLanguage} {M N : Structures L}
    (e : ℕ ≃ ℕ) (he : ∀ s a, M ⟨s,a⟩ = N ⟨s,e ∘ a⟩)
    {R : Set (ℕ × ℕ)} (hR : ∀ p ∈ R, e p.1 = p.2) : AtomicCompatible M N R := by
  refine ⟨?_,?_⟩
  · intro p hp q hq
    rw [← hR p hp,← hR q hq]
    exact e.injective.eq_iff.symm
  · intro s a ha
    have h := he s (fun i => (a i).1)
    have ht : (fun i => (a i).2) = e ∘ (fun i => (a i).1) :=
      funext (fun i => (hR (a i) (ha i)).symm)
    rwa [ht]

theorem branch_of_isomorphic {L : CountableRelationalLanguage} {M N : Structures L}
    (h : Isomorphic M N) :
    ∃ b : ℕ → ℕ, ∀ n, attemptTree M N (initialSegment b n) = true := by
  obtain ⟨e,he⟩ := h
  let b : ℕ → ℕ := fun k => if k % 2 = 0 then e (k/2) else e.symm (k/2)
  refine ⟨b,fun n => ?_⟩
  apply decide_eq_true
  apply compatible_graph e he
  intro p hp
  rw [initialSegment,pairsFrom_ofFn] at hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  simp only [Nat.zero_add]
  dsimp only [scheduledPair,b]
  split_ifs <;> simp

theorem branch_iff_isomorphic {L : CountableRelationalLanguage} (M N : Structures L) :
    (∃ b : ℕ → ℕ, ∀ n, attemptTree M N (initialSegment b n) = true) ↔ Isomorphic M N :=
  ⟨fun ⟨b,hb⟩ => isomorphic_of_branch b hb,branch_of_isomorphic⟩

theorem measurableSet_atomicCompatible {L : CountableRelationalLanguage}
    (R : Set (ℕ × ℕ)) :
    MeasurableSet {p : Structures L × Structures L | AtomicCompatible p.1 p.2 R} := by
  have heq : MeasurableSet {p : Structures L × Structures L |
      ∀ u ∈ R, ∀ v ∈ R, u.1 = v.1 ↔ u.2 = v.2} := by
    by_cases h : ∀ u ∈ R, ∀ v ∈ R, u.1 = v.1 ↔ u.2 = v.2 <;> simp [h]
  unfold AtomicCompatible
  rw [setOf_and]
  apply heq.inter
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro s
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro ha
  let c₁ : Coordinate L := ⟨s,fun i => (a i).1⟩
  let c₂ : Coordinate L := ⟨s,fun i => (a i).2⟩
  have hc₁ : Continuous (fun M : Structures L => M c₁) := _root_.continuous_apply c₁
  have hc₂ : Continuous (fun M : Structures L => M c₂) := _root_.continuous_apply c₂
  exact measurableSet_eq_fun (hc₁.comp continuous_fst).measurable
    (hc₂.comp continuous_snd).measurable

/-- The tree of all scheduled partial-isomorphism attempts depends
Borel measurably on the pair of structures. -/
theorem measurable_attemptTree {L : CountableRelationalLanguage} :
    Measurable (fun p : Structures L × Structures L => attemptTree p.1 p.2) := by
  have hemb : MeasurableEmbedding
      (fun T : RootedTrees.TreeSpace => T.val) :=
    (show Topology.IsClosedEmbedding (fun T : RootedTrees.TreeSpace => T.val) from
      RootedTrees.isClosed_prefixClosed.isClosedEmbedding_subtypeVal).measurableEmbedding
  apply hemb.measurable_comp_iff.mp
  change Measurable (fun p : Structures L × Structures L =>
    fun s : RootedTrees.Node => decide (AtomicCompatible p.1 p.2 {q | q ∈ pairsFrom 0 s}))
  apply measurable_pi_iff.mpr
  intro s
  exact Measurable.ite (measurableSet_atomicCompatible {q | q ∈ pairsFrom 0 s})
    measurable_const measurable_const

end FSCofinality.PartialIso

