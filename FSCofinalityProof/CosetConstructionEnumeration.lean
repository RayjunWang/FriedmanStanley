import FSCofinalityProof.CosetConstructionPoolCodes
import Mathlib.Data.Nat.Nth
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory

namespace FSCofinality.CosetConstruction

theorem measurable_nat_count {X : Type} [MeasurableSpace X]
    (P : X → ℕ → Prop) (hP : ∀ n, MeasurableSet {x | P x n}) (k : ℕ) :
    Measurable (fun x => Nat.count (P x) k) := by
  induction k with
  | zero => simpa only [Nat.count_zero] using
      (measurable_const : Measurable (fun _ : X => (0 : ℕ)))
  | succ k ih =>
    simp only [Nat.count_succ]
    exact ih.add (Measurable.ite (hP k) measurable_const measurable_const)

theorem measurable_nat_nth {X : Type} [MeasurableSpace X]
    (P : X → ℕ → Prop) (hP : ∀ n, MeasurableSet {x | P x n})
    (hinf : ∀ x, {n | P x n}.Infinite) (k : ℕ) :
    Measurable (fun x => Nat.nth (P x) k) := by
  apply measurable_to_countable'
  intro n
  have hcount := (measurable_nat_count P hP n) (measurableSet_singleton k)
  convert (hP n).inter hcount using 1
  ext x
  change Nat.nth (P x) k = n ↔ P x n ∧ Nat.count (P x) n = k
  constructor
  · intro h
    exact ⟨h ▸ Nat.nth_mem_of_infinite (hinf x) k,
      h ▸ Nat.count_nth_of_infinite (hinf x) k⟩
  · rintro ⟨hp,hcount⟩
    rw [←hcount]
    exact Nat.nth_count hp

def FirstOccurrence {Z : Type} (F : ℕ → Option Z) (n : ℕ) : Prop :=
  F n ≠ none ∧ ∀ m < n, F m ≠ F n

theorem firstOccurrence_some {Z : Type} (F : ℕ → Option Z) {u : Z}
    (h : ∃ n, F n = some u) :
    ∃ n, FirstOccurrence F n ∧ F n = some u := by
  let n := Nat.find h
  have hn : F n = some u := Nat.find_spec h
  refine ⟨n,⟨?_,?_⟩,hn⟩
  · rw [hn]
    exact Option.some_ne_none _
  · intro m hm heq
    exact (Nat.find_min h hm) (heq.trans hn)

theorem firstOccurrence_injOn {Z : Type} (base : Z) (F : ℕ → Option Z) :
    Set.InjOn (fun n => (F n).getD base) {n | FirstOccurrence F n} := by
  intro m hm n hn heq
  have hvalue : F m = F n := by
    cases hfm : F m with
    | none => exact False.elim (hm.1 hfm)
    | some u =>
      cases hfn : F n with
      | none => exact False.elim (hn.1 hfn)
      | some v =>
        have huv : u = v := by simpa only [hfm,hfn,Option.getD_some] using heq
        exact congrArg some huv
  exact le_antisymm (le_of_not_gt (fun hlt => hm.2 n hlt hvalue.symm))
    (le_of_not_gt (fun hlt => hn.2 m hlt hvalue))

theorem firstOccurrence_infinite {Z : Type} (base : Z) (F : ℕ → Option Z)
    (hinf : {u | ∃ n, F n = some u}.Infinite) : {n | FirstOccurrence F n}.Infinite := by
  intro hfin
  have hsub : {u | ∃ n, F n = some u} ⊆
      (fun n => (F n).getD base) '' {n | FirstOccurrence F n} := by
    intro u hu
    obtain ⟨n,hn,hvalue⟩ := firstOccurrence_some F hu
    exact ⟨n,hn,by simp only [hvalue,Option.getD_some]⟩
  exact hinf ((hfin.image _).subset hsub)

theorem measurableSet_firstOccurrence {X Z : Type} [MeasurableSpace X]
    (F : ℕ → X → Option Z)
    (hnone : ∀ n, MeasurableSet {x | F n x = none})
    (heq : ∀ m n, MeasurableSet {x | F m x = F n x}) (n : ℕ) :
    MeasurableSet {x | FirstOccurrence (fun m => F m x) n} := by
  simp only [FirstOccurrence,setOf_and,setOf_forall]
  exact (hnone n).compl.inter (MeasurableSet.iInter (fun m =>
    MeasurableSet.iInter (fun _ => (heq m n).compl)))

def enumerateValues {Z : Type} (base : Z) (F : ℕ → Option Z) (k : ℕ) : Z :=
  (F (Nat.nth (FirstOccurrence F) k)).getD base

theorem enumerateValues_injective {Z : Type} (base : Z) (F : ℕ → Option Z)
    (hinf : {u | ∃ n, F n = some u}.Infinite) :
    Function.Injective (enumerateValues base F) := by
  have hg := firstOccurrence_infinite base F hinf
  intro m n h
  apply Nat.nth_injective hg
  exact firstOccurrence_injOn base F (Nat.nth_mem_of_infinite hg m)
    (Nat.nth_mem_of_infinite hg n) h

theorem enumerateValues_range {Z : Type} (base : Z) (F : ℕ → Option Z)
    (hinf : {u | ∃ n, F n = some u}.Infinite) :
    Set.range (enumerateValues base F) = {u | ∃ n, F n = some u} := by
  have hg := firstOccurrence_infinite base F hinf
  ext u
  constructor
  · rintro ⟨k,rfl⟩
    have hgood := Nat.nth_mem_of_infinite hg k
    cases hv : F (Nat.nth (FirstOccurrence F) k) with
    | none => exact False.elim (hgood.1 hv)
    | some z => exact ⟨Nat.nth (FirstOccurrence F) k,by
        simpa only [enumerateValues,hv,Option.getD_some] using hv⟩
  · intro hu
    obtain ⟨n,hn,hvalue⟩ := firstOccurrence_some F hu
    obtain ⟨k,hk⟩ := (Nat.range_nth_of_infinite hg).symm.subset hn
    exact ⟨k,by simp only [enumerateValues,hk,hvalue,Option.getD_some]⟩

end FSCofinality.CosetConstruction
