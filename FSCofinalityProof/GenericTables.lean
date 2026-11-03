import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology TopologicalSpace

namespace FSCofinality.GenericTables

/-- Both dimensions remain part of a finite Boolean matrix, including zero dimensions. -/
def BoolMatrix := Σ l : ℕ, Σ m : ℕ, Fin l → Fin m → Bool

instance : Countable BoolMatrix := by unfold BoolMatrix; infer_instance

abbrev Index := ℕ × BoolMatrix × ℕ × ℕ
abbrev Table := Index → Bool

structure Request where
  role : ℕ
  matrix : BoolMatrix
  side : Bool
  opposite : ℕ
  value : Bool

instance : Countable Request := by
  apply Function.Injective.countable (f := fun r : Request =>
    (r.role,r.matrix,r.side,r.opposite,r.value))
  intro r s h
  cases r
  cases s
  simpa only [Prod.mk.injEq,Request.mk.injEq] using h

def Request.key (r : Request) := (r.role,r.matrix,r.side,r.opposite)

/-- `false` varies the column label, `true` varies the row label. -/
def Request.index (r : Request) (z : ℕ) : Index :=
  if r.side then (r.role,r.matrix,r.opposite,z) else (r.role,r.matrix,z,r.opposite)

def Compatible (P : Finset Request) : Prop :=
  ∀ r ∈ P, ∀ s ∈ P, r.key = s.key → r.value = s.value

theorem Request.index_eq_of_key_eq {r s : Request} (h : r.key = s.key) (z : ℕ) :
    r.index z = s.index z := by
  cases r with | mk er mr sr or vr =>
    cases s with | mk es ms ss os vs =>
      simp only [Request.key,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl,rfl⟩
      rfl

theorem compatible_of_realization (A : Table) (P : Finset Request) (z : ℕ)
    (h : ∀ r ∈ P, A (r.index z) = r.value) : Compatible P := by
  intro r hr s hs hkey
  rw [← h r hr,← h s hs,Request.index_eq_of_key_eq hkey]

theorem index_eq_key {r s : Request} {z : ℕ}
    (hr : z ≠ r.opposite) (hs : z ≠ s.opposite)
    (h : r.index z = s.index z) : r.key = s.key := by
  cases r with | mk er mr sr or vr =>
    cases s with | mk es ms ss os vs =>
      cases sr <;> cases ss <;> simp_all [Request.index,Request.key]

def patternSet (P : Finset Request) (z : ℕ) : Set Table :=
  {A | ∀ r ∈ P, A (r.index z) = r.value}

theorem isOpen_patternSet (P : Finset Request) (z : ℕ) : IsOpen (patternSet P z) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [patternSet]
  | @insert r P hr IH =>
    have heq : patternSet (insert r P) z =
        {A | A (r.index z) = r.value} ∩ patternSet P z := by
      ext A
      simp [patternSet]
    rw [heq]
    exact ((isOpen_discrete ({r.value} : Set Bool)).preimage (continuous_apply _)).inter IH

def witnessSet (D : Set ℕ) (P : Finset Request) (N : ℕ) : Set Table :=
  {A | ∃ z ∈ D, N < z ∧ A ∈ patternSet P z}

theorem isOpen_witnessSet (D : Set ℕ) (P : Finset Request) (N : ℕ) :
    IsOpen (witnessSet D P N) := by
  classical
  have heq : witnessSet D P N = ⋃ z : ℕ,
      if z ∈ D ∧ N < z then patternSet P z else ∅ := by
    ext A
    simp only [witnessSet,mem_setOf_eq,mem_iUnion]
    constructor
    · rintro ⟨z,hz,hN,hA⟩
      exact ⟨z,by simpa [hz,hN] using hA⟩
    · rintro ⟨z,hz⟩
      by_cases h : z ∈ D ∧ N < z
      · exact ⟨z,h.1,h.2,by simpa [h] using hz⟩
      · simp [h] at hz
  rw [heq]
  apply isOpen_iUnion
  intro z
  split_ifs
  · exact isOpen_patternSet P z
  · exact isOpen_empty

def modify (A : Table) (P : Finset Request) (z : ℕ) : Table :=
  fun i => if h : ∃ r ∈ P, r.index z = i then (Classical.choose h).value else A i

theorem modify_pattern (A : Table) (P : Finset Request) (hP : Compatible P)
    (z : ℕ) (hz : ∀ r ∈ P, z ≠ r.opposite) : modify A P z ∈ patternSet P z := by
  intro r hr
  have hex : ∃ s ∈ P, s.index z = r.index z := ⟨r,hr,rfl⟩
  rw [modify,dif_pos hex]
  obtain ⟨hs,hindex⟩ := Classical.choose_spec hex
  exact hP _ hs r hr (index_eq_key (hz _ hs) (hz r hr) hindex)

theorem index_varying_label (r : Request) (z : ℕ) :
    z = (r.index z).2.2.1 ∨ z = (r.index z).2.2.2 := by
  cases h : r.side <;> simp [Request.index,h]

theorem dense_witnessSet (D : Set ℕ) (hD : D.Infinite)
    (P : Finset Request) (hP : Compatible P) (N : ℕ) : Dense (witnessSet D P N) := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨A,hA⟩ := hUne
  obtain ⟨I,V,hV,hsub⟩ := isOpen_pi_iff.mp hU A hA
  let bad := I.image (fun i : Index => i.2.2.1) ∪ I.image (fun i : Index => i.2.2.2) ∪
    P.image Request.opposite ∪ Finset.range (N+1)
  obtain ⟨z,hz,hfresh⟩ := hD.exists_notMem_finset bad
  have hzold (i : Index) (hi : i ∈ I) :
      z ≠ i.2.2.1 ∧ z ≠ i.2.2.2 := by
    constructor <;> intro h
    · apply hfresh
      simp only [bad,Finset.mem_union,Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl ⟨i,hi,h.symm⟩))
    · apply hfresh
      simp only [bad,Finset.mem_union,Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨i,hi,h.symm⟩))
  have hzreq (r : Request) (hr : r ∈ P) : z ≠ r.opposite := by
    intro h
    apply hfresh
    simp only [bad,Finset.mem_union,Finset.mem_image]
    exact Or.inl (Or.inr ⟨r,hr,h.symm⟩)
  have hN : N < z := by
    by_contra h
    have hh : z ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    exact hfresh (Finset.mem_union_right _ hh)
  have hsame (i : Index) (hi : i ∈ I) : modify A P z i = A i := by
    have hnone : ¬ ∃ r ∈ P, r.index z = i := by
      rintro ⟨r,hr,heq⟩
      have hv := index_varying_label r z
      rw [heq] at hv
      exact hv.elim (hzold i hi).1 (hzold i hi).2
    simp only [modify,dif_neg hnone]
  refine ⟨modify A P z,?_,z,hz,hN,modify_pattern A P hP z hzreq⟩
  apply hsub
  intro i hi
  rw [hsame i hi]
  exact (hV i hi).2

/-- One table simultaneously realizes all finite consistent requests, along
every member of a prescribed countable family of infinite label sets. -/
def GenericOn (D : ℕ → Set ℕ) (A : Table) : Prop :=
  ∀ P : Finset Request, Compatible P → ∀ i N : ℕ,
    ∃ z ∈ D i, N < z ∧ ∀ r ∈ P, A (r.index z) = r.value

theorem exists_generic (D : ℕ → Set ℕ) (hD : ∀ i, (D i).Infinite) :
    ∃ A : Table, GenericOn D A := by
  letI : PolishSpace Table := {
    toSecondCountableTopology := inferInstance
    toIsCompletelyMetrizableSpace := inferInstance }
  let Req := {P : Finset Request // Compatible P} × ℕ × ℕ
  have hd : Dense (⋂ q : Req, witnessSet (D q.2.1) q.1.val q.2.2) :=
    dense_iInter_of_isOpen (fun q => isOpen_witnessSet _ _ _)
      (fun q => dense_witnessSet _ (hD _) _ q.1.property _)
  obtain ⟨A,hA⟩ := hd.nonempty
  refine ⟨A,fun P hP i N => ?_⟩
  exact mem_iInter.mp hA (⟨P,hP⟩,i,N)

end FSCofinality.GenericTables
