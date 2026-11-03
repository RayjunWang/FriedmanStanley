import FSCofinalityProof.ParameterClassOrbits
import Mathlib.Topology.Algebra.Group.Basic

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology TopologicalSpace MeasureTheory

namespace FSCofinality.ParameterSequences

abbrev Code := ℕ → PermutationGroup
abbrev Letter := ℕ × Bool

def evalLetter (d : Code) (a : Letter) : PermutationGroup :=
  if a.2 then d a.1 else (d a.1)⁻¹

def evalWord (d : Code) : List Letter → PermutationGroup
  | [] => 1
  | a::w => evalLetter d a * evalWord d w

theorem continuous_evalLetter (a : Letter) : Continuous (fun d : Code => evalLetter d a) := by
  rcases a with ⟨i,b⟩
  cases b
  · exact (continuous_apply i).inv
  · exact continuous_apply i

theorem continuous_evalWord (w : List Letter) : Continuous (fun d : Code => evalWord d w) := by
  induction w with
  | nil => exact continuous_const
  | cons a w ih => exact (continuous_evalLetter a).mul ih

/-- Agreement of both permutation coordinates on one finite initial segment. -/
def Approx (p q : PermutationGroup) (n : ℕ) : Prop :=
  ∀ i : Fin n, (permutationCoordinates p).1 i = (permutationCoordinates q).1 i ∧
    (permutationCoordinates p).2 i = (permutationCoordinates q).2 i

theorem approx_self (p : PermutationGroup) (n : ℕ) : Approx p p n := fun _ => ⟨rfl,rfl⟩

theorem isOpen_approx (p : PermutationGroup) (n : ℕ) : IsOpen {q | Approx q p n} := by
  have hf (i : Fin n) : IsOpen {q : PermutationGroup |
      (permutationCoordinates q).1 i = (permutationCoordinates p).1 i} :=
    (isOpen_discrete {(permutationCoordinates p).1 i}).preimage
      ((continuous_apply (i : ℕ)).comp continuous_permutationCoordinates.fst)
  have hi (i : Fin n) : IsOpen {q : PermutationGroup |
      (permutationCoordinates q).2 i = (permutationCoordinates p).2 i} :=
    (isOpen_discrete {(permutationCoordinates p).2 i}).preimage
      ((continuous_apply (i : ℕ)).comp continuous_permutationCoordinates.snd)
  simpa only [Approx,setOf_forall,setOf_and] using
    isOpen_iInter_of_finite (fun i => (hf i).inter (hi i))

theorem measurableSet_approx (n : ℕ) :
    MeasurableSet {pq : PermutationGroup × PermutationGroup | Approx pq.1 pq.2 n} := by
  have hf (i : Fin n) : MeasurableSet {pq : PermutationGroup × PermutationGroup |
      (permutationCoordinates pq.1).1 i = (permutationCoordinates pq.2).1 i} :=
    measurableSet_eq_fun
      (((continuous_apply (i : ℕ)).comp continuous_permutationCoordinates.fst).measurable.comp measurable_fst)
      (((continuous_apply (i : ℕ)).comp continuous_permutationCoordinates.fst).measurable.comp measurable_snd)
  have hi (i : Fin n) : MeasurableSet {pq : PermutationGroup × PermutationGroup |
      (permutationCoordinates pq.1).2 i = (permutationCoordinates pq.2).2 i} :=
    measurableSet_eq_fun
      (((continuous_apply (i : ℕ)).comp continuous_permutationCoordinates.snd).measurable.comp measurable_fst)
      (((continuous_apply (i : ℕ)).comp continuous_permutationCoordinates.snd).measurable.comp measurable_snd)
  simpa only [Approx,setOf_forall,setOf_and] using MeasurableSet.iInter (fun i => (hf i).inter (hi i))

/-- The range is dense in the group it generates, expressed entirely by
countably many finite-coordinate tests. -/
def Valid (d : Code) : Prop :=
  ∀ w : List Letter, ∀ n : ℕ, ∃ j : ℕ, Approx (d j) (evalWord d w) n

theorem measurableSet_valid : MeasurableSet {d : Code | Valid d} := by
  simp only [Valid,setOf_forall,setOf_exists]
  apply MeasurableSet.iInter
  intro w
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro j
  exact (measurableSet_approx n).preimage
    ((measurable_pi_apply j).prodMk (continuous_evalWord w).measurable)

theorem mem_closure_range_iff (d : Code) (p : PermutationGroup) :
    p ∈ closure (range d) ↔ ∀ n, ∃ j, Approx (d j) p n := by
  constructor
  · intro hp n
    obtain ⟨q,hq,⟨j,rfl⟩⟩ := mem_closure_iff.mp hp {q | Approx q p n}
      (isOpen_approx p n) (approx_self p n)
    exact ⟨j,hq⟩
  · intro h
    choose j hj using h
    have hf : Tendsto (fun n => (permutationCoordinates (d (j n))).1) atTop
        (𝓝 (permutationCoordinates p).1) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (i+1)] with n hn
      exact (hj n ⟨i,by omega⟩).1.symm
    have hi : Tendsto (fun n => (permutationCoordinates (d (j n))).2) atTop
        (𝓝 (permutationCoordinates p).2) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (i+1)] with n hn
      exact (hj n ⟨i,by omega⟩).2.symm
    have ht : Tendsto (fun n => d (j n)) atTop (𝓝 p) := by
      rw [nhds_induced]
      exact tendsto_comap_iff.mpr (hf.prodMk_nhds hi)
    exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall (fun n => subset_closure ⟨j n,rfl⟩))

theorem evalWord_mem_closure (d : Code) (hd : Valid d) (w : List Letter) :
    evalWord d w ∈ closure (range d) := (mem_closure_range_iff d _).mpr (hd w)

def closureSubgroup (d : Code) (hd : Valid d) : Subgroup PermutationGroup where
  carrier := closure (range d)
  one_mem' := by simpa only [evalWord] using evalWord_mem_closure d hd []
  mul_mem' := by
    intro x y hx hy
    have hdd (i j : ℕ) : d i * d j ∈ closure (range d) := by
      simpa [evalWord,evalLetter] using
        evalWord_mem_closure d hd [(i,true),(j,true)]
    have hxj (j : ℕ) : x * d j ∈ closure (range d) := by
      apply closure_minimal (t := {z : PermutationGroup | z * d j ∈ closure (range d)}) ?_
        (isClosed_closure.preimage (continuous_id.mul continuous_const)) hx
      rintro z ⟨i,rfl⟩
      exact hdd i j
    apply closure_minimal (t := {z : PermutationGroup | x * z ∈ closure (range d)}) ?_
      (isClosed_closure.preimage (continuous_const.mul continuous_id)) hy
    rintro z ⟨j,rfl⟩
    exact hxj j
  inv_mem' := by
    intro x hx
    apply closure_minimal (t := {z : PermutationGroup | z⁻¹ ∈ closure (range d)}) ?_
      (isClosed_closure.preimage continuous_inv) hx
    rintro z ⟨i,rfl⟩
    simpa [evalWord,evalLetter] using
      evalWord_mem_closure d hd [(i,false)]

def generatedClosure (d : Code) : Subgroup PermutationGroup :=
  (Subgroup.closure (range d)).topologicalClosure

theorem isClosed_generatedClosure (d : Code) :
    IsClosed (generatedClosure d : Set PermutationGroup) := Subgroup.isClosed_topologicalClosure _

theorem generatedClosure_eq_closure_range (d : Code) (hd : Valid d) :
    (generatedClosure d : Set PermutationGroup) = closure (range d) := by
  apply le_antisymm
  · have hgen : Subgroup.closure (range d) ≤ closureSubgroup d hd :=
      (Subgroup.closure_le _).mpr subset_closure
    exact Subgroup.topologicalClosure_minimal _ hgen isClosed_closure
  · apply closure_minimal ?_ (isClosed_generatedClosure d)
    intro p hp
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_closure hp)

theorem canonicalStructure_eq_sequenceStructure (d : Code) (hd : Valid d) :
    OrbitCoding.canonicalStructure (generatedClosure d) = OrbitCoding.sequenceStructure d := by
  funext ⟨s,a⟩
  simp only [OrbitCoding.canonicalStructure,OrbitCoding.sequenceStructure,decide_eq_decide]
  constructor
  · rintro ⟨g,hg⟩
    have hp : g.val ∈ closure (range d) := by
      rw [← generatedClosure_eq_closure_range d hd]
      exact g.property
    let n := Finset.univ.sup s.2 + 1
    obtain ⟨j,hj⟩ := (mem_closure_range_iff d g.val).mp hp n
    refine ⟨j,fun i => ?_⟩
    have hi : s.2 i < n := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
    exact (hj ⟨s.2 i,hi⟩).1.trans (hg i)
  · rintro ⟨j,hj⟩
    exact ⟨⟨d j,Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨j,rfl⟩)⟩,hj⟩

theorem evalWord_mem (H : Subgroup PermutationGroup) (d : Code)
    (hd : ∀ j, d j ∈ H) (w : List Letter) : evalWord d w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons a w ih =>
    apply H.mul_mem ?_ ih
    rcases a with ⟨i,b⟩
    cases b
    · exact H.inv_mem (hd i)
    · exact hd i

theorem valid_of_dense (H : Subgroup PermutationGroup) (d : ℕ → H) (hd : DenseRange d) :
    Valid (fun j => (d j).val) := by
  intro w n
  let p := evalWord (fun j => (d j).val) w
  have hp : p ∈ H := evalWord_mem H _ (fun j => (d j).property) w
  have ho : IsOpen {q : H | Approx q.val p n} :=
    (isOpen_approx p n).preimage continuous_subtype_val
  obtain ⟨j,hj⟩ := hd.exists_mem_open ho ⟨⟨p,hp⟩,approx_self p n⟩
  exact ⟨j,hj⟩

theorem generatedClosure_eq_of_dense (H : Subgroup PermutationGroup)
    (hH : IsClosed (H : Set PermutationGroup)) (d : ℕ → H) (hd : DenseRange d) :
    generatedClosure (fun j => (d j).val) = H := by
  have hcl : closure (range (fun j => (d j).val)) = (H : Set PermutationGroup) := by
    apply le_antisymm
    · exact closure_minimal (by rintro p ⟨j,rfl⟩; exact (d j).property) hH
    · intro p hp
      apply (mem_closure_range_iff _ p).mpr
      intro n
      have ho : IsOpen {q : H | Approx q.val p n} :=
        (isOpen_approx p n).preimage continuous_subtype_val
      exact hd.exists_mem_open ho ⟨⟨p,hp⟩,approx_self p n⟩
  apply SetLike.coe_injective
  rw [generatedClosure_eq_closure_range _ (valid_of_dense H d hd),hcl]

/-- Every actual closed subgroup is captured by a valid sequence code. -/
theorem exists_valid_sequence (H : Subgroup PermutationGroup)
    (hH : IsClosed (H : Set PermutationGroup)) :
    ∃ d : Code, Valid d ∧ generatedClosure d = H := by
  letI : PolishSpace H := hH.polishSpace
  let d : ℕ → H := denseSeq H
  have hd : DenseRange d := denseRange_denseSeq H
  exact ⟨fun j => (d j).val,valid_of_dense H d hd,generatedClosure_eq_of_dense H hH d hd⟩

theorem finite_orbit_iff (d : Code) (hd : Valid d) (r : ℕ) (s a : Fin r → ℕ) :
    (∃ g : generatedClosure d, ∀ i, OrbitCoding.perm g.val (s i) = a i) ↔
      ∃ j : ℕ, ∀ i, OrbitCoding.perm (d j) (s i) = a i := by
  constructor
  · rintro ⟨g,hg⟩
    have hp : g.val ∈ closure (range d) := by
      rw [← generatedClosure_eq_closure_range d hd]
      exact g.property
    let n := Finset.univ.sup s + 1
    obtain ⟨j,hj⟩ := (mem_closure_range_iff d g.val).mp hp n
    refine ⟨j,fun i => ?_⟩
    have hi : s i < n := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
    exact (hj ⟨s i,hi⟩).1.trans (hg i)
  · rintro ⟨j,hj⟩
    exact ⟨⟨d j,Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨j,rfl⟩)⟩,hj⟩

theorem measurableSet_sequence_finite_orbit (r : ℕ) (s a : Fin r → ℕ) :
    MeasurableSet {d : Code | ∃ j : ℕ, ∀ i, OrbitCoding.perm (d j) (s i) = a i} := by
  simp only [setOf_exists,setOf_forall]
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq_fun
    ((OrbitCoding.continuous_apply (s i)).measurable.comp (measurable_pi_apply j)) measurable_const

abbrev ValidCode := {d : Code // Valid d}

instance : StandardBorelSpace ValidCode := measurableSet_valid.standardBorel

theorem measurableSet_finite_orbit (r : ℕ) (s a : Fin r → ℕ) :
    MeasurableSet {d : ValidCode | ∃ g : generatedClosure d.val,
      ∀ i, OrbitCoding.perm g.val (s i) = a i} := by
  have h := (measurableSet_sequence_finite_orbit r s a).preimage
    (f := fun d : ValidCode => d.val) measurable_subtype_coe
  convert h using 1
  ext d
  exact finite_orbit_iff d.val d.property r s a

def subgroupSequence (d : Code) : ℕ → generatedClosure d :=
  fun j => ⟨d j,Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨j,rfl⟩)⟩

theorem denseRange_subgroupSequence (d : Code) (hd : Valid d) :
    DenseRange (subgroupSequence d) := by
  change Dense (range (subgroupSequence d))
  apply Subtype.dense_iff.mpr
  have heq : ((fun q : generatedClosure d => q.val) '' range (subgroupSequence d)) = range d := by
    ext p
    constructor
    · rintro ⟨q,⟨j,rfl⟩,rfl⟩
      exact ⟨j,rfl⟩
    · rintro ⟨j,rfl⟩
      exact ⟨subgroupSequence d j,⟨j,rfl⟩,rfl⟩
  change (generatedClosure d : Set PermutationGroup) ⊆
    closure ((fun q : generatedClosure d => q.val) '' range (subgroupSequence d))
  rw [heq,← generatedClosure_eq_closure_range d hd]

theorem measurableSet_generatedClosure_membership :
    MeasurableSet {p : ValidCode × PermutationGroup | p.2 ∈ generatedClosure p.1.val} := by
  have htest (n j : ℕ) : MeasurableSet {p : ValidCode × PermutationGroup |
      Approx (p.1.val j) p.2 n} := by
    exact (measurableSet_approx n).preimage
      (f := fun p : ValidCode × PermutationGroup => (p.1.val j,p.2))
      ((((measurable_pi_apply j).comp measurable_subtype_coe).comp measurable_fst).prodMk measurable_snd)
  have hfull : MeasurableSet {p : ValidCode × PermutationGroup |
      ∀ n : ℕ, ∃ j : ℕ, Approx (p.1.val j) p.2 n} := by
    simpa only [setOf_forall,setOf_exists] using
      MeasurableSet.iInter (fun n => MeasurableSet.iUnion (htest n))
  convert hfull using 1
  ext p
  change p.2 ∈ (generatedClosure p.1.val : Set PermutationGroup) ↔
    ∀ n : ℕ, ∃ j : ℕ, Approx (p.1.val j) p.2 n
  rw [generatedClosure_eq_closure_range p.1.val p.1.property]
  exact mem_closure_range_iff p.1.val p.2

theorem measurable_canonicalStructure :
    Measurable (fun d : ValidCode => OrbitCoding.canonicalStructure (generatedClosure d.val)) := by
  have h := OrbitCoding.measurable_sequenceStructure.comp
    (measurable_subtype_coe : Measurable (fun d : ValidCode => d.val))
  convert h using 1
  funext d
  exact canonicalStructure_eq_sequenceStructure d.val d.property

theorem preserves_sequenceStructure_iff (d : Code) (hd : Valid d) (p : PermutationGroup) :
    (∀ (s : OrbitCoding.language.Symbol) (a : Fin (OrbitCoding.language.arity s) → ℕ),
      OrbitCoding.sequenceStructure d ⟨s,a⟩ =
        OrbitCoding.sequenceStructure d ⟨s,(OrbitCoding.perm p) ∘ a⟩) ↔
      p ∈ generatedClosure d := by
  rw [← canonicalStructure_eq_sequenceStructure d hd]
  exact OrbitCoding.preserves_canonicalStructure_iff _ (isClosed_generatedClosure d) p

end FSCofinality.ParameterSequences
