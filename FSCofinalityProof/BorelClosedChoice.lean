import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology TopologicalSpace Metric

namespace FSCofinality.ClosedChoice

def radius (n : ℕ) : ℝ := (1/2)^n

theorem radius_pos (n : ℕ) : 0 < radius n := pow_pos (by norm_num) _

theorem radius_succ (n : ℕ) : radius (n+1) = radius n / 2 := by
  simp [radius,pow_succ,div_eq_mul_inv]

section MetricChoice
variable {X : Type} [MetricSpace X] [SeparableSpace X] [Nonempty X]

def Near (S : Set X) (n k : ℕ) : Prop :=
  (S ∩ ball (denseSeq X k) (radius n / 4)).Nonempty

theorem exists_initial (S : Set X) (hne : S.Nonempty) : ∃ k, Near S 0 k := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨k,hk⟩ := (denseRange_denseSeq X).exists_dist_lt x
    (ε := radius 0 / 4) (by norm_num [radius])
  exact ⟨k,x,hx,hk⟩

theorem exists_next (S : Set X) (n k : ℕ) (hk : Near S n k) :
    ∃ j, Near S (n+1) j ∧ dist (denseSeq X j) (denseSeq X k) < radius n := by
  obtain ⟨x,hx,hxk⟩ := hk
  obtain ⟨j,hj⟩ := (denseRange_denseSeq X).exists_dist_lt x
    (div_pos (radius_pos (n+1)) (by norm_num : (0:ℝ)<4))
  refine ⟨j,⟨x,hx,hj⟩,?_⟩
  have htri := dist_triangle (denseSeq X j) x (denseSeq X k)
  have hxk' : dist x (denseSeq X k) < radius n / 4 := hxk
  rw [dist_comm] at hj
  rw [radius_succ] at hj
  have hp := radius_pos n
  linarith

def Next (S : Set X) (n k j : ℕ) : Prop :=
  (Near S (n+1) j ∧ dist (denseSeq X j) (denseSeq X k) < radius n) ∨ ¬ Near S n k

theorem exists_next_total (S : Set X) (n k : ℕ) : ∃ j, Next S n k j := by
  by_cases hk : Near S n k
  · obtain ⟨j,hj⟩ := exists_next S n k hk
    exact ⟨j,Or.inl hj⟩
  · exact ⟨0,Or.inr hk⟩

def nextIndex (S : Set X) (n k : ℕ) : ℕ := Nat.find (exists_next_total S n k)

theorem nextIndex_spec (S : Set X) (n k : ℕ) (hk : Near S n k) :
    Near S (n+1) (nextIndex S n k) ∧
      dist (denseSeq X (nextIndex S n k)) (denseSeq X k) < radius n :=
  (Nat.find_spec (exists_next_total S n k)).resolve_right (not_not.mpr hk)

def index (S : Set X) (hne : S.Nonempty) : ℕ → ℕ
  | 0 => Nat.find (exists_initial S hne)
  | n+1 => nextIndex S n (index S hne n)

theorem index_near (S : Set X) (hne : S.Nonempty) (n : ℕ) : Near S n (index S hne n) := by
  induction n with
  | zero => exact Nat.find_spec (exists_initial S hne)
  | succ n ih => exact (nextIndex_spec S n _ ih).1

theorem index_step (S : Set X) (hne : S.Nonempty) (n : ℕ) :
    dist (denseSeq X (index S hne (n+1))) (denseSeq X (index S hne n)) < radius n :=
  (nextIndex_spec S n _ (index_near S hne n)).2

theorem index_congr {S T : Set X} (hST : S=T) (hS : S.Nonempty) (hT : T.Nonempty) :
    index S hS = index T hT := by subst T; rfl

end MetricChoice

section Measurability
variable {P X : Type} [MeasurableSpace P] [MetricSpace X] [SeparableSpace X] [Nonempty X]
    (S : P → Set X)
    (hHit : ∀ U : Set X, IsOpen U → MeasurableSet {p | (S p ∩ U).Nonempty})

include hHit

theorem measurableSet_near (n k : ℕ) : MeasurableSet {p | Near (S p) n k} :=
  hHit _ isOpen_ball

theorem measurableSet_variable_near (n : ℕ) :
    MeasurableSet {p : P × ℕ | Near (S p.1) n p.2} := by
  have hf : Measurable (fun p : P × ℕ => decide (Near (S p.1) n p.2)) := by
    apply measurable_from_prod_countable_left
    intro k
    exact Measurable.ite (measurableSet_near S hHit n k) measurable_const measurable_const
  have hm := (measurableSet_singleton true).preimage hf
  change MeasurableSet {p : P × ℕ | decide (Near (S p.1) n p.2) = true} at hm
  simpa only [decide_eq_true_eq] using hm

theorem measurable_nextIndex (n : ℕ) :
    Measurable (fun p : P × ℕ => nextIndex (S p.1) n p.2) := by
  apply measurable_find (fun p : P × ℕ => exists_next_total (S p.1) n p.2)
  intro j
  have hj : MeasurableSet {p : P × ℕ | Near (S p.1) (n+1) j} :=
    (measurableSet_near S hHit (n+1) j).preimage measurable_fst
  have hd : MeasurableSet {p : P × ℕ |
      dist (denseSeq X j) (denseSeq X p.2) < radius n} :=
    measurableSet_lt ((measurable_of_countable
      (fun k => dist (denseSeq X j) (denseSeq X k))).comp measurable_snd) measurable_const
  exact (hj.inter hd).union (measurableSet_variable_near S hHit n).compl

theorem measurable_index (hne : ∀ p, (S p).Nonempty) (n : ℕ) :
    Measurable (fun p => index (S p) (hne p) n) := by
  induction n with
  | zero =>
    exact measurable_find (fun p => exists_initial (S p) (hne p))
      (measurableSet_near S hHit 0)
  | succ n ih => exact (measurable_nextIndex S hHit n).comp (measurable_id.prodMk ih)

end Measurability

/-- Closed-set selection using only Borel open-set hit tests. The selector
is canonical as a function of the closed set, so equal sets give equal
selected points. -/
theorem exists_measurable_closed_selector {P X : Type}
    [MeasurableSpace P] [MetricSpace X] [CompleteSpace X]
    [SeparableSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (S : P → Set X) (hne : ∀ p, (S p).Nonempty) (hclosed : ∀ p, IsClosed (S p))
    (hHit : ∀ U : Set X, IsOpen U → MeasurableSet {p | (S p ∩ U).Nonempty}) :
    ∃ f : P → X, Measurable f ∧ (∀ p, f p ∈ S p) ∧
      ∀ p q, S p = S q → f p = f q := by
  have hc (p : P) : CauchySeq (fun n => denseSeq X (index (S p) (hne p) n)) := by
    apply cauchySeq_of_le_geometric (1/2) 1 (by norm_num)
    intro n
    simpa only [one_mul,radius,dist_comm] using (index_step (S p) (hne p) n).le
  choose f hf using fun p => cauchySeq_tendsto_of_complete (hc p)
  refine ⟨f,?_,?_,?_⟩
  · apply measurable_of_tendsto_metrizable _ (tendsto_pi_nhds.mpr hf)
    intro n
    exact (measurable_of_countable (denseSeq X)).comp (measurable_index S hHit hne n)
  · intro p
    have hy (n : ℕ) : ∃ y : X, y ∈ S p ∧
        dist y (denseSeq X (index (S p) (hne p) n)) < radius n / 4 :=
      index_near (S p) (hne p) n
    choose y hyS hyDist using hy
    have hr : Tendsto (fun n => radius n / 4) atTop (𝓝 0) := by
      have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)
      simpa only [radius,zero_div] using hh.div_const 4
    have hd : Tendsto (fun n => dist (denseSeq X (index (S p) (hne p) n)) (y n))
        atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [dist_comm] using (hyDist n).le) hr
    exact (hclosed p).mem_of_tendsto ((hf p).congr_dist hd) (Eventually.of_forall hyS)
  · intro p q hpq
    have heq : (fun n => denseSeq X (index (S p) (hne p) n)) =
        (fun n => denseSeq X (index (S q) (hne q) n)) := by
      rw [index_congr hpq (hne p) (hne q)]
    have ht := hf q
    rw [← heq] at ht
    exact tendsto_nhds_unique (hf p) ht

end FSCofinality.ClosedChoice
