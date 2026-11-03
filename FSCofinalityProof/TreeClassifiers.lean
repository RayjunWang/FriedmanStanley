import FSCofinalityProof.TreeIsomorphisms
import FSCofinalityProof.TreeChildClassification
import FSCofinalityProof.HierarchyProducts
import FSCofinalityProof.MultisetClosure

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order MeasureTheory

namespace FSCofinality.RootedTrees

/-- A total Borel invariant on all trees which is complete on one bounded
well-founded domain. Its definition uses no test for belonging to that domain. -/
structure Classifier (a : Ordinal.{0}) where
  stage : Ordinal.{0}
  countable : stage < Ordinal.omega 1
  code : TreeSpace → (fsTower stage).Carrier
  measurable_code : Measurable code
  invariant : ∀ T U, Isomorphic T U → (fsTower stage).rel (code T) (code U)
  reflects : ∀ T U, BoundedTree T a → BoundedTree U a →
    (fsTower stage).rel (code T) (code U) → Isomorphic T U

def Classifier.relation {a : Ordinal.{0}} (C : Classifier a) : CodedRelation where
  Carrier := TreeSpace
  measurableSpace := inferInstance
  rel := fun T U => (fsTower C.stage).rel (C.code T) (C.code U)

theorem Classifier.relation_reduces {a : Ordinal.{0}} (C : Classifier a) :
    C.relation.Reduces (fsTower C.stage) :=
  ⟨C.code,C.measurable_code,fun _ _ => Iff.rfl⟩

theorem bounded_zero_eq_empty {T : TreeSpace} (h : BoundedTree T 0) : T = emptyTree := by
  apply (noRoot_iff_eq_empty T).mp
  intro hr
  obtain ⟨rho,hrho,hdec⟩ := h
  exact (not_lt_of_ge zero_le) (hrho ⟨[],hr⟩)

def classifier_zero : Classifier 0 where
  stage := 0
  countable := (Cardinal.isSuccLimit_omega 1).pos
  code := fun _ => Classical.choice (regular_fsTower 0).nonempty
  measurable_code := measurable_const
  invariant := fun _ _ _ => (regular_fsTower 0).equivalence.refl _
  reflects := by
    intro T U hT hU h
    rw [bounded_zero_eq_empty hT,bounded_zero_eq_empty hU]
    exact isomorphic_refl _

/-- Successor construction from the exact rooted-tree multiset decomposition.
The caller supplies the separately proved padded-child decomposition. -/
theorem classifier_successor_of_decomposition {a : Ordinal.{0}} (C : Classifier a)
    (children : TreeSpace → ℕ → TreeSpace)
    (hchildren : ∀ i, Measurable (fun T => children T i))
    (hdecomp : ∀ T U, Isomorphic T U ↔ T [] = U [] ∧
      CountableMultisetRelation Isomorphic (children T) (children U))
    (hbound : ∀ T, BoundedTree T (a+1) → ∀ i, BoundedTree (children T i) a) :
    Nonempty (Classifier (a+1)) := by
  obtain ⟨b,hb,hmult⟩ := multisetJump_reduces_fsTower C.relation C.stage C.countable C.relation_reduces
  obtain ⟨f,hf,hfred⟩ := hmult
  obtain ⟨c,hc,hpair⟩ := binaryProduct_reduces_fsTower 0 b
    (Cardinal.isSuccLimit_omega 1).pos hb boolEquality_reduces_fsTower_zero (CodedRelation.Reduces.refl _)
  obtain ⟨g,hg,hgred⟩ := hpair
  refine ⟨⟨c,hc,fun T => g (T [],f (children T)),?_,?_,?_⟩⟩
  · exact hg.comp (((continuous_eval []).measurable).prodMk
      (hf.comp (measurable_pi_lambda _ hchildren)))
  · intro T U hTU
    obtain ⟨hroot,σ,hσ⟩ := (hdecomp T U).mp hTU
    apply (hgred _ _).mp
    refine ⟨hroot,?_⟩
    apply (hfred _ _).mp
    exact ⟨σ,fun i => C.invariant _ _ (hσ i)⟩
  · intro T U hT hU hTU
    have hp := (hgred _ _).mpr hTU
    obtain ⟨σ,hσ⟩ := (hfred _ _).mpr hp.2
    apply (hdecomp T U).mpr
    refine ⟨hp.1,σ,?_⟩
    intro i
    exact C.reflects _ _ (hbound T hT i) (hbound U hU (σ i)) (hσ i)

theorem classifier_limit (a : Ordinal.{0}) (ha : IsSuccLimit a) (hc : a < Ordinal.omega 1)
    (C : ∀ n, Classifier (fundamentalSequence a ha n)) : Nonempty (Classifier a) := by
  obtain ⟨b,hb,hprod⟩ := countableProduct_reduces_fsTower (fun n => fsTower (C n).stage)
    (fun n => (C n).stage) (fun n => (C n).countable) (fun _ => CodedRelation.Reduces.refl _)
  obtain ⟨f,hf,hfred⟩ := hprod
  refine ⟨⟨b,hb,fun T => f (fun n => (C n).code T),?_,?_,?_⟩⟩
  · exact hf.comp (measurable_pi_lambda _ (fun n => (C n).measurable_code))
  · intro T U hTU
    apply (hfred _ _).mp
    exact fun n => (C n).invariant T U hTU
  · intro T U hT hU hTU
    have hcoords := (hfred _ _).mpr hTU
    obtain ⟨t,ht,hTt⟩ := hT.exists_smaller_of_limit ha
    obtain ⟨u,hu,hUu⟩ := hU.exists_smaller_of_limit ha
    obtain ⟨n,hn⟩ := fundamentalSequence_cofinal a ha hc (max t u) (max_lt ht hu)
    exact (C n).reflects T U
      (hTt.mono ((le_max_left _ _).trans hn))
      (hUu.mono ((le_max_right _ _).trans hn)) (hcoords n)

theorem Classifier.treeRelation_reduces {a : Ordinal.{0}} (C : Classifier a) :
    (treeRelation a).Reduces (fsTower C.stage) := by
  refine ⟨fun T => C.code T.val,C.measurable_code.comp measurable_subtype_coe,?_⟩
  intro T U
  exact ⟨C.invariant _ _,C.reflects _ _ T.property U.property⟩

theorem classifier_successor {a : Ordinal.{0}} (C : Classifier a) :
    Nonempty (Classifier (a+1)) :=
  classifier_successor_of_decomposition C paddedChildren
    (fun i => (measurable_pi_apply i).comp measurable_paddedChildren)
    isomorphic_iff_paddedChildren (fun T hT i => hT.paddedChildren_of_succ i)

/-- Total classifiers exist at every countable bound. The limit step takes
all earlier invariants and uses no Borel test of well-founded rank. -/
theorem classifier_exists (a : Ordinal.{0}) : a < Ordinal.omega 1 → Nonempty (Classifier a) := by
  induction a using Ordinal.limitRecOn with
  | zero => intro _; exact ⟨classifier_zero⟩
  | add_one a ih =>
    intro ha
    exact classifier_successor (Classical.choice (ih (lt_trans (lt_add_one a) ha)))
  | limit a ha ih =>
    intro hc
    exact classifier_limit a ha hc (fun n => Classical.choice
      (ih (fundamentalSequence a ha n) (fundamentalSequence_lt a ha n)
        (lt_trans (fundamentalSequence_lt a ha n) hc)))

/-- The bounded rooted-tree hierarchy is cofinal below the concrete
product-limit Friedman--Stanley tower, with no ordinal-index identification. -/
theorem treeRelation_reduces_some_fsTower (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    ∃ b : Ordinal.{0}, b < Ordinal.omega 1 ∧ (treeRelation a).Reduces (fsTower b) := by
  obtain ⟨C⟩ := classifier_exists a ha
  exact ⟨C.stage,C.countable,C.treeRelation_reduces⟩

end FSCofinality.RootedTrees
