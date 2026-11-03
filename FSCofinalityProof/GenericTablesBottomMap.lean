import FSCofinalityProof.GenericTablesBottomCoordination
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import FSCofinalityProof.HierarchySigma

noncomputable section
open Set MeasureTheory

namespace FSCofinality.GenericTables.Bottom

/-- Finite ordered contexts, with repetitions and the empty tuple allowed. -/
abbrev Context (V : Type*) := Σ l : ℕ, Fin l → V

variable {V : Type} [MeasurableSpace V] [StandardBorelSpace V]

instance contextStandardBorel : StandardBorelSpace (Context V) :=
  FSCofinality.standardBorel_sigma (X := fun l => Fin l → V)

def contextCode : Context V → Cantor := Classical.choose
  (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated (Context V))

theorem measurable_contextCode : Measurable (contextCode (V := V)) :=
  (Classical.choose_spec
    (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated (Context V))).1

theorem contextCode_injective : Function.Injective (contextCode (V := V)) :=
  (Classical.choose_spec
    (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated (Context V))).2

def bottomMap (t : Context V) (k : ℕ) : Cantor := coordinatedBeta (contextCode t) k

theorem measurable_bottomMap :
    Measurable (fun p : Context V × ℕ => bottomMap p.1 p.2) :=
  continuous_coordinatedBeta.measurable.comp
    ((measurable_contextCode.comp measurable_fst).prodMk measurable_snd)

theorem bottomMap_injective :
    Function.Injective (fun p : Context V × ℕ => bottomMap p.1 p.2) := by
  intro p q heq
  have hh : (contextCode p.1,p.2) = (contextCode q.1,q.2) := coordinatedBeta_injective heq
  exact Prod.ext (contextCode_injective (congrArg (fun r : Cantor × ℕ => r.1) hh))
    (congrArg (fun r : Cantor × ℕ => r.2) hh)

theorem measurableEmbedding_bottomMap :
    MeasurableEmbedding (fun p : Context V × ℕ => bottomMap p.1 p.2) :=
  measurable_bottomMap.measurableEmbedding bottomMap_injective

theorem bottomMap_finite_independence {ι : Type*} [Fintype ι]
    (p : ι → Context V × ℕ) (hp : Function.Injective p) (epsilon : ι → Bool) (N : ℕ) :
    ∃ q > N, ∀ i, bottomMap (p i).1 (p i).2 q = epsilon i := by
  apply coordinatedBeta_finite_independence
    (fun i => (contextCode (p i).1,(p i).2)) ?_ epsilon N
  intro i j hij
  apply hp
  exact Prod.ext (contextCode_injective (congrArg (fun r : Cantor × ℕ => r.1) hij))
    (congrArg (fun r : Cantor × ℕ => r.2) hij)

/-- The full bottom-coordination lemma, uniform in a fixed raw context. -/
theorem bottomMap_realization (t : Context V) (P : ValidPattern) (s : List Bool) (N : ℕ) :
    ∃ k > N, k ∈ upperSolutions P ∧ bitsPrefix (bottomMap t k) s.length = s :=
  upper_and_bottom_realization (contextCode t) P s N

end FSCofinality.GenericTables.Bottom
