import FSCofinalityProof.TokenRecovery
import FSCofinalityProof.GenericTablesBottomMap

noncomputable section

namespace FSCofinality.Tokens
open GenericTables

def contextOfList {U : Type*} (t : List U) : Bottom.Context U := ⟨t.length,fun i => t[i]⟩

theorem contextOfList_injective {U : Type*} : Function.Injective (contextOfList (U := U)) := by
  intro s t h
  have hh := congrArg (fun c : Bottom.Context U => List.ofFn c.2) h
  change List.ofFn s.get = List.ofFn t.get at hh
  simpa only [List.ofFn_get] using hh

variable {U : Type} [MeasurableSpace U] [StandardBorelSpace U]

def bottomListMap (t : List U) (k : ℕ) : Bottom.Cantor := Bottom.bottomMap (contextOfList t) k

theorem bottomListMap_injective :
    Function.Injective (fun p : Token U => bottomListMap p.1 p.2) := by
  intro p q heq
  have hh : (contextOfList p.1,p.2) = (contextOfList q.1,q.2) := Bottom.bottomMap_injective heq
  exact Prod.ext (contextOfList_injective (congrArg Prod.fst hh))
    (congrArg (fun t : Bottom.Context U × ℕ => t.2) hh)

/-- Pointwise fixing the intended coordinate enumeration preserves exactly
the bottom neighborhood, which recovers the literal raw tuple and label. -/
theorem bottom_recovery_between_pools (P Q : Set U) (v : Token P) (w : Token Q)
    (h : bottomListMap (name P v).1 v.2 = bottomListMap (name Q w).1 w.2) :
    name P v = name Q w := bottomListMap_injective h

theorem bottomListMap_finite_independence {ι : Type*} [Fintype ι]
    (p : ι → Token U) (hp : Function.Injective p) (epsilon : ι → Bool) (N : ℕ) :
    ∃ q > N, ∀ i, bottomListMap (p i).1 (p i).2 q = epsilon i := by
  apply Bottom.bottomMap_finite_independence
    (fun i => (contextOfList (p i).1,(p i).2)) ?_ epsilon N
  intro i j heq
  apply hp
  exact Prod.ext (contextOfList_injective (congrArg Prod.fst heq))
    (congrArg (fun t : Bottom.Context U × ℕ => t.2) heq)

end FSCofinality.Tokens
