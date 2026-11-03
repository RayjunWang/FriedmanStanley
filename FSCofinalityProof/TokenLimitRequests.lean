import FSCofinalityProof.TokenFiniteCorrespondence
import FSCofinalityProof.TokenLimitFiniteType
import FSCofinalityProof.TokenFiniteRoles

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

def branchLevel (lam : LimitIndex eta) : Option (TokenSort eta) → ℕ
  | some (.inr (mu,n)) => if mu = lam then n else 0
  | _ => 0

theorem limit_requests_realized
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (v : Token (raw eta heta x (.inl lam.val)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl lam.val,v⟩ : Vertex eta heta x) ≠ p.1)
    (copyBound : ℕ) :
    ∃ w : Token (raw eta heta y (.inl lam.val)), copyBound < w.2 ∧
      (∀ (n : ℕ) (i : SortEntries eta heta R (.inl lam.val)),
        Tokens.R (limitProfile eta heta y lam) n w (targetEntry eta heta R _ i) ↔
        Tokens.R (limitProfile eta heta x lam) n v (sourceEntry eta heta R hR _ i)) ∧
      (∀ n (j : SortEntries eta heta R (.inr (lam,n))),
        branch eta heta y lam n w (targetEntry eta heta R _ j) =
          branch eta heta x lam n v (sourceEntry eta heta R hR _ j)) ∧
      OrdinaryRequestsRealized eta heta R hR (.inl lam.val) v w := by
  letI : Infinite (raw eta heta y (.inl lam.val)) :=
    pool_infinite eta heta (fun b => fullSeeds eta heta b y) (Frame.rank lam.val)
  let count (n : ℕ) := Fintype.card (SortEntries eta heta R (.inr (lam,n)))
  let idx (n : ℕ) : Fin (count n) ≃ SortEntries eta heta R (.inr (lam,n)) :=
    (Fintype.equivFin _).symm
  let cx (n : ℕ) (j : Fin (count n)) := sourceEntry eta heta R hR (.inr (lam,n)) (idx n j)
  let cy (n : ℕ) (j : Fin (count n)) := targetEntry eta heta R (.inr (lam,n)) (idx n j)
  let oldX := sourceEntry eta heta R hR (.inl lam.val)
  let oldY := targetEntry eta heta R (.inl lam.val)
  have hOldR := entries_preserve_limit_R eta heta R hR lam
  have hOldBranch (n : ℕ) (i : SortEntries eta heta R (.inl lam.val))
      (j : Fin (count n)) :
      branch eta heta x lam n (oldX i) (cx n j) =
        branch eta heta y lam n (oldY i) (cy n j) :=
    entries_preserve_branch eta heta R hR lam n i (idx n j)
  have hfreshOld (i : SortEntries eta heta R (.inl lam.val)) : v ≠ oldX i := by
    intro heq
    apply hfresh (R.get i.val) (List.get_mem _ i.val)
    exact (congrArg (fun u => (.inr ⟨.inl lam.val,u⟩ : Vertex eta heta x)) heq).trans
      (sourceEntry_vertex eta heta R hR _ i)
  have hconsistent (n : ℕ) (i j : Fin (count n)) (hij : cy n i = cy n j) :
      branch eta heta x lam n v (cx n i) = branch eta heta x lam n v (cx n j) := by
    have hsrc := (sourceEntry_eq_iff_targetEntry_eq eta heta R hR (.inr (lam,n))
      (idx n i) (idx n j)).mpr hij
    exact congrArg (branch eta heta x lam n v) hsrc
  let bound := Finset.univ.sup (fun i : Fin R.length =>
    branchLevel eta lam (sortOf eta heta (R.get i).2))
  have hbound (n : ℕ) (hn : bound < n) : count n = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    constructor
    intro i
    have hi := i.property
    have hle : branchLevel eta lam (sortOf eta heta (R.get i.val).2) ≤ bound :=
      Finset.le_sup (f := fun i : Fin R.length =>
        branchLevel eta lam (sortOf eta heta (R.get i).2)) (Finset.mem_univ i.val)
    rw [hi] at hle
    simp [branchLevel] at hle
    omega
  obtain ⟨w,hw,hrelation,hbranch,hordinary⟩ := limit_finite_type_extension
    (limitProfile eta heta x lam) (limitProfile eta heta y lam)
    (limitPropagate eta heta x lam) (limitProfile_propagate eta heta x lam)
    (limitProfile_full_injective eta heta x lam) (limitProfile_column_separating eta heta y lam)
    (fun n => roleNumber eta heta (.inr (lam,n))) count cx cy oldX oldY hOldR hOldBranch
    (ordinaryRequirements eta heta R hR (.inl lam.val) v)
    (ordinaryRequirements_roles_injective eta heta R hR (.inl lam.val) v)
    v hfreshOld hconsistent bound hbound copyBound
  refine ⟨w,hw,hrelation,?_,hordinary⟩
  intro n j
  have hh := hbranch n ((idx n).symm j)
  simpa only [cy,cx,Equiv.apply_symm_apply] using hh

end FSCofinality.CosetConstruction.TokenModel
