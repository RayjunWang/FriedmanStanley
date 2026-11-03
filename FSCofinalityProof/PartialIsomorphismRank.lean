import FSCofinalityProof.PartialIsomorphism

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

/-- The ordinary transfinite back-and-forth relation on a finite partial
correspondence. At every lower stage, one new element on either side can
be matched. Equality and all relation symbols are checked at stage zero. -/
def BackAndForth {L : CountableRelationalLanguage} (M N : Structures L)
    (a : Ordinal.{0}) (R : List (ℕ × ℕ)) : Prop :=
  AtomicCompatible M N {p | p ∈ R} ∧
  ∀ b : Ordinal.{0}, b < a →
    (∀ x : ℕ, ∃ y : ℕ, BackAndForth M N b (R ++ [(x,y)])) ∧
    (∀ y : ℕ, ∃ x : ℕ, BackAndForth M N b (R ++ [(x,y)]))
termination_by a

theorem BackAndForth.atomic {L : CountableRelationalLanguage} {M N : Structures L}
    {a : Ordinal.{0}} {R : List (ℕ × ℕ)} (h : BackAndForth M N a R) :
    AtomicCompatible M N {p | p ∈ R} := by
  rw [BackAndForth] at h
  exact h.1

theorem BackAndForth.mono {L : CountableRelationalLanguage} {M N : Structures L}
    {a b : Ordinal.{0}} {R : List (ℕ × ℕ)}
    (h : BackAndForth M N a R) (hba : b ≤ a) : BackAndForth M N b R := by
  rw [BackAndForth] at h ⊢
  exact ⟨h.1,fun c hc => h.2 c (lt_of_lt_of_le hc hba)⟩

theorem BackAndForth.scheduled_extension
    {L : CountableRelationalLanguage} {M N : Structures L}
    {a b : Ordinal.{0}} (s : List ℕ)
    (h : BackAndForth M N a (pairsFrom 0 s)) (hba : b < a) :
    ∃ n : ℕ, BackAndForth M N b (pairsFrom 0 (s ++ [n])) := by
  rw [BackAndForth] at h
  by_cases heven : s.length % 2 = 0
  · obtain ⟨y,hy⟩ := (h.2 b hba).1 (s.length/2)
    refine ⟨y,?_⟩
    simpa only [pairsFrom_append,pairsFrom,Nat.zero_add,List.append_nil,
      scheduledPair,if_pos heven] using hy
  · obtain ⟨x,hx⟩ := (h.2 b hba).2 (s.length/2)
    refine ⟨x,?_⟩
    simpa only [pairsFrom_append,pairsFrom,Nat.zero_add,List.append_nil,
      scheduledPair,if_neg heven] using hx

theorem BackAndForth.mem_attemptTree
    {L : CountableRelationalLanguage} {M N : Structures L}
    {a : Ordinal.{0}} {s : List ℕ}
    (h : BackAndForth M N a (pairsFrom 0 s)) : attemptTree M N s = true :=
  decide_eq_true h.atomic

/-- A back-and-forth level is a lower bound for every strictly decreasing
ordinal assignment on the partial-isomorphism attempt tree. -/
theorem backAndForth_le_ordinal_assignment
    {L : CountableRelationalLanguage} (M N : Structures L)
    (ρ : RootedTrees.Nodes (attemptTree M N) → Ordinal.{0})
    (hρ : ∀ s t, RootedTrees.Child s t → ρ s < ρ t)
    (a : Ordinal.{0}) (s : List ℕ)
    (h : BackAndForth M N a (pairsFrom 0 s)) :
    a ≤ ρ ⟨s,h.mem_attemptTree⟩ := by
  induction a using WellFoundedLT.induction generalizing s with
  | ind a IH =>
      by_contra hn
      have hlt : ρ ⟨s,h.mem_attemptTree⟩ < a := lt_of_not_ge hn
      obtain ⟨n,hchild⟩ := h.scheduled_extension s hlt
      have hle := IH (ρ ⟨s,h.mem_attemptTree⟩) hlt (s ++ [n]) hchild
      have hstrict := hρ ⟨s ++ [n],hchild.mem_attemptTree⟩
        ⟨s,h.mem_attemptTree⟩ ⟨n,rfl⟩
      exact (not_le_of_gt hstrict) hle

/-- A single back-and-forth equivalence at level `a` excludes every
well-founded height bound `a` on the complete attempt tree. -/
theorem not_bounded_attemptTree_of_backAndForth
    {L : CountableRelationalLanguage} {M N : Structures L} (a : Ordinal.{0})
    (h : BackAndForth M N a []) : ¬ RootedTrees.BoundedTree (attemptTree M N) a := by
  rintro ⟨ρ,hbound,hdecr⟩
  have h' : BackAndForth M N a (pairsFrom 0 []) := h
  have hle := backAndForth_le_ordinal_assignment M N ρ hdecr a [] h'
  exact (not_le_of_gt (hbound ⟨[],h'.mem_attemptTree⟩)) hle

end FSCofinality.PartialIso
