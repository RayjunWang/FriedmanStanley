import Definitions.Def_FSCofinalityTrees20261102
import Mathlib.Topology.List
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Data.List.OfFn
import Mathlib.Order.WellFounded
import Mathlib.Tactic

noncomputable section
open Set Filter TopologicalSpace Topology

namespace FSCofinality.RootedTrees

abbrev Baire := ℕ → ℕ

theorem mem_parent (T : TreeSpace) (s : Node) (n : ℕ) (h : T (s ++ [n]) = true) :
    T s = true := T.property s n h

theorem mem_of_append (T : TreeSpace) (s t : Node) (h : T (s ++ t) = true) : T s = true := by
  induction t using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton t n ih =>
    exact ih (mem_parent T (s ++ t) n (by simpa only [List.append_assoc] using h))

def branchPrefix (x : Baire) (n : ℕ) : Node := List.ofFn (fun i : Fin n => x i)

@[simp] theorem length_branchPrefix (x : Baire) (n : ℕ) : (branchPrefix x n).length = n := by
  simp [branchPrefix]

@[simp] theorem branchPrefix_zero (x : Baire) : branchPrefix x 0 = [] := rfl

theorem branchPrefix_succ (x : Baire) (n : ℕ) : branchPrefix x (n+1) = branchPrefix x n ++ [x n] := by
  simpa [branchPrefix,List.concat_eq_append] using List.ofFn_succ' (fun i : Fin (n+1) => x i)

theorem continuous_branchPrefix (n : ℕ) : Continuous (fun x : Baire => branchPrefix x n) := by
  exact (continuous_of_discreteTopology : Continuous (List.ofFn : (Fin n → ℕ) → Node)).comp
    (continuous_pi (fun i => continuous_apply (i : ℕ)))

theorem continuous_eval (s : Node) : Continuous (fun T : TreeSpace => T s) :=
  (continuous_apply s).comp continuous_subtype_val

theorem mem_take (T : TreeSpace) (s : Node) (k : ℕ) (hs : T s = true) :
    T (s.take k) = true :=
  mem_of_append T (s.take k) (s.drop k) (by simpa using hs)

@[simp] theorem take_branchPrefix (x : Baire) (n k : ℕ) :
    (branchPrefix x n).take k = branchPrefix x (min k n) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [branchPrefix]

theorem mem_branchPrefix_of_le (T : TreeSpace) (x : Baire) {k n : ℕ}
    (hkn : k ≤ n) (hn : T (branchPrefix x n) = true) : T (branchPrefix x k) = true := by
  simpa only [take_branchPrefix,Nat.min_eq_left hkn] using mem_take T (branchPrefix x n) k hn

def HasBranch (T : TreeSpace) : Prop := ∃ x : Baire, ∀ n, T (branchPrefix x n) = true

theorem tendsto_of_prefix_agreement (u : ℕ → Baire) (x : Baire)
    (h : ∀ n, branchPrefix (u n) n = branchPrefix x n) : Tendsto u atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have heq : ∀ᶠ n in atTop, u n i = x i := by
    filter_upwards [eventually_ge_atTop (i+1)] with n hn
    exact congrFun (List.ofFn_injective (h n)) ⟨i,by omega⟩
  exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)

theorem wellFounded_of_acc_root (T : TreeSpace) (hroot : T [] = true)
    (hacc : Acc (@Child T) ⟨[],hroot⟩) : WellFounded (@Child T) := by
  have hall : ∀ s : Node, ∀ hs : T s = true, Acc (@Child T) ⟨s,hs⟩ := by
    intro s
    induction s using List.reverseRecOn with
    | nil => intro hs; exact hacc
    | append_singleton s n ih =>
      intro hs
      exact (ih (T.property s n hs)).inv ⟨n,rfl⟩
  exact ⟨fun s => hall s.val s.property⟩

theorem wellFounded_child_iff_no_branch (T : TreeSpace) :
    WellFounded (@Child T) ↔ ¬ HasBranch T := by
  constructor
  · intro hwf
    rintro ⟨x,hx⟩
    let f : ℕ → Nodes T := fun n => ⟨branchPrefix x n,hx n⟩
    have hstep (n : ℕ) : Child (f (n+1)) (f n) := ⟨x n,branchPrefix_succ x n⟩
    exact (not_acc_iff_exists_descending_chain.mpr ⟨f,rfl,hstep⟩) (hwf.apply (f 0))
  · intro hnb
    by_cases hroot : T [] = true
    · apply wellFounded_of_acc_root T hroot
      by_contra hbad
      obtain ⟨f,hf0,hstep⟩ := not_acc_iff_exists_descending_chain.mp hbad
      choose k hk using hstep
      have hp : ∀ n, (f n).val = branchPrefix k n := by
        intro n
        induction n with
        | zero => exact congrArg Subtype.val hf0
        | succ n ih => rw [hk n,ih,branchPrefix_succ]
      apply hnb
      exact ⟨k,fun n => hp n ▸ (f n).property⟩
    · refine ⟨fun s => False.elim (hroot ?_)⟩
      simpa using mem_of_append T [] s.val (by simpa using s.property)

end FSCofinality.RootedTrees
