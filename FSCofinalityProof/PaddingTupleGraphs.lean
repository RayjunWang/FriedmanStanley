import FSCofinalityProof.PaddingEnumeration
import Mathlib.Topology.List

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open TopologicalSpace

namespace FSCofinality.Padding

def tupleData (G : GraphSpace) (s : List ℕ) : ℕ × (List (List Bool) × List (List Bool)) :=
  (s.length,
    (List.ofFn (fun i : Fin s.length => List.ofFn (fun j : Fin s.length =>
        decide (s.getD i.val 0 = s.getD j.val 0))),
      List.ofFn (fun i : Fin s.length => List.ofFn (fun j : Fin s.length =>
        G.val (s.getD i.val 0,s.getD j.val 0)))))

def tupleColor (G : GraphSpace) (s : List ℕ) : ℕ := Encodable.encode (tupleData G s)

theorem tupleColor_nil (G H : GraphSpace) : tupleColor G [] = tupleColor H [] := by
  rfl

theorem length_eq_of_tupleColor_eq {G H : GraphSpace} {s t : List ℕ}
    (h : tupleColor G s = tupleColor H t) : s.length = t.length :=
  congrArg Prod.fst (Encodable.encode_injective h)

/-- A tuple color records the complete equality and adjacency diagram. -/
theorem atomic_of_tupleColor_eq {G H : GraphSpace} {s t : List ℕ}
    (h : tupleColor G s = tupleColor H t) (i j : ℕ) (hi : i < s.length) (hj : j < s.length) :
    (s.getD i 0 = s.getD j 0 ↔ t.getD i 0 = t.getD j 0) ∧
      G.val (s.getD i 0,s.getD j 0) = H.val (t.getD i 0,t.getD j 0) := by
  have he := Encodable.encode_injective h
  have hlen : s.length = t.length := congrArg Prod.fst he
  have hEq := congrArg (fun x : ℕ × (List (List Bool) × List (List Bool)) => x.2.1) he
  have hAdj := congrArg (fun x : ℕ × (List (List Bool) × List (List Bool)) => x.2.2) he
  dsimp only [tupleData] at hEq hAdj
  rw [← hlen] at hEq hAdj
  have hiEq := congrFun (List.ofFn_injective hEq) ⟨i,hi⟩
  have hijEq := congrFun (List.ofFn_injective hiEq) ⟨j,hj⟩
  have hiAdj := congrFun (List.ofFn_injective hAdj) ⟨i,hi⟩
  have hijAdj := congrFun (List.ofFn_injective hiAdj) ⟨j,hj⟩
  exact ⟨by simpa only [decide_eq_decide] using hijEq,hijAdj⟩

theorem continuous_tupleColor (s : List ℕ) : Continuous (fun G : GraphSpace => tupleColor G s) := by
  have hentry (i j : Fin s.length) : Continuous (fun G : GraphSpace =>
      G.val (s.getD i.val 0,s.getD j.val 0)) :=
    (_root_.continuous_apply _).comp continuous_subtype_val
  have hrow (i : Fin s.length) : Continuous (fun G : GraphSpace =>
      List.ofFn (fun j : Fin s.length => G.val (s.getD i.val 0,s.getD j.val 0))) :=
    (continuous_of_discreteTopology : Continuous (List.ofFn : (Fin s.length → Bool) → List Bool)).comp
      (continuous_pi (fun j => hentry i j))
  have hmatrix : Continuous (fun G : GraphSpace =>
      List.ofFn (fun i : Fin s.length => List.ofFn (fun j : Fin s.length =>
        G.val (s.getD i.val 0,s.getD j.val 0)))) :=
    (continuous_of_discreteTopology : Continuous
      (List.ofFn : (Fin s.length → List Bool) → List (List Bool))).comp
        (continuous_pi hrow)
  have hdata : Continuous (fun G : GraphSpace => tupleData G s) :=
    continuous_const.prodMk (continuous_const.prodMk hmatrix)
  exact (continuous_of_discreteTopology : Continuous
    (Encodable.encode : (ℕ × (List (List Bool) × List (List Bool))) → ℕ)).comp hdata

def paddedGraphCode (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (G : GraphSpace) :
    Structures treeLanguage :=
  code (PaddedNode.tree a (tupleColor G)) (paddedEnumeration a ha)

theorem continuous_paddedGraphCode (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    Continuous (paddedGraphCode a ha) := by
  have hcolor (v : PaddedNode a) : Continuous
      (fun G : GraphSpace => PaddedNode.color (tupleColor G) v) := by
    cases v with
    | inl s => exact continuous_tupleColor s
    | inr v => exact continuous_const
  apply continuous_pi
  rintro ⟨s,t⟩
  rcases s with _ | (_ | c)
  · change Continuous (fun _ : GraphSpace => decide
      ((paddedEnumeration a ha) (t ⟨0,by simp [treeLanguage]⟩) = PaddedNode.root a))
    exact continuous_const
  · change Continuous (fun _ : GraphSpace => decide
      (PaddedNode.parent ((paddedEnumeration a ha) (t ⟨0,by simp [treeLanguage]⟩)) =
        (paddedEnumeration a ha) (t ⟨1,by simp [treeLanguage]⟩)))
    exact continuous_const
  · exact (continuous_of_discreteTopology : Continuous (fun n : ℕ => decide (n = c))).comp
      (hcolor ((paddedEnumeration a ha) (t ⟨0,by simp [treeLanguage]⟩)))

theorem measurable_paddedGraphCode (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    Measurable (paddedGraphCode a ha) := (continuous_paddedGraphCode a ha).measurable

end FSCofinality.Padding
