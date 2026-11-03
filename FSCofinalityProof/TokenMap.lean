import FSCofinalityProof.TokenRecovery

noncomputable section

namespace FSCofinality.Tokens
open GenericTables

def mapToken {U V : Type*} (f : U → V) (v : Token U) : Token V := (v.1.map f,v.2)

theorem history_mapToken {U V : Type*} (f : U → V) (v : Token U) :
    (history (mapToken f v)).val = (history v).val := by
  unfold mapToken history
  rw [List.length_map]

theorem localCode_mapToken {U V : Type*} (f : U → V) (v : Token U) (n : ℕ) :
    localCode (mapToken f v) n = localCode v n := by
  unfold localCode
  rw [history_mapToken]

theorem activeTuple_mapToken {U V : Type*} (f : U → V) (v : Token U) (n : ℕ) :
    activeTuple (mapToken f v) n = (activeTuple v n).map f := by
  unfold activeTuple activeLength
  rw [history_mapToken]
  exact List.map_take.symm

theorem branchEdge_mapToken {U V : Type*} {Col : ℕ → Type*}
    (f : U → V) (profile : ∀ n, V → Col n → Bool) (A : Table) (e n : ℕ)
    (v : Token U) (c : Token (Col n)) :
    branchEdge profile A e n (mapToken f v) c =
      branchEdge (fun n u => profile n (f u)) A e n v c := by
  simp only [branchEdge,activeProfiles,localCode_mapToken,activeTuple_mapToken,
    List.map_map,Function.comp_def]

def widen {U : Type*} {P S : Set U} (h : P ⊆ S) : Token P → Token S :=
  mapToken (fun u => ⟨u.val,h u.property⟩)

theorem name_widen {U : Type*} {P S : Set U} (h : P ⊆ S) (v : Token P) :
    name S (widen h v) = name P v := by
  simp only [name,widen,mapToken,List.map_map,Function.comp_def]

end FSCofinality.Tokens
