import FSCofinalityProof.TokenNamedRecovery
import Mathlib.Logic.Equiv.List

set_option autoImplicit false
noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

def tokenCongr {U V : Type} (f : U ≃ V) : Token U ≃ Token V :=
  Equiv.prodCongr (Equiv.listEquivOfEquiv f) (Equiv.refl ℕ)

theorem tokenCongr_apply {U V : Type} (f : U ≃ V) (v : Token U) :
    tokenCongr f v = mapToken f v := rfl

theorem ordinaryEdge_congr {U V U' V' : Type} (R : U → V → Bool) (R' : U' → V' → Bool)
    (f : U → U') (g : V → V') (hR : ∀ u v, R u v = R' (f u) (g v))
    (A : Table) (e : ℕ) (v : Token U) (w : Token V) :
    ordinaryEdge A e R v w = ordinaryEdge A e R' (mapToken f v) (mapToken g w) := by
  have hh : R = fun u v => R' (f u) (g v) := funext (fun u => funext (hR u))
  rw [hh]
  exact ordinaryEdge_map A e R' f g v w

theorem activeProfiles_precompose {U U' : Type} {C C' : ℕ → Type}
    (p : ∀ n, U → C n → Bool) (p' : ∀ n, U' → C' n → Bool)
    (f : U → U') (g : ∀ n, C n → C' n)
    (hp : ∀ n u c, p n u c = p' n (f u) (g n c)) (v : Token U) (n : ℕ) :
    (activeProfiles p' (mapToken f v) n).map (fun q c => q (g n c)) = activeProfiles p v n := by
  simp only [activeProfiles,activeTuple_mapToken,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro u _
  exact funext (fun c => (hp n u c).symm)

theorem limit_R_congr {U U' : Type} {C C' : ℕ → Type}
    (p : ∀ n, U → C n → Bool) (p' : ∀ n, U' → C' n → Bool)
    (f : U → U') (g : ∀ n, C n ≃ C' n)
    (hp : ∀ n u c, p n u c = p' n (f u) (g n c)) (v w : Token U) (n : ℕ) :
    R p n v w ↔ R p' n (mapToken f v) (mapToken f w) := by
  have hinj : Function.Injective (fun q : C' n → Bool => fun c => q (g n c)) := by
    intro q r hqr
    funext c
    obtain ⟨c,rfl⟩ := (g n).surjective c
    exact congrFun hqr c
  have hi := List.map_injective_iff.mpr hinj
  have hv := activeProfiles_precompose p p' f (fun n => g n) hp v n
  have hw := activeProfiles_precompose p p' f (fun n => g n) hp w n
  simp only [R,localCode_mapToken]
  constructor
  · rintro ⟨hl,hp⟩
    exact ⟨hl,hi (hv.trans (hp.trans hw.symm))⟩
  · rintro ⟨hl,hp⟩
    exact ⟨hl,hv.symm.trans ((congrArg (List.map (fun q c => q (g n c))) hp).trans hw)⟩

theorem branchEdge_congr {U U' : Type} {C C' : ℕ → Type}
    (p : ∀ n, U → C n → Bool) (p' : ∀ n, U' → C' n → Bool)
    (f : U → U') (g : ∀ n, C n → C' n)
    (hp : ∀ n u c, p n u c = p' n (f u) (g n c))
    (A : Table) (e n : ℕ) (v : Token U) (w : Token (C n)) :
    branchEdge p A e n v w = branchEdge p' A e n (mapToken f v) (mapToken (g n) w) := by
  have hh : p n = fun u c => p' n (f u) (g n c) := funext (fun u => funext (hp n u))
  simp only [branchEdge,activeProfiles,activeTuple_mapToken,localCode_mapToken]
  rw [hh,contextMatrix_map]
  rfl

end FSCofinality.Tokens
