import FSCofinalityProof.CosetConstructionSourceClosure

noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- The actual typed semantic downward closure, independent of any source
enumeration or representatives of countable-set invariants. -/
inductive SourceClosure (root : Ambient eta heta) : Ordinal.{0} → Ambient eta heta → Prop
  | root : SourceClosure root eta root
  | member {a : Ordinal.{0}} {v u : Ambient eta heta} :
      SourceClosure root (a+1) v → Member u v → SourceClosure root a u
  | coordinate {lam : Ordinal.{0}} (hlam : IsSuccLimit lam) {v : Ambient eta heta}
      (s : ℕ → Ambient eta heta) : SourceClosure root lam v →
      v = sourceSequence (level eta lam) s → ∀ n,
        SourceClosure root (Frame.q eta lam hlam n) (s n)

theorem codeChildValue_zero (n : ℕ) (x : (fsTower 0).Carrier) :
    codeChildValue eta heta 0 n x = none := by
  unfold codeChildValue codeChildren
  rw [Ordinal.limitRecOn_zero]
  rfl

theorem child_step_closure (root : Ambient eta heta) (a : Ordinal.{0}) :
    ∀ ha : a ≤ eta, ∀ x : (fsTower a).Carrier,
      SourceClosure eta heta root a (translate eta heta a x) → ∀ n u,
      codeChildValue eta heta a n x = some u →
        SourceClosure eta heta root ((codeChildren a).rank n) u := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    intro ha x hroot n u hu
    rw [codeChildValue_zero] at hu
    contradiction
  | add_one a IH =>
    intro ha x hroot n u hu
    rw [codeChildren_add_one_rank]
    apply SourceClosure.member hroot
    rw [translate_add_one]
    cases hs : successorCode a x with
    | none =>
      rw [codeChildValue_add_one,hs] at hu
      contradiction
    | some f =>
      rw [codeChildValue_add_one,hs,Option.map_some] at hu
      exact (member_collection_some _ _ _).mpr ⟨n,Option.some.inj hu⟩
  | limit a ha IH =>
    intro hle x hroot n u hu
    rw [codeChildren_limit_rank a ha]
    rw [codeChildValue_limit eta heta a ha] at hu
    have heq := Option.some.inj hu
    have hc := SourceClosure.coordinate ha
      (fun k => translate eta heta (fundamentalSequence a ha k) (limitCode a ha x k))
      hroot (translate_limit eta heta a ha x) n
    have hq : Frame.q eta a ha n = fundamentalSequence a ha n :=
      congrFun (Frame.q_of_le_source eta a ha hle) n
    simpa only [hq,heq] using hc

theorem path_get_in_closure (p : List ℕ) : ∀ x : (fsTower eta).Carrier,
    ∀ y : (fsTower (sourcePath eta p).rank).Carrier,
      (sourcePath eta p).get x = .inr y →
        SourceClosure eta heta (translate eta heta eta x) (sourcePath eta p).rank
          (translate eta heta (sourcePath eta p).rank y) := by
  induction p with
  | nil =>
    intro x y hy
    cases hy
    exact SourceClosure.root
  | cons n p IH =>
    intro x y hy
    cases hp : (sourcePath eta p).get x with
    | inl z =>
      simp only [sourcePath,Function.comp_apply,hp,Sum.elim_inl] at hy
      contradiction
    | inr z =>
      have hprev := IH x z hp
      have hget : (codeChildren (sourcePath eta p).rank).get n z = .inr y := by
        simpa only [sourcePath,Function.comp_apply,hp,Sum.elim_inr] using hy
      apply child_step_closure eta heta _ _ (sourcePath eta p).rank_le z hprev n
      unfold codeChildValue
      rw [hget]
      rfl

theorem sourceSeeds_iff_closure (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    (u : Ambient eta heta) : u ∈ sourceSeeds eta heta a x ↔
      SourceClosure eta heta (translate eta heta eta x) a u := by
  constructor
  · rintro ⟨p,hrank,hp⟩
    unfold sourcePathValue optionalTranslate at hp
    split at hp
    · contradiction
    · rename_i y hy
      cases hp
      have hc := path_get_in_closure eta heta p x y hy
      exact Eq.mp (congrArg (fun b => SourceClosure eta heta (translate eta heta eta x) b
        (translate eta heta (sourcePath eta p).rank y)) hrank) hc
  · intro hc
    induction hc with
    | root => exact root_mem_sourceSeeds eta heta x
    | member hparent hmember IH => exact sourceSeeds_successor_downward eta heta _ x IH hmember
    | coordinate hlam s hparent heq n IH =>
      obtain ⟨t,ht,hcoord⟩ := sourceSeeds_limit_representation eta heta _ hlam x IH
      have hst : s = t := sourceSequence_injective _ (heq.symm.trans ht)
      rw [hst]
      exact hcoord n

/-- Equal source invariants generate literally the same typed source pools. -/
theorem sourceSeeds_congr (a : Ordinal.{0}) {x y : (fsTower eta).Carrier}
    (hxy : (fsTower eta).rel x y) : sourceSeeds eta heta a x = sourceSeeds eta heta a y := by
  have heq := (translate_eq_iff eta heta eta x y).mpr hxy
  ext u
  rw [sourceSeeds_iff_closure,sourceSeeds_iff_closure,heq]

end FSCofinality.CosetConstruction
