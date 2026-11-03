import FSCofinalityProof.CosetConstructionTranslation
import FSCofinalityProof.RawObjectsCountablePools

noncomputable section
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

def codeCast {E F : CodedRelation} (h : E = F) : E.Carrier ≃ᵐ F.Carrier := by
  cases h
  exact MeasurableEquiv.refl _

theorem codeCast_apply {E F : CodedRelation} (h : E = F) (x : E.Carrier) :
    codeCast h x = cast (congrArg CodedRelation.Carrier h) x := by
  cases h
  rfl

def successorChildCode (a : Ordinal.{0}) (n : ℕ) (x : (fsTower (a+1)).Carrier) :
    Unit ⊕ (fsTower a).Carrier :=
  Sum.map id (fun u : ℕ → (fsTower a).Carrier => u n)
    (optionSumEquiv _ (codeCast (fsTower_add_one a) x))

theorem measurable_successorChildCode (a : Ordinal.{0}) (n : ℕ) :
    Measurable (successorChildCode a n) := by
  have hsum : @Measurable (setJump (fsTower a)).Carrier
      (Unit ⊕ (ℕ → (fsTower a).Carrier)) (setJump (fsTower a)).measurableSpace
      inferInstance (optionSumEquiv _) := by
    rw [setJump_measurableSpace_eq]
    exact comap_measurable _
  exact (measurable_id.sumMap (measurable_pi_apply n)).comp
    (hsum.comp (codeCast (fsTower_add_one a)).measurable)

def limitChildCode (a : Ordinal.{0}) (ha : IsSuccLimit a) (n : ℕ)
    (x : (fsTower a).Carrier) : Unit ⊕ (fsTower (fundamentalSequence a ha n)).Carrier :=
  .inr (codeCast (fsTower_limit a ha) x n)

theorem measurable_limitChildCode (a : Ordinal.{0}) (ha : IsSuccLimit a) (n : ℕ) :
    Measurable (limitChildCode a ha n) :=
  measurable_inr.comp ((measurable_pi_apply n).comp (codeCast (fsTower_limit a ha)).measurable)

structure CodeChildren (a : Ordinal.{0}) where
  rank : ℕ → Ordinal.{0}
  get : ∀ n, (fsTower a).Carrier → Unit ⊕ (fsTower (rank n)).Carrier
  measurable_get : ∀ n, Measurable (get n)
  rank_le : ∀ n, rank n ≤ a

def codeChildren (a : Ordinal.{0}) : CodeChildren a :=
  Ordinal.limitRecOn a
    ⟨fun _ => 0,fun _ _ => .inl (),fun _ => measurable_const,fun _ => le_rfl⟩
    (fun b _ => ⟨fun _ => b,successorChildCode b,measurable_successorChildCode b,
      fun _ => le_self_add⟩)
    (fun lam hlam _ => ⟨fundamentalSequence lam hlam,limitChildCode lam hlam,
      measurable_limitChildCode lam hlam,fun n => (fundamentalSequence_lt lam hlam n).le⟩)

structure PathCode (a : Ordinal.{0}) where
  rank : Ordinal.{0}
  get : (fsTower a).Carrier → Unit ⊕ (fsTower rank).Carrier
  measurable_get : Measurable get
  rank_le : rank ≤ a

/-- Paths are stored in reverse order so adding one last child is a list
constructor. All ranks depend only on the path, never on the input code. -/
def sourcePath (a : Ordinal.{0}) : List ℕ → PathCode a
  | [] => ⟨a,Sum.inr,measurable_inr,le_rfl⟩
  | n :: p =>
      let prev := sourcePath a p
      let child := codeChildren prev.rank
      ⟨child.rank n,Sum.elim (fun _ => .inl ()) (child.get n) ∘ prev.get,
        (measurable_const.sumElim (child.measurable_get n)).comp prev.measurable_get,
        (child.rank_le n).trans prev.rank_le⟩

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def optionalTranslate (a : Ordinal.{0}) (z : Unit ⊕ (fsTower a).Carrier) :
    Option (Ambient eta heta) :=
  match z with
  | .inl _ => none
  | .inr y => some (translate eta heta a y)

def sourcePathValue (p : List ℕ) (x : (fsTower eta).Carrier) : Option (Ambient eta heta) :=
  optionalTranslate eta heta (sourcePath eta p).rank ((sourcePath eta p).get x)

/-- The translated typed downward closure, with its concrete countable path
enumeration. Failed paths do not insert padding atoms into the source seed. -/
def sourceSeeds (a : Ordinal.{0}) (x : (fsTower eta).Carrier) : Set (Ambient eta heta) :=
  {u | ∃ p : List ℕ, (sourcePath eta p).rank = a ∧ sourcePathValue eta heta p x = some u}

theorem sourceSeeds_countable (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    (sourceSeeds eta heta a x).Countable := by
  apply (countable_range (fun p : List ℕ =>
    (sourcePathValue eta heta p x).getD (extraAtom 0))).mono
  rintro u ⟨p,_,hp⟩
  exact ⟨p,by simp only [hp,Option.getD_some]⟩

theorem sourceSeeds_typed (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    sourceSeeds eta heta a x ⊆ Valid eta heta a := by
  rintro u ⟨p,hrank,hp⟩
  unfold sourcePathValue optionalTranslate at hp
  split at hp
  · contradiction
  · rename_i y hy
    cases hp
    have hv := translate_typed eta heta (sourcePath eta p).rank (sourcePath eta p).rank_le y
    simpa only [hrank] using hv

theorem root_mem_sourceSeeds (x : (fsTower eta).Carrier) :
    translate eta heta eta x ∈ sourceSeeds eta heta eta x := ⟨[],rfl,rfl⟩

end FSCofinality.CosetConstruction
