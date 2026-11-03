import FSCofinalityProof.RawObjectsPools

noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- A concrete realization of source codes by actual typed raw names.
Semantic quotients carry no assumed measurable structure. -/
structure SourceRealization (a : Ordinal.{0}) (E : CodedRelation) where
  value : E.Carrier → Ambient eta heta
  faithful : ∀ x y, E.rel x y ↔ value x = value y
  typed : a ≤ eta → ∀ x, value x ∈ Valid eta heta a

def SourceRealization.transport {a : Ordinal.{0}} {E F : CodedRelation} (h : E = F)
    (r : SourceRealization eta heta a E) : SourceRealization eta heta a F := h ▸ r

theorem SourceRealization.transport_value {a : Ordinal.{0}} {E F : CodedRelation} (h : E = F)
    (r : SourceRealization eta heta a E) (x : F.Carrier) :
    (r.transport eta heta h).value x =
      r.value (cast (congrArg CodedRelation.Carrier h.symm) x) := by
  cases h
  rfl

def bottomRealization : SourceRealization eta heta 0 cantorEquality where
  value := sourceAtom
  faithful := by
    intro x y
    change x = y ↔ sourceAtom x = sourceAtom y
    exact ⟨congrArg sourceAtom,fun h => sourceAtom_injective h⟩
  typed := by
    intro _ x
    rw [valid_zero]
    exact Or.inl (mem_range_self x)

theorem collection_none_ne_some (l : Frame.Layer eta) (f : ℕ → Ambient eta heta) :
    collection l none ≠ collection l (some f) := by
  intro h
  have hm : Member (f 0) (collection l (some f)) := by simp
  rw [← h] at hm
  exact member_collection_none l (f 0) hm

def successorRealization (a : Ordinal.{0}) (E : CodedRelation)
    (r : SourceRealization eta heta a E) :
    SourceRealization eta heta (a+1) (setJump E) where
  value := fun x => collection (level eta (a+1)) (x.map (fun u n => r.value (u n)))
  faithful := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none => exact iff_of_true trivial rfl
      | some v =>
        change False ↔ collection _ none = collection _ (some (fun n => r.value (v n)))
        exact iff_of_false id (collection_none_ne_some eta heta _ _)
    | some u =>
      cases y with
      | none =>
        change False ↔ collection _ (some (fun n => r.value (u n))) = collection _ none
        exact iff_of_false id (Ne.symm (collection_none_ne_some eta heta _ _))
      | some v =>
        change ((∀ i, ∃ j, E.rel (u i) (v j)) ∧ (∀ j, ∃ i, E.rel (u i) (v j))) ↔ _
        simp only [Option.map_some]
        rw [collection_some_eq_iff]
        simp only [← r.faithful]
  typed := by
    intro ha x
    rw [valid_add_one]
    refine ⟨x.map (fun u n => r.value (u n)),rfl,?_⟩
    intro f hf i
    cases x with
    | none => simp at hf
    | some u =>
      cases hf
      exact r.typed ((show a ≤ a+1 from le_self_add).trans ha) (u i)

def limitRealization (a : Ordinal.{0}) (ha : IsSuccLimit a)
    (E : ℕ → CodedRelation)
    (r : ∀ n, SourceRealization eta heta (fundamentalSequence a ha n) (E n)) :
    SourceRealization eta heta a (countableProduct E) where
  value := fun x => sourceSequence (level eta a) (fun n => (r n).value (x n))
  faithful := by
    intro x y
    constructor
    · intro h
      apply congrArg (sourceSequence (level eta a))
      funext n
      exact ((r n).faithful (x n) (y n)).mp (h n)
    · intro h
      have hseq := sourceSequence_injective (level eta a) h
      intro n
      exact ((r n).faithful (x n) (y n)).mpr (congrFun hseq n)
  typed := by
    intro hle x
    rw [valid_limit eta heta a ha]
    left
    refine ⟨fun n => (r n).value (x n),rfl,?_⟩
    intro n
    change (r n).value (x n) ∈ Valid eta heta (Frame.q eta a ha n)
    simpa only [Frame.q_of_le_source eta a ha hle] using
      (r n).typed ((fundamentalSequence_lt a ha n).le.trans hle) (x n)

/-- Actual source-code translation, constructed through the fixed hierarchy's
successor and product-limit code spaces. -/
def sourceStage (a : Ordinal.{0}) : SourceRealization eta heta a (fsTower a) :=
  Ordinal.limitRecOn a
    ((bottomRealization eta heta).transport eta heta fsTower_zero.symm)
    (fun b r => (successorRealization eta heta b (fsTower b) r).transport eta heta
      (fsTower_add_one b).symm)
    (fun lam hlam rec =>
      (limitRealization eta heta lam hlam _
        (fun n => rec (fundamentalSequence lam hlam n) (fundamentalSequence_lt lam hlam n))).transport
          eta heta (fsTower_limit lam hlam).symm)

def translate (a : Ordinal.{0}) : (fsTower a).Carrier → Ambient eta heta :=
  (sourceStage eta heta a).value

theorem translate_eq_iff (a : Ordinal.{0}) (x y : (fsTower a).Carrier) :
    translate eta heta a x = translate eta heta a y ↔ (fsTower a).rel x y :=
  ((sourceStage eta heta a).faithful x y).symm

theorem translate_typed (a : Ordinal.{0}) (ha : a ≤ eta) (x : (fsTower a).Carrier) :
    translate eta heta a x ∈ Valid eta heta a := (sourceStage eta heta a).typed ha x

def successorCode (a : Ordinal.{0}) (x : (fsTower (a+1)).Carrier) :
    Option (ℕ → (fsTower a).Carrier) :=
  cast (congrArg CodedRelation.Carrier (fsTower_add_one a)) x

def limitCode (a : Ordinal.{0}) (ha : IsSuccLimit a) (x : (fsTower a).Carrier) :
    ∀ n, (fsTower (fundamentalSequence a ha n)).Carrier :=
  cast (congrArg CodedRelation.Carrier (fsTower_limit a ha)) x

theorem translate_add_one (a : Ordinal.{0}) (x : (fsTower (a+1)).Carrier) :
    translate eta heta (a+1) x = collection (level eta (a+1))
      ((successorCode a x).map (fun u n => translate eta heta a (u n))) := by
  unfold translate sourceStage
  rw [Ordinal.limitRecOn_add_one,SourceRealization.transport_value]
  rfl

theorem translate_limit (a : Ordinal.{0}) (ha : IsSuccLimit a) (x : (fsTower a).Carrier) :
    translate eta heta a x = sourceSequence (level eta a)
      (fun n => translate eta heta (fundamentalSequence a ha n) (limitCode a ha x n)) := by
  unfold translate sourceStage
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha,SourceRealization.transport_value]
  rfl

end FSCofinality.CosetConstruction
