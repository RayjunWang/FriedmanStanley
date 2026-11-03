import FSCofinalityProof.CosetConstructionPoolEnumeration

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

/-- The genuine standard Borel bottom raw space, with its two tagged kinds
of atoms. No measurable structure is placed on the semantic universe. -/
abbrev BottomValueSpace := (ℕ → Bool) ⊕ ℕ

instance bottomValueSpace_standardBorel : StandardBorelSpace BottomValueSpace := standardBorel_sum

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def atomObject : BottomValueSpace → Ambient eta heta := Sum.elim sourceAtom extraAtom

theorem atomObject_injective : Function.Injective (atomObject eta heta) := by
  intro u v h
  rcases u with u | u <;> rcases v with v | v
  · exact congrArg Sum.inl (sourceAtom_injective h)
  · exact False.elim (sourceAtom_ne_extraAtom u v h)
  · exact False.elim (sourceAtom_ne_extraAtom v u h.symm)
  · exact congrArg Sum.inr (extraAtom_injective h)

theorem atomObject_mem_valid (v : BottomValueSpace) : atomObject eta heta v ∈ Valid eta heta 0 := by
  rw [valid_zero]
  cases v with
  | inl r => exact Or.inl ⟨r,rfl⟩
  | inr n => exact Or.inr ⟨n,rfl⟩

def atomEquiv : BottomValueSpace ≃ Valid eta heta 0 :=
  Equiv.ofBijective (fun v => ⟨atomObject eta heta v,atomObject_mem_valid eta heta v⟩)
    ⟨fun _ _ h => atomObject_injective eta heta (congrArg Subtype.val h),by
      intro u
      have hu : u.val ∈ (range sourceAtom ∪ range extraAtom : Set (Ambient eta heta)) := by
        simpa only [valid_zero] using u.property
      rcases hu with ⟨r,hr⟩ | ⟨n,hn⟩
      · exact ⟨Sum.inl r,Subtype.ext hr⟩
      · exact ⟨Sum.inr n,Subtype.ext hn⟩⟩

@[simp] theorem atomEquiv_apply_val (v : BottomValueSpace) :
    (atomEquiv eta heta v).val = atomObject eta heta v := rfl

def bottomValue : Valid eta heta 0 → BottomValueSpace := (atomEquiv eta heta).symm

theorem bottomValue_injective : Function.Injective (bottomValue eta heta) :=
  (atomEquiv eta heta).symm.injective

@[simp] theorem bottomValue_atomObject (v : BottomValueSpace) :
    bottomValue eta heta ⟨atomObject eta heta v,atomObject_mem_valid eta heta v⟩ = v :=
  (atomEquiv eta heta).symm_apply_apply v

@[simp] theorem atomObject_bottomValue (u : Valid eta heta 0) :
    atomObject eta heta (bottomValue eta heta u) = u.val :=
  congrArg Subtype.val ((atomEquiv eta heta).apply_symm_apply u)

/-- A total semantic decoder, whose values outside the bottom layer are
irrelevant to the construction. -/
def decodeAtom (u : Ambient eta heta) : BottomValueSpace :=
  if h : u ∈ Valid eta heta 0 then bottomValue eta heta ⟨u,h⟩ else .inr 0

@[simp] theorem decodeAtom_atomObject (v : BottomValueSpace) :
    decodeAtom eta heta (atomObject eta heta v) = v := by
  rw [decodeAtom,dif_pos (atomObject_mem_valid eta heta v)]
  exact bottomValue_atomObject eta heta v

@[simp] theorem decodeAtom_sourceAtom (r : ℕ → Bool) :
    decodeAtom eta heta (sourceAtom r) = .inl r := decodeAtom_atomObject eta heta (.inl r)

@[simp] theorem decodeAtom_extraAtom (n : ℕ) :
    decodeAtom eta heta (extraAtom n) = .inr n := decodeAtom_atomObject eta heta (.inr n)

theorem decodeAtom_eq_bottomValue (u : Valid eta heta 0) :
    decodeAtom eta heta u.val = bottomValue eta heta u := by
  simp only [decodeAtom,dif_pos u.property]

theorem atomObject_decodeAtom_of_valid (u : Ambient eta heta) (hu : u ∈ Valid eta heta 0) :
    atomObject eta heta (decodeAtom eta heta u) = u := by
  rw [decodeAtom_eq_bottomValue eta heta ⟨u,hu⟩]
  exact atomObject_bottomValue eta heta ⟨u,hu⟩

theorem decodeAtom_injOn : InjOn (decodeAtom eta heta) (Valid eta heta 0) := by
  intro u hu v hv huv
  exact (atomObject_decodeAtom_of_valid eta heta u hu).symm.trans
    ((congrArg (atomObject eta heta) huv).trans (atomObject_decodeAtom_of_valid eta heta v hv))

def decodeOptionalAtom : Option (Ambient eta heta) → Unit ⊕ BottomValueSpace
  | none => .inl ()
  | some u => .inr (decodeAtom eta heta u)

theorem measurable_decodeOptional_optionalTranslate_zero :
    Measurable (fun z : Unit ⊕ (fsTower 0).Carrier =>
      decodeOptionalAtom eta heta (optionalTranslate eta heta 0 z)) := by
  have hm : Measurable (fun y : (fsTower 0).Carrier =>
      (Sum.inr (Sum.inl (codeCast fsTower_zero y)) : Unit ⊕ BottomValueSpace)) :=
    measurable_inr.comp (measurable_inl.comp (codeCast fsTower_zero).measurable)
  have h := (measurable_const : Measurable (fun _ : Unit =>
    (Sum.inl () : Unit ⊕ BottomValueSpace))).sumElim hm
  convert h using 1
  funext z
  cases z with
  | inl u => cases u; rfl
  | inr y =>
    simp only [optionalTranslate,translate_zero,decodeOptionalAtom,decodeAtom_sourceAtom,codeCast_apply]
    rfl

theorem measurable_decodeOptional_sourcePathValue (p : List ℕ)
    (hp : (sourcePath eta p).rank = 0) :
    Measurable (fun x => decodeOptionalAtom eta heta (sourcePathValue eta heta p x)) := by
  let f := Sum.map id (codeCast (congrArg fsTower hp)) ∘ (sourcePath eta p).get
  have hf : Measurable f :=
    (measurable_id.sumMap (codeCast _).measurable).comp (sourcePath eta p).measurable_get
  convert (measurable_decodeOptional_optionalTranslate_zero eta heta).comp hf using 1
  funext x
  exact congrArg (decodeOptionalAtom eta heta)
    (optionalTranslate_cast eta heta hp ((sourcePath eta p).get x)).symm

theorem measurable_decodeOptional_evalSeed_zero (s : SeedIndex) :
    Measurable (fun x => decodeOptionalAtom eta heta (evalSeed eta heta 0 s x)) := by
  cases s with
  | none =>
    have ht : (0 : Ordinal.{0}) ≠ Frame.top eta :=
      ne_of_lt (lt_of_le_of_lt zero_le (Frame.lt_top eta))
    simpa only [evalSeed,if_neg ht,decodeOptionalAtom] using
      (measurable_const : Measurable (fun _ : (fsTower eta).Carrier =>
        (Sum.inl () : Unit ⊕ BottomValueSpace)))
  | some p =>
    by_cases hp : (sourcePath eta p).rank = 0
    · simpa only [evalSeed,if_pos hp] using measurable_decodeOptional_sourcePathValue eta heta p hp
    · simpa only [evalSeed,if_neg hp,decodeOptionalAtom] using
        (measurable_const : Measurable (fun _ : (fsTower eta).Carrier =>
          (Sum.inl () : Unit ⊕ BottomValueSpace)))

theorem measurable_decodeOptional_zeroPoolCodes (c : (zeroPoolCodes eta heta).Code) :
    Measurable (fun x => decodeOptionalAtom eta heta ((zeroPoolCodes eta heta).value c x)) := by
  cases c with
  | inl s => exact measurable_decodeOptional_evalSeed_zero eta heta s
  | inr n => exact measurable_const

theorem measurable_decodeOptional_poolCodes_zero (c : (poolCodes eta heta 0).Code) :
    Measurable (fun x => decodeOptionalAtom eta heta ((poolCodes eta heta 0).value c x)) := by
  have htransfer (P : PoolCodes eta heta 0) (hP : P = zeroPoolCodes eta heta) :
      ∀ c : P.Code, Measurable (fun x => decodeOptionalAtom eta heta (P.value c x)) := by
    cases hP
    exact measurable_decodeOptional_zeroPoolCodes eta heta
  exact htransfer _ (poolCodes_zero eta heta) c

theorem measurable_decodeOptional_poolPartialList_zero (n : ℕ) :
    Measurable (fun x => decodeOptionalAtom eta heta (poolPartialList eta heta 0 n x)) :=
  measurable_decodeOptional_poolCodes_zero eta heta _

/-- The actual bottom pool enumeration has a Borel native bottom value. -/
theorem measurable_decodeAtom_poolEnumeration_zero (k : ℕ) :
    Measurable (fun x => decodeAtom eta heta (poolEnumeration eta heta 0 x k)) := by
  let f : (fsTower eta).Carrier × ℕ → Unit ⊕ BottomValueSpace :=
    fun p => decodeOptionalAtom eta heta (poolPartialList eta heta 0 p.2 p.1)
  have hf : Measurable f := measurable_from_prod_countable_left
    (fun n => measurable_decodeOptional_poolPartialList_zero eta heta n)
  have hs : Measurable (fun x => (x,poolEnumerationIndex eta heta 0 x k)) :=
    measurable_id.prodMk (measurable_poolEnumerationIndex eta heta 0 zero_le k)
  let getValue : Unit ⊕ BottomValueSpace → BottomValueSpace := Sum.elim (fun _ => .inr 0) id
  have hg : Measurable getValue := measurable_const.sumElim measurable_id
  convert hg.comp (hf.comp hs) using 1
  funext x
  change decodeAtom eta heta (poolEnumeration eta heta 0 x k) =
    getValue (decodeOptionalAtom eta heta
      (poolPartialList eta heta 0 (poolEnumerationIndex eta heta 0 x k) x))
  rw [poolEnumerationIndex_value]
  rfl

end FSCofinality.CosetConstruction
