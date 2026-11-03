import FSCofinalityProof.PaddingFatLemma

set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

theorem FatNode.infinite (a : Ordinal.{0}) (ha : 0 < a) : Infinite (FatNode a) :=
  Infinite.of_injective (fun k : ℕ => FatNode.child (FatNode.root : FatNode a) 0 ha 0 k)
    (FatNode.child_copy_injective (FatNode.root : FatNode a) 0 ha 0)

theorem PaddedNode.infinite (a : Ordinal.{0}) : Infinite (PaddedNode a) := by
  apply Infinite.of_injective (fun n : ℕ => (Sum.inl [n] : PaddedNode a))
  intro m n h
  have he := Sum.inl.inj h
  exact List.singleton_inj.mp he

theorem exists_fat_enumeration (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (hpos : 0 < a) :
    Nonempty (ℕ ≃ FatNode a) := by
  letI := FatNode.countable a ha
  letI := FatNode.infinite a hpos
  infer_instance

theorem exists_padded_enumeration (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    Nonempty (ℕ ≃ PaddedNode a) := by
  letI := PaddedNode.countable a ha
  letI := PaddedNode.infinite a
  infer_instance

def fatEnumeration (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (hpos : 0 < a) :
    ℕ ≃ FatNode a := Classical.choice (exists_fat_enumeration a ha hpos)

def paddedEnumeration (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    ℕ ≃ PaddedNode a := Classical.choice (exists_padded_enumeration a ha)

/-- The canonical and padded trees now have actual structures on the
mission's fixed domain `ℕ`; the enumerations are fixed separately for
each countable ordinal, as required by the source quantifiers. -/
theorem fat_padding_on_nat (a b : Ordinal.{0})
    (ha : a < Ordinal.omega 1) (hpos : 0 < a) (hba : cutoff b ≤ a)
    (C : List ℕ → ℕ) :
    PartialIso.BackAndForth
      (code (PaddedNode.tree a C) (paddedEnumeration a ha))
      (code (FatNode.tree a (C [])) (fatEnumeration a ha hpos)) b [] :=
  fat_padding_backAndForth a b hba C (paddedEnumeration a ha) (fatEnumeration a ha hpos)

end FSCofinality.Padding
