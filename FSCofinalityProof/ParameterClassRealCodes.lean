import FSCofinalityProof.ParameterClassSequences

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory

namespace FSCofinality.ParameterSequences

abbrev Cantor := ℕ → Bool

/-- A standard Borel code for an entire sequence of permutations. -/
def encode : Code → Cantor :=
  (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Code).choose

theorem measurable_encode : Measurable encode :=
  (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Code).choose_spec.1

theorem encode_injective : Function.Injective encode :=
  (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Code).choose_spec.2

def encodeEmbedding : MeasurableEmbedding encode :=
  measurable_encode.measurableEmbedding encode_injective

theorem measurableSet_range_encode : MeasurableSet (range encode) :=
  encodeEmbedding.measurableSet_range

/-- Total decoding, with the constant identity sequence used outside the Borel coding range. -/
def decode (r : Cantor) : Code :=
  if h : r ∈ range encode then encodeEmbedding.equivRange.symm ⟨r,h⟩ else fun _ => 1

theorem measurable_decode : Measurable decode := by
  unfold decode
  exact Measurable.dite (by fun_prop) measurable_const measurableSet_range_encode

@[simp] theorem decode_encode (d : Code) : decode (encode d) = d := by
  simp [decode]

theorem encode_decode_of_mem_range {r : Cantor} (hr : r ∈ range encode) :
    encode (decode r) = r := by
  obtain ⟨d,rfl⟩ := hr
  simp

theorem mem_range_encode_iff (r : Cantor) :
    r ∈ range encode ↔ encode (decode r) = r := by
  constructor
  · exact encode_decode_of_mem_range
  · intro h
    exact h ▸ mem_range_self (decode r)

def EncodedValid : Set Cantor := encode '' {d : Code | Valid d}

theorem measurableSet_encodedValid : MeasurableSet EncodedValid :=
  encodeEmbedding.measurableSet_image' measurableSet_valid

theorem mem_encodedValid_iff (r : Cantor) :
    r ∈ EncodedValid ↔ Valid (decode r) ∧ encode (decode r) = r := by
  constructor
  · rintro ⟨d,hd,rfl⟩
    exact ⟨by simpa using hd,by simp⟩
  · rintro ⟨hd,hr⟩
    exact ⟨decode r,hd,hr⟩

end FSCofinality.ParameterSequences
