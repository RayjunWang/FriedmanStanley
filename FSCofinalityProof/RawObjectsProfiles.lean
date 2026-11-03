import FSCofinalityProof.RawObjectsColumns
import Mathlib.Data.Finset.Preimage

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

section Profiles
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))

abbrev SourceTuple := ∀ n, {v : Ambient η hη //
  v ∈ lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n)}

abbrev LimitRow := SourceTuple η hη lam hlam lower ⊕ Finset (Birth η hη lam hlam lower)

def birthEmbedding (htop : lam ≤ Frame.top η) : Birth η hη lam hlam lower ↪ ℕ × Ambient η hη :=
  ⟨encodeBirth η hη lam hlam lower,encodeBirth_injective η hη lam hlam lower htop⟩

def rowObject (htop : lam ≤ Frame.top η) : LimitRow η hη lam hlam lower → Ambient η hη
  | Sum.inl s => sourceSequence (level η lam) (fun n => (s n).val)
  | Sum.inr A => finiteFiller (level η lam) (A.map (birthEmbedding η hη lam hlam lower htop))

theorem rowObject_injective (htop : lam ≤ Frame.top η) :
    Function.Injective (rowObject η hη lam hlam lower htop) := by
  intro r s h
  rcases r with r | A <;> rcases s with s | B
  · apply congrArg Sum.inl
    have hcoord := sourceSequence_injective (level η lam) h
    funext n
    exact Subtype.ext (congrFun hcoord n)
  · exact False.elim (sourceSequence_ne_finiteFiller _ _ _ _ h)
  · exact False.elim (sourceSequence_ne_finiteFiller _ _ _ _ h.symm)
  · exact congrArg Sum.inr ((Finset.map_injective _)
      (finiteFiller_injective (level η lam) h))

theorem rowObject_mem_limitSet (htop : lam ≤ Frame.top η)
    (r : LimitRow η hη lam hlam lower) :
    rowObject η hη lam hlam lower htop r ∈ LimitSet η hη lam hlam lower := by
  rcases r with s | A
  · exact Or.inl ⟨_,rfl,fun n => (s n).property⟩
  · apply Or.inr
    refine ⟨_,rfl,?_⟩
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hp
    exact encodeNew_mem η hη lam hlam lower b.1 b.2

theorem exists_rowObject_of_mem_limitSet (htop : lam ≤ Frame.top η)
    {x : Ambient η hη} (hx : x ∈ LimitSet η hη lam hlam lower) :
    ∃ r, rowObject η hη lam hlam lower htop r = x := by
  classical
  rcases hx with ⟨s,rfl,hs⟩ | ⟨A,rfl,hA⟩
  · exact ⟨Sum.inl (fun n => ⟨s n,hs n⟩),rfl⟩
  · let f := birthEmbedding η hη lam hlam lower htop
    let B := A.preimage f f.injective.injOn
    have hmap : B.map f = A := by
      ext p
      constructor
      · intro hp
        obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hp
        exact Finset.mem_preimage.mp hb
      · intro hp
        obtain ⟨d,hd⟩ := encodeNew_surjective η hη lam hlam lower p.1 (hA p hp)
        let b : Birth η hη lam hlam lower := ⟨p.1,d⟩
        have he : f b = p := Prod.ext rfl hd
        apply Finset.mem_map.mpr
        refine ⟨b,Finset.mem_preimage.mpr ?_,he⟩
        simpa only [he] using hp
    exact ⟨Sum.inr B,congrArg (finiteFiller (level η lam)) hmap⟩

theorem range_rowObject (htop : lam ≤ Frame.top η) :
    range (rowObject η hη lam hlam lower htop) = LimitSet η hη lam hlam lower := by
  ext x
  exact ⟨fun ⟨r,hr⟩ => hr ▸ rowObject_mem_limitSet η hη lam hlam lower htop r,
    exists_rowObject_of_mem_limitSet η hη lam hlam lower htop⟩

def markerBirth (n : ℕ) : Birth η hη lam hlam lower := ⟨n,Sum.inr (Sum.inl ())⟩

def sourceBit (s : SourceTuple η hη lam hlam lower) : Birth η hη lam hlam lower → Bool
  | ⟨n,Sum.inl v⟩ => decide (s n = v)
  | ⟨_,Sum.inr (Sum.inl _)⟩ => true
  | ⟨_,Sum.inr (Sum.inr _)⟩ => false

def rowBit : LimitRow η hη lam hlam lower → Birth η hη lam hlam lower → Bool
  | Sum.inl s,b => sourceBit η hη lam hlam lower s b
  | Sum.inr A,b => decide (b ∈ A)

theorem source_bits_ne_filler (s : SourceTuple η hη lam hlam lower)
    (A : Finset (Birth η hη lam hlam lower)) :
    rowBit η hη lam hlam lower (Sum.inl s) ≠ rowBit η hη lam hlam lower (Sum.inr A) := by
  intro h
  let n := A.sup (fun b => b.1) + 1
  have hquery := congrFun h (markerBirth η hη lam hlam lower n)
  change true = decide (markerBirth η hη lam hlam lower n ∈ A) at hquery
  have hmem := of_decide_eq_true hquery.symm
  have hle : n ≤ A.sup (fun b => b.1) :=
    Finset.le_sup (f := fun b : Birth η hη lam hlam lower => b.1) hmem
  omega

theorem rowBit_injective : Function.Injective (rowBit η hη lam hlam lower) := by
  intro r s h
  rcases r with r | A <;> rcases s with s | B
  · apply congrArg Sum.inl
    funext n
    have hquery := congrFun h (⟨n,Sum.inl (r n)⟩ : Birth η hη lam hlam lower)
    have heq : s n = r n := by
      by_contra hne
      simp only [rowBit,sourceBit,decide_true,decide_eq_false hne] at hquery
      contradiction
    exact heq.symm
  · exact False.elim (source_bits_ne_filler η hη lam hlam lower r B h)
  · exact False.elim (source_bits_ne_filler η hη lam hlam lower s A h.symm)
  · apply congrArg Sum.inr
    ext b
    have hquery := congrFun h b
    by_cases ha : b ∈ A <;> by_cases hb : b ∈ B <;> simp_all [rowBit]

/-- A dedicated column name is its birth ancestor together with the assertion
that its birth precedes the current level. -/
def Column (n : ℕ) := {b : Birth η hη lam hlam lower // b.1 ≤ n}

def propagate (n : ℕ) : Column η hη lam hlam lower n → Column η hη lam hlam lower (n+1) :=
  fun c => ⟨c.val,Nat.le_succ_of_le c.property⟩

theorem propagate_injective (n : ℕ) : Function.Injective (propagate η hη lam hlam lower n) := by
  intro c d h
  exact Subtype.ext (congrArg (fun z : Column η hη lam hlam lower (n+1) => z.val) h)

def profile (n : ℕ) (r : LimitRow η hη lam hlam lower)
    (c : Column η hη lam hlam lower n) : Bool := rowBit η hη lam hlam lower r c.val

theorem profile_propagate (n : ℕ) (r : LimitRow η hη lam hlam lower)
    (c : Column η hη lam hlam lower n) :
    profile η hη lam hlam lower (n+1) r (propagate η hη lam hlam lower n c) =
      profile η hη lam hlam lower n r c := rfl

theorem fullProfile_injective :
    Function.Injective (fun r : LimitRow η hη lam hlam lower => fun n => profile η hη lam hlam lower n r) := by
  intro r s h
  apply rowBit_injective η hη lam hlam lower
  funext b
  exact congrFun (congrFun h b.1) ⟨b,le_rfl⟩

theorem profile_column_separating (n : ℕ) :
    Function.Injective (fun c : Column η hη lam hlam lower n =>
      fun r => profile η hη lam hlam lower n r c) := by
  intro c d h
  have hquery := congrFun h (Sum.inr {c.val})
  have hm : d.val ∈ ({c.val} : Finset (Birth η hη lam hlam lower)) := by
    by_contra hn
    simp only [profile,rowBit,Finset.mem_singleton,decide_true] at hquery
    simp only [Finset.mem_singleton] at hn
    simp only [decide_eq_false hn] at hquery
    contradiction
  exact Subtype.ext (Finset.mem_singleton.mp hm).symm

end Profiles
end FSCofinality.RawObjects
