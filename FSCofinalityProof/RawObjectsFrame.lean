import FSCofinalityProof.HierarchyBasics
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects.Frame

def top (η : Ordinal.{0}) : Ordinal.{0} := η + Ordinal.omega0

theorem lt_top (η : Ordinal.{0}) : η < top η :=
  lt_add_of_pos_right η Ordinal.omega0_pos

theorem top_isSuccLimit (η : Ordinal.{0}) : IsSuccLimit (top η) :=
  Ordinal.isSuccLimit_add η Ordinal.isSuccLimit_omega0

theorem top_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) :
    top η < Ordinal.omega 1 :=
  (Ordinal.isPrincipal_add_omega 1) hη Ordinal.omega0_lt_omega_one

/-- The top fundamental sequence is prescribed; all lower source stages
keep the fundamental sequences in the fixed hierarchy definitions. -/
def q (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) : ℕ → Ordinal.{0} :=
  if lam = top η then fun n => η + n else fundamentalSequence lam hlam

@[simp] theorem q_top (η : Ordinal.{0}) (n : ℕ) :
    q η (top η) (top_isSuccLimit η) n = η + n := by simp [q]

theorem q_of_le_source (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (h : lam ≤ η) :
    q η lam hlam = fundamentalSequence lam hlam := by
  have hne : lam ≠ top η := ne_of_lt (lt_of_le_of_lt h (lt_top η))
  simp only [q,if_neg hne]

theorem q_lt (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) : q η lam hlam n < lam := by
  by_cases h : lam = top η
  · subst lam
    simp only [q,if_pos rfl]
    exact (add_lt_add_iff_left η).mpr (Ordinal.natCast_lt_omega0 n)
  · simpa only [q,if_neg h] using fundamentalSequence_lt lam hlam n

theorem q_strictMono (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (hc : lam < Ordinal.omega 1) : StrictMono (q η lam hlam) := by
  by_cases h : lam = top η
  · subst lam
    intro n m hnm
    simp only [q,if_pos rfl]
    exact (add_lt_add_iff_left η).mpr (by exact_mod_cast hnm)
  · simpa only [q,if_neg h] using fundamentalSequence_strictMono lam hlam hc

theorem q_cofinal (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (hc : lam < Ordinal.omega 1) (b : Ordinal.{0}) (hb : b < lam) :
    ∃ n, b ≤ q η lam hlam n := by
  by_cases h : lam = top η
  · subst lam
    obtain ⟨d,hd,hbd⟩ := (Ordinal.lt_add_iff Ordinal.omega0_ne_zero).mp hb
    obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp hd
    exact ⟨n,by simpa only [q,if_pos rfl,hn] using hbd⟩
  · simpa only [q,if_neg h] using fundamentalSequence_cofinal lam hlam hc b hb

def sigma (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) : ℕ → Ordinal.{0}
  | 0 => q η lam hlam 0
  | n+1 => max (q η lam hlam (n+1)) (sigma η lam hlam n + 2)

def rho (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) : Ordinal.{0} :=
  sigma η lam hlam n + 1

def delta (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) : Ordinal.{0} :=
  sigma η lam hlam n + 2

theorem q_le_sigma (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    q η lam hlam n ≤ sigma η lam hlam n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

theorem delta_le_sigma_next (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    delta η lam hlam n ≤ sigma η lam hlam (n+1) := le_max_right _ _

theorem sigma_lt (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    sigma η lam hlam n < lam := by
  induction n with
  | zero => exact q_lt η lam hlam 0
  | succ n ih =>
    apply max_lt (q_lt η lam hlam (n+1))
    simpa only [succ_eq_add_one,add_assoc,one_add_one_eq_two] using
      hlam.succ_lt (hlam.succ_lt ih)

theorem rho_lt (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    rho η lam hlam n < lam := hlam.succ_lt (sigma_lt η lam hlam n)

theorem delta_lt (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    delta η lam hlam n < lam := by
  simpa only [delta,succ_eq_add_one,add_assoc,one_add_one_eq_two] using
    hlam.succ_lt (hlam.succ_lt (sigma_lt η lam hlam n))

theorem delta_strictMono (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    StrictMono (delta η lam hlam) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact lt_of_le_of_lt (delta_le_sigma_next η lam hlam n)
    (lt_add_of_pos_right _ (by norm_num : (0 : Ordinal.{0}) < 2))

theorem delta_cofinal (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (hc : lam < Ordinal.omega 1) (b : Ordinal.{0}) (hb : b < lam) :
    ∃ n, b ≤ delta η lam hlam n := by
  obtain ⟨n,hn⟩ := q_cofinal η lam hlam hc b hb
  exact ⟨n,hn.trans ((q_le_sigma η lam hlam n).trans le_self_add)⟩

theorem exists_le_rho (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (hc : lam < Ordinal.omega 1) (b : Ordinal.{0}) (hb : b < lam) :
    ∃ n, b ≤ rho η lam hlam n := by
  obtain ⟨n,hn⟩ := q_cofinal η lam hlam hc b hb
  exact ⟨n,hn.trans ((q_le_sigma η lam hlam n).trans le_self_add)⟩

/-- Small codes for exactly the layers at or below the top ordinal. -/
abbrev Layer (η : Ordinal.{0}) := (top η + 1).ToType

def rank {η : Ordinal.{0}} (l : Layer η) : Ordinal.{0} := l.toOrd.val

theorem rank_le_top {η : Ordinal.{0}} (l : Layer η) : rank l ≤ top η :=
  lt_add_one_iff.mp l.toOrd.property

def ofOrdinal (η a : Ordinal.{0}) (ha : a ≤ top η) : Layer η :=
  Ordinal.ToType.mk ⟨a,lt_add_one_iff.mpr ha⟩

@[simp] theorem rank_ofOrdinal (η a : Ordinal.{0}) (ha : a ≤ top η) :
    rank (ofOrdinal η a ha) = a := by
  exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

@[simp] theorem ofOrdinal_rank {η : Ordinal.{0}} (l : Layer η) :
    ofOrdinal η (rank l) (rank_le_top l) = l := Ordinal.ToType.mk.apply_symm_apply l

theorem layer_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) : Countable (Layer η) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType]
  apply Cardinal.lt_aleph_one_iff.mp
  apply Cardinal.lt_omega_iff_card_lt.mp
  exact (Cardinal.isSuccLimit_omega 1).succ_lt (top_countable η hη)

def layerCode (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) : Layer η ↪ ℕ := by
  letI := layer_countable η hη
  letI := Encodable.ofCountable (Layer η)
  exact ⟨Encodable.encode,Encodable.encode_injective⟩

end FSCofinality.RawObjects.Frame
