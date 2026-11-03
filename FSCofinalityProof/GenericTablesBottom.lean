import FSCofinalityProof.GenericTablesHistories
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.List

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology

namespace FSCofinality.GenericTables.Bottom

abbrev Cantor := ℕ → Bool
abbrev Pattern := ℕ × Finset (ℕ × List Bool)

def bitsPrefix (z : Cantor) (n : ℕ) : List Bool := List.ofFn (fun i : Fin n => z i)

theorem continuous_bitsPrefix (n : ℕ) : Continuous (fun z : Cantor => bitsPrefix z n) :=
  (continuous_of_discreteTopology : Continuous (List.ofFn : (Fin n → Bool) → List Bool)).comp
    (continuous_pi (fun i => continuous_apply (i : ℕ)))

def coordinatePattern (q : ℕ) : Pattern :=
  (Encodable.decode (α := Pattern) (Nat.unpair q).1).getD (0,∅)

@[simp] theorem coordinatePattern_pair (p : Pattern) (t : ℕ) :
    coordinatePattern (Nat.pair (Encodable.encode p) t) = p := by
  simp [coordinatePattern,Nat.unpair_pair]

/-- A continuous family of independent rows with arbitrary fixed finite prefixes. -/
def beta (fixed : ℕ → List Bool) (z : Cantor) (k : ℕ) : Cantor := fun q =>
  if hq : q < (fixed k).length then (fixed k)[q]
  else decide ((k,bitsPrefix z (coordinatePattern q).1) ∈ (coordinatePattern q).2)

theorem beta_prefix (fixed : ℕ → List Bool) (z : Cantor) (k i : ℕ)
    (hi : i < (fixed k).length) : beta fixed z k i = (fixed k)[i] := by
  simp [beta,hi]

theorem continuous_beta_fixed (fixed : ℕ → List Bool) (k : ℕ) :
    Continuous (fun z : Cantor => beta fixed z k) := by
  apply continuous_pi
  intro q
  by_cases hq : q < (fixed k).length
  · simp only [beta,dif_pos hq]
    exact continuous_const
  · simp only [beta,dif_neg hq]
    apply (continuous_of_discreteTopology : Continuous
      (fun s : List Bool => decide ((k,s) ∈ (coordinatePattern q).2))).comp
    exact continuous_bitsPrefix _

theorem continuous_beta (fixed : ℕ → List Bool) :
    Continuous (fun p : Cantor × ℕ => beta fixed p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hk : ∀ᶠ q : Cantor × ℕ in 𝓝 p, q.2 = p.2 :=
    (continuous_snd.tendsto p).eventually ((isOpen_discrete {p.2}).mem_nhds rfl)
  have hc : ContinuousAt (fun q : Cantor × ℕ => beta fixed q.1 p.2) p :=
    ((continuous_beta_fixed fixed p.2).comp continuous_fst).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [hk] with q hq
  rw [hq]

theorem exists_prefix_injective {ι : Type*} [Fintype ι] (p : ι → Cantor × ℕ)
    (hp : Function.Injective p) :
    ∃ n : ℕ, Function.Injective (fun i => ((p i).2,bitsPrefix (p i).1 n)) := by
  classical
  have hpair (i j : ι) : ∃ n : ℕ, ∀ m ≥ n,
      ((p i).2,bitsPrefix (p i).1 m) = ((p j).2,bitsPrefix (p j).1 m) → i = j := by
    by_cases hij : i = j
    · exact ⟨0,fun _ _ _ => hij⟩
    by_cases hk : (p i).2 = (p j).2
    · have hz : (p i).1 ≠ (p j).1 := by
        intro h
        exact hij (hp (Prod.ext h hk))
      have hex : ∃ r : ℕ, (p i).1 r ≠ (p j).1 r := by
        by_contra! h
        exact hz (funext h)
      obtain ⟨r,hr⟩ := hex
      refine ⟨r+1,fun m hm heq => ?_⟩
      have hh : bitsPrefix (p i).1 m = bitsPrefix (p j).1 m := congrArg Prod.snd heq
      have hpoint := congrFun (List.ofFn_injective hh) ⟨r,by omega⟩
      exact False.elim (hr hpoint)
    · exact ⟨0,fun _ _ heq => False.elim (hk (congrArg Prod.fst heq))⟩
  choose n hn using hpair
  let N : ℕ := Finset.univ.sup (fun ij : ι×ι => n ij.1 ij.2)
  refine ⟨N,fun i j heq => hn i j N ?_ heq⟩
  exact Finset.le_sup (f := fun ij : ι×ι => n ij.1 ij.2) (Finset.mem_univ (i,j))

/-- Every pattern on finitely many distinct rows occurs beyond every bound.
This supplies the finite independence used for new coordinate vertices. -/
theorem beta_finite_independence (fixed : ℕ → List Bool)
    {ι : Type*} [Fintype ι] (p : ι → Cantor × ℕ) (hp : Function.Injective p)
    (epsilon : ι → Bool) (N : ℕ) :
    ∃ q > N, ∀ i, beta fixed (p i).1 (p i).2 q = epsilon i := by
  classical
  obtain ⟨n,hn⟩ := exists_prefix_injective p hp
  let key : ι → ℕ × List Bool := fun i => ((p i).2,bitsPrefix (p i).1 n)
  let pos : Finset (ℕ × List Bool) :=
    (Finset.univ.filter (fun i => epsilon i = true)).image key
  have hpos (i : ι) : decide (key i ∈ pos) = epsilon i := by
    cases hi : epsilon i
    · apply decide_eq_false_iff_not.mpr
      rintro hh
      obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hh
      have heq : j = i := hn hji
      subst j
      have htrue : epsilon i = true := (Finset.mem_filter.mp hj).2
      rw [hi] at htrue
      contradiction
    · apply decide_eq_true
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  let L := Finset.univ.sup (fun i : ι => (fixed (p i).2).length)
  let q := Nat.pair (Encodable.encode (n,pos)) (N+L+1)
  have hq : N+L+1 ≤ q := Nat.right_le_pair _ _
  refine ⟨q,by omega,fun i => ?_⟩
  have hi : ¬ q < (fixed (p i).2).length := by
    have hl : (fixed (p i).2).length ≤ L :=
      Finset.le_sup (f := fun j : ι => (fixed (p j).2).length) (Finset.mem_univ i)
    omega
  simp only [beta,dif_neg hi,q,coordinatePattern_pair]
  exact hpos i

theorem beta_injective (fixed : ℕ → List Bool) :
    Function.Injective (fun p : Cantor × ℕ => beta fixed p.1 p.2) := by
  intro p q heq
  by_contra hpq
  let f : Bool → Cantor × ℕ := fun b => if b then q else p
  have hf : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp_all [f]
  obtain ⟨j,_,hj⟩ := beta_finite_independence fixed f hf id 0
  have h0 := hj false
  have h1 := hj true
  simp only [f,Bool.false_eq_true,if_false,if_true,id_eq] at h0 h1
  have h := congrFun heq j
  change beta fixed p.1 p.2 j = beta fixed q.1 q.2 j at h
  rw [h0,h1] at h
  contradiction

end FSCofinality.GenericTables.Bottom
