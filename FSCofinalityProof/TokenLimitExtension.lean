import FSCofinalityProof.TokenLimitBlock
import FSCofinalityProof.TokenLimitUpper
import FSCofinalityProof.TokenAnchor

noncomputable section

namespace FSCofinality.Tokens
open GenericTables

/-- Limit one-point extension, starting from a prescribed finite history.
The new point separates from every old point at `start`, retains the entire
earlier history, realizes the finitely many branch levels, and then realizes
all ordinary upper requirements without disturbing those choices. -/
theorem limit_extension_core {U : Type} [Nonempty U] {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool)
    (hcol : ∀ n, Function.Injective (fun c : Col n => fun u => profile n u c))
    (e count : ℕ → ℕ) (c : ∀ n, Fin (count n) → Token (Col n))
    (epsilon : ∀ n, Fin (count n) → Bool)
    (hconsistent : ∀ n i j, c n i = c n j → epsilon n i = epsilon n j)
    {Old Upper : Type} [Fintype Old] [Fintype Upper]
    (old : Old → Token U) (upper : Upper → FiniteRole U)
    (hupper : Function.Injective (fun i => (upper i).role))
    (v : Token U) (start steps : ℕ) (hsteps : 0 < steps)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ start) (copyBound : ℕ) :
    ∃ w : Token U, copyBound < w.2 ∧
      (∀ m < start, localCode w m = localCode v m ∧ activeTuple w m = activeTuple v m) ∧
      (∀ n ≥ start, ∀ i, ¬ R profile n w (old i)) ∧
      (∀ i < steps, ∀ j,
        branchEdge profile genericTable (e (start+i)) (start+i) w (c (start+i) j) =
          epsilon (start+i) j) ∧
      ∀ i j, genericTable (((upper i).request w.1 j).index w.2) = (upper i).bit j := by
  classical
  let B : ℕ := Finset.univ.sup (fun i : Old => localCode (old i) start)
  obtain ⟨v0,hb0,hpast,hbits⟩ := limit_branch_block profile hcol e count c epsilon
    hconsistent (fun _ => B) v start steps hbound
  obtain ⟨w,hcopy,hsnap,hupperbits⟩ := limit_upper_extension upper hupper v0
    (start+steps) hb0 copyBound
  have hstart : B < localCode w start := by
    have hb := (hbits 0 hsteps).1
    simp only [Nat.add_zero] at hb
    rw [(hsnap start (by omega)).1]
    exact hb
  refine ⟨w,hcopy,?_,?_,?_,hupperbits⟩
  · intro m hm
    have hs := hsnap m (by omega)
    have hp := hpast m hm
    exact ⟨hs.1.trans hp.1,hs.2.trans hp.2⟩
  · intro n hn i hR
    have heq : localCode w start = localCode (old i) start :=
      localCode_eq_of_le (history w).val (history (old i)).val hn hR.1
    have hi : localCode (old i) start ≤ B :=
      Finset.le_sup (f := fun i : Old => localCode (old i) start) (Finset.mem_univ i)
    rw [heq] at hstart
    exact not_lt_of_ge hi hstart
  · intro i hi j
    have hs := hsnap (start+i) (by omega)
    exact (branchEdge_eq_of_snapshot profile genericTable (e (start+i)) (start+i)
      hs.1 hs.2 (c (start+i) j)).trans ((hbits i hi).2 j)

/-- The anchored form retains the complete early equivalence type. Any
consistent extension sharing a class last at `N` has this form, with its
old anchor supplying all earlier branch bits. -/
theorem anchored_limit_extension {U : Type} [Nonempty U] {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool)
    (hcol : ∀ n, Function.Injective (fun c : Col n => fun u => profile n u c))
    (e count : ℕ → ℕ) (c : ∀ n, Fin (count n) → Token (Col n))
    (epsilon : ∀ n, Fin (count n) → Bool)
    (hconsistent : ∀ n i j, c n i = c n j → epsilon n i = epsilon n j)
    {Old Upper : Type} [Fintype Old] [Fintype Upper]
    (old : Old → Token U) (upper : Upper → FiniteRole U)
    (hupper : Function.Injective (fun i => (upper i).role))
    (anchor : Token U) (N steps : ℕ) (hsteps : 0 < steps) (copyBound : ℕ) :
    ∃ w : Token U, copyBound < w.2 ∧
      (∀ m ≤ N, R profile m w anchor) ∧
      (∀ n > N, ∀ i, ¬ R profile n w (old i)) ∧
      (∀ i < steps, ∀ j,
        branchEdge profile genericTable (e (N+1+i)) (N+1+i) w (c (N+1+i) j) =
          epsilon (N+1+i) j) ∧
      ∀ i j, genericTable (((upper i).request w.1 j).index w.2) = (upper i).bit j := by
  have hb : ∀ a ∈ (history (truncate anchor N)).val.activation, a ≤ N+1 :=
    fun a ha => (truncate_activation_bound anchor N a ha).trans (Nat.le_succ N)
  obtain ⟨w,hcopy,hpast,hsep,hbranch,hupperbits⟩ := limit_extension_core profile hcol
    e count c epsilon hconsistent old upper hupper (truncate anchor N) (N+1) steps hsteps hb copyBound
  refine ⟨w,hcopy,?_,?_,hbranch,hupperbits⟩
  · intro m hm
    have hp := hpast m (by omega)
    have ha := truncate_snapshot anchor N m hm
    refine ⟨hp.1.trans ha.1,?_⟩
    simp only [activeProfiles,hp.2,ha.2]
  · intro n hn
    exact hsep n (by omega)

end FSCofinality.Tokens
