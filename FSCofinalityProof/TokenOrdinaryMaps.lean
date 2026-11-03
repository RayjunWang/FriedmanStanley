import FSCofinalityProof.TokenFiniteRoles

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem raw_nonempty (z : (fsTower eta).Carrier) (s : TokenSort eta) : Nonempty (raw eta heta z s) := by
  cases s with
  | inl a =>
    letI : Infinite (raw eta heta z (.inl a)) := pool_infinite eta heta _ _
    exact Infinite.nonempty _
  | inr c =>
    exact ⟨⟨markerBirth eta heta _ c.1.property _ 0,Nat.zero_le c.2⟩⟩

theorem ordinary_requests_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (initial : List (raw eta heta y s)) (N : ℕ) :
    ∃ w : Token (raw eta heta y s), N < w.2 ∧ (∃ extra, w.1=initial++extra) ∧
      OrdinaryRequestsRealized eta heta R hR s v w := by
  letI := raw_nonempty eta heta y s
  obtain ⟨rows,k,hk,hrows,hbits⟩ := ordinary_extension (ordinaryRequirements eta heta R hR s v)
    (ordinaryRequirements_roles_injective eta heta R hR s v) initial N
  exact ⟨(rows,k),hk,hrows,hbits⟩

theorem ordinary_bottom_requests_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (v : Token (raw eta heta x (zeroSort eta))) (s : List Bool) (N : ℕ) :
    ∃ w : Token (raw eta heta y (zeroSort eta)), N < w.2 ∧
      OrdinaryRequestsRealized eta heta R hR (zeroSort eta) v w ∧
      Bottom.bitsPrefix (bottom eta heta y w) s.length=s := by
  letI := raw_nonempty eta heta y (zeroSort eta)
  obtain ⟨rows,k,hk,_,hbits,hbottom⟩ := ordinary_bottom_extension_mapped
    (fun u : raw eta heta y (zeroSort eta) => decodeAtom eta heta u.val)
    (ordinaryRequirements eta heta R hR (zeroSort eta) v)
    (ordinaryRequirements_roles_injective eta heta R hR (zeroSort eta) v) [] s N
  exact ⟨(rows,k),hk,hbits,hbottom⟩

def branchRequirement (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n)))) :
    FiniteRole (raw eta heta y (.inr (lam,n))) := by
  let I := SortEntries eta heta R (.inl lam.val)
  let idx := (Fintype.equivFin I).symm
  exact {
    Opposite := raw eta heta y (.inr (lam,n)) → Bool
    count := Fintype.card I
    context := fun j => activeProfiles (limitProfile eta heta y lam) (targetEntry eta heta R _ (idx j)) n
    label := fun j => localCode (targetEntry eta heta R _ (idx j)) n
    bit := fun j => branch eta heta x lam n (sourceEntry eta heta R hR _ (idx j)) v
    raw := fun c f => f c
    separated := fun f g h => funext (fun c => congrFun h c)
    direction := false
    role := roleNumber eta heta (.inr (lam,n))
    consistent := by
      intro i j hc hl
      have hRY : Tokens.R (limitProfile eta heta y lam) n
          (targetEntry eta heta R _ (idx i)) (targetEntry eta heta R _ (idx j)) := ⟨hl,hc⟩
      have hRX := (entries_preserve_limit_R eta heta R hR lam n (idx i) (idx j)).mpr hRY
      exact (R_iff_branch_neighborhood _ genericTable_generic (roleNumber eta heta (.inr (lam,n))) n _ _).mp hRX v }

def columnRequirements (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n)))) :
    (finiteOrdinaryRoles eta heta R (.inr (lam,n))) ⊕ Unit → FiniteRole (raw eta heta y (.inr (lam,n))) :=
  Sum.elim (ordinaryRequirements eta heta R hR (.inr (lam,n)) v)
    (fun _ => branchRequirement eta heta R hR lam n v)

theorem columnRequirements_roles_injective (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n)))) :
    Function.Injective (fun i => (columnRequirements eta heta R hR lam n v i).role) := by
  intro i j hij
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
  · exact congrArg Sum.inl (ordinaryRequirements_roles_injective eta heta R hR _ v hij)
  · simp only [columnRequirements,Sum.elim_inl,Sum.elim_inr,ordinaryRequirements,
      ordinaryRequirement_role,branchRequirement] at hij
    have hh := (roleNumber eta heta).injective hij
    cases hh
  · simp only [columnRequirements,Sum.elim_inl,Sum.elim_inr,ordinaryRequirements,
      ordinaryRequirement_role,branchRequirement] at hij
    have hh := (roleNumber eta heta).injective hij
    cases hh
  · rfl

theorem column_requests_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n)))) (N : ℕ) :
    ∃ w : Token (raw eta heta y (.inr (lam,n))), N < w.2 ∧
      OrdinaryRequestsRealized eta heta R hR (.inr (lam,n)) v w ∧
      ∀ i : SortEntries eta heta R (.inl lam.val),
        branch eta heta x lam n (sourceEntry eta heta R hR _ i) v =
          branch eta heta y lam n (targetEntry eta heta R _ i) w := by
  letI := raw_nonempty eta heta y (.inr (lam,n))
  obtain ⟨rows,k,hk,_,hbits⟩ := ordinary_extension (columnRequirements eta heta R hR lam n v)
    (columnRequirements_roles_injective eta heta R hR lam n v) [] N
  refine ⟨(rows,k),hk,(fun i j => hbits (.inl i) j),fun i => ?_⟩
  have hh := hbits (.inr ()) ((Fintype.equivFin (SortEntries eta heta R (.inl lam.val))) i)
  have heval : (fun (f : raw eta heta y (.inr (lam,n)) → Bool) u => f u) = id := rfl
  simpa only [columnRequirements,Sum.elim_inr,branchRequirement,FiniteRole.request,orientMatrix,
    Bool.false_eq_true,if_false,Request.index,Equiv.symm_apply_apply,transpose_contextMatrix,
    branch,branchEdge,heval,List.map_id] using hh.symm

end FSCofinality.CosetConstruction.TokenModel
