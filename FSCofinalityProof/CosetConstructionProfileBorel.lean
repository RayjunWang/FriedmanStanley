import FSCofinalityProof.CosetConstructionProfileShapes
import FSCofinalityProof.CosetConstructionSelectionBorel

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta)

abbrev LimitCode := SeedIndex ⊕ Finset (BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a))

def ProfileCodeTrue (row : LimitCode eta heta lam hlam) {n : ℕ}
    (c : ColumnCode eta heta lam hlam n) (x : (fsTower eta).Carrier) : Prop :=
  match row with
  | .inl s => evalSeed eta heta lam s x ≠ none ∧
      match c.val.2 with
      | .inl d => (poolCodes eta heta (Frame.q eta lam hlam c.val.1)).value d x ≠ none ∧
          seedCoordinate eta heta lam s c.val.1 x =
            (poolCodes eta heta (Frame.q eta lam hlam c.val.1)).value d x
      | .inr (.inl _) => True
      | .inr (.inr _) => False
  | .inr A =>
      liftFinite (0,extraAtom 0)
        (fun b => evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x) A ≠ none ∧
      evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x ≠ none ∧
      ∃ b ∈ A, evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x =
        evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x

include htop in
theorem measurableSet_profileCodeTrue (row : LimitCode eta heta lam hlam) {n : ℕ}
    (c : ColumnCode eta heta lam hlam n) : MeasurableSet {x | ProfileCodeTrue eta heta lam hlam row c x} := by
  have hnone := measurableSet_evalBirthCode_none eta heta lam hlam (fun a _ => poolCodes eta heta a)
    (fun a ha => (poolCodes_borel eta heta a (ha.le.trans htop)).absent)
  have heq := measurableSet_evalBirthCode_equal eta heta lam hlam (fun a _ => poolCodes eta heta a) htop
    (fun a ha => (poolCodes_borel eta heta a (ha.le.trans htop)).absent)
    (fun a ha => (poolCodes_borel eta heta a (ha.le.trans htop)).equal)
  cases row with
  | inl s =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    rcases c with d|⟨⟨⟩⟩|d
    · change MeasurableSet {x | evalSeed eta heta lam s x ≠ none ∧
        (poolCodes eta heta (Frame.q eta lam hlam k)).value d x ≠ none ∧
        seedCoordinate eta heta lam s k x = (poolCodes eta heta (Frame.q eta lam hlam k)).value d x}
      simp only [setOf_and]
      exact (measurableSet_evalSeed_absent eta heta lam s).compl.inter
        (((poolCodes_borel eta heta _ ((Frame.q_lt eta lam hlam k).le.trans htop)).absent d).compl.inter
          (measurableSet_codeRep_eq_diagonal eta heta _ ((Frame.q_lt eta lam hlam k).le.trans htop)
            (codeRep_seedCoordinate eta heta lam hlam htop s k) (codeRep_value eta heta _ d)))
    · simpa only [ProfileCodeTrue,and_true] using (measurableSet_evalSeed_absent eta heta lam s).compl
    · simp only [ProfileCodeTrue,and_false,setOf_false]
      exact MeasurableSet.empty
  | inr A =>
    simp only [ProfileCodeTrue,setOf_and]
    refine (measurableSet_liftFinite_none (0,extraAtom 0) _ hnone A).compl.inter
      ((hnone c.val).compl.inter ?_)
    simp only [←exists_prop,setOf_exists]
    exact MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun _ =>
      (heq b c.val).preimage (measurable_id.prodMk measurable_id)))

theorem profileCodeTrue_spec (x : (fsTower eta).Carrier)
    (row : LimitCode eta heta lam hlam) (v : Ambient eta heta)
    (hr : (limitPoolCodes eta heta lam hlam (fun a _ => poolCodes eta heta a)).value row x = some v)
    (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (d : Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n)
    (hc : columnCodeValue eta heta lam hlam n c x = some d) :
    ambientProfile eta heta lam hlam htop n v
      (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n d) =
      decide (ProfileCodeTrue eta heta lam hlam row c x) := by
  cases row with
  | inl s =>
    change evalSeed eta heta lam s x = some v at hr
    obtain ⟨z,hz⟩ := evalSeed_limit_source eta heta lam hlam s x v hr
    have hsource : evalSeed eta heta lam s x = some (sourceSequence (level eta lam) z) :=
      hr.trans (congrArg some hz)
    let t := seedSourceTuple eta heta lam hlam htop s x z hsource
    have hcoord (k) := seedCoordinate_source eta heta lam hlam s k x z hsource
    rw [hz]
    have hshape := ambientProfile_source_shape eta heta lam hlam htop x t n d
    change ambientProfile eta heta lam hlam htop n (sourceSequence (level eta lam) (fun k => (t k).val))
      (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n d) = _
    rw [hshape]
    rcases c with ⟨⟨k,c⟩,hk⟩
    rcases c with c|⟨⟨⟩⟩|c
    · dsimp only [columnCodeValue,freshBirthCodeValue] at hc
      split at hc
      · simp at hc
      · rename_i u hu
        cases hc
        simp [sourceBit,ProfileCodeTrue,hr,hu,hcoord,t,seedSourceTuple]
    · cases hc
      simp [sourceBit,ProfileCodeTrue,hr]
    · dsimp only [columnCodeValue,freshBirthCodeValue] at hc
      split at hc
      · simp at hc
      · rename_i u hu
        cases hc
        simp [sourceBit,ProfileCodeTrue]
  | inr A =>
    change (liftFinite (0,extraAtom 0)
      (fun b => evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x) A).map
        (finiteFiller (level eta lam)) = some v at hr
    cases hA : liftFinite (0,extraAtom 0)
        (fun b => evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x) A with
    | none => simp only [hA,Option.map_none] at hr; contradiction
    | some B =>
      have hv : finiteFiller (level eta lam) B = v := by
        simpa only [hA,Option.map_some,Option.some.injEq] using hr
      have hB : ∀ b ∈ B, NewColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) b.1 b.2 := by
        intro b hb
        obtain ⟨e,_,he⟩ := liftFinite_mem _ _ A B hA b hb
        exact (evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a) x b).mp ⟨e,he⟩
      have hbirth : evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x =
          some (encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) d.val) := by
        have h := encodeBirth_columnCodeValue eta heta lam hlam n c x
        rw [hc,Option.map_some] at h
        exact h.symm
      rw [←hv,ambientProfile_filler_shape eta heta lam hlam htop x B hB n d]
      congr 1
      simp only [ProfileCodeTrue,hA,hbirth]
      apply propext
      simpa using liftFinite_mem_iff _ _ A B hA
        (encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) d.val)

theorem poolCodes_cast_value {a : Ordinal.{0}} {P Q : PoolCodes eta heta a}
    (h : P=Q) (c : P.Code) (x : (fsTower eta).Carrier) :
    Q.value (cast (congrArg PoolCodes.Code h) c) x = P.value c x := by
  cases h
  rfl

def limitCodeOfPoolCode (c : (poolCodes eta heta lam).Code) : LimitCode eta heta lam hlam :=
  cast (congrArg PoolCodes.Code (poolCodes_limit eta heta lam hlam)) c

theorem limitCodeOfPoolCode_value (c : (poolCodes eta heta lam).Code) (x : (fsTower eta).Carrier) :
    (limitPoolCodes eta heta lam hlam (fun a _ => poolCodes eta heta a)).value
      (limitCodeOfPoolCode eta heta lam hlam c) x = (poolCodes eta heta lam).value c x :=
  poolCodes_cast_value eta heta (poolCodes_limit eta heta lam hlam) c x

theorem columnCodeValue_enumerated (n : ℕ) (x : (fsTower eta).Carrier) (k : ℕ) :
    columnCodeValue eta heta lam hlam n
      (columnCodeList eta heta lam hlam n (columnEnumerationIndex eta heta lam hlam n x k)) x =
      some (columnEnumerationRaw eta heta lam hlam htop n x k) := by
  apply (option_map_eq_iff_of_injective
    (encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n)
    (encodeColumn_injective eta heta lam hlam _ htop n) _ _).mp
  rw [encodeColumn_columnCodeValue,Option.map_some,encodeColumn_columnEnumerationRaw]
  exact columnEnumerationIndex_value eta heta lam hlam htop n x k

theorem measurable_profile_pool_columnEnumeration (n i j : ℕ) :
    Measurable (fun x : (fsTower eta).Carrier =>
      ambientProfile eta heta lam hlam htop n (poolEnumeration eta heta lam x i)
        (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n
          (columnEnumerationRaw eta heta lam hlam htop n x j))) := by
  let P (r c : ℕ) (x : (fsTower eta).Carrier) := ProfileCodeTrue eta heta lam hlam
    (limitCodeOfPoolCode eta heta lam hlam (poolCodeList eta heta lam r))
    (columnCodeList eta heta lam hlam n c) x
  have hP (r c : ℕ) : MeasurableSet {x | P r c x} :=
    measurableSet_profileCodeTrue eta heta lam hlam htop _ _
  have hselected := measurableSet_selected₂ P hP
    (fun x => poolEnumerationIndex eta heta lam x i)
    (fun x => columnEnumerationIndex eta heta lam hlam n x j)
    (measurable_poolEnumerationIndex eta heta lam htop i)
    (measurable_columnEnumerationIndex eta heta lam hlam htop n j)
  have hbool : Measurable (fun x => decide (P (poolEnumerationIndex eta heta lam x i)
      (columnEnumerationIndex eta heta lam hlam n x j) x)) := by
    apply measurable_to_bool
    change MeasurableSet {x | decide (P (poolEnumerationIndex eta heta lam x i)
      (columnEnumerationIndex eta heta lam hlam n x j) x) = true}
    simpa only [decide_eq_true_eq] using hselected
  convert hbool using 1
  funext x
  apply profileCodeTrue_spec eta heta lam hlam htop x _ _ _ n _ _
    (columnCodeValue_enumerated eta heta lam hlam htop n x j)
  rw [limitCodeOfPoolCode_value]
  exact poolEnumerationIndex_value eta heta lam x i

end FSCofinality.CosetConstruction
