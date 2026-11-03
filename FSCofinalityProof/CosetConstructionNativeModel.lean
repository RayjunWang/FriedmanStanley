import FSCofinalityProof.CosetConstructionModelBorel
import FSCofinalityProof.CosetConstructionProfileBorel
import FSCofinalityProof.CosetConstructionColumnMemberBorel

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def rawEnumeration (x : (fsTower eta).Carrier) : (s : TokenSort eta) → ℕ ≃ raw eta heta x s
  | .inl a => poolEnumerationEquiv eta heta (Frame.rank a) x
  | .inr (lam,n) => columnEnumerationEquiv eta heta (Frame.rank lam.val) lam.property
      (Frame.rank_le_top lam.val) n x

def nativeEnumeration (x : (fsTower eta).Carrier) : ℕ ≃ Vertex eta heta x :=
  vertexEnumeration eta heta (rawEnumeration eta heta) x

def nativeModel (x : (fsTower eta).Carrier) : Structures (language eta heta) :=
  modelWithEnumeration eta heta (bottom eta heta) x (nativeEnumeration eta heta x)

theorem measurable_ordinaryMatrix_rawEnumeration (r : OrdinaryRole eta) (i j : ℕ) :
    Measurable (fun x => ordinaryMatrix eta heta x r
      (rawEnumeration eta heta x (rowSort eta r) i) (rawEnumeration eta heta x (colSort eta r) j)) := by
  cases r with
  | inl a =>
    have h : Measurable (fun x : (fsTower eta).Carrier =>
        ordinaryRaw (poolEnumeration eta heta (Frame.rank a.val+1) x i)
          (poolEnumeration eta heta (Frame.rank a.val) x j)) := by
      apply measurable_to_bool
      change MeasurableSet {x | decide (Member (poolEnumeration eta heta (Frame.rank a.val) x j)
        (poolEnumeration eta heta (Frame.rank a.val+1) x i)) = true}
      simpa only [decide_eq_true_eq] using
        measurableSet_member_poolEnumeration eta heta (Frame.rank a.val) a.property i j
    simpa only [ordinaryMatrix,rawEnumeration,rowSort,colSort,mainSort,Frame.rank_ofOrdinal,
      poolEnumerationEquiv,Equiv.ofBijective_apply] using h
  | inr c =>
    rcases c with ⟨lam,n⟩
    have h : Measurable (fun x : (fsTower eta).Carrier =>
        ordinaryRaw (columnEnumeration eta heta (Frame.rank lam.val) lam.property n x i)
          (poolEnumeration eta heta (Frame.rho eta (Frame.rank lam.val) lam.property n) x j)) := by
      apply measurable_to_bool
      change MeasurableSet {x | decide (Member
        (poolEnumeration eta heta (Frame.rho eta (Frame.rank lam.val) lam.property n) x j)
        (columnEnumeration eta heta (Frame.rank lam.val) lam.property n x i)) = true}
      simpa only [decide_eq_true_eq] using measurableSet_member_column_poolEnumeration eta heta
        (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val) n i j
    convert h using 1
    funext x
    change ordinaryRaw (encodeColumn eta heta (Frame.rank lam.val) lam.property
      (lowerPools eta heta x (Frame.rank lam.val)) n
      (columnEnumerationRaw eta heta (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val) n x i))
      (poolEnumeration eta heta (Frame.rank (Frame.ofOrdinal eta
        (Frame.rho eta (Frame.rank lam.val) lam.property n) _)) x j) = _
    rw [Frame.rank_ofOrdinal,encodeColumn_columnEnumerationRaw]

theorem measurable_limitProfile_rawEnumeration (lam : LimitIndex eta) (n i j : ℕ) :
    Measurable (fun x => limitProfile eta heta x lam n
      (rawEnumeration eta heta x (.inl lam.val) i) (rawEnumeration eta heta x (.inr (lam,n)) j)) := by
  exact measurable_profile_pool_columnEnumeration eta heta (Frame.rank lam.val) lam.property
    (Frame.rank_le_top lam.val) n i j

theorem measurable_bottom_rawEnumeration (v : Token ℕ) (n : ℕ) :
    Measurable (fun x => bottom eta heta x
      (mapToken (rawEnumeration eta heta x (zeroSort eta)) v) n) := by
  let C (x : (fsTower eta).Carrier) : Bottom.Context BottomValueSpace :=
    ⟨v.1.length,fun i => decodeAtom eta heta (poolEnumeration eta heta 0 x v.1[i])⟩
  have hmk : Measurable (fun z : Fin v.1.length → BottomValueSpace =>
      (⟨v.1.length,z⟩ : Bottom.Context BottomValueSpace)) := by
    intro s hs
    exact MeasurableSpace.measurableSet_iInf.mp hs v.1.length
  have hC : Measurable C := hmk.comp (measurable_pi_lambda _ (fun i =>
    measurable_decodeAtom_poolEnumeration_zero eta heta v.1[i]))
  have h := (measurable_pi_apply n).comp (Bottom.measurable_bottomMap.comp
    (hC.prodMk (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => v.2))))
  convert h using 1
  funext x
  unfold bottom bottomListMap decodedBottom contextOfList
  apply congrArg (fun c : Bottom.Context BottomValueSpace => Bottom.bottomMap c v.2 n)
  have hctx {V : Type} (c d : Bottom.Context V)
      (h : List.ofFn c.2 = List.ofFn d.2) : c=d := by
    rcases c with ⟨l,c⟩
    rcases d with ⟨m,d⟩
    have hl : l=m := by simpa only [List.length_ofFn] using congrArg List.length h
    subst m
    apply congrArg (fun f => (⟨l,f⟩ : Bottom.Context V))
    funext i
    have hi := congrArg (fun t : List V => t[i.val]?) h
    simpa only [List.getElem?_ofFn,dif_pos i.isLt,Option.some.injEq] using hi
  apply hctx
  change List.ofFn (List.get _) = List.ofFn (C x).2
  rw [List.ofFn_get]
  apply List.ext_getElem
  · simp [C,mapToken]
  · intro i hi hj
    simp [C,mapToken,rawEnumeration,zeroSort,mainSort,Frame.rank_ofOrdinal,poolEnumerationEquiv]
    rfl

theorem measurable_nativeModel : Measurable (nativeModel eta heta) :=
  measurable_modelWithTemplateEnumeration eta heta (rawEnumeration eta heta)
    (measurable_ordinaryMatrix_rawEnumeration eta heta)
    (measurable_limitProfile_rawEnumeration eta heta) (measurable_bottom_rawEnumeration eta heta)

theorem nativeEnumeration_coordinate_preimage (x : (fsTower eta).Carrier) (n : ℕ) :
    (nativeEnumeration eta heta x).symm (.inl n) = (templateEnumeration eta heta).symm (.inl n) :=
  vertexEnumeration_coordinate_preimage eta heta (rawEnumeration eta heta) x n

end FSCofinality.CosetConstruction.TokenModel
