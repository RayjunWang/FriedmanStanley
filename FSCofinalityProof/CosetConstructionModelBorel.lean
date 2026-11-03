import FSCofinalityProof.CosetConstructionModelEnumeration
import FSCofinalityProof.CosetConstructionSelectionBorel

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem boolMatrix_ext (M N : BoolMatrix) (hl : M.1=N.1) (hm : M.2.1=N.2.1)
    (he : ∀ i j, M.entry i j = N.entry i j) : M=N := by
  rcases M with ⟨l,m,f⟩
  rcases N with ⟨l',m',g⟩
  dsimp only at hl hm
  subst l'
  subst m'
  apply congrArg (fun k => (⟨l,m,k⟩ : BoolMatrix))
  funext i j
  have h := he i.val j.val
  simpa only [BoolMatrix.entry,dif_pos i.isLt,dif_pos j.isLt] using h

theorem contextMatrix_map_normal {U V : Type} (R : U → V → Bool) (v : List U) (w : List V) :
    contextMatrix (v.map R) w =
      ⟨v.length,w.length,fun i j => R v[i] w[j]⟩ := by
  apply boolMatrix_ext
  · exact List.length_map _
  · rfl
  · intro i j
    by_cases hi : i<v.length <;> by_cases hj : j<w.length <;>
      simp [contextMatrix,BoolMatrix.entry,hi,hj]

theorem ordinaryEdge_mapToken_both {U V W Z : Type}
    (A : Table) (e : ℕ) (R : W → Z → Bool) (f : U → W) (g : V → Z)
    (v : Token U) (w : Token V) :
    ordinaryEdge A e R (mapToken f v) (mapToken g w) =
      ordinaryEdge A e (fun u v => R (f u) (g v)) v w := by
  simp only [ordinaryEdge,mapToken]
  apply congrArg (fun M => A (e,M,w.2,v.2))
  apply boolMatrix_ext
  · simp [contextMatrix]
  · simp [contextMatrix]
  · intro i j
    by_cases hi : i<v.1.length <;> by_cases hj : j<w.1.length <;>
      simp [contextMatrix,BoolMatrix.entry,hi,hj]

theorem branchEdge_mapToken_both {U V : Type} {Col D : ℕ → Type}
    (A : Table) (e n : ℕ) (P : ∀ n, V → D n → Bool)
    (f : U → V) (g : ∀ n, Col n → D n) (v : Token U) (w : Token (Col n)) :
    branchEdge P A e n (mapToken f v) (mapToken (g n) w) =
      branchEdge (fun n u c => P n (f u) (g n c)) A e n v w := by
  simp only [branchEdge,activeProfiles]
  rw [activeTuple_mapToken,localCode_mapToken]
  simp only [mapToken]
  apply congrArg (fun M => A (e,M,w.2,localCode v n))
  apply boolMatrix_ext
  · simp [contextMatrix]
  · simp [contextMatrix]
  · intro i j
    by_cases hi : i<(activeTuple v n).length <;> by_cases hj : j<w.1.length <;>
      simp [contextMatrix,BoolMatrix.entry,hi,hj]

theorem measurable_ordinaryEdge {X : Type} [MeasurableSpace X]
    (A : Table) (e : ℕ) (R : X → ℕ → ℕ → Bool)
    (hR : ∀ i j, Measurable (fun x => R x i j)) (v w : Token ℕ) :
    Measurable (fun x => ordinaryEdge A e (R x) v w) := by
  let M (x : X) : Fin v.1.length → Fin w.1.length → Bool := fun i j => R x v.1[i] w.1[j]
  have hM : Measurable M := measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => hR _ _))
  let F (m : Fin v.1.length → Fin w.1.length → Bool) := A (e,⟨v.1.length,w.1.length,m⟩,w.2,v.2)
  convert (measurable_of_countable F).comp hM using 1
  funext x
  simp only [ordinaryEdge,contextMatrix_map_normal]
  rfl

theorem measurable_branchEdge {X : Type} [MeasurableSpace X]
    (A : Table) (e n : ℕ) (P : X → ℕ → ℕ → ℕ → Bool)
    (hP : ∀ n i j, Measurable (fun x => P x n i j)) (v w : Token ℕ) :
    Measurable (fun x => branchEdge (P x) A e n v w) := by
  let M (x : X) : Fin (activeTuple v n).length → Fin w.1.length → Bool :=
    fun i j => P x n (activeTuple v n)[i] w.1[j]
  have hM : Measurable M := measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => hP _ _ _))
  let F (m : Fin (activeTuple v n).length → Fin w.1.length → Bool) :=
    A (e,⟨(activeTuple v n).length,w.1.length,m⟩,w.2,localCode v n)
  convert (measurable_of_countable F).comp hM using 1
  funext x
  simp only [branchEdge,activeProfiles,contextMatrix_map_normal]
  rfl

theorem measurable_edgeAt_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (s t : TokenSort eta)
    (f : ∀ x, Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (hf : ∀ v w : Token ℕ, Measurable (fun x => f x (mapToken (e x s) v) (mapToken (e x t) w)))
    (u v : Template eta) :
    Measurable (fun x => edgeAt eta heta s t (f x)
      (templateVertexEquiv eta heta x (e x) u) (templateVertexEquiv eta heta x (e x) v)) := by
  simp only [edgeAt,tokenAt_templateVertexEquiv]
  cases hu : templateTokenAt eta s u with
  | none => simpa only [Option.map_none,Option.elim_none] using
      (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => false))
  | some a =>
    cases hv : templateTokenAt eta t v with
    | none => simpa only [Option.map_some,Option.map_none,Option.elim_some,Option.elim_none] using
        (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => false))
    | some b => simpa only [Option.map_some,Option.elim_some] using hf a b

theorem measurable_ordinary_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hO : ∀ r i j, Measurable (fun x => ordinaryMatrix eta heta x r
      (e x (rowSort eta r) i) (e x (colSort eta r) j)))
    (r : OrdinaryRole eta) (v w : Token ℕ) :
    Measurable (fun x => ordinary eta heta x r
      (mapToken (e x (rowSort eta r)) v) (mapToken (e x (colSort eta r)) w)) := by
  simp only [ordinary,ordinaryEdge_mapToken_both]
  exact measurable_ordinaryEdge genericTable _ _ (hO r) v w

theorem measurable_branch_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hP : ∀ lam n i j, Measurable (fun x => limitProfile eta heta x lam n
      (e x (.inl lam.val) i) (e x (.inr (lam,n)) j)))
    (lam : LimitIndex eta) (n : ℕ) (v w : Token ℕ) :
    Measurable (fun x => branch eta heta x lam n
      (mapToken (e x (.inl lam.val)) v) (mapToken (e x (.inr (lam,n))) w)) := by
  have h := measurable_branchEdge genericTable (roleNumber eta heta (.inr (lam,n))) n
    (fun x m i j => limitProfile eta heta x lam m
      (e x (.inl lam.val) i) (e x (.inr (lam,m)) j)) (hP lam) v w
  convert h using 1
  funext x
  exact branchEdge_mapToken_both genericTable _ n (limitProfile eta heta x lam)
    (e x (.inl lam.val)) (fun m => e x (.inr (lam,m))) v w

theorem measurable_R_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hP : ∀ lam n i j, Measurable (fun x => limitProfile eta heta x lam n
      (e x (.inl lam.val) i) (e x (.inr (lam,n)) j)))
    (lam : LimitIndex eta) (n : ℕ) (v w : Token ℕ) :
    Measurable (fun x => decide (R (limitProfile eta heta x lam) n
      (mapToken (e x (.inl lam.val)) v) (mapToken (e x (.inl lam.val)) w))) := by
  apply measurable_to_bool
  change MeasurableSet {x : (fsTower eta).Carrier | decide (R (limitProfile eta heta x lam) n
    (mapToken (e x (.inl lam.val)) v) (mapToken (e x (.inl lam.val)) w)) = true}
  simp only [decide_eq_true_eq]
  have hiff (x : (fsTower eta).Carrier) :
      R (limitProfile eta heta x lam) n (mapToken (e x (.inl lam.val)) v)
        (mapToken (e x (.inl lam.val)) w) ↔
      ∀ c : Token ℕ, branch eta heta x lam n (mapToken (e x (.inl lam.val)) v)
          (mapToken (e x (.inr (lam,n))) c) =
        branch eta heta x lam n (mapToken (e x (.inl lam.val)) w)
          (mapToken (e x (.inr (lam,n))) c) := by
    rw [R_iff_branch_neighborhood _ genericTable_generic (roleNumber eta heta (.inr (lam,n))) n]
    constructor
    · exact fun h c => h (mapToken (e x (.inr (lam,n))) c)
    · intro h c
      obtain ⟨d,hd⟩ := (tokenEquiv (e x (.inr (lam,n)))).surjective c
      change mapToken (e x (.inr (lam,n))) d = c at hd
      simpa only [branch,hd] using h d
  simp only [hiff,setOf_forall]
  exact MeasurableSet.iInter (fun c => measurableSet_eq_fun
    (measurable_branch_templates eta heta e hP lam n v c)
    (measurable_branch_templates eta heta e hP lam n w c))

theorem measurable_diagram_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hO : ∀ r i j, Measurable (fun x => ordinaryMatrix eta heta x r
      (e x (rowSort eta r) i) (e x (colSort eta r) j)))
    (hP : ∀ lam n i j, Measurable (fun x => limitProfile eta heta x lam n
      (e x (.inl lam.val) i) (e x (.inr (lam,n)) j)))
    (hB : ∀ v : Token ℕ, ∀ n, Measurable (fun x => bottom eta heta x
      (mapToken (e x (zeroSort eta)) v) n))
    (s : Symbol eta) (a : Fin (arity eta s) → Template eta) :
    Measurable (fun x => diagram eta heta (bottom eta heta) x s
      (templateVertexEquiv eta heta x (e x) ∘ a)) := by
  rcases s with s|r|⟨lam,n⟩|⟨lam,n⟩|unit
  · simp only [diagram,Function.comp_apply,sortOf_templateVertexEquiv]
    exact measurable_const
  · change Fin 2 → Template eta at a
    exact measurable_edgeAt_templates eta heta e _ _ (fun x => ordinary eta heta x r)
      (measurable_ordinary_templates eta heta e hO r) (a 0) (a 1)
  · change Fin 2 → Template eta at a
    exact measurable_edgeAt_templates eta heta e _ _ (fun x => branch eta heta x lam n)
      (measurable_branch_templates eta heta e hP lam n) (a 0) (a 1)
  · change Fin 2 → Template eta at a
    exact measurable_edgeAt_templates eta heta e _ _
      (fun x v w => decide (R (limitProfile eta heta x lam) n v w))
      (measurable_R_templates eta heta e hP lam n) (a 0) (a 1)
  · change Fin 2 → Template eta at a
    simp only [diagram,Function.comp_apply,tokenAt_templateVertexEquiv,coordinateAt_templateVertexEquiv]
    cases ht : templateTokenAt eta (zeroSort eta) (a 0) with
    | none => simpa only [Option.map_none,Option.elim_none] using
        (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => false))
    | some v =>
      cases hn : templateCoordinateAt eta (a 1) with
      | none => simpa only [Option.map_some,Option.elim_some,Option.elim_none] using
          (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => false))
      | some n => simpa only [Option.map_some,Option.elim_some] using hB v n

theorem measurable_modelWithTemplateEnumeration
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hO : ∀ r i j, Measurable (fun x => ordinaryMatrix eta heta x r
      (e x (rowSort eta r) i) (e x (colSort eta r) j)))
    (hP : ∀ lam n i j, Measurable (fun x => limitProfile eta heta x lam n
      (e x (.inl lam.val) i) (e x (.inr (lam,n)) j)))
    (hB : ∀ v : Token ℕ, ∀ n, Measurable (fun x => bottom eta heta x
      (mapToken (e x (zeroSort eta)) v) n)) :
    Measurable (fun x => modelWithEnumeration eta heta (bottom eta heta) x
      (vertexEnumeration eta heta e x)) := by
  change @Measurable (fsTower eta).Carrier (Coordinate (language eta heta) → Bool)
    (fsTower eta).measurableSpace (borel (Coordinate (language eta heta) → Bool)) _
  rw [← BorelSpace.measurable_eq (α := Coordinate (language eta heta) → Bool)]
  apply measurable_pi_iff.mpr
  intro c
  exact measurable_diagram_templates eta heta e hO hP hB c.1
    (templateEnumeration eta heta ∘ c.2)

end FSCofinality.CosetConstruction.TokenModel
