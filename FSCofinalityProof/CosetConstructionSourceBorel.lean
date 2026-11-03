import FSCofinalityProof.CosetConstructionSourcePaths

noncomputable section
open Set MeasureTheory

namespace FSCofinality.CosetConstruction

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- Equality of the represented optional semantic values is Borel on each
fixed source code level, although the raw semantic universe has no Borel
structure installed on it. -/
theorem measurableSet_optionalTranslate_eq (a : Ordinal.{0}) :
    MeasurableSet {p : (Unit ⊕ (fsTower a).Carrier) × (Unit ⊕ (fsTower a).Carrier) |
      optionalTranslate eta heta a p.1 = optionalTranslate eta heta a p.2} := by
  let E := fsTower a
  have hE := regular_fsTower a
  letI : StandardBorelSpace E.Carrier := hE.standardBorel
  letI : StandardBorelSpace (Unit ⊕ E.Carrier) := standardBorel_sum
  let base : E.Carrier := Classical.choice hE.nonempty
  let get : Unit ⊕ E.Carrier → E.Carrier := Sum.elim (fun _ => base) id
  have hg : Measurable get := measurable_const.sumElim measurable_id
  have hn : MeasurableSet {x : Unit ⊕ E.Carrier | x = .inl ()} :=
    measurableSet_singleton _
  have heq := hE.measurable_graph.preimage
    ((hg.comp measurable_fst).prodMk (hg.comp measurable_snd))
  have hboth := (hn.preimage measurable_fst).inter (hn.preimage measurable_snd)
  have hsome := (hn.preimage measurable_fst).compl.inter (hn.preimage measurable_snd).compl
  convert hboth.union (hsome.inter heq) using 1
  ext p
  rcases p with ⟨x,y⟩
  rcases x with ⟨⟨⟩⟩ | x <;> rcases y with ⟨⟨⟩⟩ | y
  all_goals simp [optionalTranslate,get,translate_eq_iff]
  all_goals rfl

theorem optionalTranslate_cast {a b : Ordinal.{0}} (h : a = b)
    (z : Unit ⊕ (fsTower a).Carrier) :
    optionalTranslate eta heta b (Sum.map id (codeCast (congrArg fsTower h)) z) =
      optionalTranslate eta heta a z := by
  cases h
  cases z <;> rfl

/-- The semantic equality tests needed to remove repetitions from the
countable source-path enumeration are actual Borel predicates. -/
theorem measurableSet_sourcePathValue_eq (p q : List ℕ)
    (hrank : (sourcePath eta p).rank = (sourcePath eta q).rank) :
    MeasurableSet {xy : (fsTower eta).Carrier × (fsTower eta).Carrier |
      sourcePathValue eta heta p xy.1 = sourcePathValue eta heta q xy.2} := by
  let f := (sourcePath eta p).get
  let g := Sum.map id (codeCast (congrArg fsTower hrank.symm)) ∘ (sourcePath eta q).get
  have hf : Measurable f := (sourcePath eta p).measurable_get
  have hg : Measurable g := (measurable_id.sumMap (codeCast _).measurable).comp
    (sourcePath eta q).measurable_get
  have h := (measurableSet_optionalTranslate_eq eta heta (sourcePath eta p).rank).preimage
    ((hf.comp measurable_fst).prodMk (hg.comp measurable_snd))
  convert h using 1
  ext xy
  simp only [mem_setOf_eq,mem_preimage,sourcePathValue,f,g,Function.comp_apply]
  rw [optionalTranslate_cast eta heta hrank.symm]

end FSCofinality.CosetConstruction
