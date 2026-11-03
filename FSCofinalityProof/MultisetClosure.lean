import FSCofinalityProof.Multiset
import FSCofinalityProof.HierarchySums

noncomputable section
open Set MeasureTheory Ordinal Order

namespace FSCofinality

theorem naturalTagged_reduces_countableSum (E : CodedRelation) :
    (naturalTagged E).Reduces (countableSum (fun _ => E)) := by
  refine ⟨fun x => ⟨x.2,x.1⟩,?_,?_⟩
  · exact measurable_from_prod_countable_left (fun n => measurable_sigma_mk n)
  · rintro ⟨x,n⟩ ⟨y,m⟩
    constructor
    · rintro ⟨hxy,h⟩
      change n = m at h
      subst m
      exact ⟨rfl,hxy⟩
    · rintro ⟨h,hxy⟩
      change n = m at h
      subst m
      exact ⟨hxy,rfl⟩

theorem equivalence_of_reduces {E F : CodedRelation} (hEF : E.Reduces F)
    (hF : Equivalence F.rel) : Equivalence E.rel := by
  obtain ⟨f,hf,hred⟩ := hEF
  exact ⟨fun x => (hred x x).mpr (hF.refl _),
    fun h => (hred _ _).mpr (hF.symm ((hred _ _).mp h)),
    fun h k => (hred _ _).mpr (hF.trans ((hred _ _).mp h) ((hred _ _).mp k))⟩

theorem measurable_graph_of_reduces {E F : CodedRelation} (hEF : E.Reduces F)
    (hF : @MeasurableSet (F.Carrier × F.Carrier)
      (F.measurableSpace.prod F.measurableSpace) {p | F.rel p.1 p.2}) :
    @MeasurableSet (E.Carrier × E.Carrier)
      (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2} := by
  obtain ⟨f,hf,hred⟩ := hEF
  have hm : Measurable (fun p : E.Carrier × E.Carrier => (f p.1,f p.2)) :=
    (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)
  have hpre := hF.preimage hm
  convert hpre using 1
  ext p
  exact hred p.1 p.2

/-- Cofinality is preserved by the multiplicity-sensitive countable jump.
Borelness and equivalence of the input follow from its reduction to a tower stage. -/
theorem multisetJump_reduces_fsTower (E : CodedRelation) (b : Ordinal.{0})
    (hb : b < Ordinal.omega 1) (hE : E.Reduces (fsTower b)) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ (multisetJump E).Reduces (fsTower a) := by
  obtain ⟨a,ha,hsum⟩ := countableSum_reduces_fsTower (fun _ => E) (fun _ => b)
    (fun _ => hb) (fun _ => hE)
  have htag := (naturalTagged_reduces_countableSum E).trans hsum
  have hmult := multisetJump_reduces_setJump_naturalTagged E
    (equivalence_of_reduces hE (regular_fsTower b).equivalence)
    (measurable_graph_of_reduces hE (regular_fsTower b).measurable_graph)
  refine ⟨a+1,?_,?_⟩
  · simpa only [succ_eq_add_one] using (Cardinal.isSuccLimit_omega 1).succ_lt ha
  · rw [fsTower_add_one]
    exact hmult.trans (reduces_setJump_map htag)

end FSCofinality
