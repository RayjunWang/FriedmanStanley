import FSCofinalityProof.CosetConstructionPoolBorelLimit

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- A single code, fixed before the source input is supplied, realizes the
specified partial semantic operation. -/
def CodeRep (a : Ordinal.{0}) (F : (fsTower eta).Carrier → Option (Ambient eta heta)) : Prop :=
  ∃ c : (poolCodes eta heta a).Code, ∀ x, (poolCodes eta heta a).value c x = F x

theorem codeRep_value (a : Ordinal.{0}) (c : (poolCodes eta heta a).Code) :
    CodeRep eta heta a ((poolCodes eta heta a).value c) := ⟨c,fun _ => rfl⟩

theorem codeRep_congr (a : Ordinal.{0})
    {F G : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta a F) (h : ∀ x, F x = G x) : CodeRep eta heta a G := by
  obtain ⟨c,hc⟩ := hF
  exact ⟨c,fun x => (hc x).trans (h x)⟩

theorem codeRep_seed (a : Ordinal.{0}) (s : SeedIndex) :
    CodeRep eta heta a (evalSeed eta heta a s) :=
  ⟨(poolCodes eta heta a).seed s,(poolCodes eta heta a).value_seed s⟩

theorem codeRep_none (a : Ordinal.{0}) :
    CodeRep eta heta a (fun _ => none) := by
  by_cases ha : a = Frame.top eta
  · apply codeRep_congr eta heta a (codeRep_seed eta heta a (some []))
    intro x
    have hne : eta ≠ a := by rw [ha]; exact ne_of_lt (Frame.lt_top eta)
    simp only [evalSeed,sourcePath,if_neg hne]
  · apply codeRep_congr eta heta a (codeRep_seed eta heta a none)
    intro x
    simp only [evalSeed,if_neg ha]

theorem codeRep_extra (n : ℕ) :
    CodeRep eta heta 0 (fun _ => some (extraAtom n)) := by
  unfold CodeRep
  rw [poolCodes_zero]
  exact ⟨.inr n,fun _ => rfl⟩

theorem codeRep_singleton (a : Ordinal.{0})
    (F : (fsTower eta).Carrier → Option (Ambient eta heta)) (hF : CodeRep eta heta a F) :
    CodeRep eta heta (a+1) (fun x => (F x).map (singleton (level eta (a+1)))) := by
  obtain ⟨c,hc⟩ := hF
  unfold CodeRep
  rw [poolCodes_add_one]
  refine ⟨.inr {c},?_⟩
  intro x
  change (liftFinite (extraAtom 0) (fun d => (poolCodes eta heta a).value d x) {c}).map _ = _
  cases h : F x <;> simp [liftFinite,hc x,h,finiteCollection_singleton]

theorem codeRep_doubleton (a : Ordinal.{0})
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (G : (fsTower eta).Carrier → Ambient eta heta)
    (hF : CodeRep eta heta a F) (hG : CodeRep eta heta a (fun x => some (G x))) :
    CodeRep eta heta (a+1) (fun x => (F x).map (fun u => doubleton (level eta (a+1)) u (G x))) := by
  obtain ⟨c,hc⟩ := hF
  obtain ⟨d,hd⟩ := hG
  unfold CodeRep
  rw [poolCodes_add_one]
  refine ⟨.inr {c,d},?_⟩
  intro x
  change (liftFinite (extraAtom 0) (fun e => (poolCodes eta heta a).value e x) {c,d}).map _ = _
  cases h : F x <;> simp [liftFinite,hc x,hd x,h,finiteCollection_doubleton]

theorem codeRep_limit_singleton (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ)
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (hF : CodeRep eta heta (Frame.rho eta lam hlam n) F) :
    CodeRep eta heta lam (fun x => (F x).map (fun u => finiteFiller (level eta lam)
      {(n,singleton (level eta (Frame.delta eta lam hlam n)) u)})) := by
  obtain ⟨c,hc⟩ := hF
  unfold CodeRep
  rw [poolCodes_limit eta heta lam hlam]
  let b : BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) := ⟨n,.inr (.inr c)⟩
  refine ⟨.inr {b},?_⟩
  intro x
  change (liftFinite (0,extraAtom 0) (fun e => evalBirthCode eta heta lam hlam _ e x) {b}).map _ = _
  have hb : evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x =
      (F x).map (fun u => (n,singleton (level eta (Frame.delta eta lam hlam n)) u)) := by
    change ((poolCodes eta heta (Frame.rho eta lam hlam n)).value c x).map _ = _
    rw [hc]
  cases h : F x <;> simp [liftFinite,hb,h]

theorem codeRep_lift (b a : Ordinal.{0}) (hba : b ≤ a) (ha : a ≤ Frame.top eta)
    (F : (fsTower eta).Carrier → Option (Ambient eta heta)) (hF : CodeRep eta heta b F) :
    CodeRep eta heta a (fun x => (F x).map (lift eta heta b a)) := by
  induction a using Ordinal.limitRecOn generalizing b with
  | zero =>
    have hb : b = 0 := le_antisymm hba zero_le
    subst b
    simpa only [lift_self,Option.map_id] using hF
  | add_one a ih =>
    by_cases hb : b = a+1
    · subst b
      simpa only [lift_self,Option.map_id] using hF
    · have hba' : b ≤ a := lt_add_one_iff.mp (lt_of_le_of_ne hba hb)
      have ha' : a ≤ Frame.top eta := (show a ≤ a+1 from le_self_add).trans ha
      have hrec := ih b hba' ha' hF
      have hs := codeRep_singleton eta heta a _ hrec
      simpa only [RawObjects.lift_add_one,if_neg hb,Option.map_map,Function.comp_def] using hs
  | limit lam hlam ih =>
    by_cases hb : b = lam
    · subst b
      simpa only [lift_self,Option.map_id] using hF
    · have hblt : b < lam := lt_of_le_of_ne hba hb
      let n := liftIndex eta heta lam hlam ha b hblt
      have hrec := ih (Frame.rho eta lam hlam n) (Frame.rho_lt eta lam hlam n)
        b (liftIndex_spec eta heta lam hlam ha b hblt)
        ((Frame.rho_lt eta lam hlam n).le.trans ha) hF
      have hs := codeRep_limit_singleton eta heta lam hlam n _ hrec
      simpa only [lift_limit eta heta lam hlam ha b hblt,Option.map_map,Function.comp_def] using hs

theorem codeRep_tag (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) (n : ℕ) :
    CodeRep eta heta a (fun _ => some (tag eta heta a n)) := by
  simpa only [Option.map_some,tag] using
    codeRep_lift eta heta 0 a zero_le ha (fun _ => some (extraAtom n)) (codeRep_extra eta heta n)

theorem codeRep_doubleton_left (a : Ordinal.{0})
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (G : (fsTower eta).Carrier → Ambient eta heta)
    (hF : CodeRep eta heta a F) (hG : CodeRep eta heta a (fun x => some (G x))) :
    CodeRep eta heta (a+1) (fun x => (F x).map (fun u => doubleton (level eta (a+1)) (G x) u)) := by
  apply codeRep_congr eta heta (a+1) (codeRep_doubleton eta heta a F G hF hG)
  intro x
  exact congrArg (fun f => (F x).map f) (funext (fun u => doubleton_comm _ u (G x)))

theorem codeRep_enc (a : Ordinal.{0})
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (T B : (fsTower eta).Carrier → Ambient eta heta)
    (hF : CodeRep eta heta a F)
    (hT : CodeRep eta heta a (fun x => some (T x)))
    (hB : CodeRep eta heta a (fun x => some (B x))) :
    CodeRep eta heta (a+2) (fun x => (F x).map
      (Enc (level eta (a+1)) (level eta (a+2)) (T x) (B x))) := by
  have hpair := codeRep_doubleton_left eta heta a F B hF hB
  have htag : CodeRep eta heta (a+1) (fun x => some (singleton (level eta (a+1)) (T x))) := by
    simpa only [Option.map_some] using codeRep_singleton eta heta a (fun x => some (T x)) hT
  have hout := codeRep_doubleton_left eta heta (a+1) _ _ hpair htag
  have hstage : a+1+1 = a+2 := by rw [add_assoc,one_add_one_eq_two]
  simpa only [hstage,Option.map_map,Function.comp_def,Enc] using hout

theorem codeRep_dataColumn (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (n : ℕ)
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (hF : CodeRep eta heta (Frame.q eta lam hlam n) F) :
    CodeRep eta heta (Frame.delta eta lam hlam n)
      (fun x => (F x).map (dataColumn eta heta lam hlam n)) := by
  have hs : Frame.sigma eta lam hlam n ≤ Frame.top eta := (Frame.sigma_lt eta lam hlam n).le.trans htop
  have hlift := codeRep_lift eta heta _ _ (Frame.q_le_sigma eta lam hlam n) hs F hF
  have henc := codeRep_enc eta heta (Frame.sigma eta lam hlam n) _
    (fun _ => tag eta heta (Frame.sigma eta lam hlam n) 1)
    (fun _ => tag eta heta (Frame.sigma eta lam hlam n) 3) hlift
    (codeRep_tag eta heta _ hs 1) (codeRep_tag eta heta _ hs 3)
  simpa only [Frame.delta,Frame.rho,Option.map_map,Function.comp_def,dataColumn] using henc

theorem codeRep_markerColumn (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (n : ℕ) :
    CodeRep eta heta (Frame.delta eta lam hlam n)
      (fun _ => some (markerColumn eta heta lam hlam n)) := by
  have hs : Frame.sigma eta lam hlam n ≤ Frame.top eta := (Frame.sigma_lt eta lam hlam n).le.trans htop
  simpa only [Frame.delta,Frame.rho,Option.map_some,markerColumn] using
    codeRep_enc eta heta (Frame.sigma eta lam hlam n) (fun _ => some (tag eta heta _ 3))
      (fun _ => tag eta heta _ 2) (fun _ => tag eta heta _ 3)
      (codeRep_tag eta heta _ hs 3) (codeRep_tag eta heta _ hs 2) (codeRep_tag eta heta _ hs 3)

theorem codeRep_oldColumn (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (n : ℕ)
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (hF : CodeRep eta heta (Frame.delta eta lam hlam n) F) :
    CodeRep eta heta (Frame.delta eta lam hlam (n+1))
      (fun x => (F x).map (oldColumn eta heta lam hlam n)) := by
  have hs : Frame.sigma eta lam hlam (n+1) ≤ Frame.top eta :=
    (Frame.sigma_lt eta lam hlam (n+1)).le.trans htop
  have hlift := codeRep_lift eta heta _ _ (Frame.delta_le_sigma_next eta lam hlam n) hs F hF
  have henc := codeRep_enc eta heta (Frame.sigma eta lam hlam (n+1)) _
    (fun _ => tag eta heta (Frame.sigma eta lam hlam (n+1)) 0)
    (fun _ => tag eta heta (Frame.sigma eta lam hlam (n+1)) 3) hlift
    (codeRep_tag eta heta _ hs 0) (codeRep_tag eta heta _ hs 3)
  simpa only [Frame.delta,Frame.rho,Option.map_map,Function.comp_def,oldColumn] using henc

theorem codeRep_birthColumn (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta)
    (c : BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a)) :
    CodeRep eta heta (Frame.delta eta lam hlam c.1) (fun x =>
      (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c x).map Prod.snd) := by
  rcases c with ⟨n,c⟩
  rcases c with c|⟨⟨⟩⟩|c
  · simpa only [evalBirthCode,Option.map_map,Function.comp_def] using
      codeRep_dataColumn eta heta lam hlam htop n _ (codeRep_value eta heta _ c)
  · simpa only [evalBirthCode,Option.map_some] using
      codeRep_markerColumn eta heta lam hlam htop n
  · have hstage : Frame.rho eta lam hlam n + 1 = Frame.delta eta lam hlam n := by
      simp only [Frame.rho,Frame.delta,add_assoc,one_add_one_eq_two]
    simpa only [evalBirthCode,Option.map_map,Function.comp_def,hstage] using
      codeRep_singleton eta heta (Frame.rho eta lam hlam n) _ (codeRep_value eta heta _ c)

end FSCofinality.CosetConstruction
