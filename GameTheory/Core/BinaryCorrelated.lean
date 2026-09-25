/-
# Binary correlated games

The correlated-equilibrium calculation for a Matching-Pennies-like form. Four
recommendation-dependent deviations force a cycle of inequalities among the
four pure-profile masses; normalization then makes every mass one quarter.
-/

import GameTheory.Core.BinaryMixed
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

namespace GameForm.MatchingPenniesLike

variable {F : GameForm (Fin 2)} {utility : F.sig.Outcome → Fin 2 → ℝ}
  (h : F.MatchingPenniesLike utility)

theorem encodeProfile_injective : Function.Injective h.encodeProfile := by
  intro first second heq
  rw [← h.profile_encodeProfile first, ← h.profile_encodeProfile second, heq]

/-- Boolean labels give a finite profile carrier. -/
private theorem finiteProfiles (h : F.MatchingPenniesLike utility) :
    Finite (Profile F.sig) :=
  Finite.of_injective h.encodeProfile h.encodeProfile_injective

/-- An injective Boolean encoding preserves the mass of each decoded profile. -/
private theorem map_profile_mass (law : PMF (Profile F.sig))
    (bits : Fin 2 → Bool) :
    (law.map h.encodeProfile) bits = law (h.profile bits) := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_single (h.profile bits)]
  · simp
  · intro profile hne
    have hbits : bits ≠ h.encodeProfile profile := by
      intro heq
      apply hne
      calc
        profile = h.profile (h.encodeProfile profile) :=
          h.profile_encodeProfile profile |>.symm
        _ = h.profile bits := congrArg h.profile heq.symm
    simp [hbits]

/-- Reindex an expectation over pure profiles by the four Boolean labels. -/
theorem expect_eq_sum_profile (law : PMF (Profile F.sig))
    (observable : Profile F.sig → ℝ)
    (hintegrable : PayoffIntegrable law observable) :
    expect law observable hintegrable =
      ∑ bits : Fin 2 → Bool,
        (law (h.profile bits)).toReal * observable (h.profile bits) := by
  classical
  let ν := law.map h.encodeProfile
  let value : (Fin 2 → Bool) → ℝ := fun bits => observable (h.profile bits)
  have hvalue : ∀ profile, observable profile = value (h.encodeProfile profile) := by
    intro profile
    simp [value, h.profile_encodeProfile]
  have hpull : PayoffIntegrable law (value ∘ h.encodeProfile) :=
    payoffIntegrable_congr_on_support (fun profile _ => hvalue profile) hintegrable
  have hν : PayoffIntegrable ν value :=
    (payoffIntegrable_map_iff h.encodeProfile law value).2 hpull
  calc
    expect law observable hintegrable = expect law (value ∘ h.encodeProfile) hpull :=
      expect_congr_on_support (fun profile _ => hvalue profile) hintegrable hpull
    _ = expect ν value hν := (expect_map h.encodeProfile law value hpull hν).symm
    _ = ∑ bits : Fin 2 → Bool,
          (law (h.profile bits)).toReal * observable (h.profile bits) := by
      rw [expect_eq_sum]
      apply Finset.sum_congr rfl
      intro bits _
      rw [map_profile_mass]

private theorem responseLawIntegrable (h : F.MatchingPenniesLike utility)
    (law : PMF (Profile F.sig))
    (who : Fin 2) (q : Profile F.sig → PMF F.sig.Outcome)
    (hcond : ∀ profile, UtilityIntegrable utility who (q profile)) :
    UtilityIntegrable utility who (law.bind q) := by
  exact @payoffIntegrable_bind_of_finite (Profile F.sig) F.sig.Outcome
    (h.finiteProfiles) law q (fun outcome => utility outcome who) hcond

private theorem outcomeLawIntegrable (h : F.MatchingPenniesLike utility)
    (law : PMF (Profile F.sig)) (who : Fin 2) :
    UtilityIntegrable utility who (F.outcomeLaw law) := by
  have hbind := h.responseLawIntegrable law who F.play
    (fun profile => h.integrable who profile)
  simpa only [GameForm.outcomeLaw, UtilityIntegrable] using hbind

@[simp]
theorem update_profile_zero (bits : Fin 2 → Bool) (bit : Bool) :
    Profile.update (h.profile bits) 0 (h.action 0 bit) =
      h.profile ![bit, bits 1] := by
  apply h.encodeProfile_injective
  funext i
  fin_cases i
  · simp [encodeProfile, profile]
  · simp [encodeProfile, profile]

@[simp]
theorem update_profile_one (bits : Fin 2 → Bool) (bit : Bool) :
    Profile.update (h.profile bits) 1 (h.action 1 bit) =
      h.profile ![bits 0, bit] := by
  apply h.encodeProfile_injective
  funext i
  fin_cases i
  · simp [encodeProfile, profile]
  · simp [encodeProfile, profile]

private def bitsTT : Fin 2 → Bool := ![true, true]
private def bitsTF : Fin 2 → Bool := ![true, false]
private def bitsFT : Fin 2 → Bool := ![false, true]
private def bitsFF : Fin 2 → Bool := ![false, false]

private theorem boolProfiles :
    (Finset.univ : Finset (Fin 2 → Bool)) =
      {bitsTT, bitsTF, bitsFT, bitsFF} := by
  decide

private theorem expect_eq_four (law : PMF (Profile F.sig))
    (observable : Profile F.sig → ℝ) (hintegrable : PayoffIntegrable law observable) :
    expect law observable hintegrable =
      (law (h.profile bitsTT)).toReal * observable (h.profile bitsTT) +
      ((law (h.profile bitsTF)).toReal * observable (h.profile bitsTF) +
      ((law (h.profile bitsFT)).toReal * observable (h.profile bitsFT) +
       (law (h.profile bitsFF)).toReal * observable (h.profile bitsFF))) := by
  rw [h.expect_eq_sum_profile law observable hintegrable, boolProfiles,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem expectedUtility_bind_eq_four
    (law : PMF (Profile F.sig)) (who : Fin 2)
    (q : Profile F.sig → PMF F.sig.Outcome)
    (hbind : UtilityIntegrable utility who (law.bind q))
    (hcond : ∀ profile, UtilityIntegrable utility who (q profile)) :
    expectedUtility utility who (law.bind q) hbind =
      (law (h.profile bitsTT)).toReal *
          expectedUtility utility who (q (h.profile bitsTT))
            (hcond (h.profile bitsTT)) +
      ((law (h.profile bitsTF)).toReal *
          expectedUtility utility who (q (h.profile bitsTF))
            (hcond (h.profile bitsTF)) +
      ((law (h.profile bitsFT)).toReal *
          expectedUtility utility who (q (h.profile bitsFT))
            (hcond (h.profile bitsFT)) +
       (law (h.profile bitsFF)).toReal *
          expectedUtility utility who (q (h.profile bitsFF))
            (hcond (h.profile bitsFF)))) := by
  let value := fun profile => expectedUtility utility who (q profile) (hcond profile)
  let houter := payoffIntegrable_bind_conditionalExpectation law q
    (fun outcome => utility outcome who) hbind hcond
  calc
    expectedUtility utility who (law.bind q) hbind =
        expect law value houter := expectedUtility_bind utility who law q hbind hcond
    _ = (law (h.profile bitsTT)).toReal * value (h.profile bitsTT) +
        ((law (h.profile bitsTF)).toReal * value (h.profile bitsTF) +
        ((law (h.profile bitsFT)).toReal * value (h.profile bitsFT) +
         (law (h.profile bitsFF)).toReal * value (h.profile bitsFF))) :=
      expect_eq_four h law value houter

private theorem ce_prob_true_true_ge_true_false
    {law : PMF (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    (law (h.profile bitsTT)).toReal ≥ (law (h.profile bitsTF)).toReal := by
  let dev : F.sig.Strategy 0 → F.sig.Strategy 0 := fun action =>
    if (h.action 0).symm action then h.action 0 false else action
  have hpref := (isCorrelatedEq_iff law).1 hCE 0 dev
  let q : Profile F.sig → PMF F.sig.Outcome := fun profile =>
    F.play (Profile.update profile 0 (dev (profile 0)))
  have hbase := h.outcomeLawIntegrable law 0
  have hdeviation := h.responseLawIntegrable law 0 q
    (fun profile => h.integrable 0 (Profile.update profile 0 (dev (profile 0))))
  have hineq := (euPreference_iff utility 0 (F.outcomeLaw law) (law.bind q)
    hbase hdeviation).1 hpref
  have hbaseValue := h.expectedUtility_bind_eq_four law 0 F.play hbase
    (fun profile => h.integrable 0 profile)
  have hdeviationValue := h.expectedUtility_bind_eq_four law 0 q hdeviation
    (fun profile => h.integrable 0 (Profile.update profile 0 (dev (profile 0))))
  unfold GameForm.outcomeLaw at hineq
  rw [hbaseValue, hdeviationValue] at hineq
  simp only [q, GameTheory.GameForm.MatchingPenniesLike.profile,
    bitsTT, bitsTF, bitsFT, bitsFF,
    Matrix.cons_val_zero, dev, Equiv.symm_apply_apply, ite_true,
    Bool.false_eq_true, ite_false, h.update_profile_zero] at hineq
  simp_rw [h.expectedUtility_profile_zero] at hineq
  norm_num at hineq
  simp only [bitsTT, bitsTF] at ⊢
  nlinarith [h.scale_pos]

private theorem ce_prob_true_false_ge_false_false
    {law : PMF (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    (law (h.profile bitsTF)).toReal ≥ (law (h.profile bitsFF)).toReal := by
  let dev : F.sig.Strategy 1 → F.sig.Strategy 1 := fun action =>
    if (h.action 1).symm action then action else h.action 1 true
  have hpref := (isCorrelatedEq_iff law).1 hCE 1 dev
  let q : Profile F.sig → PMF F.sig.Outcome := fun profile =>
    F.play (Profile.update profile 1 (dev (profile 1)))
  have hbase := h.outcomeLawIntegrable law 1
  have hdeviation := h.responseLawIntegrable law 1 q
    (fun profile => h.integrable 1 (Profile.update profile 1 (dev (profile 1))))
  have hineq := (euPreference_iff utility 1 (F.outcomeLaw law) (law.bind q)
    hbase hdeviation).1 hpref
  have hbaseValue := h.expectedUtility_bind_eq_four law 1 F.play hbase
    (fun profile => h.integrable 1 profile)
  have hdeviationValue := h.expectedUtility_bind_eq_four law 1 q hdeviation
    (fun profile => h.integrable 1 (Profile.update profile 1 (dev (profile 1))))
  unfold GameForm.outcomeLaw at hineq
  rw [hbaseValue, hdeviationValue] at hineq
  simp only [q, GameTheory.GameForm.MatchingPenniesLike.profile,
    bitsTT, bitsTF, bitsFT, bitsFF,
    Matrix.cons_val_zero, Matrix.cons_val_one, dev,
    Equiv.symm_apply_apply, ite_true,
    Bool.false_eq_true, ite_false, h.update_profile_one] at hineq
  simp_rw [h.expectedUtility_profile_one] at hineq
  norm_num at hineq
  simp only [bitsTF, bitsFF] at ⊢
  nlinarith [h.scale_pos]

private theorem ce_prob_false_false_ge_false_true
    {law : PMF (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    (law (h.profile bitsFF)).toReal ≥ (law (h.profile bitsFT)).toReal := by
  let dev : F.sig.Strategy 0 → F.sig.Strategy 0 := fun action =>
    if (h.action 0).symm action then action else h.action 0 true
  have hpref := (isCorrelatedEq_iff law).1 hCE 0 dev
  let q : Profile F.sig → PMF F.sig.Outcome := fun profile =>
    F.play (Profile.update profile 0 (dev (profile 0)))
  have hbase := h.outcomeLawIntegrable law 0
  have hdeviation := h.responseLawIntegrable law 0 q
    (fun profile => h.integrable 0 (Profile.update profile 0 (dev (profile 0))))
  have hineq := (euPreference_iff utility 0 (F.outcomeLaw law) (law.bind q)
    hbase hdeviation).1 hpref
  have hbaseValue := h.expectedUtility_bind_eq_four law 0 F.play hbase
    (fun profile => h.integrable 0 profile)
  have hdeviationValue := h.expectedUtility_bind_eq_four law 0 q hdeviation
    (fun profile => h.integrable 0 (Profile.update profile 0 (dev (profile 0))))
  unfold GameForm.outcomeLaw at hineq
  rw [hbaseValue, hdeviationValue] at hineq
  simp only [q, GameTheory.GameForm.MatchingPenniesLike.profile,
    bitsTT, bitsTF, bitsFT, bitsFF,
    Matrix.cons_val_zero, dev, Equiv.symm_apply_apply, ite_true,
    Bool.false_eq_true, ite_false, h.update_profile_zero] at hineq
  simp_rw [h.expectedUtility_profile_zero] at hineq
  norm_num at hineq
  simp only [bitsFF, bitsFT] at ⊢
  nlinarith [h.scale_pos]

private theorem ce_prob_false_true_ge_true_true
    {law : PMF (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    (law (h.profile bitsFT)).toReal ≥ (law (h.profile bitsTT)).toReal := by
  let dev : F.sig.Strategy 1 → F.sig.Strategy 1 := fun action =>
    if (h.action 1).symm action then h.action 1 false else action
  have hpref := (isCorrelatedEq_iff law).1 hCE 1 dev
  let q : Profile F.sig → PMF F.sig.Outcome := fun profile =>
    F.play (Profile.update profile 1 (dev (profile 1)))
  have hbase := h.outcomeLawIntegrable law 1
  have hdeviation := h.responseLawIntegrable law 1 q
    (fun profile => h.integrable 1 (Profile.update profile 1 (dev (profile 1))))
  have hineq := (euPreference_iff utility 1 (F.outcomeLaw law) (law.bind q)
    hbase hdeviation).1 hpref
  have hbaseValue := h.expectedUtility_bind_eq_four law 1 F.play hbase
    (fun profile => h.integrable 1 profile)
  have hdeviationValue := h.expectedUtility_bind_eq_four law 1 q hdeviation
    (fun profile => h.integrable 1 (Profile.update profile 1 (dev (profile 1))))
  unfold GameForm.outcomeLaw at hineq
  rw [hbaseValue, hdeviationValue] at hineq
  simp only [q, GameTheory.GameForm.MatchingPenniesLike.profile,
    bitsTT, bitsTF, bitsFT, bitsFF,
    Matrix.cons_val_zero, Matrix.cons_val_one, dev,
    Equiv.symm_apply_apply, ite_true,
    Bool.false_eq_true, ite_false, h.update_profile_one] at hineq
  simp_rw [h.expectedUtility_profile_one] at hineq
  norm_num at hineq
  simp only [bitsFT, bitsTT] at ⊢
  nlinarith [h.scale_pos]

/-- Every pure profile receives probability one quarter in a correlated
equilibrium of a Matching-Pennies-like game. -/
theorem correlatedEq_profile_prob_eq_quarter
    {law : PMF (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law)
    (bits : Fin 2 → Bool) :
    (law (h.profile bits)).toReal = (1 / 4 : ℝ) := by
  classical
  have hTT_TF := h.ce_prob_true_true_ge_true_false hCE
  have hTF_FF := h.ce_prob_true_false_ge_false_false hCE
  have hFF_FT := h.ce_prob_false_false_ge_false_true hCE
  have hFT_TT := h.ce_prob_false_true_ge_true_true hCE
  have hall :
      (law (h.profile bitsTT)).toReal = (law (h.profile bitsTF)).toReal ∧
      (law (h.profile bitsTF)).toReal = (law (h.profile bitsFF)).toReal ∧
      (law (h.profile bitsFF)).toReal = (law (h.profile bitsFT)).toReal := by
    constructor
    · linarith
    constructor <;> linarith
  have hsum : ∑ labels : Fin 2 → Bool,
      (law (h.profile labels)).toReal = 1 := by
    have hsum := ENNReal.tsum_toReal_eq
      (fun labels : Fin 2 → Bool =>
        PMF.apply_ne_top (law.map h.encodeProfile) labels)
    rw [PMF.tsum_coe] at hsum
    rw [tsum_fintype] at hsum
    simpa only [h.map_profile_mass, ENNReal.toReal_one] using hsum.symm
  rw [boolProfiles,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  have hquarter : (law (h.profile bitsTT)).toReal = (1 / 4 : ℝ) := by
    linarith
  have hlabels : bits ∈
      ({bitsTT, bitsTF, bitsFT, bitsFF} : Finset (Fin 2 → Bool)) := by
    rw [← boolProfiles]
    exact Finset.mem_univ bits
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlabels
  rcases hlabels with rfl | rfl | rfl | rfl
  · exact hquarter
  · linarith [hall.1]
  · linarith [hall.1, hall.2.1, hall.2.2]
  · linarith [hall.1, hall.2.1]

/-- The independent product of the fair marginals is a mixed Nash profile. -/
theorem fairProfile_isNash :
    IsNash F.mixed (euPreference utility) h.fairProfile :=
  (h.isNash_iff_half h.fairProfile).2
    ⟨h.probTrue_fairProfile 0, h.probTrue_fairProfile 1⟩

/-- The independent product of the fair marginals is a correlated
equilibrium. -/
theorem fairProduct_isCorrelatedEq :
    IsCorrelatedEq F (euPreference utility) (independentProduct h.fairProfile) :=
  h.fairProfile_isNash.isCorrelatedEq_pi

/-- Any correlated equilibrium of a Matching-Pennies-like game equals the
independent product of its fair marginals. -/
theorem correlatedEq_unique
    {law : PMF (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    law = independentProduct h.fairProfile := by
  apply PMF.ext
  intro pureProfile
  have hleft := h.correlatedEq_profile_prob_eq_quarter hCE
    (h.encodeProfile pureProfile)
  have hright :
      ((independentProduct h.fairProfile) (h.profile (h.encodeProfile pureProfile))).toReal =
        (1 / 4 : ℝ) := by
    rw [independentProduct_apply, ENNReal.toReal_prod]
    simp only [profile]
    rw [Fin.prod_univ_two, h.fairProfile_prob_action, h.fairProfile_prob_action]
    norm_num
  have hreal : (law pureProfile).toReal =
      ((independentProduct h.fairProfile) pureProfile).toReal := by
    rw [← h.profile_encodeProfile pureProfile]
    exact hleft.trans hright.symm
  exact (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top law pureProfile)
    (PMF.apply_ne_top (independentProduct h.fairProfile) pureProfile)).1 hreal

/-- A Matching-Pennies-like game has exactly one correlated equilibrium: the
independent product of its fair marginals. -/
theorem existsUnique_correlatedEq (h : F.MatchingPenniesLike utility) :
    ∃! law : PMF (Profile F.sig),
      IsCorrelatedEq F (euPreference utility) law :=
  ⟨independentProduct h.fairProfile, h.fairProduct_isCorrelatedEq,
    fun _ lawIsCE => h.correlatedEq_unique lawIsCE⟩

end GameForm.MatchingPenniesLike

end GameTheory
