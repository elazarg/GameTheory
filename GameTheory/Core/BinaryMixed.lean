/-
# Binary mixed games

The reusable two-by-two calculation behind Matching Pennies. The form may be
stochastic and the action carriers may have descriptive names; an equivalence
with `Bool` supplies only the two labels needed by the theorem.
-/

import GameTheory.Core.Mixed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

namespace GameForm

/-- A two-player form has the Matching Pennies payoff pattern when each action
carrier has two labels and the players receive opposite, nonzero rewards for
matching versus mismatching labels. -/
structure MatchingPenniesLike (F : GameForm (Fin 2))
    (utility : F.sig.Outcome → Fin 2 → ℝ) where
  /-- The two action labels for each player. -/
  action : ∀ i, Bool ≃ F.sig.Strategy i
  /-- The positive magnitude of the payoff. -/
  scale : ℝ
  scale_pos : 0 < scale
  /-- Every actual pure action profile has defined utility for both players. -/
  integrable : GameForm.HasIntegrableUtility F utility
  payoff_zero : ∀ bits : Fin 2 → Bool,
    expectedUtility utility 0
        (F.play (fun i => action i (bits i)))
        (integrable 0 (fun i => action i (bits i))) =
      if bits 0 = bits 1 then scale else -scale
  payoff_one : ∀ bits : Fin 2 → Bool,
    expectedUtility utility 1
        (F.play (fun i => action i (bits i)))
        (integrable 1 (fun i => action i (bits i))) =
      -(if bits 0 = bits 1 then scale else -scale)

namespace MatchingPenniesLike

variable {F : GameForm (Fin 2)} {utility : F.sig.Outcome → Fin 2 → ℝ}
  (h : F.MatchingPenniesLike utility)

/-- Decode Boolean labels into a pure profile. -/
def profile (bits : Fin 2 → Bool) : Profile F.sig :=
  fun i => h.action i (bits i)

/-- Encode a pure profile by its Boolean labels. -/
def encodeProfile (pureProfile : Profile F.sig) : Fin 2 → Bool :=
  fun i => (h.action i).symm (pureProfile i)

theorem expectedUtility_profile_zero (bits : Fin 2 → Bool) :
    expectedUtility utility 0 (F.play (h.profile bits))
      (h.integrable 0 (h.profile bits)) =
      if bits 0 = bits 1 then h.scale else -h.scale := by
  unfold profile
  exact h.payoff_zero bits

theorem expectedUtility_profile_one (bits : Fin 2 → Bool) :
    expectedUtility utility 1 (F.play (h.profile bits))
      (h.integrable 1 (h.profile bits)) =
      -(if bits 0 = bits 1 then h.scale else -h.scale) := by
  unfold profile
  exact h.payoff_one bits

@[simp]
theorem profile_encodeProfile (pureProfile : Profile F.sig) :
    h.profile (h.encodeProfile pureProfile) = pureProfile := by
  funext i
  simp [profile, encodeProfile]

@[simp]
theorem encodeProfile_profile (bits : Fin 2 → Bool) :
    h.encodeProfile (h.profile bits) = bits := by
  funext i
  simp [profile, encodeProfile]

/-- Mixed-play utility is integrable because each binary action carrier is finite. -/
theorem mixedUtilityIntegrable (h : F.MatchingPenniesLike utility)
    (mixedProfile : Profile F.sig.mixed)
    (who : Fin 2) : UtilityIntegrable utility who (F.mixed.play mixedProfile) := by
  have hfinite : ∀ i, Finite (F.sig.Strategy i) := fun i =>
    Finite.of_equiv Bool (h.action i)
  have hmix : GameForm.HasIntegrableUtility F.mixed utility :=
    @GameForm.HasIntegrableUtility.mixed_of_finite (Fin 2) inferInstance
      F utility h.integrable hfinite
  exact hmix who mixedProfile

/-- The canonical fair mixed profile supplied by the two Boolean labels. -/
def fairProfile : Profile F.sig.mixed :=
  fun i => mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (h.action i true)) (PMF.pure (h.action i false))

@[simp]
theorem fairProfile_prob_action (who : Fin 2) (bit : Bool) :
    ((h.fairProfile who) (h.action who bit)).toReal = (1 / 2 : ℝ) := by
  have hne : h.action who true ≠ h.action who false := fun heq =>
    Bool.noConfusion ((h.action who).injective heq)
  cases bit
  · simp [fairProfile, mix_apply, PMF.pure_apply, Ne.symm hne]
    norm_num
  · simp [fairProfile, mix_apply, PMF.pure_apply, hne]

/-- Probability assigned to the action labeled `true`. -/
def probTrue (mixedProfile : Profile F.sig.mixed) (who : Fin 2) : ℝ :=
  ((mixedProfile who) (h.action who true)).toReal

@[simp]
theorem probTrue_fairProfile (who : Fin 2) :
    h.probTrue h.fairProfile who = (1 / 2 : ℝ) := by
  simpa only [probTrue] using h.fairProfile_prob_action who true

theorem probTrue_nonneg (mixedProfile : Profile F.sig.mixed) (who : Fin 2) :
    0 ≤ h.probTrue mixedProfile who :=
  ENNReal.toReal_nonneg

theorem probTrue_le_one (mixedProfile : Profile F.sig.mixed) (who : Fin 2) :
    h.probTrue mixedProfile who ≤ 1 :=
  ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)

@[simp]
theorem probTrue_update_pure_true (mixedProfile : Profile F.sig.mixed)
    (who : Fin 2) :
    h.probTrue
        (Profile.update mixedProfile who (PMF.pure (h.action who true))) who = 1 := by
  classical
  simp [probTrue]

@[simp]
theorem probTrue_update_pure_false (mixedProfile : Profile F.sig.mixed)
    (who : Fin 2) :
    h.probTrue
        (Profile.update mixedProfile who (PMF.pure (h.action who false))) who = 0 := by
  simp [probTrue, Profile.update_same, PMF.pure_apply,
    (h.action who).injective.eq_iff]

@[simp]
theorem probTrue_update_of_ne (mixedProfile : Profile F.sig.mixed)
    {who other : Fin 2} (replacement : PMF (F.sig.Strategy who))
    (hne : other ≠ who) :
    h.probTrue (Profile.update mixedProfile who replacement) other =
      h.probTrue mixedProfile other := by
  simp [probTrue, hne]

private theorem probTrue_update_zero_one (mixedProfile : Profile F.sig.mixed)
    (replacement : PMF (F.sig.Strategy 0)) :
    h.probTrue (Profile.update mixedProfile 0 replacement) 1 =
      h.probTrue mixedProfile 1 :=
  h.probTrue_update_of_ne mixedProfile replacement (by decide)

private theorem probTrue_update_one_zero (mixedProfile : Profile F.sig.mixed)
    (replacement : PMF (F.sig.Strategy 1)) :
    h.probTrue (Profile.update mixedProfile 1 replacement) 0 =
      h.probTrue mixedProfile 0 :=
  h.probTrue_update_of_ne mixedProfile replacement (by decide)

private def bitsTT : Fin 2 → Bool := ![true, true]
private def bitsTF : Fin 2 → Bool := ![true, false]
private def bitsFT : Fin 2 → Bool := ![false, true]
private def bitsFF : Fin 2 → Bool := ![false, false]

private theorem boolProfiles :
    (Finset.univ : Finset (Fin 2 → Bool)) =
      {bitsTT, bitsTF, bitsFT, bitsFF} := by
  decide

private theorem prob_encoded (mixedProfile : Profile F.sig.mixed)
    (who : Fin 2) (bit : Bool) :
    (((mixedProfile who).map (h.action who).symm) bit).toReal =
      ((mixedProfile who) (h.action who bit)).toReal := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_single (h.action who bit)]
  · simp
  · intro a ha
    have hne : bit ≠ (h.action who).symm a := by
      intro heq
      apply ha
      calc
        a = h.action who ((h.action who).symm a) := by simp
        _ = h.action who bit := congrArg (h.action who) heq.symm
    simp [hne]

private theorem probFalse (mixedProfile : Profile F.sig.mixed) (who : Fin 2) :
    ((mixedProfile who) (h.action who false)).toReal =
      1 - h.probTrue mixedProfile who := by
  have htotal :
      ((((mixedProfile who).map (h.action who).symm) false).toReal +
        (((mixedProfile who).map (h.action who).symm) true).toReal) = 1 := by
    have hsum := ENNReal.tsum_toReal_eq
      (fun bit : Bool => PMF.apply_ne_top ((mixedProfile who).map (h.action who).symm) bit)
    rw [PMF.tsum_coe] at hsum
    simpa [tsum_fintype, Fintype.sum_bool, add_comm] using hsum.symm
  rw [h.prob_encoded, h.prob_encoded] at htotal
  unfold probTrue
  linarith

private theorem mixedExpectedUtility_eq_sum
    (mixedProfile : Profile F.sig.mixed) (who : Fin 2) :
    expectedUtility utility who (F.mixed.play mixedProfile)
        (mixedUtilityIntegrable h mixedProfile who) =
      ∑ bits : Fin 2 → Bool,
        (∏ i, ((mixedProfile i) (h.action i (bits i))).toReal) *
          expectedUtility utility who (F.play (h.profile bits))
            (h.integrable who (h.profile bits)) := by
  let encoded : Fin 2 → PMF Bool :=
    fun i => (mixedProfile i).map (h.action i).symm
  let μ := independentProduct mixedProfile
  let ν := independentProduct encoded
  let value : (Fin 2 → Bool) → ℝ := fun bits =>
    expectedUtility utility who (F.play (h.profile bits))
      (h.integrable who (h.profile bits))
  have hmap : μ.map h.encodeProfile = ν := by
    show (independentProduct mixedProfile).map
      (fun pureProfile i => (h.action i).symm (pureProfile i)) = _
    simpa [ν, encoded] using
      independentProduct_map mixedProfile (fun i => (h.action i).symm)
  have hcond : ∀ pureProfile, UtilityIntegrable utility who (F.play pureProfile) :=
    fun pureProfile => h.integrable who pureProfile
  have houter : PayoffIntegrable μ (fun pureProfile =>
      expectedUtility utility who (F.play pureProfile) (hcond pureProfile)) := by
    simpa only [expectedUtility, UtilityIntegrable] using
      payoffIntegrable_bind_conditionalExpectation μ F.play
        (fun outcome => utility outcome who)
        (mixedUtilityIntegrable h mixedProfile who) hcond
  have hvalue : ∀ pureProfile,
      expectedUtility utility who (F.play pureProfile) (hcond pureProfile) =
        value (h.encodeProfile pureProfile) := by
    intro pureProfile
    simp [value, h.profile_encodeProfile]
  have hpull : PayoffIntegrable μ (value ∘ h.encodeProfile) :=
    payoffIntegrable_congr_on_support
      (fun profile _ => hvalue profile) houter
  have hmapped : PayoffIntegrable (μ.map h.encodeProfile) value :=
    (payoffIntegrable_map_iff h.encodeProfile μ value).2 hpull
  have hmass (bits : Fin 2 → Bool) :
      (ν bits).toReal = ∏ i, ((mixedProfile i) (h.action i (bits i))).toReal := by
    rw [independentProduct_apply, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact prob_encoded h mixedProfile i (bits i)
  calc
    expectedUtility utility who (F.mixed.play mixedProfile)
        (mixedUtilityIntegrable h mixedProfile who) =
        expect μ (fun pureProfile =>
          expectedUtility utility who (F.play pureProfile) (hcond pureProfile)) houter := by
      exact expectedUtility_bind utility who μ F.play
        (mixedUtilityIntegrable h mixedProfile who) hcond
    _ = expect (μ.map h.encodeProfile) value hmapped := by
      calc
        _ = expect μ (value ∘ h.encodeProfile) hpull :=
          expect_congr_on_support (fun profile _ => hvalue profile) houter hpull
        _ = expect (μ.map h.encodeProfile) value hmapped :=
          (expect_map h.encodeProfile μ value hpull hmapped).symm
    _ = expect ν value (payoffIntegrable_congr_law hmap hmapped) :=
      expect_congr_law hmap value hmapped
        (payoffIntegrable_congr_law hmap hmapped)
    _ = ∑ bits : Fin 2 → Bool,
          (∏ i, ((mixedProfile i) (h.action i (bits i))).toReal) * value bits := by
      rw [expect_eq_sum]
      apply Finset.sum_congr rfl
      intro bits _
      rw [hmass]

/-- Expected utility of player zero as a polynomial in the two `true`
probabilities. -/
theorem mixedExpectedUtility_zero (mixedProfile : Profile F.sig.mixed) :
    expectedUtility utility 0 (F.mixed.play mixedProfile)
        (mixedUtilityIntegrable h mixedProfile 0) =
      h.scale * ((2 * h.probTrue mixedProfile 0 - 1) *
        (2 * h.probTrue mixedProfile 1 - 1)) := by
  rw [h.mixedExpectedUtility_eq_sum, boolProfiles,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Fin.prod_univ_two]
  rw [h.expectedUtility_profile_zero, h.expectedUtility_profile_zero,
    h.expectedUtility_profile_zero, h.expectedUtility_profile_zero]
  simp only [bitsTT, bitsTF, bitsFT, bitsFF, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [h.probFalse mixedProfile 0, h.probFalse mixedProfile 1]
  simp only [probTrue, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true]
  ring

/-- Expected utility of player one is the negative of player zero's
Matching Pennies polynomial. -/
theorem mixedExpectedUtility_one (mixedProfile : Profile F.sig.mixed) :
    expectedUtility utility 1 (F.mixed.play mixedProfile)
        (mixedUtilityIntegrable h mixedProfile 1) =
      -h.scale * ((2 * h.probTrue mixedProfile 0 - 1) *
        (2 * h.probTrue mixedProfile 1 - 1)) := by
  rw [h.mixedExpectedUtility_eq_sum, boolProfiles,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Fin.prod_univ_two]
  rw [h.expectedUtility_profile_one, h.expectedUtility_profile_one,
    h.expectedUtility_profile_one, h.expectedUtility_profile_one]
  simp only [bitsTT, bitsTF, bitsFT, bitsFF, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [h.probFalse mixedProfile 0, h.probFalse mixedProfile 1]
  simp only [probTrue, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true]
  ring

/-- **Exact mixed Nash characterization for Matching-Pennies-like games.**
Nash equilibrium holds exactly when each player assigns probability one half
to the action labeled `true`. -/
theorem isNash_iff_half (mixedProfile : Profile F.sig.mixed) :
    IsNash F.mixed (euPreference utility) mixedProfile ↔
      h.probTrue mixedProfile 0 = (1 / 2 : ℝ) ∧
        h.probTrue mixedProfile 1 = (1 / 2 : ℝ) := by
  have hdev : ∀ who (replacement : PMF (F.sig.Strategy who)),
      UtilityIntegrable utility who
        (F.mixed.play (Profile.update mixedProfile who replacement)) := by
    intro who replacement
    exact mixedUtilityIntegrable h (Profile.update mixedProfile who replacement) who
  have hnash_iff := isNash_mixed_iff (F := F) (utility := utility)
    mixedProfile hdev
  constructor
  · intro hnash
    rw [hnash_iff] at hnash
    have hbase0 := mixedUtilityIntegrable h mixedProfile 0
    have hbase1 := mixedUtilityIntegrable h mixedProfile 1
    have hdev0t := mixedUtilityIntegrable h
      (Profile.update mixedProfile 0 (PMF.pure (h.action 0 true))) 0
    have hdev0f := mixedUtilityIntegrable h
      (Profile.update mixedProfile 0 (PMF.pure (h.action 0 false))) 0
    have hdev1t := mixedUtilityIntegrable h
      (Profile.update mixedProfile 1 (PMF.pure (h.action 1 true))) 1
    have hdev1f := mixedUtilityIntegrable h
      (Profile.update mixedProfile 1 (PMF.pure (h.action 1 false))) 1
    have h0t := (euPreference_iff utility 0 (F.mixed.play mixedProfile)
      (F.mixed.play (Profile.update mixedProfile 0
        (PMF.pure (h.action 0 true)))) hbase0 hdev0t).1
      (hnash 0 (h.action 0 true))
    have h0f := (euPreference_iff utility 0 (F.mixed.play mixedProfile)
      (F.mixed.play (Profile.update mixedProfile 0
        (PMF.pure (h.action 0 false)))) hbase0 hdev0f).1
      (hnash 0 (h.action 0 false))
    have h1t := (euPreference_iff utility 1 (F.mixed.play mixedProfile)
      (F.mixed.play (Profile.update mixedProfile 1
        (PMF.pure (h.action 1 true)))) hbase1 hdev1t).1
      (hnash 1 (h.action 1 true))
    have h1f := (euPreference_iff utility 1 (F.mixed.play mixedProfile)
      (F.mixed.play (Profile.update mixedProfile 1
        (PMF.pure (h.action 1 false)))) hbase1 hdev1f).1
      (hnash 1 (h.action 1 false))
    rw [h.mixedExpectedUtility_zero, h.mixedExpectedUtility_zero] at h0t h0f
    rw [h.mixedExpectedUtility_one, h.mixedExpectedUtility_one] at h1t h1f
    simp only [h.probTrue_update_pure_true, h.probTrue_update_pure_false,
      h.probTrue_update_zero_one, h.probTrue_update_one_zero] at h0t h0f h1t h1f
    have hp0 := h.probTrue_nonneg mixedProfile 0
    have hp1 := h.probTrue_le_one mixedProfile 0
    have hq0 := h.probTrue_nonneg mixedProfile 1
    have hq1 := h.probTrue_le_one mixedProfile 1
    constructor <;> nlinarith [h.scale_pos]
  · rintro ⟨hp, hq⟩
    rw [hnash_iff]
    intro who replacement
    obtain ⟨bit, rfl⟩ := (h.action who).surjective replacement
    by_cases hwho : who = 0
    · subst who
      cases bit
      · apply (euPreference_iff utility 0 (F.mixed.play mixedProfile)
          (F.mixed.play (Profile.update mixedProfile 0
            (PMF.pure (h.action 0 false))))
          (mixedUtilityIntegrable h mixedProfile 0)
          (mixedUtilityIntegrable h
            (Profile.update mixedProfile 0
              (PMF.pure (h.action 0 false))) 0)).2
        rw [h.mixedExpectedUtility_zero, h.mixedExpectedUtility_zero]
        simp [hp, hq]
      · apply (euPreference_iff utility 0 (F.mixed.play mixedProfile)
          (F.mixed.play (Profile.update mixedProfile 0
            (PMF.pure (h.action 0 true))))
          (mixedUtilityIntegrable h mixedProfile 0)
          (mixedUtilityIntegrable h
            (Profile.update mixedProfile 0
              (PMF.pure (h.action 0 true))) 0)).2
        rw [h.mixedExpectedUtility_zero, h.mixedExpectedUtility_zero]
        simp [hp, hq]
    · have hwho' : who = 1 := Fin.eq_one_of_ne_zero who hwho
      subst who
      cases bit
      · apply (euPreference_iff utility 1 (F.mixed.play mixedProfile)
          (F.mixed.play (Profile.update mixedProfile 1
            (PMF.pure (h.action 1 false))))
          (mixedUtilityIntegrable h mixedProfile 1)
          (mixedUtilityIntegrable h
            (Profile.update mixedProfile 1
              (PMF.pure (h.action 1 false))) 1)).2
        rw [h.mixedExpectedUtility_one, h.mixedExpectedUtility_one]
        simp [hp, hq]
      · apply (euPreference_iff utility 1 (F.mixed.play mixedProfile)
          (F.mixed.play (Profile.update mixedProfile 1
            (PMF.pure (h.action 1 true))))
          (mixedUtilityIntegrable h mixedProfile 1)
          (mixedUtilityIntegrable h
            (Profile.update mixedProfile 1
              (PMF.pure (h.action 1 true))) 1)).2
        rw [h.mixedExpectedUtility_one, h.mixedExpectedUtility_one]
        simp [hp, hq]

end MatchingPenniesLike
end GameForm
end GameTheory
