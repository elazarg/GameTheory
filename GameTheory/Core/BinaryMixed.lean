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
  payoff_zero : ∀ bits : Fin 2 → Bool,
    expectedUtility utility 0
        (F.play (fun i => action i (bits i))) =
      if bits 0 = bits 1 then scale else -scale
  payoff_one : ∀ bits : Fin 2 → Bool,
    expectedUtility utility 1
        (F.play (fun i => action i (bits i))) =
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
    expectedUtility utility 0 (F.play (h.profile bits)) =
      if bits 0 = bits 1 then h.scale else -h.scale := by
  unfold profile
  exact h.payoff_zero bits

theorem expectedUtility_profile_one (bits : Fin 2 → Bool) :
    expectedUtility utility 1 (F.play (h.profile bits)) =
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

/-- The canonical fair mixed profile supplied by the two Boolean labels. -/
def fairProfile : Profile F.sig.mixed :=
  fun i => FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (h.action i true)) (FinDist.pure (h.action i false))

@[simp]
theorem fairProfile_prob_action (who : Fin 2) (bit : Bool) :
    (h.fairProfile who).prob (h.action who bit) = (1 / 2 : ℝ) := by
  classical
  cases bit
  · simp [fairProfile, FinDist.prob_pure_of_ne]
    norm_num
  · simp [fairProfile, FinDist.prob_pure_of_ne]

/-- Probability assigned to the action labeled `true`. -/
def probTrue (mixedProfile : Profile F.sig.mixed) (who : Fin 2) : ℝ :=
  (mixedProfile who).prob (h.action who true)

@[simp]
theorem probTrue_fairProfile (who : Fin 2) :
    h.probTrue h.fairProfile who = (1 / 2 : ℝ) := by
  simp [probTrue]

theorem probTrue_nonneg (mixedProfile : Profile F.sig.mixed) (who : Fin 2) :
    0 ≤ h.probTrue mixedProfile who :=
  FinDist.prob_nonneg _ _

theorem probTrue_le_one (mixedProfile : Profile F.sig.mixed) (who : Fin 2) :
    h.probTrue mixedProfile who ≤ 1 :=
  FinDist.prob_le_one _ _

@[simp]
theorem probTrue_update_pure_true (mixedProfile : Profile F.sig.mixed)
    (who : Fin 2) :
    h.probTrue
        (Profile.update mixedProfile who (FinDist.pure (h.action who true))) who = 1 := by
  classical
  simp [probTrue]

@[simp]
theorem probTrue_update_pure_false (mixedProfile : Profile F.sig.mixed)
    (who : Fin 2) :
    h.probTrue
        (Profile.update mixedProfile who (FinDist.pure (h.action who false))) who = 0 := by
  rw [probTrue, Profile.update_same, FinDist.prob_pure_of_ne]
  exact fun heq => Bool.noConfusion ((h.action who).injective heq)

@[simp]
theorem probTrue_update_of_ne (mixedProfile : Profile F.sig.mixed)
    {who other : Fin 2} (replacement : FinDist (F.sig.Strategy who))
    (hne : other ≠ who) :
    h.probTrue (Profile.update mixedProfile who replacement) other =
      h.probTrue mixedProfile other := by
  simp [probTrue, hne]

@[simp]
private theorem probTrue_update_zero_one (mixedProfile : Profile F.sig.mixed)
    (replacement : FinDist (F.sig.Strategy 0)) :
    h.probTrue (Profile.update mixedProfile 0 replacement) 1 =
      h.probTrue mixedProfile 1 :=
  h.probTrue_update_of_ne mixedProfile replacement (by decide)

@[simp]
private theorem probTrue_update_one_zero (mixedProfile : Profile F.sig.mixed)
    (replacement : FinDist (F.sig.Strategy 1)) :
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
    ((mixedProfile who).map (h.action who).symm).prob bit =
      (mixedProfile who).prob (h.action who bit) := by
  classical
  simpa using FinDist.prob_map_of_injective
    (h.action who).symm (h.action who).symm.injective
    (mixedProfile who) (h.action who bit)

private theorem probFalse (mixedProfile : Profile F.sig.mixed) (who : Fin 2) :
    (mixedProfile who).prob (h.action who false) =
      1 - h.probTrue mixedProfile who := by
  have htotal := FinDist.sum_prob ((mixedProfile who).map (h.action who).symm)
  rw [Fintype.sum_bool, h.prob_encoded, h.prob_encoded] at htotal
  unfold probTrue
  linarith

private theorem mixedExpectedUtility_eq_sum
    (mixedProfile : Profile F.sig.mixed) (who : Fin 2) :
    expectedUtility utility who (F.mixed.play mixedProfile) =
      ∑ bits : Fin 2 → Bool,
        (∏ i, (mixedProfile i).prob (h.action i (bits i))) *
          expectedUtility utility who (F.play (h.profile bits)) := by
  let encoded : Fin 2 → FinDist Bool :=
    fun i => (mixedProfile i).map (h.action i).symm
  have hpi :
      FinDist.pi encoded =
        (FinDist.pi mixedProfile).map h.encodeProfile := by
    exact FinDist.pi_map (fun i => (h.action i).symm) mixedProfile
  calc
    expectedUtility utility who (F.mixed.play mixedProfile) =
        (FinDist.pi mixedProfile).expect fun pureProfile =>
          expectedUtility utility who (F.play pureProfile) := by
      rw [GameForm.mixed_play, expectedUtility_bind]
    _ = ((FinDist.pi mixedProfile).map h.encodeProfile).expect fun bits =>
          expectedUtility utility who (F.play (h.profile bits)) := by
      rw [FinDist.expect_map]
      apply FinDist.expect_congr
      intro pureProfile _
      rw [h.profile_encodeProfile]
    _ = (FinDist.pi encoded).expect fun bits =>
          expectedUtility utility who (F.play (h.profile bits)) := by
      rw [hpi]
    _ = ∑ bits : Fin 2 → Bool,
          (∏ i, (mixedProfile i).prob (h.action i (bits i))) *
            expectedUtility utility who (F.play (h.profile bits)) := by
      rw [FinDist.expect_eq_sum]
      apply Finset.sum_congr rfl
      intro bits _
      rw [FinDist.prob_pi]
      congr 2
      funext i
      exact h.prob_encoded mixedProfile i (bits i)

/-- Expected utility of player zero as a polynomial in the two `true`
probabilities. -/
theorem mixedExpectedUtility_zero (mixedProfile : Profile F.sig.mixed) :
    expectedUtility utility 0 (F.mixed.play mixedProfile) =
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
  simp only [probTrue, Bool.true_eq_false, Bool.false_eq_true, if_false, if_true]
  ring

/-- Expected utility of player one is the negative of player zero's
Matching Pennies polynomial. -/
theorem mixedExpectedUtility_one (mixedProfile : Profile F.sig.mixed) :
    expectedUtility utility 1 (F.mixed.play mixedProfile) =
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
  simp only [probTrue, Bool.true_eq_false, Bool.false_eq_true, if_false, if_true]
  ring

/-- **Exact mixed Nash characterization for Matching-Pennies-like games.**
Nash equilibrium holds exactly when each player assigns probability one half
to the action labeled `true`. -/
theorem isNash_iff_half (mixedProfile : Profile F.sig.mixed) :
    IsNash F.mixed (euPreference utility) mixedProfile ↔
      h.probTrue mixedProfile 0 = (1 / 2 : ℝ) ∧
        h.probTrue mixedProfile 1 = (1 / 2 : ℝ) := by
  constructor
  · intro hnash
    rw [isNash_mixed_iff] at hnash
    have h0t := hnash 0 (h.action 0 true)
    have h0f := hnash 0 (h.action 0 false)
    have h1t := hnash 1 (h.action 1 true)
    have h1f := hnash 1 (h.action 1 false)
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
    rw [isNash_mixed_iff]
    intro who replacement
    obtain ⟨bit, rfl⟩ := (h.action who).surjective replacement
    by_cases hwho : who = 0
    · subst who
      cases bit <;>
        rw [h.mixedExpectedUtility_zero, h.mixedExpectedUtility_zero] <;>
        simp [hp, hq]
    · have hwho' : who = 1 := Fin.eq_one_of_ne_zero who hwho
      subst who
      cases bit <;>
        rw [h.mixedExpectedUtility_one, h.mixedExpectedUtility_one] <;>
        simp [hp, hq]

end MatchingPenniesLike
end GameForm
end GameTheory
