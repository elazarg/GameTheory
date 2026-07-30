/-
# Finite no-regret learning

External regret is defined from the canonical unilateral profile update and the
accepted `GameForm` play law. Approximate coarse correlated equilibrium is the
same utility comparison with an additive tolerance; it is not a second
deviation or correlation model.

The finite-horizon theorem is pure averaging. No strategy carrier, outcome
carrier, or player type needs to be finite because every law has finite support;
only the time index `Fin T` is enumerated.
-/

import GameTheory.Core.Utility

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

variable {ι : Type uι}

namespace UtilityGame

variable [DecidableEq ι]

/-- Expected gain from replacing one player's recommendation by a fixed
strategy. Positive values mean that the constant deviation is profitable. -/
def externalRegret (G : UtilityGame.{uι, us, uo} ι)
    (statusQuo : FinDist (Profile G.form.sig)) (who : ι)
    (replacement : G.form.sig.Strategy who) : ℝ :=
  expectedUtility G.utility who
      (statusQuo.bind fun profile =>
        G.form.play (Profile.update profile who replacement)) -
    expectedUtility G.utility who (G.form.outcomeLaw statusQuo)

/-- External regret is the status-quo expectation of pointwise deviation
gain. This is the affine form used by finite time averaging. -/
theorem externalRegret_eq_expect_gain (G : UtilityGame.{uι, us, uo} ι)
    (statusQuo : FinDist (Profile G.form.sig)) (who : ι)
    (replacement : G.form.sig.Strategy who) :
    G.externalRegret statusQuo who replacement =
      statusQuo.expect fun profile =>
        expectedUtility G.utility who
            (G.form.play (Profile.update profile who replacement)) -
          expectedUtility G.utility who (G.form.play profile) := by
  unfold externalRegret GameForm.outcomeLaw
  rw [expectedUtility_bind, expectedUtility_bind]
  calc
    statusQuo.expect
          (fun profile =>
            expectedUtility G.utility who
              (G.form.play (Profile.update profile who replacement))) -
        statusQuo.expect
          (fun profile => expectedUtility G.utility who (G.form.play profile)) =
        statusQuo.expect
            (fun profile =>
              expectedUtility G.utility who
                  (G.form.play (Profile.update profile who replacement))) +
          (-1) *
            statusQuo.expect
              (fun profile => expectedUtility G.utility who (G.form.play profile)) := by
                ring
    _ = statusQuo.expect
          (fun profile =>
            expectedUtility G.utility who
                (G.form.play (Profile.update profile who replacement)) +
              (-1) *
                expectedUtility G.utility who (G.form.play profile)) := by
              rw [← FinDist.expect_smul, ← FinDist.expect_add]
    _ = statusQuo.expect
          (fun profile =>
            expectedUtility G.utility who
                (G.form.play (Profile.update profile who replacement)) -
              expectedUtility G.utility who (G.form.play profile)) := by
              congr 1
              funext profile
              ring

/-- An `ε`-coarse correlated equilibrium: every constant unilateral
deviation has external regret at most `ε`. -/
def IsεCoarseCorrelatedEq (G : UtilityGame.{uι, us, uo} ι) (ε : ℝ)
    (statusQuo : FinDist (Profile G.form.sig)) : Prop :=
  ∀ who replacement, G.externalRegret statusQuo who replacement ≤ ε

theorem isεCoarseCorrelatedEq_iff_externalRegret_le
    (G : UtilityGame.{uι, us, uo} ι) {ε : ℝ}
    {statusQuo : FinDist (Profile G.form.sig)} :
    G.IsεCoarseCorrelatedEq ε statusQuo ↔
      ∀ who replacement, G.externalRegret statusQuo who replacement ≤ ε :=
  Iff.rfl

/-- Exact CCE is the zero-tolerance case of the regret formulation. -/
theorem isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero
    (G : UtilityGame.{uι, us, uo} ι)
    {statusQuo : FinDist (Profile G.form.sig)} :
    IsCoarseCorrelatedEq G.form G.preference statusQuo ↔
      G.IsεCoarseCorrelatedEq 0 statusQuo := by
  rw [isCoarseCorrelatedEq_iff]
  constructor
  · intro h who replacement
    have hpref := h who replacement
    rw [UtilityGame.preference, euPreference_apply] at hpref
    unfold externalRegret
    linarith
  · intro h who replacement
    rw [UtilityGame.preference, euPreference_apply]
    have hregret := h who replacement
    unfold externalRegret at hregret
    linarith

/-- The uniform time average of finitely many laws over pure profiles. -/
def timeAverage (G : UtilityGame.{uι, us, uo} ι) {T : ℕ} [NeZero T]
    (roundLaw : Fin T → FinDist (Profile G.form.sig)) :
    FinDist (Profile G.form.sig) :=
  (FinDist.uniformFin T).bind roundLaw

/-- External regret of a finite time average is average external regret. -/
theorem externalRegret_timeAverage (G : UtilityGame.{uι, us, uo} ι)
    {T : ℕ} [NeZero T]
    (roundLaw : Fin T → FinDist (Profile G.form.sig)) (who : ι)
    (replacement : G.form.sig.Strategy who) :
    G.externalRegret (G.timeAverage roundLaw) who replacement =
      (∑ t, G.externalRegret (roundLaw t) who replacement) / T := by
  rw [externalRegret_eq_expect_gain]
  unfold timeAverage
  rw [FinDist.expect_bind, FinDist.expect_uniformFin]
  congr 1
  exact Finset.sum_congr rfl fun t _ =>
    (G.externalRegret_eq_expect_gain (roundLaw t) who replacement).symm

/-- **Finite no-regret implies approximate coarse correlated equilibrium.**
If every player's cumulative external regret against every fixed strategy is
at most `R`, the time average is an `(R / T)`-CCE. -/
theorem timeAverage_isεCoarseCorrelatedEq_of_regret_le
    (G : UtilityGame.{uι, us, uo} ι) {T : ℕ} [NeZero T]
    {roundLaw : Fin T → FinDist (Profile G.form.sig)} {R : ℝ}
    (hregret :
      ∀ who replacement,
        (∑ t, G.externalRegret (roundLaw t) who replacement) ≤ R) :
    G.IsεCoarseCorrelatedEq (R / T) (G.timeAverage roundLaw) := by
  intro who replacement
  rw [externalRegret_timeAverage]
  have hT : (0 : ℝ) < T := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  exact (div_le_div_iff_of_pos_right hT).2 (hregret who replacement)

end UtilityGame

end GameTheory
