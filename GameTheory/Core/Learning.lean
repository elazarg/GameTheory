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

/-- An `ε`-coarse correlated equilibrium is the canonical coarse correlated
equilibrium predicate for expected utility relaxed by `ε`. -/
def IsεCoarseCorrelatedEq (G : UtilityGame.{uι, us, uo} ι) (ε : ℝ)
    (statusQuo : FinDist (Profile G.form.sig)) : Prop :=
  IsCoarseCorrelatedEq G.form (euPreferenceWithin ε G.utility) statusQuo

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

/-- The learning-facing external-regret characterization of the canonical
approximate coarse-correlated-equilibrium predicate. -/
theorem isεCoarseCorrelatedEq_iff_externalRegret_le
    (G : UtilityGame.{uι, us, uo} ι) {ε : ℝ}
    {statusQuo : FinDist (Profile G.form.sig)} :
    G.IsεCoarseCorrelatedEq ε statusQuo ↔
      ∀ who replacement, G.externalRegret statusQuo who replacement ≤ ε := by
  rw [UtilityGame.IsεCoarseCorrelatedEq, isCoarseCorrelatedEq_iff]
  constructor
  · intro h who replacement
    have hpref := h who replacement
    rw [euPreferenceWithin_apply] at hpref
    unfold externalRegret
    linarith
  · intro h who replacement
    rw [euPreferenceWithin_apply]
    have hregret := h who replacement
    unfold externalRegret at hregret
    linarith

/-- Exact CCE is the zero-tolerance case of the regret formulation. -/
theorem isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero
    (G : UtilityGame.{uι, us, uo} ι)
    {statusQuo : FinDist (Profile G.form.sig)} :
    IsCoarseCorrelatedEq G.form G.preference statusQuo ↔
      G.IsεCoarseCorrelatedEq 0 statusQuo := by
  rw [isCoarseCorrelatedEq_iff, UtilityGame.IsεCoarseCorrelatedEq,
    isCoarseCorrelatedEq_iff]
  constructor
  · intro h who replacement
    have hpref := h who replacement
    rw [UtilityGame.preference, euPreference_apply] at hpref
    rw [euPreferenceWithin_apply]
    linarith
  · intro h who replacement
    rw [UtilityGame.preference, euPreference_apply]
    have hpref := h who replacement
    rw [euPreferenceWithin_apply] at hpref
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
  rw [G.isεCoarseCorrelatedEq_iff_externalRegret_le]
  intro who replacement
  rw [externalRegret_timeAverage]
  have hT : (0 : ℝ) < T := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  exact (div_le_div_iff_of_pos_right hT).2 (hregret who replacement)

/-! ## Independent self-play

The learning reduction above accepts an arbitrary finite law over pure
profiles.  Independent self-play is the special case in which each round is a
product of players' mixed actions.  This section keeps that bridge at the
same finite-support layer: it neither installs an algorithm nor assumes that
the strategy carriers themselves are finite.

The multiplicative-weights recurrence from the pinned library deliberately
does not live here.  Its quantitative regret theorem belongs to the
game-independent online-learning layer; see the D-LEARN self-play coverage
record for the bounded follow-up experiment.
-/

variable [Fintype ι]

private theorem finDist_map_const {α β : Type*} (μ : FinDist α) (b : β) :
    μ.map (fun _ => b) = FinDist.pure b := by
  apply FinDist.ext
  ext a
  simp [FinDist.toPMF_map]

/-- The external regret of an independent profile law is exactly the gain from
replacing that player's mixed action by a point mass in the mixed extension. -/
theorem externalRegret_pi (G : UtilityGame.{uι, us, uo} ι)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (replacement : G.form.sig.Strategy who) :
    G.externalRegret (FinDist.pi mixedProfile) who replacement =
      expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update mixedProfile who (FinDist.pure replacement))) -
        expectedUtility G.utility who (G.form.mixed.play mixedProfile) := by
  have hpi := GameForm.pi_map_recommendation G.form.sig mixedProfile who
    (fun _ => replacement)
  rw [finDist_map_const] at hpi
  unfold externalRegret
  rw [GameForm.outcomeLaw, GameForm.mixed_play, GameForm.mixed_play, ← hpi, FinDist.bind_map]

/-- A pure-action payoff in independent play, normalized to the unit interval
using a player-specific payoff band.  This is the input interface a future
finite online-learning algorithm consumes. -/
def normGain (G : UtilityGame.{uι, us, uo} ι) (lo : ι → ℝ) (width : ℝ)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) : ℝ :=
  (expectedUtility G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (FinDist.pure action))) - lo who) / width

/-- Mixing a player's pure-action values against their own mixed action gives
their status-quo utility. -/
theorem expect_expectedUtility_update (G : UtilityGame.{uι, us, uo} ι)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) :
    (mixedProfile who).expect (fun action =>
      expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (FinDist.pure action)))) =
      expectedUtility G.utility who (G.form.mixed.play mixedProfile) := by
  conv_rhs => rw [show mixedProfile =
      Profile.update mixedProfile who (mixedProfile who) from
        (Profile.update_eq_self mixedProfile who).symm]
  rw [GameForm.mixed_play_update, expectedUtility_bind]

/-- Normalized pure-action gains lie in `[0, 1]` whenever every outcome
utility lies in the advertised player-specific band. -/
theorem normGain_mem_Icc (G : UtilityGame.{uι, us, uo} ι)
    {lo : ι → ℝ} {width : ℝ} (hwidth : 0 < width)
    (hband : ∀ who outcome, G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) :
    G.normGain lo width mixedProfile who action ∈ Set.Icc (0 : ℝ) 1 := by
  have hlower : lo who ≤ expectedUtility G.utility who
      (G.form.mixed.play (Profile.update mixedProfile who (FinDist.pure action))) := by
    rw [expectedUtility]
    have h := FinDist.expect_mono (μ :=
      G.form.mixed.play (Profile.update mixedProfile who (FinDist.pure action)))
      (u := fun _ => lo who) (v := fun outcome => G.utility outcome who)
      (fun outcome _ => (hband who outcome).1)
    simpa using h
  have hupper : expectedUtility G.utility who
      (G.form.mixed.play (Profile.update mixedProfile who (FinDist.pure action))) ≤
        lo who + width := by
    rw [expectedUtility]
    have h := FinDist.expect_mono (μ :=
      G.form.mixed.play (Profile.update mixedProfile who (FinDist.pure action)))
      (u := fun outcome => G.utility outcome who) (v := fun _ => lo who + width)
      (fun outcome _ => (hband who outcome).2)
    simpa using h
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · rw [normGain]
    exact div_nonneg (sub_nonneg.mpr hlower) hwidth.le
  · rw [normGain, div_le_one hwidth]
    linarith

/-- The expected normalized gain is the normalized status-quo utility. -/
theorem expect_normGain (G : UtilityGame.{uι, us, uo} ι)
    (lo : ι → ℝ) (width : ℝ) (mixedProfile : Profile G.form.sig.mixed) (who : ι) :
    (mixedProfile who).expect (G.normGain lo width mixedProfile who) =
      (expectedUtility G.utility who (G.form.mixed.play mixedProfile) - lo who) / width := by
  rw [show G.normGain lo width mixedProfile who = fun action =>
      (1 / width) *
        (expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update mixedProfile who (FinDist.pure action))) - lo who) by
      funext action
      rw [normGain]
      ring,
    FinDist.expect_smul]
  have hsub :
      (mixedProfile who).expect (fun action =>
        expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update mixedProfile who (FinDist.pure action))) - lo who) =
        expectedUtility G.utility who (G.form.mixed.play mixedProfile) - lo who := by
    calc
      (mixedProfile who).expect (fun action =>
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who (FinDist.pure action))) - lo who) =
          (mixedProfile who).expect (fun action =>
            expectedUtility G.utility who
              (G.form.mixed.play
                (Profile.update mixedProfile who (FinDist.pure action))) + (-1) * lo who) := by
            congr 1
            funext action
            ring
      _ = (mixedProfile who).expect (fun action =>
            expectedUtility G.utility who
              (G.form.mixed.play
                (Profile.update mixedProfile who (FinDist.pure action)))) +
          (-1) * (mixedProfile who).expect (fun _ => lo who) := by
            rw [FinDist.expect_add, FinDist.expect_smul]
      _ = expectedUtility G.utility who (G.form.mixed.play mixedProfile) - lo who := by
            rw [G.expect_expectedUtility_update, FinDist.expect_const]
            ring
  rw [hsub]
  ring

/-- Scaling normalized gains back by the width recovers a pure-deviation gain. -/
theorem expectedUtility_deviation_eq_width_mul_normGain
    (G : UtilityGame.{uι, us, uo} ι) {lo : ι → ℝ} {width : ℝ}
    (hwidth : 0 < width) (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) :
    expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (FinDist.pure action))) -
      expectedUtility G.utility who (G.form.mixed.play mixedProfile) =
      width * (G.normGain lo width mixedProfile who action -
        (mixedProfile who).expect (G.normGain lo width mixedProfile who)) := by
  rw [G.expect_normGain]
  simp only [normGain]
  have hne : width ≠ 0 := hwidth.ne'
  field_simp
  ring

/-- **Independent no-regret self-play yields an approximate CCE.** A bound on
every pure deviation's cumulative mixed-extension gain is transferred through
the finite product law at every round. -/
theorem selfPlay_timeAverage_isεCoarseCorrelatedEq
    (G : UtilityGame.{uι, us, uo} ι) {T : ℕ} [NeZero T]
    (mixedProfile : Fin T → Profile G.form.sig.mixed) {bound : ℝ}
    (hregret : ∀ who action,
      (∑ round : Fin T, (expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update (mixedProfile round) who (FinDist.pure action))) -
        expectedUtility G.utility who (G.form.mixed.play (mixedProfile round)))) ≤ bound) :
    G.IsεCoarseCorrelatedEq (bound / T)
      (G.timeAverage fun round => FinDist.pi (mixedProfile round)) := by
  apply G.timeAverage_isεCoarseCorrelatedEq_of_regret_le
  intro who action
  rw [show (∑ round : Fin T, G.externalRegret
      (FinDist.pi (mixedProfile round)) who action) =
      ∑ round : Fin T, (expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update (mixedProfile round) who (FinDist.pure action))) -
        expectedUtility G.utility who (G.form.mixed.play (mixedProfile round))) by
      apply Finset.sum_congr rfl
      intro round _
      exact G.externalRegret_pi (mixedProfile round) who action]
  exact hregret who action

end UtilityGame

end GameTheory
