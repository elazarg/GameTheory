/-
# Fictitious-play trajectories

Fictitious play repeatedly chooses a pure best response to the independent
empirical marginals of past play.  This file owns the topology-free state and
recurrence.  Claims about limits of these beliefs live in the analytic
consumer; the core interface itself is just finite-support probability and the
canonical best-response predicate.
-/

import GameTheory.Core.MixedImprovement
import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

namespace UtilityGame

variable {ι : Type uι}
variable (G : UtilityGame.{uι, us, uo} ι)

/-- The empirical law of one player's actions during the first `T` rounds. -/
def empiricalMarginal (history : ℕ → Profile G.form.sig) (who : ι)
    (T : ℕ) [NeZero T] : FinDist (G.form.sig.Strategy who) :=
  (FinDist.uniformFin T).map fun round : Fin T => history round.val who

/-- An empirical marginal is the uniform finite average of the matching past
actions. -/
theorem empiricalMarginal_prob (history : ℕ → Profile G.form.sig) (who : ι)
    (T : ℕ) [NeZero T] [DecidableEq (G.form.sig.Strategy who)]
    (action : G.form.sig.Strategy who) :
    (G.empiricalMarginal history who T).prob action =
      ((Finset.univ.filter fun round : Fin T => history round who = action).card : ℝ) / T := by
  rw [empiricalMarginal, FinDist.prob_map, FinDist.expect_uniformFin]
  simp [div_eq_mul_inv, mul_comm, eq_comm]

/-- Expectation under an empirical marginal is the ordinary finite average. -/
theorem empiricalMarginal_expect (history : ℕ → Profile G.form.sig) (who : ι)
    (T : ℕ) [NeZero T] (observable : G.form.sig.Strategy who → ℝ) :
    (G.empiricalMarginal history who T).expect observable =
      (∑ round : Fin T, observable (history round who)) / T := by
  rw [empiricalMarginal, FinDist.expect_map, FinDist.expect_uniformFin]

/-- Adding one observation updates every empirical expectation by the usual
running-average recurrence. -/
theorem empiricalMarginal_succ_expect (history : ℕ → Profile G.form.sig)
    (who : ι) (t : ℕ) (observable : G.form.sig.Strategy who → ℝ) :
    (G.empiricalMarginal history who (t + 2)).expect observable =
      ((t + 1 : ℝ) / (t + 2 : ℝ)) *
          (G.empiricalMarginal history who (t + 1)).expect observable +
        (1 / (t + 2 : ℝ)) * observable (history (t + 1) who) := by
  rw [G.empiricalMarginal_expect, G.empiricalMarginal_expect]
  have hsum :
      (∑ round : Fin (t + 2), observable (history round who)) =
        (∑ round : Fin (t + 1), observable (history round who)) +
          observable (history (t + 1) who) := by
    rw [show t + 2 = (t + 1) + 1 by omega, Fin.sum_univ_castSucc]
    rfl
  rw [hsum]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp

/-- The independent empirical belief profile available after `T` rounds. -/
def empiricalBelief (history : ℕ → Profile G.form.sig) (T : ℕ) [NeZero T] :
    Profile G.form.sig.mixed :=
  fun who => G.empiricalMarginal history who T

variable [Fintype ι] [DecidableEq ι]

/-- A history is fictitious play when every action after the initial round is
a pure best response to the empirical belief formed from all earlier rounds.
The predicate reuses the canonical mixed extension and `IsBestResponse`; it is
not a parallel equilibrium or payoff semantics. -/
def IsFictitiousPlay (history : ℕ → Profile G.form.sig) : Prop :=
  ∀ (t : ℕ) (who : ι),
    IsBestResponse G.form.mixed (euPreference G.utility) who
      (G.empiricalBelief history (t + 1))
      (FinDist.pure (history (t + 1) who))

/-- The defining best-response obligation of fictitious play. -/
theorem IsFictitiousPlay.isBestResponse {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) (who : ι) :
    IsBestResponse G.form.mixed (euPreference G.utility) who
      (G.empiricalBelief history (t + 1))
      (FinDist.pure (history (t + 1) who)) :=
  hplay t who

/-- The gain of the pure action actually played at the next round, measured
against the empirical belief entering that round. -/
def playedGain (history : ℕ → Profile G.form.sig) (t : ℕ) (who : ι) : ℝ :=
  G.mixedGain (G.empiricalBelief history (t + 1)) who
    (history (t + 1) who)

/-- Advancing one coordinate to its next empirical marginal is affine at the
expected-utility level. -/
theorem expectedUtility_update_empiricalMarginal_succ
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ) :
    expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2)))) =
      ((t + 1 : ℝ) / (t + 2 : ℝ)) *
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who
                (G.empiricalMarginal history who (t + 1)))) +
        (1 / (t + 2 : ℝ)) *
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who
                (FinDist.pure (history (t + 1) who)))) := by
  rw [GameForm.mixed_play_update, expectedUtility_bind,
    G.empiricalMarginal_succ_expect history who t
      (fun action => expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (FinDist.pure action))))]
  rw [← expectedUtility_bind, ← GameForm.mixed_play_update]

/-- Difference form of the one-coordinate empirical expected-utility
recurrence. -/
theorem expectedUtility_update_empiricalMarginal_succ_sub
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ) :
    expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2)))) -
      expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 1)))) =
      (1 / (t + 2 : ℝ)) *
        (expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who
                (FinDist.pure (history (t + 1) who)))) -
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who
                (G.empiricalMarginal history who (t + 1))))) := by
  rw [G.expectedUtility_update_empiricalMarginal_succ history mixedProfile who t]
  have hnonzero : (t + 2 : ℝ) ≠ 0 := by positivity
  field_simp [hnonzero]
  ring

/-- Against the current empirical belief, advancing one coordinate changes
that player's expected utility by the step size times its played gain. -/
theorem expectedUtility_belief_update_empiricalMarginal_succ_sub
    (history : ℕ → Profile G.form.sig) (who : ι) (t : ℕ) :
    expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update (G.empiricalBelief history (t + 1)) who
            (G.empiricalMarginal history who (t + 2)))) -
      expectedUtility G.utility who
        (G.form.mixed.play (G.empiricalBelief history (t + 1))) =
      (1 / (t + 2 : ℝ)) * G.playedGain history t who := by
  have hsame :
      Profile.update (G.empiricalBelief history (t + 1)) who
          (G.empiricalMarginal history who (t + 1)) =
        G.empiricalBelief history (t + 1) :=
    Profile.update_eq_self _ _
  have hrecurrence := G.expectedUtility_update_empiricalMarginal_succ_sub
    history (G.empiricalBelief history (t + 1)) who t
  rw [hsame] at hrecurrence
  exact hrecurrence

/-- In a team game, the same empirical coordinate increment holds for every
observer's common payoff. -/
theorem IsTeamGame.expectedUtility_belief_update_empiricalMarginal_succ_sub
    (hteam : IsTeamGame G.utility)
    (history : ℕ → Profile G.form.sig) (observer who : ι) (t : ℕ) :
    expectedUtility G.utility observer
        (G.form.mixed.play
          (Profile.update (G.empiricalBelief history (t + 1)) who
            (G.empiricalMarginal history who (t + 2)))) -
      expectedUtility G.utility observer
        (G.form.mixed.play (G.empiricalBelief history (t + 1))) =
      (1 / (t + 2 : ℝ)) * G.playedGain history t who := by
  rw [hteam.expectedUtility_eq _ observer who,
    hteam.expectedUtility_eq _ observer who]
  exact G.expectedUtility_belief_update_empiricalMarginal_succ_sub history who t

/-- The aggregate gain of the actions played at one fictitious-play round. -/
def aggregatePlayedGain (history : ℕ → Profile G.form.sig) (t : ℕ) : ℝ :=
  ∑ who, G.playedGain history t who

/-- Played gain weighted by each player's number of pure actions. -/
def weightedPlayedGain [∀ who, Fintype (G.form.sig.Strategy who)]
    (history : ℕ → Profile G.form.sig) (t : ℕ) : ℝ :=
  ∑ who, (Fintype.card (G.form.sig.Strategy who) : ℝ) *
    G.playedGain history t who

/-- A best-response action has nonnegative gain because the current mixed
coordinate averages all pure-deviation gains to zero. -/
theorem IsFictitiousPlay.playedGain_nonneg
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) (who : ι) :
    0 ≤ G.playedGain history t who := by
  let belief := G.empiricalBelief history (t + 1)
  let played := history (t + 1) who
  have hpoint :
      ∀ action ∈ (belief who).support,
        G.mixedGain belief who action ≤ G.mixedGain belief who played := by
    intro action _
    have hbest :=
      UtilityGame.IsFictitiousPlay.isBestResponse (G := G) hplay t who
        (FinDist.pure action)
    rw [euPreference_apply] at hbest
    unfold mixedGain
    linarith
  have havg := FinDist.expect_mono hpoint
  rw [G.expect_mixedGain_self_zero belief who,
    FinDist.expect_const] at havg
  exact havg

theorem IsFictitiousPlay.aggregatePlayedGain_nonneg
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) :
    0 ≤ G.aggregatePlayedGain history t := by
  rw [aggregatePlayedGain]
  exact Finset.sum_nonneg fun who _ =>
    UtilityGame.IsFictitiousPlay.playedGain_nonneg (G := G) hplay t who

/-- Under fictitious play, the total positive pure-deviation gap is bounded by
the strategy-cardinality-weighted gain of the actions actually played. -/
theorem IsFictitiousPlay.mixedImprovement_le_weightedPlayedGain
    [∀ who, Fintype (G.form.sig.Strategy who)]
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) :
    G.mixedImprovement (G.empiricalBelief history (t + 1)) ≤
      G.weightedPlayedGain history t := by
  rw [mixedImprovement, weightedPlayedGain]
  refine Finset.sum_le_sum fun who _ => ?_
  have hplayed : 0 ≤ G.playedGain history t who :=
    UtilityGame.IsFictitiousPlay.playedGain_nonneg (G := G) hplay t who
  have hpoint :
      ∀ action : G.form.sig.Strategy who,
        max (G.mixedGain (G.empiricalBelief history (t + 1)) who action) 0 ≤
          G.playedGain history t who := by
    intro action
    have hbest :=
      UtilityGame.IsFictitiousPlay.isBestResponse (G := G) hplay t who
        (FinDist.pure action)
    rw [euPreference_apply] at hbest
    apply max_le
    · unfold playedGain mixedGain
      linarith
    · exact hplayed
  calc
    (∑ action : G.form.sig.Strategy who,
        max (G.mixedGain (G.empiricalBelief history (t + 1)) who action) 0) ≤
        ∑ _action : G.form.sig.Strategy who,
          G.playedGain history t who :=
      Finset.sum_le_sum fun action _ => hpoint action
    _ = (Fintype.card (G.form.sig.Strategy who) : ℝ) *
        G.playedGain history t who := by
      simp [Finset.sum_const, nsmul_eq_mul]

end UtilityGame

end GameTheory
