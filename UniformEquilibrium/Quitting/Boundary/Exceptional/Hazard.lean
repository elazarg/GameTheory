/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.LiveTail
import UniformEquilibrium.Quitting.Paths.OpponentLiveMass

/-!
# At most one exceptional opponent-survival coordinate

For two distinct players, every absorbing joint action involves an opponent
of at least one of them.  At one stage this bounds the total absorption
hazard by the sum of their two opponent-only hazards.  The corresponding
finite cumulative bound follows by summation.

The stronger multiplicative form says that the product of the two
opponent-only continue masses is at most the total continue mass.  Iterating
it shows that the product of the two opponent-only live masses is at most
the total live mass.  Hence, if total survival tends to zero, opponent-only
survival can fail to tend to zero for at most one player.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Conditional probability of absorption at the current live stage. -/
def quittingAbsorptionHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) : ℝ :=
  1 - quittingJointContinueMass reward profile time

/-- Conditional probability that some opponent of `who` quits at the
current live stage. -/
def quittingOpponentAbsorptionHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) : ℝ :=
  quittingAbsorptionHazard reward
    (quittingOpponentOnlyProfile reward profile who) time

omit [DecidableEq ι] in
/-- The all-continue mass is the product of the players' live-history
continue probabilities. -/
theorem quittingJointContinueMass_eq_product
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingJointContinueMass reward profile time =
      ∏ player,
        ((profile player time (quittingLiveHist reward time)) false).toReal := by
  unfold quittingJointContinueMass StochasticGame.stageActionDist
  rw [pmfPi_apply, ENNReal.toReal_prod]
  rfl

/-- Forcing `who` to continue deletes exactly their factor from the
all-continue product. -/
theorem quittingJointContinueMass_opponentOnly_eq_product
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) :
    quittingJointContinueMass reward
        (quittingOpponentOnlyProfile reward profile who) time =
      ∏ player,
        if player = who then 1 else
          ((profile player time (quittingLiveHist reward time)) false).toReal := by
  rw [quittingJointContinueMass_eq_product]
  apply Finset.prod_congr rfl
  intro player _
  by_cases hp : player = who
  · subst player
    simp [quittingOpponentOnlyProfile, quittingAlwaysContinueStrategy]
  · simp [quittingOpponentOnlyProfile, hp]

/-- For distinct players, the product of their opponent-only continue masses
is bounded by the total all-continue mass. -/
theorem quittingOpponentContinueMass_mul_le_jointContinueMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {first second : ι} (hne : first ≠ second) (time : ℕ) :
    quittingJointContinueMass reward
          (quittingOpponentOnlyProfile reward profile first) time *
        quittingJointContinueMass reward
          (quittingOpponentOnlyProfile reward profile second) time ≤
      quittingJointContinueMass reward profile time := by
  let continueProbability : ι → ℝ := fun player =>
    ((profile player time (quittingLiveHist reward time)) false).toReal
  have hnonneg (player : ι) : 0 ≤ continueProbability player :=
    ENNReal.toReal_nonneg
  have hleOne (player : ι) : continueProbability player ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one
        (profile player time (quittingLiveHist reward time)) false)
  rw [quittingJointContinueMass_opponentOnly_eq_product,
    quittingJointContinueMass_opponentOnly_eq_product,
    quittingJointContinueMass_eq_product]
  change
    (∏ player, if player = first then 1 else continueProbability player) *
        (∏ player, if player = second then 1 else continueProbability player) ≤
      ∏ player, continueProbability player
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro player _
    positivity
  · intro player _
    by_cases hfirst : player = first
    · subst player
      simp [hne]
    · by_cases hsecond : player = second
      · subst player
        simp [hfirst]
      · simp only [if_neg hfirst, if_neg hsecond]
        nlinarith [hnonneg player, hleOne player]

/-- Every absorbing root event is charged to the opponent hazard of at least
one of two distinct players. -/
theorem quittingAbsorptionHazard_le_add_opponentAbsorptionHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {first second : ι} (hne : first ≠ second) (time : ℕ) :
    quittingAbsorptionHazard reward profile time ≤
      quittingOpponentAbsorptionHazard reward profile first time +
        quittingOpponentAbsorptionHazard reward profile second time := by
  have hproduct :=
    quittingOpponentContinueMass_mul_le_jointContinueMass
      reward profile hne time
  have hfirst := quittingJointContinueMass_le_one reward
    (quittingOpponentOnlyProfile reward profile first) time
  have hsecond := quittingJointContinueMass_le_one reward
    (quittingOpponentOnlyProfile reward profile second) time
  have hcomplements :
      0 ≤
        (1 - quittingJointContinueMass reward
          (quittingOpponentOnlyProfile reward profile first) time) *
        (1 - quittingJointContinueMass reward
          (quittingOpponentOnlyProfile reward profile second) time) :=
    mul_nonneg (sub_nonneg.mpr hfirst) (sub_nonneg.mpr hsecond)
  unfold quittingOpponentAbsorptionHazard quittingAbsorptionHazard
  nlinarith

/-- Finite cumulative total hazard is bounded by the sum of any two
distinct players' cumulative opponent hazards. -/
theorem sum_quittingAbsorptionHazard_le_add_opponentAbsorptionHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {first second : ι} (hne : first ≠ second) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
        quittingAbsorptionHazard reward profile time) ≤
      (∑ time ∈ Finset.range horizon,
          quittingOpponentAbsorptionHazard reward profile first time) +
        ∑ time ∈ Finset.range horizon,
          quittingOpponentAbsorptionHazard reward profile second time := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun time _ =>
    quittingAbsorptionHazard_le_add_opponentAbsorptionHazard
      reward profile hne time

/-- At every finite time, the product of two distinct players'
opponent-only live masses is bounded by the total live mass. -/
theorem quittingOpponentLiveMass_mul_le_liveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {first second : ι} (hne : first ≠ second) :
    ∀ time,
      quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile first) time *
          quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile second) time ≤
        quittingLiveMass reward profile time := by
  intro time
  induction time with
  | zero => simp
  | succ time ih =>
      rw [quittingLiveMass_succ, quittingLiveMass_succ,
        quittingLiveMass_succ]
      calc
        (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile first) time *
            quittingJointContinueMass reward
              (quittingOpponentOnlyProfile reward profile first) time) *
            (quittingLiveMass reward
                (quittingOpponentOnlyProfile reward profile second) time *
              quittingJointContinueMass reward
                (quittingOpponentOnlyProfile reward profile second) time) =
          (quittingLiveMass reward
                (quittingOpponentOnlyProfile reward profile first) time *
              quittingLiveMass reward
                (quittingOpponentOnlyProfile reward profile second) time) *
            (quittingJointContinueMass reward
                (quittingOpponentOnlyProfile reward profile first) time *
              quittingJointContinueMass reward
                (quittingOpponentOnlyProfile reward profile second) time) := by
                  ring
        _ ≤ quittingLiveMass reward profile time *
            (quittingJointContinueMass reward
                (quittingOpponentOnlyProfile reward profile first) time *
              quittingJointContinueMass reward
                (quittingOpponentOnlyProfile reward profile second) time) := by
              exact mul_le_mul_of_nonneg_right ih
                (mul_nonneg
                  (quittingJointContinueMass_nonneg reward
                    (quittingOpponentOnlyProfile reward profile first) time)
                  (quittingJointContinueMass_nonneg reward
                    (quittingOpponentOnlyProfile reward profile second) time))
        _ ≤ quittingLiveMass reward profile time *
            quittingJointContinueMass reward profile time := by
              exact mul_le_mul_of_nonneg_left
                (quittingOpponentContinueMass_mul_le_jointContinueMass
                  reward profile hne time)
                (quittingLiveMass_nonneg reward profile time)

/-- The product of two distinct opponent-only survival limits is bounded by
the total survival limit. -/
theorem quittingOpponentLiveMassLimit_mul_le_liveMassLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {first second : ι} (hne : first ≠ second) :
    quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile first) *
        quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile second) ≤
      quittingLiveMassLimit reward profile := by
  apply le_of_tendsto_of_tendsto
    ((tendsto_quittingLiveMass reward
      (quittingOpponentOnlyProfile reward profile first)).mul
      (tendsto_quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile second)))
    (tendsto_quittingLiveMass reward profile)
  exact Filter.Eventually.of_forall
    (quittingOpponentLiveMass_mul_le_liveMass reward profile hne)

/-- If total survival dies, then for every two distinct players at least one
of their opponent-only survival probabilities also dies. -/
theorem quittingOpponentLiveMassLimit_eq_zero_or_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (htotal : quittingLiveMassLimit reward profile = 0)
    {first second : ι} (hne : first ≠ second) :
    quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile first) = 0 ∨
      quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile second) = 0 := by
  have hle := quittingOpponentLiveMassLimit_mul_le_liveMassLimit
    reward profile hne
  have hnonneg := mul_nonneg
    (quittingLiveMassLimit_nonneg reward
      (quittingOpponentOnlyProfile reward profile first))
    (quittingLiveMassLimit_nonneg reward
      (quittingOpponentOnlyProfile reward profile second))
  have hproduct :
      quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile first) *
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile second) = 0 := by
    rw [htotal] at hle
    exact le_antisymm hle hnonneg
  exact mul_eq_zero.mp hproduct

/-- Tendsto form: if total survival tends to zero, opponent-only survival
can fail to tend to zero for at most one player. -/
theorem tendsto_zero_quittingOpponentLiveMass_or
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (htotal : Tendsto (quittingLiveMass reward profile) atTop (nhds 0))
    {first second : ι} (hne : first ≠ second) :
    Tendsto (quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile first)) atTop (nhds 0) ∨
      Tendsto (quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile second)) atTop (nhds 0) := by
  have htotalLimit : quittingLiveMassLimit reward profile = 0 :=
    tendsto_nhds_unique (tendsto_quittingLiveMass reward profile) htotal
  rcases quittingOpponentLiveMassLimit_eq_zero_or_eq_zero
      reward profile htotalLimit hne with hfirst | hsecond
  · left
    simpa [hfirst] using tendsto_quittingLiveMass reward
      (quittingOpponentOnlyProfile reward profile first)
  · right
    simpa [hsecond] using tendsto_quittingLiveMass reward
      (quittingOpponentOnlyProfile reward profile second)

/-- Equivalent uniqueness formulation of the exceptional-player conclusion. -/
theorem eq_of_opponentLiveMass_not_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (htotal : Tendsto (quittingLiveMass reward profile) atTop (nhds 0))
    {first second : ι}
    (hfirst : ¬Tendsto (quittingLiveMass reward
      (quittingOpponentOnlyProfile reward profile first)) atTop (nhds 0))
    (hsecond : ¬Tendsto (quittingLiveMass reward
      (quittingOpponentOnlyProfile reward profile second)) atTop (nhds 0)) :
    first = second := by
  by_contra hne
  exact (tendsto_zero_quittingOpponentLiveMass_or
    reward profile htotal hne).elim hfirst hsecond

end GameTheory
