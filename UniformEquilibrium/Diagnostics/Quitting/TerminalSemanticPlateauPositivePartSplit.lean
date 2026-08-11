/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloSpineOccupation

/-!
# Positive-part charging on a semantic plateau

A limiting pure-time best-response law represents one player's best-response
debt by an exact signed terminal reward moment.  Passing to positive parts
splits that debt into two aggregate resources:

* a harmonic `Never` contribution;
* a finite contribution carried by coalitions containing a quitting opponent.

Unlike a selected-atom argument, this split has no loss depending on the
number of terminal outcomes.  Under a uniform reward bound the finite resource
controls the total deleted-player absorption probability of the same law.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive contribution of the harmonic `Never` boundary to one player's
terminal gain. -/
def quittingTerminalPositiveHarmonicContribution
    (pair : QuittingTerminalSemanticPair ι) (who : ι)
    (mass : QuittingTerminalOutcome ι → ℝ) : ℝ :=
  mass none * max 0 (-pair.1 who)

/-- Aggregate positive contribution of finite terminal coalitions to one
player's terminal gain. -/
def quittingTerminalPositiveFiniteContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (who : ι)
    (mass : QuittingTerminalOutcome ι → ℝ) : ℝ :=
  ∑ terminal, mass (some terminal) * max 0 (reward terminal who - pair.1 who)

/-- Total finite terminal mass carried by coalitions other than the selected
player's singleton.  Since every terminal coalition is nonempty, this is
exactly the probability that at least one opponent of `who` quits. -/
def quittingTerminalOpponentContainingMass
    (who : ι) (mass : QuittingTerminalOutcome ι → ℝ) : ℝ :=
  ∑ terminal ∈ Finset.univ.filter (fun terminal => terminal.val ≠ {who}),
    mass (some terminal)

/-- Opponent-containing mass is a continuous linear statistic of a finite
terminal law. -/
theorem continuous_quittingTerminalOpponentContainingMass (who : ι) :
    Continuous (quittingTerminalOpponentContainingMass who) := by
  unfold quittingTerminalOpponentContainingMass
  fun_prop

omit [DecidableEq ι] in
/-- The exact signed terminal moment is bounded by the harmonic plus finite
positive-part contributions. -/
theorem quittingTerminalSemanticDebt_le_positiveHarmonic_add_finite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (who : ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hmoment : quittingTerminalRewardMoment reward mass who = pair.2 who) :
    quittingTerminalSemanticDebt pair who ≤
      quittingTerminalPositiveHarmonicContribution pair who mass +
        quittingTerminalPositiveFiniteContribution reward pair who mass := by
  let gain : QuittingTerminalOutcome ι → ℝ := fun outcome =>
    quittingTerminalOutcomeReward reward outcome who - pair.1 who
  have hsigned : (∑ outcome, mass outcome * gain outcome) =
      quittingTerminalSemanticDebt pair who := by
    dsimp only [gain]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hmass.2, one_mul]
    unfold quittingTerminalRewardMoment at hmoment
    unfold quittingTerminalSemanticDebt
    linarith
  have hpositive : (∑ outcome, mass outcome * gain outcome) ≤
      ∑ outcome, mass outcome * max 0 (gain outcome) := by
    apply Finset.sum_le_sum
    intro outcome _houtcome
    exact mul_le_mul_of_nonneg_left (le_max_right 0 (gain outcome))
      (hmass.1 outcome)
  rw [hsigned] at hpositive
  calc
    quittingTerminalSemanticDebt pair who ≤
        ∑ outcome, mass outcome * max 0 (gain outcome) := hpositive
    _ = quittingTerminalPositiveHarmonicContribution pair who mass +
        quittingTerminalPositiveFiniteContribution reward pair who mass := by
      rw [Fintype.sum_option]
      simp [gain, quittingTerminalPositiveHarmonicContribution,
        quittingTerminalPositiveFiniteContribution,
        quittingTerminalOutcomeReward]

omit [DecidableEq ι] in
/-- Every split threshold gives either a harmonic share or a finite killed
share of the debt. -/
theorem positiveHarmonic_or_finiteContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (who : ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hmoment : quittingTerminalRewardMoment reward mass who = pair.2 who)
    (theta : ℝ) :
    theta * quittingTerminalSemanticDebt pair who ≤
        quittingTerminalPositiveHarmonicContribution pair who mass ∨
      (1 - theta) * quittingTerminalSemanticDebt pair who ≤
        quittingTerminalPositiveFiniteContribution reward pair who mass := by
  have hsplit := quittingTerminalSemanticDebt_le_positiveHarmonic_add_finite
    reward pair who mass hmass hmoment
  by_cases hharmonic : theta * quittingTerminalSemanticDebt pair who ≤
      quittingTerminalPositiveHarmonicContribution pair who mass
  · exact Or.inl hharmonic
  · right
    linarith

omit [DecidableEq ι] in
/-- A coordinate of a finite probability vector is at most one. -/
theorem terminalOutcomeMass_le_one
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (outcome : QuittingTerminalOutcome ι) :
    mass outcome ≤ 1 := by
  calc
    mass outcome ≤ ∑ candidate, mass candidate := by
      exact Finset.single_le_sum (fun candidate _ => hmass.1 candidate)
        (Finset.mem_univ outcome)
    _ = 1 := hmass.2

/-- All positive finite contribution is charged to coalitions containing at
least one quitting opponent.  The factor `2*M` is the largest possible gain
when rewards and the prescribed coordinate lie in `[-M,M]`. -/
theorem positiveFiniteContribution_le_two_mul_opponentContainingMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hprescribed : |pair.1 who| ≤ M)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι)) :
    quittingTerminalPositiveFiniteContribution reward pair who mass ≤
      2 * M * quittingTerminalOpponentContainingMass who mass := by
  have hsingleton :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward pair.1).mp hnash who
  unfold quittingTerminalPositiveFiniteContribution
  calc
    (∑ terminal, mass (some terminal) *
        max 0 (reward terminal who - pair.1 who)) ≤
        ∑ terminal, if terminal.val ≠ {who} then
          2 * M * mass (some terminal) else 0 := by
      apply Finset.sum_le_sum
      intro terminal _hterminal
      by_cases hother : terminal.val ≠ {who}
      · rw [if_pos hother]
        have hrewardUpper := (abs_le.mp (hreward terminal who)).2
        have hprescribedLower := (abs_le.mp hprescribed).1
        have hgainUpper : reward terminal who - pair.1 who ≤ 2 * M := by
          linarith
        have hpositiveUpper :
            max 0 (reward terminal who - pair.1 who) ≤ 2 * M := by
          exact max_le (by linarith) hgainUpper
        calc
          mass (some terminal) *
              max 0 (reward terminal who - pair.1 who) ≤
              mass (some terminal) * (2 * M) :=
            mul_le_mul_of_nonneg_left hpositiveUpper (hmass.1 (some terminal))
          _ = 2 * M * mass (some terminal) := by ring
      · rw [if_neg hother]
        have hterminal : terminal = quittingSingletonTerminal who := by
          apply Subtype.ext
          simpa [quittingSingletonTerminal] using not_ne_iff.mp hother
        subst terminal
        have hgainNonpos :
            reward (quittingSingletonTerminal who) who - pair.1 who ≤ 0 := by
          linarith
        rw [max_eq_left hgainNonpos, mul_zero]
    _ = 2 * M * quittingTerminalOpponentContainingMass who mass := by
      rw [← Finset.sum_filter]
      unfold quittingTerminalOpponentContainingMass
      rw [Finset.mul_sum]

omit [DecidableEq ι] in
/-- A large harmonic contribution forces both a negative prescribed value and
a quantitative `Never` mass. -/
theorem harmonicContribution_quantitative_bounds
    (pair : QuittingTerminalSemanticPair ι) (who : ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    {M theta : ℝ} (hM : 0 < M)
    (hprescribed : |pair.1 who| ≤ M)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hdebt : 0 < quittingTerminalSemanticDebt pair who)
    (htheta : 0 < theta)
    (hharmonic : theta * quittingTerminalSemanticDebt pair who ≤
      quittingTerminalPositiveHarmonicContribution pair who mass) :
    pair.1 who ≤ -theta * quittingTerminalSemanticDebt pair who ∧
      theta * quittingTerminalSemanticDebt pair who / M ≤ mass none := by
  have hmassNonneg := hmass.1 none
  have hmassOne := terminalOutcomeMass_le_one mass hmass none
  have hpositiveNonneg : 0 ≤ max 0 (-pair.1 who) := le_max_left _ _
  have hthresholdPos : 0 < theta * quittingTerminalSemanticDebt pair who :=
    mul_pos htheta hdebt
  have hpositiveThreshold : theta * quittingTerminalSemanticDebt pair who ≤
      max 0 (-pair.1 who) := by
    calc
      theta * quittingTerminalSemanticDebt pair who ≤
          quittingTerminalPositiveHarmonicContribution pair who mass :=
        hharmonic
      _ ≤ max 0 (-pair.1 who) := by
        unfold quittingTerminalPositiveHarmonicContribution
        nlinarith
  have hnegative : pair.1 who < 0 := by
    by_contra hnot
    have hnonneg : 0 ≤ pair.1 who := le_of_not_gt hnot
    have hzero : max 0 (-pair.1 who) = 0 := max_eq_left (by linarith)
    rw [hzero] at hpositiveThreshold
    linarith
  have hmaxEq : max 0 (-pair.1 who) = -pair.1 who :=
    max_eq_right (by linarith)
  have hvalue : pair.1 who ≤
      -theta * quittingTerminalSemanticDebt pair who := by
    rw [hmaxEq] at hpositiveThreshold
    linarith
  have hpositiveUpper : max 0 (-pair.1 who) ≤ M := by
    rw [hmaxEq]
    linarith [(abs_le.mp hprescribed).1]
  have hthresholdMass : theta * quittingTerminalSemanticDebt pair who ≤
      mass none * M := by
    calc
      theta * quittingTerminalSemanticDebt pair who ≤
          quittingTerminalPositiveHarmonicContribution pair who mass :=
        hharmonic
      _ ≤ mass none * M := by
        unfold quittingTerminalPositiveHarmonicContribution
        exact mul_le_mul_of_nonneg_left hpositiveUpper hmassNonneg
  refine ⟨hvalue, (div_le_iff₀ hM).2 ?_⟩
  nlinarith

/-- A large finite positive contribution forces an outcome-count-free lower
bound on the total probability of opponent-containing absorption. -/
theorem finiteContribution_opponentContainingMass_lower_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    {M charge : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hprescribed : |pair.1 who| ≤ M)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hfinite : charge ≤
      quittingTerminalPositiveFiniteContribution reward pair who mass) :
    charge / (2 * M) ≤ quittingTerminalOpponentContainingMass who mass := by
  have hupper := positiveFiniteContribution_le_two_mul_opponentContainingMass
    reward pair hnash who mass hM.le hreward hprescribed hmass
  apply (div_le_iff₀ (by positivity : 0 < 2 * M)).2
  linarith

/-- Quantitative harmonic-versus-killed-mass passport.  Both alternatives
refer to the same terminal law. -/
theorem negativeNever_or_opponentContainingMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    {M theta : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hprescribed : |pair.1 who| ≤ M)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hmoment : quittingTerminalRewardMoment reward mass who = pair.2 who)
    (hdebt : 0 < quittingTerminalSemanticDebt pair who)
    (htheta : 0 < theta) (_hthetaOne : theta < 1) :
    (pair.1 who ≤ -theta * quittingTerminalSemanticDebt pair who ∧
        theta * quittingTerminalSemanticDebt pair who / M ≤ mass none) ∨
      (1 - theta) * quittingTerminalSemanticDebt pair who / (2 * M) ≤
        quittingTerminalOpponentContainingMass who mass := by
  rcases positiveHarmonic_or_finiteContribution
      reward pair who mass hmass hmoment theta with hharmonic | hfinite
  · exact Or.inl (harmonicContribution_quantitative_bounds
      pair who mass hM hprescribed hmass hdebt htheta hharmonic)
  · exact Or.inr (finiteContribution_opponentContainingMass_lower_bound
      reward pair hnash who mass hM hreward hprescribed hmass hfinite)

/-- If the prescribed coordinate is nonnegative, the harmonic contribution
vanishes and the full debt is charged to opponent-containing finite mass. -/
theorem opponentContainingMass_lower_bound_of_prescribed_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hprescribed : |pair.1 who| ≤ M)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hmoment : quittingTerminalRewardMoment reward mass who = pair.2 who)
    (hprescribedNonneg : 0 ≤ pair.1 who) :
    quittingTerminalSemanticDebt pair who / (2 * M) ≤
      quittingTerminalOpponentContainingMass who mass := by
  have hsplit := quittingTerminalSemanticDebt_le_positiveHarmonic_add_finite
    reward pair who mass hmass hmoment
  have hharmonicZero :
      quittingTerminalPositiveHarmonicContribution pair who mass = 0 := by
    unfold quittingTerminalPositiveHarmonicContribution
    rw [max_eq_left (by linarith), mul_zero]
  rw [hharmonicZero, zero_add] at hsplit
  exact finiteContribution_opponentContainingMass_lower_bound
    reward pair hnash who mass hM hreward hprescribed hmass hsplit

/-- The opponent-containing terminal mass of an executable profile is exactly
the aggregate chronological stage charge. -/
theorem opponentContainingMass_outcomeMass_eq_stageCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalOpponentContainingMass who
        (quittingTerminalOutcomeMass reward profile) =
      ∑ terminal ∈ Finset.univ.filter (fun terminal => terminal.val ≠ {who}),
        ∑' time, quittingStageCoalitionMass reward profile time terminal := by
  unfold quittingTerminalOpponentContainingMass
  apply Finset.sum_congr rfl
  intro terminal _hterminal
  exact quittingTerminalOutcomeMass_eq_timeDisintegration
    reward profile (some terminal)

/-- **Same-law plateau capstone.**  A positive best-response debt admits one
realizing sequence and one limiting pure-time deviation law on which either:

* a fixed fraction of the debt survives harmonically at `Never`, forcing a
  negative prescribed value and eventually literal `Never` deviations; or
* a fixed fraction is carried by opponent-containing absorption, and the
  same actual deviated profiles eventually carry half that fraction in their
  exact chronological stage charge.

There is no terminal-outcome cardinality loss.  The finite branch is already
expressed in the time-disintegrated currency used by prefix incidence. -/
theorem exists_samePureTimeLaw_negativeNever_or_chronologicalOpponentCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (hdebt : 0 < quittingTerminalSemanticDebt pair who)
    {M theta : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∃ (profiles : ℕ → (quittingGame reward).BehaviorProfile)
        (quitTime : ℕ → Option ℕ)
        (mass : QuittingTerminalOutcome ι → ℝ)
        (subseq : ℕ → ℕ),
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
          atTop (𝓝 pair) ∧
      mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
      StrictMono subseq ∧
      Tendsto (fun n => quittingTerminalOutcomeMass reward
          (Function.update (profiles (subseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq n)))))
        atTop (𝓝 mass) ∧
      ((pair.1 who ≤ -theta * quittingTerminalSemanticDebt pair who ∧
          theta * quittingTerminalSemanticDebt pair who / M ≤ mass none ∧
          ∀ᶠ n in atTop, quitTime (subseq n) = none) ∨
        ((1 - theta) * quittingTerminalSemanticDebt pair who / (2 * M) ≤
            quittingTerminalOpponentContainingMass who mass ∧
          ∀ᶠ n in atTop,
            ((1 - theta) * quittingTerminalSemanticDebt pair who /
                (2 * M)) / 2 <
              ∑ terminal ∈ Finset.univ.filter
                  (fun terminal => terminal.val ≠ {who}),
                ∑' time, quittingStageCoalitionMass reward
                  (Function.update (profiles (subseq n)) who
                    (quittingPureTimeBehaviorStrategy reward who
                      (quitTime (subseq n)))) time terminal)) := by
  obtain ⟨profiles, quitTime, mass, subseq, hprofiles, hmass, hsubseq,
      hmassLimit, hmoment⟩ :=
    exists_pureTimeDeviation_terminalLaw_tendsto_semanticEnvelope
      reward pair hpair who hM.le hreward
  have hbox := quittingTerminalSemanticCarrier_mem_box
    (reward := reward) pair hM.le hreward hpair
  have hprescribed : |pair.1 who| ≤ M :=
    abs_le.mpr ⟨hbox.1.1 who, hbox.1.2 who⟩
  have hpassport := negativeNever_or_opponentContainingMass
    reward pair hnash who mass hM hreward hprescribed hmass hmoment hdebt
      htheta hthetaOne
  refine ⟨profiles, quitTime, mass, subseq, hprofiles, hmass, hsubseq,
    hmassLimit, ?_⟩
  rcases hpassport with hnever | hfinite
  · left
    refine ⟨hnever.1, hnever.2, ?_⟩
    let lower := theta * quittingTerminalSemanticDebt pair who / M
    have hlower : 0 < lower := by
      dsimp only [lower]
      positivity
    have hcoordinate : Tendsto (fun n =>
        quittingTerminalOutcomeMass reward
          (Function.update (profiles (subseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq n)))) none)
        atTop (𝓝 (mass none)) :=
      ((continuous_apply none).tendsto mass).comp hmassLimit
    have hpersistent : ∀ᶠ n in atTop, lower / 2 <
        quittingTerminalOutcomeMass reward
          (Function.update (profiles (subseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq n)))) none :=
      hcoordinate.eventually
        (Ioi_mem_nhds (lt_of_lt_of_le (half_lt_self hlower) hnever.2))
    exact eventually_quitTime_eq_none_of_persistent_neverMass reward
      (fun n => profiles (subseq n)) who (fun n => quitTime (subseq n))
      (lower / 2) (half_pos hlower) hpersistent
  · right
    refine ⟨hfinite, ?_⟩
    let lower := (1 - theta) * quittingTerminalSemanticDebt pair who / (2 * M)
    let deviated : ℕ → (quittingGame reward).BehaviorProfile := fun n =>
      Function.update (profiles (subseq n)) who
        (quittingPureTimeBehaviorStrategy reward who (quitTime (subseq n)))
    have hlower : 0 < lower := by
      dsimp only [lower]
      positivity
    have hlowerLe : lower ≤
        quittingTerminalOpponentContainingMass who mass := by
      simpa only [lower] using hfinite
    have hmassLimit' : Tendsto (fun n =>
        quittingTerminalOutcomeMass reward (deviated n)) atTop (𝓝 mass) := by
      simpa only [deviated] using hmassLimit
    have hopponentLimit : Tendsto (fun n =>
        quittingTerminalOpponentContainingMass who
          (quittingTerminalOutcomeMass reward (deviated n)))
        atTop (𝓝 (quittingTerminalOpponentContainingMass who mass)) :=
      (continuous_quittingTerminalOpponentContainingMass who).tendsto mass |>.comp
        hmassLimit'
    have hpersistent : ∀ᶠ n in atTop, lower / 2 <
        quittingTerminalOpponentContainingMass who
          (quittingTerminalOutcomeMass reward (deviated n)) :=
      hopponentLimit.eventually
        (Ioi_mem_nhds (lt_of_lt_of_le (half_lt_self hlower) hlowerLe))
    filter_upwards [hpersistent] with n hn
    simpa only [lower, deviated,
      opponentContainingMass_outcomeMass_eq_stageCharge] using hn

end GameTheory
