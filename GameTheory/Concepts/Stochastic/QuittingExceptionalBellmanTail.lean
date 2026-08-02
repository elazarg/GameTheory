/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBellmanTelescope

/-!
# Finite exceptional-clock Bellman tail

The exceptional branch has two independent finite survival coordinates:
`π`, the opponents' survival probability, and `α`, the prescribed player's
own survival probability.  This file keeps both coordinates.  In particular,
it does not discard the own-never atom `π * R * α` and makes no infinite-tail
closure claim.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

/-- Removing one distinguished atom from a finite expectation costs at most
the payoff bound times the complementary probability mass. -/
theorem abs_expect_sub_singletonContribution_le
    {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (distribution : PMF Ω) (point : Ω) (value : Ω → ℝ)
    (pointValue bound : ℝ)
    (hpoint : value point = pointValue)
    (hbound : ∀ outcome, |value outcome| ≤ bound) :
    |expect distribution value -
        (distribution point).toReal * pointValue| ≤
      bound * (1 - (distribution point).toReal) := by
  rw [expect_eq_sum]
  have hmass : ∑ outcome : Ω, (distribution outcome).toReal = 1 :=
    pmf_toReal_sum_one distribution
  have hsplitMass := Finset.add_sum_erase
    (Finset.univ : Finset Ω) (fun outcome =>
      (distribution outcome).toReal) (Finset.mem_univ point)
  calc
    |(∑ outcome : Ω, (distribution outcome).toReal * value outcome) -
          (distribution point).toReal * pointValue| =
        |∑ outcome ∈ (Finset.univ : Finset Ω).erase point,
          (distribution outcome).toReal * value outcome| := by
            rw [← Finset.add_sum_erase (Finset.univ : Finset Ω)
              (fun outcome =>
                (distribution outcome).toReal * value outcome)
              (Finset.mem_univ point), hpoint]
            ring_nf
    _ ≤ ∑ outcome ∈ (Finset.univ : Finset Ω).erase point,
          |(distribution outcome).toReal * value outcome| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ outcome ∈ (Finset.univ : Finset Ω).erase point,
          (distribution outcome).toReal * |value outcome| := by
      apply Finset.sum_congr rfl
      intro outcome _
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ outcome ∈ (Finset.univ : Finset Ω).erase point,
          (distribution outcome).toReal * bound := by
      apply Finset.sum_le_sum
      intro outcome _
      exact mul_le_mul_of_nonneg_left (hbound outcome)
        ENNReal.toReal_nonneg
    _ = bound * (1 - (distribution point).toReal) := by
      rw [← Finset.sum_mul]
      have herase :
          ∑ outcome ∈ (Finset.univ : Finset Ω).erase point,
              (distribution outcome).toReal =
            1 - (distribution point).toReal := by
        rw [hmass] at hsplitMass
        linarith
      rw [herase]
      ring_nf

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The pure joint action at which exactly `who` quits. -/
def quittingSoloQuitAction (who : ι) : ι → Bool :=
  Function.update quittingAllContinueAction who true

/-- Exactly `who` quits in the solo-quit action. -/
@[simp] theorem quittingQuitters_soloQuitAction (who : ι) :
    quittingQuitters (quittingSoloQuitAction who) = {who} := by
  ext player
  by_cases hp : player = who
  · subst player
    simp [quittingQuitters, quittingSoloQuitAction]
  · simp [quittingQuitters, quittingSoloQuitAction,
      quittingAllContinueAction, hp]

/-- The payoff at the solo-quit action is the singleton terminal reward. -/
@[simp] theorem quittingRootPayoff_soloQuitAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (who : ι) :
    quittingRootPayoff reward continuation (quittingSoloQuitAction who) who =
      reward (quittingSingletonTerminal who) who := by
  have hnonempty :
      (quittingQuitters (quittingSoloQuitAction who)).Nonempty := by
    rw [quittingQuitters_soloQuitAction]
    exact Finset.singleton_nonempty who
  unfold quittingRootPayoff
  rw [dif_pos hnonempty]
  congr
  exact quittingQuitters_soloQuitAction who

/-- The probability of the solo-quit action when `who` quits surely is the
probability that every opponent continues. -/
theorem pmfPi_update_pure_true_soloQuitAction_toReal
    (root : ι → PMF Bool) (who : ι) :
    ((pmfPi (Function.update root who (PMF.pure true)))
        (quittingSoloQuitAction who)).toReal =
      quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) := by
  unfold quittingStationaryContinueMass
  apply congrArg ENNReal.toReal
  rw [pmfPi_apply, pmfPi_apply]
  apply Finset.prod_congr rfl
  intro player _
  by_cases hp : player = who
  · subst player
    simp [quittingSoloQuitAction, quittingAllContinueAction]
  · simp [quittingSoloQuitAction, Function.update_of_ne hp]

/-- Current absorption while `who` continues is paid entirely by the
opponent hazard. -/
theorem abs_quittingFixedOpponentsContinueReward_le_hazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ)
    (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound) :
    |quittingFixedOpponentsContinueReward reward roots who time| ≤
      bound * (1 - quittingFixedOpponentsContinueMass roots who time) := by
  let root := Function.update (roots time) who (PMF.pure false)
  have hpoint : quittingRootPayoff reward (0 : Payoff ι)
      (quittingAllContinueAction : ι → Bool) who = 0 := by
    simp [quittingRootPayoff]
  have hpayoff : ∀ action : ι → Bool,
      |quittingRootPayoff reward (0 : Payoff ι) action who| ≤ bound := by
    intro action
    by_cases hquit : (quittingQuitters action).Nonempty
    · simpa [quittingRootPayoff, hquit] using
        hreward ⟨quittingQuitters action, hquit⟩
    · simpa [quittingRootPayoff, hquit] using hbound0
  have hestimate := abs_expect_sub_singletonContribution_le
    (pmfPi root) (quittingAllContinueAction : ι → Bool)
      (fun action => quittingRootPayoff reward (0 : Payoff ι) action who)
      0 bound hpoint hpayoff
  simpa [root, quittingFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueMass, quittingRootAbsorbingContribution,
    quittingRootExpectedPayoff, quittingStationaryContinueMass] using hestimate

/-- Quitting now differs from the solo reward times opponent survival only
on events where at least one opponent also quits. -/
theorem abs_quittingFixedOpponentsQuitValue_sub_continueMass_mul_solo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ)
    (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound) :
    |quittingFixedOpponentsQuitValue reward roots who time -
        quittingFixedOpponentsContinueMass roots who time *
          reward (quittingSingletonTerminal who) who| ≤
      bound * (1 - quittingFixedOpponentsContinueMass roots who time) := by
  let root := Function.update (roots time) who (PMF.pure true)
  let soloAction : ι → Bool := quittingSoloQuitAction who
  have hpoint : quittingRootPayoff reward (0 : Payoff ι) soloAction who =
      reward (quittingSingletonTerminal who) who := by
    simp [soloAction]
  have hpayoff : ∀ action : ι → Bool,
      |quittingRootPayoff reward (0 : Payoff ι) action who| ≤ bound := by
    intro action
    by_cases hquit : (quittingQuitters action).Nonempty
    · simpa [quittingRootPayoff, hquit] using
        hreward ⟨quittingQuitters action, hquit⟩
    · simpa [quittingRootPayoff, hquit] using hbound0
  have hestimate := abs_expect_sub_singletonContribution_le
    (pmfPi root) soloAction
      (fun action => quittingRootPayoff reward (0 : Payoff ι) action who)
      (reward (quittingSingletonTerminal who) who) bound hpoint hpayoff
  have hmass := pmfPi_update_pure_true_soloQuitAction_toReal
    (roots time) who
  have hmass' : ((pmfPi root) soloAction).toReal =
      quittingFixedOpponentsContinueMass roots who time := by
    simpa [root, soloAction, quittingFixedOpponentsContinueMass] using hmass
  rw [hmass'] at hestimate
  simpa [quittingFixedOpponentsQuitValue,
    quittingFixedOpponentsContinueMass, quittingRootAbsorbingContribution,
    quittingRootExpectedPayoff, root, soloAction] using hestimate

/-- Finite survival generated by a scalar sequence of continue masses.  The
recursion is oriented from the current live stage, matching the Bellman
recursions. -/
def quittingFiniteContinueWeight
    (continueMass : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | start, fuel + 1 =>
      continueMass start *
        quittingFiniteContinueWeight continueMass (start + 1) fuel

/-- A finite product of nonnegative continue masses is nonnegative. -/
theorem quittingFiniteContinueWeight_nonneg
    (continueMass : ℕ → ℝ)
    (hmass : ∀ time, 0 ≤ continueMass time) :
    ∀ start fuel, 0 ≤ quittingFiniteContinueWeight continueMass start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingFiniteContinueWeight]
  | succ fuel ih =>
      rw [quittingFiniteContinueWeight]
      exact mul_nonneg (hmass start) (ih (start + 1))

/-- A finite product of continue masses bounded by one is bounded by one. -/
theorem quittingFiniteContinueWeight_le_one
    (continueMass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ continueMass time)
    (hmass1 : ∀ time, continueMass time ≤ 1) :
    ∀ start fuel, quittingFiniteContinueWeight continueMass start fuel ≤ 1 := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingFiniteContinueWeight]
  | succ fuel ih =>
      rw [quittingFiniteContinueWeight]
      calc
        continueMass start *
              quittingFiniteContinueWeight continueMass (start + 1) fuel ≤
            continueMass start * 1 :=
              mul_le_mul_of_nonneg_left (ih (start + 1)) (hmass0 start)
        _ = continueMass start := mul_one _
        _ ≤ 1 := hmass1 start

/-- Finite survival of the prescribed player's own continue hazards. -/
def quittingFiniteOwnContinueWeight
    (hazard : ℕ → PMF Bool) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | start, fuel + 1 =>
      (hazard start false).toReal *
        quittingFiniteOwnContinueWeight hazard (start + 1) fuel

/-- The own-continue weight is the last (`never within the cutoff`) hazard
simplex weight. -/
theorem quittingFiniteOwnContinueWeight_eq_hazardWeight_last
    (hazard : ℕ → PMF Bool) :
    ∀ start fuel,
      quittingFiniteOwnContinueWeight hazard start fuel =
        quittingFiniteHazardWeight hazard start fuel (Fin.last fuel) := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingFiniteOwnContinueWeight,
      quittingFiniteHazardWeight]
  | succ fuel ih =>
      rw [show Fin.last (fuel + 1) = (Fin.last fuel).succ by rfl]
      simp only [quittingFiniteOwnContinueWeight,
        quittingFiniteHazardWeight, Fin.cases_succ, ih]

/-- Deterministic finite quit times have the expected exceptional-clock
estimate.  Every choice that quits within the cutoff is within
`M * (1 - π)` of `π * R`; continuing throughout is within that error of
zero. -/
theorem quittingFinitePureTime_exceptional_bounds
    (quitValue continueReward continueMass : ℕ → ℝ)
    (start fuel : ℕ) (soloReward bound : ℝ)
    (hsolo0 : 0 ≤ soloReward) (hsoloBound : soloReward ≤ bound)
    (hmass0 : ∀ time, 0 ≤ continueMass time)
    (hmass1 : ∀ time, continueMass time ≤ 1)
    (hquit : ∀ time,
      |quitValue time - continueMass time * soloReward| ≤
        bound * (1 - continueMass time))
    (hcontinue : ∀ time,
      |continueReward time| ≤ bound * (1 - continueMass time)) :
    (∀ choice : Fin fuel,
      |quittingFinitePureTimeValue quitValue continueReward continueMass
          start fuel choice.castSucc -
        quittingFiniteContinueWeight continueMass start fuel * soloReward| ≤
      bound *
        (1 - quittingFiniteContinueWeight continueMass start fuel)) ∧
    |quittingFinitePureTimeValue quitValue continueReward continueMass
        start fuel (Fin.last fuel)| ≤
      bound *
        (1 - quittingFiniteContinueWeight continueMass start fuel) := by
  induction fuel generalizing start with
  | zero =>
      constructor
      · intro choice
        exact Fin.elim0 choice
      · simp [quittingFinitePureTimeValue, quittingFiniteContinueWeight]
  | succ fuel ih =>
      let currentMass := continueMass start
      let tailWeight :=
        quittingFiniteContinueWeight continueMass (start + 1) fuel
      have hcurrent0 : 0 ≤ currentMass := hmass0 start
      have hcurrent1 : currentMass ≤ 1 := hmass1 start
      have htail0 : 0 ≤ tailWeight :=
        quittingFiniteContinueWeight_nonneg continueMass hmass0
          (start + 1) fuel
      have htail1 : tailWeight ≤ 1 :=
        quittingFiniteContinueWeight_le_one continueMass hmass0 hmass1
          (start + 1) fuel
      have hmissingNonneg :
          0 ≤ currentMass * (1 - tailWeight) *
            (bound - soloReward) :=
        mul_nonneg
          (mul_nonneg hcurrent0 (sub_nonneg.mpr htail1))
          (sub_nonneg.mpr hsoloBound)
      have hquitNow :
          |quitValue start -
              currentMass * tailWeight * soloReward| ≤
            bound * (1 - currentMass * tailWeight) := by
        calc
          |quitValue start - currentMass * tailWeight * soloReward| =
              |(quitValue start - currentMass * soloReward) +
                currentMass * soloReward * (1 - tailWeight)| := by
                  congr 1
                  ring
          _ ≤ |quitValue start - currentMass * soloReward| +
              |currentMass * soloReward * (1 - tailWeight)| :=
                abs_add_le _ _
          _ ≤ bound * (1 - currentMass) +
              currentMass * soloReward * (1 - tailWeight) := by
                apply add_le_add (hquit start)
                rw [abs_of_nonneg]
                exact mul_nonneg
                  (mul_nonneg hcurrent0 hsolo0)
                  (sub_nonneg.mpr htail1)
          _ ≤ bound * (1 - currentMass * tailWeight) := by
                nlinarith
      have htail := ih (start + 1)
      constructor
      · intro choice
        refine Fin.cases ?_ (fun later => ?_) choice
        · simpa only [quittingFinitePureTimeValue,
            quittingFiniteContinueWeight, Fin.castSucc_zero,
            Fin.cases_zero] using hquitNow
        · have htailQuit := htail.1 later
          have hscaledTail :
              currentMass *
                  |quittingFinitePureTimeValue quitValue continueReward
                      continueMass (start + 1) fuel later.castSucc -
                    tailWeight * soloReward| ≤
                currentMass * (bound * (1 - tailWeight)) :=
            mul_le_mul_of_nonneg_left htailQuit hcurrent0
          simp only [Fin.castSucc_succ, quittingFinitePureTimeValue,
            Fin.cases_succ, quittingFiniteContinueWeight]
          change
            |continueReward start + currentMass *
                  quittingFinitePureTimeValue quitValue continueReward
                    continueMass (start + 1) fuel later.castSucc -
                currentMass * tailWeight * soloReward| ≤
              bound * (1 - currentMass * tailWeight)
          calc
            |continueReward start + currentMass *
                  quittingFinitePureTimeValue quitValue continueReward
                    continueMass (start + 1) fuel later.castSucc -
                currentMass * tailWeight * soloReward| =
                |continueReward start + currentMass *
                  (quittingFinitePureTimeValue quitValue continueReward
                    continueMass (start + 1) fuel later.castSucc -
                      tailWeight * soloReward)| := by
                    congr 1
                    ring
            _ ≤ |continueReward start| + currentMass *
                  |quittingFinitePureTimeValue quitValue continueReward
                    continueMass (start + 1) fuel later.castSucc -
                      tailWeight * soloReward| := by
                    calc
                      _ ≤ |continueReward start| +
                          |currentMass *
                            (quittingFinitePureTimeValue quitValue
                              continueReward continueMass (start + 1) fuel
                                later.castSucc - tailWeight * soloReward)| :=
                            abs_add_le _ _
                      _ = _ := by rw [abs_mul, abs_of_nonneg hcurrent0]
            _ ≤ bound * (1 - currentMass) +
                  currentMass * (bound * (1 - tailWeight)) :=
                    add_le_add (hcontinue start) hscaledTail
            _ = bound * (1 - currentMass * tailWeight) := by ring
      · have htailNever := htail.2
        have hscaledTail :
            currentMass *
                |quittingFinitePureTimeValue quitValue continueReward
                    continueMass (start + 1) fuel (Fin.last fuel)| ≤
              currentMass * (bound * (1 - tailWeight)) :=
          mul_le_mul_of_nonneg_left htailNever hcurrent0
        rw [show Fin.last (fuel + 1) = (Fin.last fuel).succ by rfl]
        simp only [quittingFinitePureTimeValue, Fin.cases_succ,
          quittingFiniteContinueWeight]
        change
          |continueReward start + currentMass *
              quittingFinitePureTimeValue quitValue continueReward
                continueMass (start + 1) fuel (Fin.last fuel)| ≤
            bound * (1 - currentMass * tailWeight)
        calc
          |continueReward start + currentMass *
              quittingFinitePureTimeValue quitValue continueReward
                continueMass (start + 1) fuel (Fin.last fuel)| ≤
              |continueReward start| + currentMass *
                |quittingFinitePureTimeValue quitValue continueReward
                  continueMass (start + 1) fuel (Fin.last fuel)| := by
                calc
                  _ ≤ |continueReward start| +
                      |currentMass *
                        quittingFinitePureTimeValue quitValue continueReward
                          continueMass (start + 1) fuel (Fin.last fuel)| :=
                        abs_add_le _ _
                  _ = _ := by rw [abs_mul, abs_of_nonneg hcurrent0]
          _ ≤ bound * (1 - currentMass) +
                currentMass * (bound * (1 - tailWeight)) :=
                  add_le_add (hcontinue start) hscaledTail
          _ = bound * (1 - currentMass * tailWeight) := by ring

/-- The prescribed finite hazard payoff is close to the no-opponent-event
payoff `π * R * (1 - α)`, with every event involving an opponent charged to
`1 - π`. -/
theorem abs_quittingFiniteHazardValue_sub_exceptionalTarget_le
    (quitValue continueReward continueMass : ℕ → ℝ)
    (hazard : ℕ → PMF Bool)
    (start fuel : ℕ) (soloReward bound : ℝ)
    (hsolo0 : 0 ≤ soloReward) (hsoloBound : soloReward ≤ bound)
    (hmass0 : ∀ time, 0 ≤ continueMass time)
    (hmass1 : ∀ time, continueMass time ≤ 1)
    (hquit : ∀ time,
      |quitValue time - continueMass time * soloReward| ≤
        bound * (1 - continueMass time))
    (hcontinue : ∀ time,
      |continueReward time| ≤ bound * (1 - continueMass time)) :
    |quittingFiniteHazardValue quitValue continueReward continueMass
          hazard start fuel -
        quittingFiniteContinueWeight continueMass start fuel * soloReward *
          (1 - quittingFiniteOwnContinueWeight hazard start fuel)| ≤
      bound *
        (1 - quittingFiniteContinueWeight continueMass start fuel) := by
  induction fuel generalizing start with
  | zero =>
      simp [quittingFiniteHazardValue, quittingFiniteContinueWeight,
        quittingFiniteOwnContinueWeight]
  | succ fuel ih =>
      let currentMass := continueMass start
      let tailWeight :=
        quittingFiniteContinueWeight continueMass (start + 1) fuel
      let tailOwnWeight :=
        quittingFiniteOwnContinueWeight hazard (start + 1) fuel
      let quitProbability := (hazard start true).toReal
      let continueProbability := (hazard start false).toReal
      let tailValue :=
        quittingFiniteHazardValue quitValue continueReward continueMass
          hazard (start + 1) fuel
      let continueValue := continueReward start + currentMass * tailValue
      let quitTarget := currentMass * tailWeight * soloReward
      let continueTarget :=
        currentMass * tailWeight * soloReward * (1 - tailOwnWeight)
      let error := bound * (1 - currentMass * tailWeight)
      have hcurrent0 : 0 ≤ currentMass := hmass0 start
      have hquitProbability0 : 0 ≤ quitProbability := ENNReal.toReal_nonneg
      have hcontinueProbability0 : 0 ≤ continueProbability :=
        ENNReal.toReal_nonneg
      have hprobabilitySum : quitProbability + continueProbability = 1 := by
        dsimp [quitProbability, continueProbability]
        simpa [Fintype.sum_bool] using pmf_toReal_sum_one (hazard start)
      have hquitBranch :
          |quitValue start - quitTarget| ≤ error := by
        have hpure := (quittingFinitePureTime_exceptional_bounds
          quitValue continueReward continueMass start (fuel + 1)
          soloReward bound hsolo0 hsoloBound hmass0 hmass1 hquit hcontinue).1
          (0 : Fin (fuel + 1))
        simpa only [quittingFinitePureTimeValue,
          quittingFiniteContinueWeight, Fin.castSucc_zero,
          Fin.cases_zero] using hpure
      have htail := ih (start + 1)
      have hcontinueBranch :
          |continueValue - continueTarget| ≤ error := by
        have hscaledTail :
            currentMass *
                |tailValue - tailWeight * soloReward *
                  (1 - tailOwnWeight)| ≤
              currentMass * (bound * (1 - tailWeight)) :=
          mul_le_mul_of_nonneg_left htail hcurrent0
        calc
          |continueValue - continueTarget| =
              |continueReward start + currentMass *
                (tailValue - tailWeight * soloReward *
                  (1 - tailOwnWeight))| := by
                    congr 1
                    dsimp [continueValue, continueTarget]
                    ring
          _ ≤ |continueReward start| + currentMass *
                |tailValue - tailWeight * soloReward *
                  (1 - tailOwnWeight)| := by
                  calc
                    _ ≤ |continueReward start| +
                        |currentMass *
                          (tailValue - tailWeight * soloReward *
                            (1 - tailOwnWeight))| := abs_add_le _ _
                    _ = _ := by rw [abs_mul, abs_of_nonneg hcurrent0]
          _ ≤ bound * (1 - currentMass) +
                currentMass * (bound * (1 - tailWeight)) :=
                  add_le_add (hcontinue start) hscaledTail
          _ = error := by dsimp [error]; ring
      have htarget :
          currentMass * tailWeight * soloReward *
              (1 - continueProbability * tailOwnWeight) =
            quitProbability * quitTarget +
              continueProbability * continueTarget := by
        dsimp [quitTarget, continueTarget]
        rw [show quitProbability = 1 - continueProbability by linarith]
        ring
      simp only [quittingFiniteHazardValue,
        quittingFiniteContinueWeight, quittingFiniteOwnContinueWeight]
      change
        |quitProbability * quitValue start +
              continueProbability * continueValue -
            currentMass * tailWeight * soloReward *
              (1 - continueProbability * tailOwnWeight)| ≤ error
      rw [htarget]
      calc
        |quitProbability * quitValue start +
              continueProbability * continueValue -
            (quitProbability * quitTarget +
              continueProbability * continueTarget)| =
            |quitProbability * (quitValue start - quitTarget) +
              continueProbability * (continueValue - continueTarget)| := by
                congr 1
                ring
        _ ≤ quitProbability * |quitValue start - quitTarget| +
              continueProbability * |continueValue - continueTarget| := by
                calc
                  _ ≤ |quitProbability * (quitValue start - quitTarget)| +
                        |continueProbability *
                          (continueValue - continueTarget)| :=
                        abs_add_le _ _
                  _ = _ := by
                    rw [abs_mul, abs_mul,
                      abs_of_nonneg hquitProbability0,
                      abs_of_nonneg hcontinueProbability0]
        _ ≤ quitProbability * error + continueProbability * error :=
          add_le_add
            (mul_le_mul_of_nonneg_left hquitBranch hquitProbability0)
            (mul_le_mul_of_nonneg_left hcontinueBranch
              hcontinueProbability0)
        _ = error := by rw [← add_mul, hprobabilitySum, one_mul]

/-- Every arbitrary finite deviation hazard is bounded by the corrected
exceptional cap estimate `π * R + M * (1 - π)`. -/
theorem quittingFiniteHazardValue_le_exceptionalCap
    (quitValue continueReward continueMass : ℕ → ℝ)
    (hazard : ℕ → PMF Bool)
    (start fuel : ℕ) (soloReward bound : ℝ)
    (hsolo0 : 0 ≤ soloReward) (hsoloBound : soloReward ≤ bound)
    (hmass0 : ∀ time, 0 ≤ continueMass time)
    (hmass1 : ∀ time, continueMass time ≤ 1)
    (hquit : ∀ time,
      |quitValue time - continueMass time * soloReward| ≤
        bound * (1 - continueMass time))
    (hcontinue : ∀ time,
      |continueReward time| ≤ bound * (1 - continueMass time)) :
    quittingFiniteHazardValue quitValue continueReward continueMass
        hazard start fuel ≤
      quittingFiniteContinueWeight continueMass start fuel * soloReward +
        bound *
          (1 - quittingFiniteContinueWeight continueMass start fuel) := by
  obtain ⟨choice, hchoice⟩ :=
    exists_pureTime_ge_quittingFiniteHazardValue
      quitValue continueReward continueMass hazard start fuel
  have hpure := quittingFinitePureTime_exceptional_bounds
    quitValue continueReward continueMass start fuel soloReward bound
      hsolo0 hsoloBound hmass0 hmass1 hquit hcontinue
  have hweight0 := quittingFiniteContinueWeight_nonneg
    continueMass hmass0 start fuel
  refine le_trans hchoice ?_
  refine Fin.lastCases ?_ (fun earlier => ?_) choice
  · have hnever := hpure.2
    have hupper :
        quittingFinitePureTimeValue quitValue continueReward continueMass
            start fuel (Fin.last fuel) ≤
          bound *
            (1 - quittingFiniteContinueWeight continueMass start fuel) :=
      le_trans (le_abs_self _) hnever
    nlinarith [mul_nonneg hweight0 hsolo0]
  · have hquitChoice := hpure.1 earlier
    rw [abs_le] at hquitChoice
    linarith

/-- Corrected finite exceptional gap between an arbitrary deviation hazard
and the prescribed hazard.  The own-survival atom is retained explicitly. -/
theorem quittingFiniteHazardGap_le_exceptional
    (quitValue continueReward continueMass : ℕ → ℝ)
    (prescribedHazard deviationHazard : ℕ → PMF Bool)
    (start fuel : ℕ) (soloReward bound : ℝ)
    (hsolo0 : 0 ≤ soloReward) (hsoloBound : soloReward ≤ bound)
    (hmass0 : ∀ time, 0 ≤ continueMass time)
    (hmass1 : ∀ time, continueMass time ≤ 1)
    (hquit : ∀ time,
      |quitValue time - continueMass time * soloReward| ≤
        bound * (1 - continueMass time))
    (hcontinue : ∀ time,
      |continueReward time| ≤ bound * (1 - continueMass time)) :
    quittingFiniteHazardValue quitValue continueReward continueMass
          deviationHazard start fuel -
        quittingFiniteHazardValue quitValue continueReward continueMass
          prescribedHazard start fuel ≤
      quittingFiniteContinueWeight continueMass start fuel * soloReward *
          quittingFiniteOwnContinueWeight prescribedHazard start fuel +
        2 * bound *
          (1 - quittingFiniteContinueWeight continueMass start fuel) := by
  have hprescribed :=
    abs_quittingFiniteHazardValue_sub_exceptionalTarget_le
      quitValue continueReward continueMass prescribedHazard start fuel
        soloReward bound hsolo0 hsoloBound hmass0 hmass1 hquit hcontinue
  have hcap := quittingFiniteHazardValue_le_exceptionalCap
    quitValue continueReward continueMass deviationHazard start fuel
      soloReward bound hsolo0 hsoloBound hmass0 hmass1 hquit hcontinue
  rw [abs_le] at hprescribed
  nlinarith

/-- The two finite exceptional-tail estimates imply the corrected cap-gap
bound, including the own-never atom. -/
theorem exceptionalBellmanGap_le_of_prescribed_and_cap_bounds
    (prescribed cap opponentSurvival ownSurvival soloReward bound : ℝ)
    (hprescribed :
      |prescribed - opponentSurvival * soloReward * (1 - ownSurvival)| ≤
        bound * (1 - opponentSurvival))
    (hcap :
      cap ≤ opponentSurvival * soloReward +
        bound * (1 - opponentSurvival)) :
    cap - prescribed ≤
      opponentSurvival * soloReward * ownSurvival +
        2 * bound * (1 - opponentSurvival) := by
  rw [abs_le] at hprescribed
  nlinarith

end GameTheory
