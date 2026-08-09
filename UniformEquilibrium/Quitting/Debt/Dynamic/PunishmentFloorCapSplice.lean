/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCapCarrier
import UniformEquilibrium.Diagnostics.Uniform.NonexistenceCertificate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact cap-seeded finite splicing

A cap-seeded chronological prefix carries two evaluations of the same root
word.  The `cap` evaluation is exact Nash--Bellman against its successor cap;
the `value` evaluation is honest policy evaluation against the actual suffix
value.  Their difference is transported exactly by joint all-Continue
survival.

The cap evaluation is also the literal finite terminal-boundary unilateral
cap, not merely a supersolution.  To connect this finite statement to an
arbitrary infinite suffix one must separately realize the supplied terminal
cap as that suffix profile's complete behavioral best-reply value.  The
terminal-gap theorem below therefore takes this realization as an explicit
hypothesis.  No arbitrary-tail splice realization is asserted here.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A chronological finite root word evaluated both at an exact unilateral
cap and at the honest suffix value. -/
structure QuittingCapSeededPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  cap : ℕ → Payoff ι
  value : ℕ → Payoff ι
  horizon : ℕ
  cap_policy : ∀ time, time < horizon →
    cap time = quittingRootSuccessorPayoff reward (cap (time + 1)) (roots time)
  value_policy : ∀ time, time < horizon →
    value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time)
  exactNash : ∀ time, time < horizon →
    IsεQuittingRootNash reward (cap (time + 1)) 0 (roots time)

namespace QuittingCapSeededPrefix

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Exact affine transport of the cap/value difference through every
subword of a cap-seeded prefix. -/
theorem cap_sub_value_eq_jointSurvivalWeight_mul
    (splice : QuittingCapSeededPrefix reward) (who : ι) :
    ∀ start fuel, start + fuel ≤ splice.horizon →
      splice.cap start who - splice.value start who =
        quittingJointSurvivalWeight splice.roots start fuel *
          (splice.cap (start + fuel) who -
            splice.value (start + fuel) who) := by
  intro start fuel hwindow
  induction fuel generalizing start with
  | zero =>
      simp [quittingJointSurvivalWeight,
        quittingFiniteContinueWeight]
  | succ fuel ih =>
      have hstart : start < splice.horizon := by omega
      have htail : start + 1 + fuel ≤ splice.horizon := by omega
      have hindex : start + (fuel + 1) = start + 1 + fuel := by omega
      rw [hindex]
      have hstep := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
        reward (splice.cap (start + 1)) (splice.value (start + 1))
          (splice.roots start) who
      rw [← congrFun (splice.cap_policy start hstart) who,
        ← congrFun (splice.value_policy start hstart) who] at hstep
      rw [hstep, ih (start + 1) htail]
      rw [show fuel + 1 = 1 + fuel by omega,
        quittingJointSurvivalWeight_add]
      have hone : quittingJointSurvivalWeight splice.roots start 1 =
          quittingStationaryContinueMass (splice.roots start) := by
        rw [quittingJointSurvivalWeight_eq_prod]
        simp
      rw [hone]
      ring

/-- Full-prefix form of exact cap/value transport. -/
theorem cap_sub_value_eq_jointSurvivalWeight_mul_terminal
    (splice : QuittingCapSeededPrefix reward) (who : ι) :
    splice.cap 0 who - splice.value 0 who =
      quittingJointSurvivalWeight splice.roots 0 splice.horizon *
        (splice.cap splice.horizon who -
          splice.value splice.horizon who) := by
  simpa using splice.cap_sub_value_eq_jointSurvivalWeight_mul
    who 0 splice.horizon (by omega)

/-- The exact Nash cap evaluation equals the literal finite Bellman stopping
maximum with the terminal suffix cap installed at the end of the word. -/
theorem finiteTerminalBestResponseValue_eq_cap
    (splice : QuittingCapSeededPrefix reward) (who : ι) :
    ∀ start fuel, start + fuel ≤ splice.horizon →
      quittingFiniteTerminalBestResponseValue reward splice.roots who
          (splice.cap (start + fuel) who) start fuel =
        splice.cap start who := by
  intro start fuel hwindow
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      have hstart : start < splice.horizon := by omega
      have htail : start + 1 + fuel ≤ splice.horizon := by omega
      have hindex : start + (fuel + 1) = start + 1 + fuel := by omega
      rw [quittingFiniteTerminalBestResponseValue, hindex,
        ih (start + 1) htail]
      have hnash := splice.exactNash start hstart
      have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
        reward (splice.cap (start + 1)) (splice.roots start) who hnash
      have hcontinue := quittingRootContinuePayoff_le_successor_of_isZeroNash
        reward (splice.cap (start + 1)) (splice.roots start) who hnash
      rw [← congrFun (splice.cap_policy start hstart) who] at hquit hcontinue
      have hupper :
          max (quittingFixedOpponentsQuitValue reward splice.roots who start)
              (quittingFixedOpponentsContinueReward reward splice.roots who start +
                quittingFixedOpponentsContinueMass splice.roots who start *
                  splice.cap (start + 1) who) ≤
            splice.cap start who := by
        apply max_le
        · rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
            reward splice.roots who (splice.cap (start + 1)) start]
          exact hquit
        · rw [← quittingRootContinuePayoff_eq_fixedOpponents
            reward splice.roots who (splice.cap (start + 1)) start]
          exact hcontinue
      have hlower : splice.cap start who ≤
          max (quittingFixedOpponentsQuitValue reward splice.roots who start)
            (quittingFixedOpponentsContinueReward reward splice.roots who start +
              quittingFixedOpponentsContinueMass splice.roots who start *
                splice.cap (start + 1) who) := by
        rw [splice.cap_policy start hstart]
        exact quittingRootSuccessorPayoff_le_liveBellmanValue reward
          splice.roots who (fun time => splice.cap time who) start
      exact le_antisymm hupper hlower

/-- Full-prefix form of the literal finite unilateral-cap identity. -/
theorem finiteTerminalBestResponseValue_eq_initialCap
    (splice : QuittingCapSeededPrefix reward) (who : ι) :
    quittingFiniteTerminalBestResponseValue reward splice.roots who
        (splice.cap splice.horizon who) 0 splice.horizon =
      splice.cap 0 who := by
  simpa using splice.finiteTerminalBestResponseValue_eq_cap
    who 0 splice.horizon (by omega)

/-- If one actual behavior profile realizes the honest initial value and the
computed initial cap, a terminal exploitability gap is carried by one
coordinate of the exact joint-survival-scaled terminal cap difference. -/
theorem exists_terminalGap_le_jointSurvivalWeight_mul_terminalDifference
    (splice : QuittingCapSeededPrefix reward)
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame reward).BehaviorProfile)
    (hvalue : quittingTerminalPayoff reward profile = splice.value 0)
    (hcap : ∀ who,
      quittingBestReplyValue reward profile who = splice.cap 0 who) :
    ∃ who,
      gap ≤ quittingJointSurvivalWeight splice.roots 0 splice.horizon *
        (splice.cap splice.horizon who -
          splice.value splice.horizon who) := by
  obtain ⟨who, deviation, hgain⟩ := hexploit profile
  have hbest := le_quittingBestReplyValue reward profile who deviation
  have hgap : gap ≤ splice.cap 0 who - splice.value 0 who := by
    rw [← hcap who, ← congrFun hvalue who]
    linarith
  rw [splice.cap_sub_value_eq_jointSurvivalWeight_mul_terminal who] at hgap
  exact ⟨who, hgap⟩

/-- Division-free quantitative form: if every terminal cap difference is at
most `capBound`, a realized terminal gap is at most joint survival times that
common bound. -/
theorem terminalGap_le_jointSurvivalWeight_mul_capBound
    (splice : QuittingCapSeededPrefix reward)
    {gap capBound : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame reward).BehaviorProfile)
    (hvalue : quittingTerminalPayoff reward profile = splice.value 0)
    (hcap : ∀ who,
      quittingBestReplyValue reward profile who = splice.cap 0 who)
    (hterminalBound : ∀ who,
      splice.cap splice.horizon who -
        splice.value splice.horizon who ≤ capBound) :
    gap ≤ quittingJointSurvivalWeight splice.roots 0 splice.horizon *
      capBound := by
  obtain ⟨who, hgap⟩ :=
    splice.exists_terminalGap_le_jointSurvivalWeight_mul_terminalDifference
      hexploit profile hvalue hcap
  exact hgap.trans (mul_le_mul_of_nonneg_left (hterminalBound who)
    (quittingJointSurvivalWeight_nonneg splice.roots 0 splice.horizon))

end QuittingCapSeededPrefix

/-! ## Logarithmic charge accounting -/

omit [DecidableEq ι] in
/-- Positive finite joint survival bounds cumulative absorption charge by its
negative logarithm.  This is the exact logarithmic accounting used after a
division-free lower bound on survival has been established. -/
theorem sum_quittingRootAbsorptionMass_le_neg_log_jointSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (start fuel : ℕ)
    (hsurvival : 0 < quittingJointSurvivalWeight roots start fuel) :
    (∑ offset ∈ Finset.range fuel,
        quittingRootAbsorptionMass (roots (start + offset))) ≤
      -Real.log (quittingJointSurvivalWeight roots start fuel) := by
  rw [quittingJointSurvivalWeight_eq_prod] at hsurvival ⊢
  have hfactor : ∀ offset ∈ Finset.range fuel,
      0 < quittingStationaryContinueMass (roots (start + offset)) := by
    intro offset hoffset
    apply lt_of_le_of_ne
      (quittingStationaryContinueMass_nonneg _)
    intro hzero
    have : (∏ index ∈ Finset.range fuel,
        quittingStationaryContinueMass (roots (start + index))) = 0 := by
      exact Finset.prod_eq_zero hoffset hzero.symm
    linarith
  have hpoint : ∀ offset ∈ Finset.range fuel,
      quittingRootAbsorptionMass (roots (start + offset)) ≤
        -Real.log (quittingStationaryContinueMass
          (roots (start + offset))) := by
    intro offset hoffset
    rw [quittingRootAbsorptionMass]
    have hlog := Real.log_le_sub_one_of_pos (hfactor offset hoffset)
    linarith
  calc
    (∑ offset ∈ Finset.range fuel,
        quittingRootAbsorptionMass (roots (start + offset))) ≤
      ∑ offset ∈ Finset.range fuel,
        -Real.log (quittingStationaryContinueMass
          (roots (start + offset))) :=
        Finset.sum_le_sum fun offset hoffset => hpoint offset hoffset
    _ = -Real.log (∏ offset ∈ Finset.range fuel,
        quittingStationaryContinueMass (roots (start + offset))) := by
      rw [Real.log_prod (fun offset hoffset =>
        (hfactor offset hoffset).ne')]
      simp

namespace QuittingCapSeededPrefix

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A positive realized terminal gap and a positive common terminal cap bound
give the advertised dimensionless logarithmic charge ceiling. -/
theorem sum_absorptionMass_le_log_capBound_div_terminalGap
    (splice : QuittingCapSeededPrefix reward)
    {gap capBound : ℝ} (hgap_pos : 0 < gap) (hcapBound_pos : 0 < capBound)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame reward).BehaviorProfile)
    (hvalue : quittingTerminalPayoff reward profile = splice.value 0)
    (hcap : ∀ who,
      quittingBestReplyValue reward profile who = splice.cap 0 who)
    (hterminalBound : ∀ who,
      splice.cap splice.horizon who -
        splice.value splice.horizon who ≤ capBound) :
    (∑ time ∈ Finset.range splice.horizon,
        quittingRootAbsorptionMass (splice.roots time)) ≤
      Real.log (capBound / gap) := by
  have hgapBound := splice.terminalGap_le_jointSurvivalWeight_mul_capBound
    hexploit profile hvalue hcap hterminalBound
  let survival :=
    quittingJointSurvivalWeight splice.roots 0 splice.horizon
  have hsurvival_pos : 0 < survival := by
    by_contra hnot
    have hsurvival_nonpos : survival ≤ 0 := le_of_not_gt hnot
    have hproduct_nonpos : survival * capBound ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hsurvival_nonpos hcapBound_pos.le
    dsimp only [survival] at hproduct_nonpos
    linarith
  have hcharge :=
    sum_quittingRootAbsorptionMass_le_neg_log_jointSurvivalWeight
      splice.roots 0 splice.horizon (by simpa [survival] using hsurvival_pos)
  have hratio : gap / capBound ≤ survival := by
    apply (div_le_iff₀ hcapBound_pos).2
    simpa [survival, mul_comm] using hgapBound
  have hlog := Real.log_le_log (div_pos hgap_pos hcapBound_pos) hratio
  have hlogBound : -Real.log survival ≤ Real.log (capBound / gap) := by
    rw [Real.log_div hcapBound_pos.ne' hgap_pos.ne']
    rw [Real.log_div hgap_pos.ne' hcapBound_pos.ne'] at hlog
    linarith
  simpa [survival] using hcharge.trans hlogBound

end QuittingCapSeededPrefix

end GameTheory
