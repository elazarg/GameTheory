/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseClosure

/-!
# A fixed inactive outsider in the diffuse defect branch

The scalar diffuse rescaled-Quit defect is a finite-player sum.  Its
persistent positivity therefore has a fixed player subbranch.  The active
singleton-tight estimate makes that player eventually source-inactive.  The
same finite mesh estimate identifies the limiting obstruction more sharply:
at the selected dates the conditioned value lies uniformly below the player's
singleton payoff.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

/-! The fixed-player conclusion, with the singleton/conditioned-value
    consequence retained at the same selected dates. -/
theorem exists_fixed_inactive_rescaledQuitDefect_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ who : ι, ∃ eta : ℝ, 0 < eta ∧ ∀ start, ∃ time, start ≤ time ∧
      quittingDynamicDebtTailRoots seam.tail time who = PMF.pure false ∧
      eta ≤ max 0
        (quittingStationaryFixedOpponentsQuitValue reward
            (quittingTailDiffuseRescaledRoot
              (quittingDynamicDebtTailRoots seam.tail) time
              (hpositive time)) who -
          quittingTailConditionedValue
            (quittingDynamicDebtTailRoots seam.tail)
            (fun date => (seam.tail date).1.1) seam.limit.value time who) ∧
      quittingTailConditionedValue
          (quittingDynamicDebtTailRoots seam.tail)
          (fun date => (seam.tail date).1.1) seam.limit.value time who ≤
        reward (quittingSingletonTerminal who) who - eta := by
  let roots := quittingDynamicDebtTailRoots seam.tail
  let value : ℕ → Payoff ι := fun time => (seam.tail time).1.1
  let boundary := seam.limit.value
  let alpha : ℕ → ℝ := fun time ↦
    quittingTailConditionedAbsorptionWeight roots time
  let quitValue : ℕ → ι → ℝ := fun time who ↦
    quittingStationaryFixedOpponentsQuitValue reward
      (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who
  let conditionedValue : ℕ → ι → ℝ := fun time who ↦
    quittingTailConditionedValue roots value boundary time who
  let defect : ℕ → ι → ℝ := fun time who ↦
    max 0 (quitValue time who - conditionedValue time who)
  letI : Nonempty ι := regime.nonempty_players
  have hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time) := by
    intro time
    exact (seam.tail_edge time).1.1
  have hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time) := by
    intro time
    simpa only [value, roots, quittingDynamicDebtTailRoots] using
      (seam.tail_edge time).1.2
  have hbound : 0 ≤ quittingRewardBound reward :=
    quittingRewardBound_nonneg reward
  have hreward : ∀ terminal player, |reward terminal player| ≤
      quittingRewardBound reward :=
    abs_reward_le_quittingRewardBound reward
  have hactiveTight : ∀ᶠ time : ℕ in atTop, ∀ who,
      roots time who ≠ PMF.pure false →
        boundary who = quittingSoloBaseline reward who := by
    simpa only [roots, boundary] using
      seam.eventually_active_implies_limitValue_eq_singleton
  have hscaled : Tendsto (fun time =>
      (Fintype.card ι : ℝ) * alpha time) atTop (nhds 0) := by
    simpa [alpha, roots] using hmesh.const_mul (Fintype.card ι : ℝ)
  have halpha : ∀ time, 0 ≤ alpha time := by
    intro time
    exact quittingTailConditionedAbsorptionWeight_nonneg roots time
      (hpositive time)
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have herror : Tendsto (fun time =>
      6 * quittingRewardBound reward *
        ((Fintype.card ι : ℝ) * alpha time)) atTop (nhds 0) := by
    simpa [mul_assoc] using hscaled.const_mul
      (6 * quittingRewardBound reward)
  have hclose : Tendsto (fun time =>
      2 * quittingRewardBound reward *
        ((Fintype.card ι : ℝ) * alpha time)) atTop (nhds 0) := by
    simpa [mul_assoc] using hscaled.const_mul
      (2 * quittingRewardBound reward)
  obtain ⟨eta₀, heta₀, hpersistent⟩ :=
    seam.exists_persistent_rescaledQuitDefect_of_diffuse hpositive hmesh
  let eta : ℝ := eta₀ / (2 * (Fintype.card ι : ℝ))
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have htwice : 2 * eta = eta₀ / (Fintype.card ι : ℝ) := by
    dsimp [eta]
    field_simp
  have hsmall : ∀ᶠ time : ℕ in atTop,
      (Fintype.card ι : ℝ) * alpha time ≤ 1 := by
    have hlt : ∀ᶠ time : ℕ in atTop,
        (Fintype.card ι : ℝ) * alpha time < 1 :=
      (tendsto_order.1 hscaled).2 1 zero_lt_one
    exact hlt.mono fun time htime => htime.le
  have hactiveDefect : ∀ᶠ time : ℕ in atTop, ∀ who,
      roots time who ≠ PMF.pure false → defect time who < 2 * eta := by
    have herror' : ∀ᶠ time : ℕ in atTop,
        6 * quittingRewardBound reward *
            ((Fintype.card ι : ℝ) * alpha time) < 2 * eta := by
      have htarget : 0 < 2 * eta := by positivity
      exact (tendsto_order.1 herror).2 (2 * eta) htarget
    filter_upwards [hactiveTight, hsmall, herror'] with time htight hsmall herror' who hactive
    have hupper :=
      quittingStationaryFixedOpponentsQuitValue_rescaledRoot_le_conditionedValue_add_of_nash
        (reward := reward) roots value boundary hpolicy hnash time who
        hbound hreward (hpositive time) (htight who hactive) hsmall
    have hdefect : defect time who ≤
        6 * quittingRewardBound reward *
          ((Fintype.card ι : ℝ) * alpha time) := by
      unfold defect quitValue conditionedValue
      apply max_le
      · have hcardalpha : 0 ≤ (Fintype.card ι : ℝ) * alpha time :=
          mul_nonneg hcard.le (halpha time)
        exact mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 6 by norm_num)
          hbound) hcardalpha
      · dsimp [alpha]
        linarith [hupper]
    exact lt_of_le_of_lt hdefect herror'
  have hcloseEventually : ∀ᶠ time : ℕ in atTop, ∀ who,
      |quitValue time who - reward (quittingSingletonTerminal who) who| < eta := by
    have hclose' : ∀ᶠ time : ℕ in atTop,
        2 * quittingRewardBound reward *
            ((Fintype.card ι : ℝ) * alpha time) < eta := by
      exact (tendsto_order.1 hclose).2 eta heta
    filter_upwards [hclose'] with time htime who
    have hopponent :=
      quittingTailDiffuseRescaledRoot_opponentAbsorption_le_card_mul_weight
        roots time who (hpositive time)
    have habs :=
      abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
        (reward := reward)
        (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who
        hbound hreward
    have hmajor :
        2 * quittingRewardBound reward *
            quittingRootOpponentAbsorptionMass
              (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who < eta := by
      calc
        2 * quittingRewardBound reward *
              quittingRootOpponentAbsorptionMass
                (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who ≤
            2 * quittingRewardBound reward *
              ((Fintype.card ι : ℝ) * alpha time) := by
          apply mul_le_mul_of_nonneg_left hopponent
          positivity
        _ < eta := htime
    exact lt_of_le_of_lt habs hmajor
  obtain ⟨activeCutoff, hactiveCutoff⟩ :=
    Filter.eventually_atTop.1 hactiveDefect
  obtain ⟨closeCutoff, hcloseCutoff⟩ :=
    Filter.eventually_atTop.1 hcloseEventually
  let cutoff := max activeCutoff closeCutoff
  have hpair : ∀ start : ℕ, ∃ pair : ℕ × ι,
      max start cutoff ≤ pair.1 ∧ 2 * eta ≤ defect pair.1 pair.2 := by
    intro start
    obtain ⟨time, htime, hdefectSum⟩ := hpersistent (max start cutoff)
    have hsumLower : eta₀ ≤ ∑ who, defect time who := by
      simpa [defect, quitValue, conditionedValue,
        quittingConditionedRescaledQuitDefect] using hdefectSum
    have hplayer : ∃ who, 2 * eta ≤ defect time who := by
      by_contra hnone
      push Not at hnone
      have hlt : ∀ who, defect time who < 2 * eta := by
        intro who
        exact hnone who
      have hsum : ∑ who, defect time who <
          ∑ who : ι, (2 * eta) := by
        apply Finset.sum_lt_sum
        · intro who _
          exact (hlt who).le
        · let who : ι := Classical.choice (inferInstance : Nonempty ι)
          exact ⟨who, Finset.mem_univ who, hlt who⟩
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
      have hupper : ∑ who, defect time who < eta₀ := by
        calc
          _ < (Fintype.card ι : ℝ) * (2 * eta) := hsum
          _ = eta₀ := by
            rw [htwice]
            field_simp
      linarith
    exact ⟨⟨time, Classical.choose hplayer⟩, htime,
      Classical.choose_spec hplayer⟩
  let selected : ℕ → ℕ × ι := fun start => Classical.choose (hpair start)
  have hselected : ∀ start,
      max start cutoff ≤ (selected start).1 ∧
        2 * eta ≤ defect (selected start).1 (selected start).2 := by
    intro start
    exact Classical.choose_spec (hpair start)
  let color : ℕ → ι := fun start => (selected start).2
  obtain ⟨who, hinfinite⟩ := Finite.exists_infinite_fiber color
  have hinfinite' : Set.Infinite {start : ℕ | color start = who} :=
    Set.infinite_coe_iff.1 hinfinite
  refine ⟨who, eta, heta, ?_⟩
  intro start
  obtain ⟨index, hindex, hindex_gt⟩ := hinfinite'.exists_gt start
  have hsel := hselected index
  have hcolor : (selected index).2 = who := hindex
  have htime : start ≤ (selected index).1 :=
    le_trans (Nat.le_of_lt hindex_gt) (le_trans (le_max_left _ _) hsel.1)
  have hcut : cutoff ≤ (selected index).1 :=
    le_trans (le_max_right _ _) hsel.1
  have hnotactive : roots (selected index).1 who = PMF.pure false := by
    by_contra hactive
    have hactiveCut : activeCutoff ≤ (selected index).1 :=
      le_trans (le_max_left _ _) hcut
    have hlt := hactiveCutoff (selected index).1 hactiveCut who hactive
    have hsel2 := hsel.2
    rw [hcolor] at hsel2
    change max 0 (quitValue (selected index).1 who -
      conditionedValue (selected index).1 who) < 2 * eta at hlt
    change 2 * eta ≤ max 0 (quitValue (selected index).1 who -
      conditionedValue (selected index).1 who) at hsel2
    linarith
  have hcloseCut : closeCutoff ≤ (selected index).1 :=
    le_trans (le_max_right _ _) hcut
  have hclose := hcloseCutoff (selected index).1 hcloseCut who
  have hselectedDefect : 2 * eta ≤ defect (selected index).1 who := by
    have h := hsel.2
    rw [hcolor] at h
    exact h
  have hdefect : eta ≤ defect (selected index).1 who := by
    linarith
  have hvalue : conditionedValue (selected index).1 who ≤
      reward (quittingSingletonTerminal who) who - eta := by
    have hdiff : 2 * eta ≤
        quitValue (selected index).1 who -
          conditionedValue (selected index).1 who := by
      have hselectedDefect' := hselectedDefect
      change 2 * eta ≤ max 0 (quitValue (selected index).1 who -
        conditionedValue (selected index).1 who) at hselectedDefect'
      have hnonneg : 0 ≤ quitValue (selected index).1 who -
          conditionedValue (selected index).1 who := by
        by_contra hnegative
        rw [max_eq_left (le_of_not_ge hnegative)] at hselectedDefect'
        linarith
      simpa [max_eq_right hnonneg] using hselectedDefect'
    have hquitClose : quitValue (selected index).1 who ≤
        reward (quittingSingletonTerminal who) who + eta := by
      have habs := abs_le.mp (le_of_lt hclose)
      linarith
    linarith
  exact ⟨(selected index).1, htime, hnotactive, hdefect, by
    simpa only [conditionedValue] using hvalue⟩

/-! The same fixed outsider also creates a literal endpoint gap.  The extra
    half-`eta` loss is only the deleted-clock Continue charge. -/
theorem exists_cofinal_fixed_inactive_rescaledEndpointGap_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ who : ι, ∃ eta : ℝ, 0 < eta ∧ ∀ start, ∃ time, start ≤ time ∧
      quittingDynamicDebtTailRoots seam.tail time who = PMF.pure false ∧
      eta ≤ max 0
        (quittingStationaryFixedOpponentsQuitValue reward
            (quittingTailDiffuseRescaledRoot
              (quittingDynamicDebtTailRoots seam.tail) time
              (hpositive time)) who -
          quittingTailConditionedValue
            (quittingDynamicDebtTailRoots seam.tail)
            (fun date => (seam.tail date).1.1) seam.limit.value time who) ∧
      eta / 2 ≤ quittingRootEndpointDifference reward
        (quittingTailConditionedValue
          (quittingDynamicDebtTailRoots seam.tail)
          (fun date => (seam.tail date).1.1) seam.limit.value (time + 1))
        (quittingTailDiffuseRescaledRoot
          (quittingDynamicDebtTailRoots seam.tail) time
          (hpositive time)) who := by
  obtain ⟨who, eta, heta, hdates⟩ :=
    seam.exists_fixed_inactive_rescaledQuitDefect_of_diffuse hpositive hmesh
  let roots := quittingDynamicDebtTailRoots seam.tail
  let value : ℕ → Payoff ι := fun time => (seam.tail time).1.1
  let boundary := seam.limit.value
  let alpha : ℕ → ℝ := fun time ↦
    quittingTailConditionedAbsorptionWeight roots time
  letI : Nonempty ι := regime.nonempty_players
  have hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time) := by
    intro time
    exact (seam.tail_edge time).1.1
  have hbound : 0 ≤ quittingRewardBound reward :=
    quittingRewardBound_nonneg reward
  have hreward : ∀ terminal player, |reward terminal player| ≤
      quittingRewardBound reward :=
    abs_reward_le_quittingRewardBound reward
  have hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤
        quittingRewardBound reward := by
    intro time player
    exact abs_quittingTailConditionedValue_le roots value boundary
      hpolicy hbound hreward seam.value_tendsto time (hpositive time) player
  have hscaled : Tendsto (fun time =>
      (Fintype.card ι : ℝ) * alpha time) atTop (nhds 0) := by
    simpa [alpha, roots] using hmesh.const_mul (Fintype.card ι : ℝ)
  have halpha : ∀ time, 0 ≤ alpha time := by
    intro time
    exact quittingTailConditionedAbsorptionWeight_nonneg roots time
      (hpositive time)
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsmallEventually : ∀ᶠ time : ℕ in atTop,
      (Fintype.card ι : ℝ) * alpha time ≤ 1 := by
    have hlt : ∀ᶠ time : ℕ in atTop,
        (Fintype.card ι : ℝ) * alpha time < 1 :=
      (tendsto_order.1 hscaled).2 1 zero_lt_one
    exact hlt.mono fun time htime => htime.le
  have hchargeEventually : ∀ᶠ time : ℕ in atTop,
      6 * quittingRewardBound reward *
          ((Fintype.card ι : ℝ) * alpha time) < eta / 2 := by
    have hchargeTendsto : Tendsto (fun time =>
        6 * quittingRewardBound reward *
          ((Fintype.card ι : ℝ) * alpha time)) atTop (nhds 0) := by
      simpa [mul_assoc] using hscaled.const_mul
        (6 * quittingRewardBound reward)
    exact (tendsto_order.1 hchargeTendsto).2 (eta / 2) (by positivity)
  obtain ⟨smallCutoff, hsmallCutoff⟩ :=
    Filter.eventually_atTop.1 hsmallEventually
  obtain ⟨chargeCutoff, hchargeCutoff⟩ :=
    Filter.eventually_atTop.1 hchargeEventually
  let cutoff := max smallCutoff chargeCutoff
  refine ⟨who, eta, heta, ?_⟩
  intro start
  obtain ⟨time, htime, hinactive, hdefect, _⟩ :=
    hdates (max start cutoff)
  have hcut : cutoff ≤ time :=
    le_trans (le_max_right _ _) htime
  have hsmall : (Fintype.card ι : ℝ) * alpha time ≤ 1 :=
    hsmallCutoff time (le_trans (le_max_left _ _) hcut)
  have hchargeSmall : 6 * quittingRewardBound reward *
      ((Fintype.card ι : ℝ) * alpha time) < eta / 2 :=
    hchargeCutoff time (le_trans (le_max_right _ _) hcut)
  let targetRoot := quittingTailDiffuseRescaledRoot roots time
    (hpositive time)
  let next : Payoff ι := quittingTailConditionedValue roots value boundary
    (time + 1)
  have hcontinue :=
    rescaledContinuePayoff_le_conditionedValue_add_jointCharge_of_source_pure_false
      (reward := reward) (M := quittingRewardBound reward) (rho := alpha time)
      roots value boundary hpolicy hbound hreward hconditionedBound time who
      (hpositive time) (hpositive (time + 1)) hinactive (le_rfl) hsmall
  have htargetInactive : targetRoot who = PMF.pure false :=
    quittingTailDiffuseRescaledRoot_eq_pure_false_of_source_eq_pure_false
      roots time who (hpositive time) hinactive
  have hquit : quittingRootQuitPayoff reward next targetRoot who =
      quittingStationaryFixedOpponentsQuitValue reward targetRoot who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
        (fun _ => targetRoot) who next 0)
  have hcontinuePayoff : quittingRootContinuePayoff reward next targetRoot who =
      quittingStationaryFixedOpponentsContinueReward reward targetRoot who +
        quittingStationaryFixedOpponentsContinueMass targetRoot who * next who := by
    simpa [quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
      (quittingRootContinuePayoff_eq_fixedOpponents
        reward (fun _ => targetRoot) who next 0)
  have hendpoint : quittingRootEndpointDifference reward next targetRoot who =
      quittingStationaryFixedOpponentsQuitValue reward targetRoot who -
        (quittingStationaryFixedOpponentsContinueReward reward targetRoot who +
          quittingStationaryFixedOpponentsContinueMass targetRoot who * next who) := by
    unfold quittingRootEndpointDifference
    rw [hquit, hcontinuePayoff]
  have hdiff : eta ≤
      quittingStationaryFixedOpponentsQuitValue reward targetRoot who -
        quittingTailConditionedValue roots value boundary time who := by
    change eta ≤ max 0
      (quittingStationaryFixedOpponentsQuitValue reward targetRoot who -
        quittingTailConditionedValue roots value boundary time who) at hdefect
    have hnonneg : 0 ≤
        quittingStationaryFixedOpponentsQuitValue reward targetRoot who -
          quittingTailConditionedValue roots value boundary time who := by
      by_contra hnegative
      rw [max_eq_left (le_of_not_ge hnegative)] at hdefect
      linarith
    rw [max_eq_right hnonneg] at hdefect
    exact hdefect
  have hmassle : quittingRootOpponentAbsorptionMass targetRoot who ≤ 1 := by
    unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_nonneg
      (Function.update targetRoot who (PMF.pure false))]
  have hcoeff : 0 ≤ 6 * quittingRewardBound reward *
      ((Fintype.card ι : ℝ) * alpha time) := by
    exact mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 6 by norm_num) hbound)
      (mul_nonneg hcard.le (halpha time))
  have hcharge :
      (6 * quittingRewardBound reward *
        ((Fintype.card ι : ℝ) * alpha time)) *
          quittingRootOpponentAbsorptionMass targetRoot who ≤ eta / 2 := by
    calc
      _ ≤ 6 * quittingRewardBound reward *
          ((Fintype.card ι : ℝ) * alpha time) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hmassle hcoeff)
      _ ≤ eta / 2 := hchargeSmall.le
  have hendpointLower : eta / 2 ≤
      quittingRootEndpointDifference reward next targetRoot who := by
    rw [hendpoint]
    linarith
  exact ⟨time, le_trans (le_max_left _ _) htime, hinactive, hdefect, by
    simpa only [roots, value, boundary, targetRoot, next] using hendpointLower⟩

end QuittingCounterexampleSeamWitness

end GameTheory
