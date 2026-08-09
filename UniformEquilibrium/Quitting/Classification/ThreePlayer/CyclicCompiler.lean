/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the LICENSE file.
-/

import UniformEquilibrium.Quitting.Cycles.SingletonArcCycle

/-!
# Explicit three-player cyclic singleton compiler

This is the finite algebraic consumer for the strict cyclic branch. The rates
below solve the three projective cyclic equations; their denominators reflect
the three distinct equations rather than a formal cyclic copy. The stochastic
part is delegated to the singleton-arc compiler.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math Math.Probability Math.PMFProduct

abbrev CyclicThreePlayer := Fin 3

abbrev QuittingReward3 :=
  {S : Finset CyclicThreePlayer // S.Nonempty} → Payoff CyclicThreePlayer

/-! ## Right-cyclic data -/

structure RightSingletonCycle (reward : QuittingReward3) where
  h01 : quittingSoloReward reward 1 0 < quittingSoloReward reward 0 0
  h02 : quittingSoloReward reward 0 0 < quittingSoloReward reward 2 0
  h21 : quittingSoloReward reward 2 1 < quittingSoloReward reward 1 1
  h10 : quittingSoloReward reward 1 1 < quittingSoloReward reward 0 1
  h02' : quittingSoloReward reward 0 2 < quittingSoloReward reward 2 2
  h12 : quittingSoloReward reward 2 2 < quittingSoloReward reward 1 2
  hdet :
    (quittingSoloReward reward 2 0 - quittingSoloReward reward 0 0) *
        (quittingSoloReward reward 0 1 - quittingSoloReward reward 1 1) *
        (quittingSoloReward reward 1 2 - quittingSoloReward reward 2 2) >
      (quittingSoloReward reward 0 0 - quittingSoloReward reward 1 0) *
        (quittingSoloReward reward 1 1 - quittingSoloReward reward 2 1) *
        (quittingSoloReward reward 2 2 - quittingSoloReward reward 0 2)

def rightP (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 0 0 - quittingSoloReward reward 1 0

def rightQ (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 2 0 - quittingSoloReward reward 0 0

def rightR (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 1 1 - quittingSoloReward reward 2 1

def rightS (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 0 1 - quittingSoloReward reward 1 1

def rightT (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 2 2 - quittingSoloReward reward 0 2

def rightU (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 1 2 - quittingSoloReward reward 2 2

def rightDelta (reward : QuittingReward3) : ℝ :=
  rightQ reward * rightS reward * rightU reward -
    rightP reward * rightR reward * rightT reward

def rightAlpha (reward : QuittingReward3) : ℝ :=
  rightDelta reward /
    (rightQ reward * rightS reward * rightU reward +
      rightQ reward * rightS reward * rightT reward +
      rightP reward * rightS reward * rightT reward)

def rightBeta (reward : QuittingReward3) : ℝ :=
  rightDelta reward /
    (rightQ reward * rightS reward * rightU reward +
      rightP reward * rightS reward * rightU reward +
      rightP reward * rightR reward * rightU reward)

def rightGamma (reward : QuittingReward3) : ℝ :=
  rightDelta reward /
    (rightQ reward * rightS reward * rightU reward +
      rightQ reward * rightR reward * rightU reward +
      rightQ reward * rightR reward * rightT reward)

theorem right_gaps_pos {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    0 < rightP reward ∧ 0 < rightQ reward ∧ 0 < rightR reward ∧
      0 < rightS reward ∧ 0 < rightT reward ∧ 0 < rightU reward := by
  unfold rightP rightQ rightR rightS rightT rightU
  constructor
  · linarith [d.h01]
  constructor
  · linarith [d.h02]
  constructor
  · linarith [d.h21]
  constructor
  · linarith [d.h10]
  constructor
  · linarith [d.h02']
  · linarith [d.h12]

theorem right_delta_pos {reward : QuittingReward3}
    (d : RightSingletonCycle reward) : 0 < rightDelta reward := by
  have hdet : rightQ reward * rightS reward * rightU reward >
      rightP reward * rightR reward * rightT reward := by
    simpa [rightP, rightQ, rightR, rightS, rightT, rightU] using d.hdet
  exact sub_pos.mpr hdet

private theorem right_alpha_den_pos {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    0 < rightQ reward * rightS reward * rightU reward +
      rightQ reward * rightS reward * rightT reward +
      rightP reward * rightS reward * rightT reward := by
  rcases right_gaps_pos d with ⟨hp, hq, hr, hs, ht, hu⟩
  positivity

private theorem right_beta_den_pos {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    0 < rightQ reward * rightS reward * rightU reward +
      rightP reward * rightS reward * rightU reward +
      rightP reward * rightR reward * rightU reward := by
  rcases right_gaps_pos d with ⟨hp, hq, hr, hs, ht, hu⟩
  positivity

private theorem right_gamma_den_pos {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    0 < rightQ reward * rightS reward * rightU reward +
      rightQ reward * rightR reward * rightU reward +
      rightQ reward * rightR reward * rightT reward := by
  rcases right_gaps_pos d with ⟨hp, hq, hr, hs, ht, hu⟩
  positivity

theorem right_rates_pos {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    0 < rightAlpha reward ∧ 0 < rightBeta reward ∧ 0 < rightGamma reward := by
  unfold rightAlpha rightBeta rightGamma
  refine ⟨div_pos (right_delta_pos d) (right_alpha_den_pos d),
    div_pos (right_delta_pos d) (right_beta_den_pos d),
    div_pos (right_delta_pos d) (right_gamma_den_pos d)⟩

theorem right_rates_lt_one {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    rightAlpha reward < 1 ∧ rightBeta reward < 1 ∧ rightGamma reward < 1 := by
  rcases right_gaps_pos d with ⟨hp, hq, hr, hs, ht, hu⟩
  have hd := right_delta_pos d
  have ha := right_alpha_den_pos d
  have hb := right_beta_den_pos d
  have hg := right_gamma_den_pos d
  have hda : rightDelta reward <
      rightQ reward * rightS reward * rightU reward +
        rightQ reward * rightS reward * rightT reward +
        rightP reward * rightS reward * rightT reward := by
    unfold rightDelta
    have : 0 < rightQ reward * rightS reward * rightT reward +
        rightP reward * rightS reward * rightT reward +
        rightP reward * rightR reward * rightT reward := by positivity
    nlinarith
  have hdb : rightDelta reward <
      rightQ reward * rightS reward * rightU reward +
        rightP reward * rightS reward * rightU reward +
        rightP reward * rightR reward * rightU reward := by
    unfold rightDelta
    have : 0 < rightP reward * rightS reward * rightU reward +
        rightP reward * rightR reward * rightU reward +
        rightP reward * rightR reward * rightT reward := by positivity
    nlinarith
  have hdg : rightDelta reward <
      rightQ reward * rightS reward * rightU reward +
        rightQ reward * rightR reward * rightU reward +
        rightQ reward * rightR reward * rightT reward := by
    unfold rightDelta
    have : 0 < rightQ reward * rightR reward * rightU reward +
        rightQ reward * rightR reward * rightT reward +
        rightP reward * rightR reward * rightT reward := by positivity
    nlinarith
  unfold rightAlpha rightBeta rightGamma
  constructor
  · apply (div_lt_iff₀ ha).2
    simpa only [one_mul] using hda
  constructor
  · apply (div_lt_iff₀ hb).2
    simpa only [one_mul] using hdb
  · apply (div_lt_iff₀ hg).2
    simpa only [one_mul] using hdg

/-! The three indifference identities. -/

theorem right_balance_one {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    rightBeta reward * rightP reward =
      (1 - rightBeta reward) * rightGamma reward * rightQ reward := by
  have ha := right_alpha_den_pos d
  have hb := right_beta_den_pos d
  have hg := right_gamma_den_pos d
  rw [rightBeta, rightGamma]
  let B := rightQ reward * rightS reward * rightU reward +
    rightP reward * rightS reward * rightU reward + rightP reward * rightR reward * rightU reward
  let C := rightQ reward * rightS reward * rightU reward +
    rightQ reward * rightR reward * rightU reward + rightQ reward * rightR reward * rightT reward
  have hB : B ≠ 0 := by dsimp [B]; exact ne_of_gt hb
  have hC : C ≠ 0 := by dsimp [C]; exact ne_of_gt hg
  change (rightDelta reward / B) * rightP reward =
    (1 - rightDelta reward / B) * (rightDelta reward / C) * rightQ reward
  simp only [rightDelta]
  field_simp [hB, hC]
  ring

theorem right_balance_two {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    rightGamma reward * rightR reward =
      (1 - rightGamma reward) * rightAlpha reward * rightS reward := by
  have ha := right_alpha_den_pos d
  have hb := right_beta_den_pos d
  have hg := right_gamma_den_pos d
  rw [rightGamma, rightAlpha]
  let A := rightQ reward * rightS reward * rightU reward +
    rightQ reward * rightS reward * rightT reward + rightP reward * rightS reward * rightT reward
  let C := rightQ reward * rightS reward * rightU reward +
    rightQ reward * rightR reward * rightU reward + rightQ reward * rightR reward * rightT reward
  have hA : A ≠ 0 := by dsimp [A]; exact ne_of_gt ha
  have hC : C ≠ 0 := by dsimp [C]; exact ne_of_gt hg
  change (rightDelta reward / C) * rightR reward =
    (1 - rightDelta reward / C) * (rightDelta reward / A) * rightS reward
  simp only [rightDelta]
  field_simp [hA, hC]
  ring

theorem right_balance_three {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    rightAlpha reward * rightT reward =
      (1 - rightAlpha reward) * rightBeta reward * rightU reward := by
  have ha := right_alpha_den_pos d
  have hb := right_beta_den_pos d
  have hg := right_gamma_den_pos d
  rw [rightAlpha, rightBeta]
  let A := rightQ reward * rightS reward * rightU reward +
    rightQ reward * rightS reward * rightT reward + rightP reward * rightS reward * rightT reward
  let B := rightQ reward * rightS reward * rightU reward +
    rightP reward * rightS reward * rightU reward + rightP reward * rightR reward * rightU reward
  have hA : A ≠ 0 := by dsimp [A]; exact ne_of_gt ha
  have hB : B ≠ 0 := by dsimp [B]; exact ne_of_gt hb
  change (rightDelta reward / A) * rightT reward =
    (1 - rightDelta reward / A) * (rightDelta reward / B) * rightU reward
  simp only [rightDelta]
  field_simp [hA, hB]
  ring

/-! ## Right coarse values and their arc certificate -/

def rightOwner : Fin 3 → Fin 3 := ![0, 1, 2]

def rightCoarse (reward : QuittingReward3) : Fin 3 → Payoff (Fin 3) :=
  ![
    ![quittingSoloReward reward 0 0,
      (1 - rightAlpha reward) * quittingSoloReward reward 1 1 +
        rightAlpha reward * quittingSoloReward reward 0 1,
      quittingSoloReward reward 2 2],
    ![quittingSoloReward reward 0 0, quittingSoloReward reward 1 1,
      (1 - rightBeta reward) * quittingSoloReward reward 2 2 +
        rightBeta reward * quittingSoloReward reward 1 2],
    ![(1 - rightGamma reward) * quittingSoloReward reward 0 0 +
        rightGamma reward * quittingSoloReward reward 2 0,
      quittingSoloReward reward 1 1, quittingSoloReward reward 2 2]
  ]

theorem right_coarse_active {reward : QuittingReward3}
    (_d : RightSingletonCycle reward) :
    ∀ block, rightCoarse reward block (rightOwner block) =
      quittingSoloReward reward (rightOwner block) (rightOwner block) := by
  intro block
  fin_cases block <;> simp [rightCoarse, rightOwner]

theorem right_coarse_arc {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    ∀ block, rightCoarse reward block =
      quittingSingletonArcPayoff
        (![rightAlpha reward, rightBeta reward, rightGamma reward] block)
        (quittingSoloReward reward (rightOwner block))
        (rightCoarse reward (finRotate 3 block)) := by
  have h1 := right_balance_one d
  have h2 := right_balance_two d
  have h3 := right_balance_three d
  simp only [rightP, rightQ, rightR, rightS, rightT, rightU] at h1 h2 h3
  intro block
  fin_cases block <;>
    funext who <;> fin_cases who <;>
    simp [rightCoarse, rightOwner, quittingSingletonArcPayoff] <;>
    ring_nf at h1 h2 h3 ⊢ <;>
    nlinarith

theorem right_coarse_floor {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    ∀ block who,
      quittingSoloReward reward who who ≤ rightCoarse reward block who := by
  rcases right_rates_pos d with ⟨ha, hb, hg⟩
  rcases right_rates_lt_one d with ⟨ha1, hb1, hg1⟩
  have h1 := right_balance_one d
  have h2 := right_balance_two d
  have h3 := right_balance_three d
  have haS : 0 < rightAlpha reward *
      (quittingSoloReward reward 0 1 - quittingSoloReward reward 1 1) :=
    mul_pos ha (sub_pos.mpr d.h10)
  have hbU : 0 < rightBeta reward *
      (quittingSoloReward reward 1 2 - quittingSoloReward reward 2 2) :=
    mul_pos hb (sub_pos.mpr d.h12)
  have hgQ : 0 < rightGamma reward *
      (quittingSoloReward reward 2 0 - quittingSoloReward reward 0 0) :=
    mul_pos hg (sub_pos.mpr d.h02)
  have h1' : rightBeta reward *
      (quittingSoloReward reward 0 0 - quittingSoloReward reward 1 0) =
      (1 - rightBeta reward) * rightGamma reward *
        (quittingSoloReward reward 2 0 - quittingSoloReward reward 0 0) := by
    simpa [rightP, rightQ] using h1
  have h2' : rightGamma reward *
      (quittingSoloReward reward 1 1 - quittingSoloReward reward 2 1) =
      (1 - rightGamma reward) * rightAlpha reward *
        (quittingSoloReward reward 0 1 - quittingSoloReward reward 1 1) := by
    simpa [rightR, rightS] using h2
  have h3' : rightAlpha reward *
      (quittingSoloReward reward 2 2 - quittingSoloReward reward 0 2) =
      (1 - rightAlpha reward) * rightBeta reward *
        (quittingSoloReward reward 1 2 - quittingSoloReward reward 2 2) := by
    simpa [rightT, rightU] using h3
  intro block who
  fin_cases block <;> fin_cases who
  case «0».«0» => simp [rightCoarse]
  case «0».«1» => simp [rightCoarse]; nlinarith [haS]
  case «0».«2» => simp [rightCoarse]
  case «1».«0» => simp [rightCoarse]
  case «1».«1» => simp [rightCoarse]
  case «1».«2» => simp [rightCoarse]; nlinarith [hbU]
  case «2».«0» => simp [rightCoarse]; nlinarith [hgQ]
  case «2».«1» => simp [rightCoarse]
  case «2».«2» => simp [rightCoarse]

/-! ## Generic collision and intensity bounds -/

def threePlayerCycleD (reward : QuittingReward3) : ℝ :=
  2 * quittingRewardBound reward

def threePlayerCycleAStar (p : Fin 3 → ℝ) : ℝ :=
  max (max (quittingMeshIntensity (p 0))
    (quittingMeshIntensity (p 1))) (quittingMeshIntensity (p 2))

theorem threePlayerCycleD_nonneg (reward : QuittingReward3) :
    0 ≤ threePlayerCycleD reward := by
  dsimp [threePlayerCycleD]
  exact mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)

theorem threePlayerCycle_collision_bound (reward : QuittingReward3)
    (owner other : Fin 3) (_hne : other ≠ owner) :
    max (quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other) 0 ≤ threePlayerCycleD reward := by
  have hbound := quittingRewardBound_nonneg reward
  have hcol := abs_reward_le_quittingRewardBound reward
    ⟨{owner, other}, by simp⟩ other
  have hsolo := abs_reward_le_quittingRewardBound reward
    ⟨{other}, by simp⟩ other
  have hdiff : quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other ≤ 2 * quittingRewardBound reward := by
    unfold quittingSingletonCollisionReward quittingSoloReward
    linarith [abs_le.mp hcol, abs_le.mp hsolo]
  apply max_le
  · exact hdiff
  · dsimp [threePlayerCycleD]
    linarith

theorem threePlayerCycle_intensity_bound {p : Fin 3 → ℝ} :
    ∀ block, quittingMeshIntensity (p block) ≤ threePlayerCycleAStar p := by
  intro block
  fin_cases block
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

theorem right_coarse_contracts {reward : QuittingReward3}
    (d : RightSingletonCycle reward) :
    ∀ who, (∏ block : Fin 3,
      if who = rightOwner block then 1 else
        1 - ![rightAlpha reward, rightBeta reward, rightGamma reward] block) < 1 := by
  rcases right_rates_pos d with ⟨ha, hb, hg⟩
  rcases right_rates_lt_one d with ⟨ha1, hb1, hg1⟩
  intro who
  fin_cases who <;>
    simp [rightOwner, Fin.prod_univ_succ] <;>
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - rightAlpha reward)
      (by linarith : 0 ≤ 1 - rightBeta reward),
      mul_nonneg (by linarith : 0 ≤ 1 - rightBeta reward)
        (by linarith : 0 ≤ 1 - rightGamma reward),
      mul_nonneg (by linarith : 0 ≤ 1 - rightAlpha reward)
        (by linarith : 0 ≤ 1 - rightGamma reward)]

/-- A strict right-oriented singleton cycle yields the displayed ordinary
uniform-equilibrium payoff through its exact singleton-arc realization. -/
theorem rightSingletonCycle_isUniformEquilibriumPayoff
    (reward : QuittingReward3) (d : RightSingletonCycle reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (rightCoarse reward 0) := by
  have hp0 : ∀ block, 0 ≤
      ![rightAlpha reward, rightBeta reward, rightGamma reward] block := by
    have hpos := right_rates_pos d
    intro block
    fin_cases block
    · exact le_of_lt hpos.1
    · exact le_of_lt hpos.2.1
    · exact le_of_lt hpos.2.2
  have hp1 : ∀ block, (![rightAlpha reward, rightBeta reward,
      rightGamma reward] block) < 1 := by
    intro block
    fin_cases block <;> simp [right_rates_lt_one d]
  have hD := threePlayerCycleD_nonneg reward
  have hA := threePlayerCycle_intensity_bound
    (p := ![rightAlpha reward, rightBeta reward, rightGamma reward])
  apply singletonArcCycle_isUniformEquilibriumPayoff
    reward rightOwner (![rightAlpha reward, rightBeta reward, rightGamma reward])
      (rightCoarse reward) 0
  · exact hp0
  · exact hp1
  · exact hA
  · exact hD
  · exact right_coarse_arc d
  · exact right_coarse_active d
  · exact right_coarse_floor d
  · intro block other hne
    exact threePlayerCycle_collision_bound reward (rightOwner block) other hne
  · exact right_coarse_contracts d

/-! ## Left cyclic data, obtained by the 2↔3 reversal -/

structure LeftSingletonCycle (reward : QuittingReward3) where
  h00 : quittingSoloReward reward 2 0 < quittingSoloReward reward 0 0
  h01 : quittingSoloReward reward 0 0 < quittingSoloReward reward 1 0
  h10 : quittingSoloReward reward 0 1 < quittingSoloReward reward 1 1
  h11 : quittingSoloReward reward 1 1 < quittingSoloReward reward 2 1
  h20 : quittingSoloReward reward 1 2 < quittingSoloReward reward 2 2
  h21 : quittingSoloReward reward 2 2 < quittingSoloReward reward 0 2
  hdet :
    (quittingSoloReward reward 1 0 - quittingSoloReward reward 0 0) *
        (quittingSoloReward reward 0 2 - quittingSoloReward reward 2 2) *
        (quittingSoloReward reward 2 1 - quittingSoloReward reward 1 1) >
      (quittingSoloReward reward 0 0 - quittingSoloReward reward 2 0) *
        (quittingSoloReward reward 2 2 - quittingSoloReward reward 1 2) *
        (quittingSoloReward reward 1 1 - quittingSoloReward reward 0 1)

def leftToRightReward (reward : QuittingReward3) : QuittingReward3 :=
  fun S i => reward S (![0, 2, 1] i)

def leftToRightPayoff (v : Payoff CyclicThreePlayer) : Payoff CyclicThreePlayer :=
  fun i => v (![0, 2, 1] i)

def leftP (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 0 0 - quittingSoloReward reward 2 0

def leftQ (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 1 0 - quittingSoloReward reward 0 0

def leftR (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 2 2 - quittingSoloReward reward 1 2

def leftS (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 0 2 - quittingSoloReward reward 2 2

def leftT (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 1 1 - quittingSoloReward reward 0 1

def leftU (reward : QuittingReward3) : ℝ :=
  quittingSoloReward reward 2 1 - quittingSoloReward reward 1 1

def leftDelta (reward : QuittingReward3) : ℝ :=
  leftQ reward * leftS reward * leftU reward -
    leftP reward * leftR reward * leftT reward

def leftAlpha (reward : QuittingReward3) : ℝ :=
  leftDelta reward /
    (leftQ reward * leftS reward * leftU reward +
      leftQ reward * leftS reward * leftT reward +
      leftP reward * leftS reward * leftT reward)

def leftBeta (reward : QuittingReward3) : ℝ :=
  leftDelta reward /
    (leftQ reward * leftS reward * leftU reward +
      leftP reward * leftS reward * leftU reward +
      leftP reward * leftR reward * leftU reward)

def leftGamma (reward : QuittingReward3) : ℝ :=
  leftDelta reward /
    (leftQ reward * leftS reward * leftU reward +
      leftQ reward * leftR reward * leftU reward +
      leftQ reward * leftR reward * leftT reward)

theorem left_gaps_pos {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    0 < leftP reward ∧ 0 < leftQ reward ∧ 0 < leftR reward ∧
      0 < leftS reward ∧ 0 < leftT reward ∧ 0 < leftU reward := by
  unfold leftP leftQ leftR leftS leftT leftU
  constructor
  · linarith [d.h00, d.h01]
  constructor
  · linarith [d.h01]
  constructor
  · linarith [d.h20]
  constructor
  · linarith [d.h21, d.h20]
  constructor
  · linarith [d.h10]
  · linarith [d.h11]

theorem left_delta_pos {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) : 0 < leftDelta reward := by
  have hdet : leftQ reward * leftS reward * leftU reward >
      leftP reward * leftR reward * leftT reward := by
    simpa [leftP, leftQ, leftR, leftS, leftT, leftU] using d.hdet
  exact sub_pos.mpr hdet

private theorem left_alpha_den_pos {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    0 < leftQ reward * leftS reward * leftU reward +
      leftQ reward * leftS reward * leftT reward +
      leftP reward * leftS reward * leftT reward := by
  rcases left_gaps_pos d with ⟨hp, hq, hr, hs, ht, hu⟩
  positivity

private theorem left_beta_den_pos {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    0 < leftQ reward * leftS reward * leftU reward +
      leftP reward * leftS reward * leftU reward +
      leftP reward * leftR reward * leftU reward := by
  rcases left_gaps_pos d with ⟨hp, hq, hr, hs, ht, hu⟩
  positivity

private theorem left_gamma_den_pos {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    0 < leftQ reward * leftS reward * leftU reward +
      leftQ reward * leftR reward * leftU reward +
      leftQ reward * leftR reward * leftT reward := by
  rcases left_gaps_pos d with ⟨hp, hq, hr, hs, ht, hu⟩
  positivity

theorem left_rates_pos {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    0 < leftAlpha reward ∧ 0 < leftBeta reward ∧ 0 < leftGamma reward := by
  unfold leftAlpha leftBeta leftGamma
  exact ⟨div_pos (left_delta_pos d) (left_alpha_den_pos d),
    div_pos (left_delta_pos d) (left_beta_den_pos d),
    div_pos (left_delta_pos d) (left_gamma_den_pos d)⟩

theorem left_rates_lt_one {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    leftAlpha reward < 1 ∧ leftBeta reward < 1 ∧ leftGamma reward < 1 := by
  rcases left_gaps_pos d with ⟨hp, hq, hr, hs, ht, hu⟩
  have ha := left_alpha_den_pos d
  have hb := left_beta_den_pos d
  have hg := left_gamma_den_pos d
  have hda : leftDelta reward <
      leftQ reward * leftS reward * leftU reward +
        leftQ reward * leftS reward * leftT reward +
        leftP reward * leftS reward * leftT reward := by
    unfold leftDelta
    have : 0 < leftQ reward * leftS reward * leftT reward +
        leftP reward * leftS reward * leftT reward +
        leftP reward * leftR reward * leftT reward := by positivity
    nlinarith
  have hdb : leftDelta reward <
      leftQ reward * leftS reward * leftU reward +
        leftP reward * leftS reward * leftU reward +
        leftP reward * leftR reward * leftU reward := by
    unfold leftDelta
    have : 0 < leftP reward * leftS reward * leftU reward +
        leftP reward * leftR reward * leftU reward +
        leftP reward * leftR reward * leftT reward := by positivity
    nlinarith
  have hdg : leftDelta reward <
      leftQ reward * leftS reward * leftU reward +
        leftQ reward * leftR reward * leftU reward +
        leftQ reward * leftR reward * leftT reward := by
    unfold leftDelta
    have : 0 < leftQ reward * leftR reward * leftU reward +
        leftQ reward * leftR reward * leftT reward +
        leftP reward * leftR reward * leftT reward := by positivity
    nlinarith
  unfold leftAlpha leftBeta leftGamma
  constructor
  · apply (div_lt_iff₀ ha).2
    simpa only [one_mul] using hda
  constructor
  · apply (div_lt_iff₀ hb).2
    simpa only [one_mul] using hdb
  · apply (div_lt_iff₀ hg).2
    simpa only [one_mul] using hdg

theorem left_balance_one {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    leftBeta reward * leftP reward =
      (1 - leftBeta reward) * leftGamma reward * leftQ reward := by
  have ha := left_alpha_den_pos d
  have hb := left_beta_den_pos d
  have hg := left_gamma_den_pos d
  rw [leftBeta, leftGamma]
  let B := leftQ reward * leftS reward * leftU reward +
    leftP reward * leftS reward * leftU reward + leftP reward * leftR reward * leftU reward
  let C := leftQ reward * leftS reward * leftU reward +
    leftQ reward * leftR reward * leftU reward + leftQ reward * leftR reward * leftT reward
  have hB : B ≠ 0 := by dsimp [B]; exact ne_of_gt hb
  have hC : C ≠ 0 := by dsimp [C]; exact ne_of_gt hg
  change (leftDelta reward / B) * leftP reward =
    (1 - leftDelta reward / B) * (leftDelta reward / C) * leftQ reward
  simp only [leftDelta]
  field_simp [hB, hC]
  ring

theorem left_balance_two {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    leftGamma reward * leftR reward =
      (1 - leftGamma reward) * leftAlpha reward * leftS reward := by
  have ha := left_alpha_den_pos d
  have hb := left_beta_den_pos d
  have hg := left_gamma_den_pos d
  rw [leftGamma, leftAlpha]
  let A := leftQ reward * leftS reward * leftU reward +
    leftQ reward * leftS reward * leftT reward + leftP reward * leftS reward * leftT reward
  let C := leftQ reward * leftS reward * leftU reward +
    leftQ reward * leftR reward * leftU reward + leftQ reward * leftR reward * leftT reward
  have hA : A ≠ 0 := by dsimp [A]; exact ne_of_gt ha
  have hC : C ≠ 0 := by dsimp [C]; exact ne_of_gt hg
  change (leftDelta reward / C) * leftR reward =
    (1 - leftDelta reward / C) * (leftDelta reward / A) * leftS reward
  simp only [leftDelta]
  field_simp [hA, hC]
  ring

theorem left_balance_three {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    leftAlpha reward * leftT reward =
      (1 - leftAlpha reward) * leftBeta reward * leftU reward := by
  have ha := left_alpha_den_pos d
  have hb := left_beta_den_pos d
  have hg := left_gamma_den_pos d
  rw [leftAlpha, leftBeta]
  let A := leftQ reward * leftS reward * leftU reward +
    leftQ reward * leftS reward * leftT reward + leftP reward * leftS reward * leftT reward
  let B := leftQ reward * leftS reward * leftU reward +
    leftP reward * leftS reward * leftU reward + leftP reward * leftR reward * leftU reward
  have hA : A ≠ 0 := by dsimp [A]; exact ne_of_gt ha
  have hB : B ≠ 0 := by dsimp [B]; exact ne_of_gt hb
  change (leftDelta reward / A) * leftT reward =
    (1 - leftDelta reward / A) * (leftDelta reward / B) * leftU reward
  simp only [leftDelta]
  field_simp [hA, hB]
  ring

def leftOwner : Fin 3 → Fin 3 := ![0, 2, 1]

def leftCoarse (reward : QuittingReward3) : Fin 3 → Payoff (Fin 3) :=
  ![
    ![quittingSoloReward reward 0 0,
      quittingSoloReward reward 1 1,
      (1 - leftAlpha reward) * quittingSoloReward reward 2 2 +
        leftAlpha reward * quittingSoloReward reward 0 2],
    ![quittingSoloReward reward 0 0,
      (1 - leftBeta reward) * quittingSoloReward reward 1 1 +
        leftBeta reward * quittingSoloReward reward 2 1,
      quittingSoloReward reward 2 2],
    ![(1 - leftGamma reward) * quittingSoloReward reward 0 0 +
        leftGamma reward * quittingSoloReward reward 1 0,
      quittingSoloReward reward 1 1,
      quittingSoloReward reward 2 2]
  ]

theorem left_coarse_active {reward : QuittingReward3}
    (_d : LeftSingletonCycle reward) :
    ∀ block, leftCoarse reward block (leftOwner block) =
      quittingSoloReward reward (leftOwner block) (leftOwner block) := by
  intro block
  fin_cases block <;> simp [leftCoarse, leftOwner]

theorem left_coarse_arc {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    ∀ block, leftCoarse reward block =
      quittingSingletonArcPayoff
        (![leftAlpha reward, leftBeta reward, leftGamma reward] block)
        (quittingSoloReward reward (leftOwner block))
        (leftCoarse reward (finRotate 3 block)) := by
  have h1 := left_balance_one d
  have h2 := left_balance_two d
  have h3 := left_balance_three d
  simp only [leftP, leftQ, leftR, leftS, leftT, leftU] at h1 h2 h3
  intro block
  fin_cases block <;>
    funext who <;> fin_cases who <;>
    simp [leftCoarse, leftOwner, quittingSingletonArcPayoff] <;>
    ring_nf at h1 h2 h3 ⊢ <;>
    nlinarith

theorem left_coarse_floor {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    ∀ block who,
      quittingSoloReward reward who who ≤ leftCoarse reward block who := by
  rcases left_rates_pos d with ⟨ha, hb, hg⟩
  have h1 := left_balance_one d
  have h2 := left_balance_two d
  have h3 := left_balance_three d
  have haS : 0 < leftAlpha reward *
      (quittingSoloReward reward 0 2 - quittingSoloReward reward 2 2) :=
    mul_pos ha (sub_pos.mpr d.h21)
  have hbU : 0 < leftBeta reward *
      (quittingSoloReward reward 2 1 - quittingSoloReward reward 1 1) :=
    mul_pos hb (sub_pos.mpr d.h11)
  have hgQ : 0 < leftGamma reward *
      (quittingSoloReward reward 1 0 - quittingSoloReward reward 0 0) :=
    mul_pos hg (sub_pos.mpr d.h01)
  have h1' : leftBeta reward *
      (quittingSoloReward reward 0 0 - quittingSoloReward reward 2 0) =
      (1 - leftBeta reward) * leftGamma reward *
        (quittingSoloReward reward 1 0 - quittingSoloReward reward 0 0) := by
    simpa [leftP, leftQ] using h1
  have h2' : leftGamma reward *
      (quittingSoloReward reward 2 2 - quittingSoloReward reward 1 2) =
      (1 - leftGamma reward) * leftAlpha reward *
        (quittingSoloReward reward 0 2 - quittingSoloReward reward 2 2) := by
    simpa [leftR, leftS] using h2
  have h3' : leftAlpha reward *
      (quittingSoloReward reward 1 1 - quittingSoloReward reward 0 1) =
      (1 - leftAlpha reward) * leftBeta reward *
        (quittingSoloReward reward 2 1 - quittingSoloReward reward 1 1) := by
    simpa [leftT, leftU] using h3
  intro block who
  fin_cases block <;> fin_cases who
  case «0».«0» => simp [leftCoarse]
  case «0».«1» => simp [leftCoarse]
  case «0».«2» => simp [leftCoarse]; nlinarith [haS]
  case «1».«0» => simp [leftCoarse]
  case «1».«1» => simp [leftCoarse]; nlinarith [hbU]
  case «1».«2» => simp [leftCoarse]
  case «2».«0» => simp [leftCoarse]; nlinarith [hgQ]
  case «2».«1» => simp [leftCoarse]
  case «2».«2» => simp [leftCoarse]

theorem left_coarse_contracts {reward : QuittingReward3}
    (d : LeftSingletonCycle reward) :
    ∀ who, (∏ block : Fin 3,
      if who = leftOwner block then 1 else
        1 - ![leftAlpha reward, leftBeta reward, leftGamma reward] block) < 1 := by
  rcases left_rates_pos d with ⟨ha, hb, hg⟩
  rcases left_rates_lt_one d with ⟨ha1, hb1, hg1⟩
  intro who
  fin_cases who <;>
    simp [leftOwner, Fin.prod_univ_succ] <;>
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - leftAlpha reward)
      (by linarith : 0 ≤ 1 - leftBeta reward),
      mul_nonneg (by linarith : 0 ≤ 1 - leftBeta reward)
        (by linarith : 0 ≤ 1 - leftGamma reward),
      mul_nonneg (by linarith : 0 ≤ 1 - leftAlpha reward)
        (by linarith : 0 ≤ 1 - leftGamma reward)]

/-- A strict left-oriented singleton cycle yields the displayed ordinary
uniform-equilibrium payoff through its exact singleton-arc realization. -/
theorem leftSingletonCycle_isUniformEquilibriumPayoff
    (reward : QuittingReward3) (d : LeftSingletonCycle reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (leftCoarse reward 0) := by
  have hp0 : ∀ block, 0 ≤
      ![leftAlpha reward, leftBeta reward, leftGamma reward] block := by
    have hpos := left_rates_pos d
    intro block
    fin_cases block
    · exact le_of_lt hpos.1
    · exact le_of_lt hpos.2.1
    · exact le_of_lt hpos.2.2
  have hp1 : ∀ block, (![leftAlpha reward, leftBeta reward,
      leftGamma reward] block) < 1 := by
    intro block
    fin_cases block <;> simp [left_rates_lt_one d]
  have hA := threePlayerCycle_intensity_bound
    (p := ![leftAlpha reward, leftBeta reward, leftGamma reward])
  apply singletonArcCycle_isUniformEquilibriumPayoff
    reward leftOwner (![leftAlpha reward, leftBeta reward, leftGamma reward])
      (leftCoarse reward) 0
  · exact hp0
  · exact hp1
  · exact hA
  · exact threePlayerCycleD_nonneg reward
  · exact left_coarse_arc d
  · exact left_coarse_active d
  · exact left_coarse_floor d
  · intro block other hne
    exact threePlayerCycle_collision_bound reward (leftOwner block) other hne
  · exact left_coarse_contracts d

end GameTheory
