/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Positive common-base transfers need not balance

The one-step stopping-law reset theorem starts at a minimum-debt profile,
decreases the mover's debt, and forces positive aggregate debt change on the
opposite player face.  Coordinatewise debt convexity additionally puts the
target below the chord joining the source and best-response endpoint.

Those facts alone do not produce a nonnegative debt circulation, even when
every named recipient already belongs to the positive-debt support and the
recipient labels form a directed cycle.  This file gives the finite
three-player regression.

The common source debt is `(1,1,1)`.  The three half-reset directions are

* `(-1/2, 1, 0)`;
* `(0, -1/2, 1)`;
* `(1, 0, -1/2)`.

Each is the exact midpoint direction toward a nonnegative endpoint which
kills the mover's debt.  Each ray has its strict minimum at the common
source.  Nevertheless every direction has total excess `1/2`, so every
nonzero nonnegative combination has strictly positive coordinate sum and
cannot balance to zero.

The same rays are then realized by a literal three-player quitting reward and
full behavioral best-response envelopes.  That game has a zero-debt
grand-coalition exit profile, so it is not a quitting-game counterexample:
the source is minimal only on the displayed common-base rays, not globally.
This isolates global minimality as the only supplied hypothesis not realized
by the local semantic regression.  A common-base support-entry/cycle argument
still needs an additional zero-excess, minimum-fiber return, or quantitative
reprojection theorem.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

/-- At a total-debt minimum, a balanced nonnegative combination can use only
directions whose targets remain on the same total-debt fiber.

This elementary invariant is the exact obstruction behind the finite table
below.  Minimum-debt comparison makes every target's total excess
nonnegative.  If a nonnegative combination balances coordinatewise, the
weighted sum of those excesses is zero, so every positively weighted excess
must vanish. -/
theorem balanced_minimumDebtDirections_use_only_minimumTargets
    {move player : Type} [Fintype move] [Fintype player]
    (source : player → ℝ) (target : move → player → ℝ)
    (weight : move → ℝ)
    (hminimum : ∀ mover,
      (∑ observer, source observer) ≤ ∑ observer, target mover observer)
    (hweight : ∀ mover, 0 ≤ weight mover)
    (hbalanced : ∀ observer,
      (∑ mover,
        weight mover * (target mover observer - source observer)) = 0) :
    ∀ mover, 0 < weight mover →
      (∑ observer, target mover observer) = ∑ observer, source observer := by
  have hcoordinateSum :
      (∑ observer,
        ∑ mover,
          weight mover * (target mover observer - source observer)) = 0 := by
    simp_rw [hbalanced]
    simp
  have hexcessSum :
      (∑ mover,
        weight mover *
          ((∑ observer, target mover observer) -
            ∑ observer, source observer)) = 0 := by
    rw [Finset.sum_comm] at hcoordinateSum
    calc
      (∑ mover,
          weight mover *
            ((∑ observer, target mover observer) -
              ∑ observer, source observer)) =
          ∑ mover,
            ∑ observer,
              weight mover *
                (target mover observer - source observer) := by
        apply Finset.sum_congr rfl
        intro mover _hmover
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro observer _hobserver
        ring
      _ = 0 := hcoordinateSum
  intro mover hmover
  have hterm : weight mover *
      ((∑ observer, target mover observer) -
        ∑ observer, source observer) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun candidate _candidateMem =>
      mul_nonneg (hweight candidate)
        (sub_nonneg.mpr (hminimum candidate)))).mp hexcessSum
          mover (Finset.mem_univ mover)
  have hweightNe : weight mover ≠ 0 := ne_of_gt hmover
  have hexcessZero :
      (∑ observer, target mover observer) -
        ∑ observer, source observer = 0 :=
    (mul_eq_zero.mp hterm).resolve_left hweightNe
  linarith

/-! ## Zero normalized excess does not give a minimum-face tangent -/

/-- A compact convex parabolic epigraph.  The second coordinate is the
abstract total-debt objective. -/
def quittingParabolicMinimumCarrier : Set (ℝ × ℝ) :=
  (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩
    {point | point.1 ^ 2 ≤ point.2}

theorem quittingParabolicMinimumCarrier_isCompact :
    IsCompact quittingParabolicMinimumCarrier := by
  apply (isCompact_Icc.prod isCompact_Icc).inter_right
  exact isClosed_le (continuous_fst.pow 2) continuous_snd

theorem quittingParabolicMinimumCarrier_convex :
    Convex ℝ quittingParabolicMinimumCarrier := by
  have hbox : Convex ℝ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (-1 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1)
  have hepigraph : Convex ℝ {point : ℝ × ℝ | point.1 ^ 2 ≤ point.2} := by
    intro first hfirst second hsecond left right hleft hright hsum
    change (left * first.1 + right * second.1) ^ 2 ≤
      left * first.2 + right * second.2
    change first.1 ^ 2 ≤ first.2 at hfirst
    change second.1 ^ 2 ≤ second.2 at hsecond
    have hfirstScaled := mul_le_mul_of_nonneg_left hfirst hleft
    have hsecondScaled := mul_le_mul_of_nonneg_left hsecond hright
    have hcross : 0 ≤ left * right * (first.1 - second.1) ^ 2 :=
      mul_nonneg (mul_nonneg hleft hright) (sq_nonneg _)
    nlinarith
  exact hbox.inter hepigraph

/-- The objective-minimizing face of the parabolic carrier is a singleton. -/
theorem quittingParabolicMinimumCarrier_second_eq_zero_iff
    (point : ℝ × ℝ) :
    point ∈ quittingParabolicMinimumCarrier ∧ point.2 = 0 ↔
      point = (0, 0) := by
  constructor
  · rintro ⟨⟨_hbox, hepigraph⟩, hsecond⟩
    change point.1 ^ 2 ≤ point.2 at hepigraph
    have hfirst : point.1 = 0 := by
      rw [hsecond] at hepigraph
      nlinarith [sq_nonneg point.1]
    exact Prod.ext hfirst hsecond
  · rintro rfl
    norm_num [quittingParabolicMinimumCarrier]

/-- A near-minimum source on the vertical axis. -/
def quittingParabolicNearMinimumSource (scale : ℝ) : ℝ × ℝ :=
  (0, scale ^ 3)

/-- A target on the curved lower boundary. -/
def quittingParabolicNearMinimumTarget (scale : ℝ) : ℝ × ℝ :=
  (scale, scale ^ 2)

/-- The corresponding normalized secant. -/
def quittingParabolicNormalizedDirection (scale : ℝ) : ℝ × ℝ :=
  (1, scale - scale ^ 2)

theorem quittingParabolicNearMinimumSource_mem
    (scale : ℝ) (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) :
    quittingParabolicNearMinimumSource scale ∈
      quittingParabolicMinimumCarrier := by
  constructor
  · constructor
    · constructor <;> norm_num [quittingParabolicNearMinimumSource]
    · constructor
      · dsimp [quittingParabolicNearMinimumSource]
        positivity
      · dsimp [quittingParabolicNearMinimumSource]
        exact pow_le_one₀ hscale0 hscale1
  · dsimp [quittingParabolicNearMinimumSource]
    norm_num
    positivity

theorem quittingParabolicNearMinimumTarget_mem
    (scale : ℝ) (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) :
    quittingParabolicNearMinimumTarget scale ∈
      quittingParabolicMinimumCarrier := by
  constructor
  · constructor <;> constructor <;>
      dsimp [quittingParabolicNearMinimumTarget] <;> nlinarith
  · dsimp [quittingParabolicNearMinimumTarget]
    rfl

/-- The displayed direction is exactly the source-to-target secant divided
by the positive scale. -/
theorem quittingParabolicNormalizedDirection_eq_smul_sub
    (scale : ℝ) (hscale : 0 < scale) :
    quittingParabolicNormalizedDirection scale =
      scale⁻¹ •
        (quittingParabolicNearMinimumTarget scale -
          quittingParabolicNearMinimumSource scale) := by
  apply Prod.ext
  · dsimp [quittingParabolicNormalizedDirection,
      quittingParabolicNearMinimumTarget,
      quittingParabolicNearMinimumSource]
    field_simp
    ring
  · dsimp [quittingParabolicNormalizedDirection,
      quittingParabolicNearMinimumTarget,
      quittingParabolicNearMinimumSource]
    field_simp

/-- The normalized total-objective excess vanishes at first order. -/
theorem quittingParabolic_normalizedExcess_tendsto_zero :
    Tendsto (fun scale : ℝ ↦ scale - scale ^ 2) (nhds 0) (nhds 0) := by
  have hcontinuous : ContinuousAt (fun scale : ℝ ↦ scale - scale ^ 2) 0 := by
    fun_prop
  unfold ContinuousAt at hcontinuous
  norm_num at hcontinuous
  exact hcontinuous

/-- Nevertheless the normalized carrier secants converge to the nonzero
horizontal direction `(1,0)`.  Since the exact minimum face is the singleton
`{(0,0)}`, this direction cannot be a secant or contingent direction of that
face. -/
theorem quittingParabolicNormalizedDirection_tendsto_nonzero :
    Tendsto quittingParabolicNormalizedDirection (nhds 0) (nhds (1, 0)) := by
  have hcontinuous : ContinuousAt quittingParabolicNormalizedDirection 0 := by
    unfold quittingParabolicNormalizedDirection
    fun_prop
  unfold ContinuousAt at hcontinuous
  simpa [quittingParabolicNormalizedDirection] using hcontinuous

/-! ## A literal quitting-table realization of the local geometry -/

/-- The cyclic recipient of a reset mover in the three-player regression. -/
def quittingFinThreeResetRecipient : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- The predecessor in the cyclic three-player table. -/
def quittingFinThreeResetPredecessor : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

/-- A literal quitting reward which realizes the passive-shear reset rays.
A quitter receives one, plus a bonus two when its cyclic predecessor quits
at the same date.  A player which does not quit receives zero. -/
def quittingFinThreePassiveShearReward :
    {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3) :=
  fun terminal player =>
    if player ∈ terminal.val then
      if quittingFinThreeResetPredecessor player ∈ terminal.val then 3 else 1
    else 0

theorem abs_quittingFinThreePassiveShearReward_le_three
    (terminal : {S : Finset (Fin 3) // S.Nonempty}) (player : Fin 3) :
    |quittingFinThreePassiveShearReward terminal player| ≤ 3 := by
  unfold quittingFinThreePassiveShearReward
  split_ifs <;> norm_num

/-- The exact behavioral best-response cap against a pure sure-exit set is
the better membership toggle.  This local adapter lets the regression use
the repository's full history-dependent deviation semantics. -/
theorem quittingContinuationBestResponseValue_pureSetRoot_eq
    {player : Type} [Fintype player] [DecidableEq player]
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (exit : Finset player) (observer : player)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward (quittingPureSetRoot exit)) observer =
      max (quittingSetReward reward (insert observer exit) observer)
        (quittingSetReward reward (exit.erase observer) observer) := by
  let profile := quittingStationaryProfile reward (quittingPureSetRoot exit)
  have hbdd : BddAbove (Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy observer =>
        quittingTerminalPayoff reward
          (Function.update profile observer deviation) observer) :=
    bddAbove_range_quittingTerminalPayoff_update
      reward profile observer hM hreward
  unfold quittingContinuationBestResponseValue
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro payoff ⟨deviation, rfl⟩
      exact quittingTerminalPayoff_update_pureSetRoot_le
        reward exit observer deviation
  · apply max_le
    · apply le_csSup hbdd
      refine ⟨quittingPureTimeBehaviorStrategy reward observer (some 0), ?_⟩
      exact quittingTerminalPayoff_update_pureSetRoot_quitNow
        reward exit observer
    · apply le_csSup hbdd
      refine ⟨quittingAlwaysContinueStrategy reward observer, ?_⟩
      exact quittingTerminalPayoff_update_pureSetRoot_alwaysContinue
        reward exit observer

/-- Consequently, semantic debt at a pure sure-exit profile is exactly the
membership-toggle cap minus the current set reward. -/
theorem quittingTerminalSemanticDebt_pureSetRoot_eq
    {player : Type} [Fintype player] [DecidableEq player]
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (exit : Finset player) (observer : player)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStationaryProfile reward (quittingPureSetRoot exit)))
        observer =
      max (quittingSetReward reward (insert observer exit) observer)
          (quittingSetReward reward (exit.erase observer) observer) -
        quittingSetReward reward exit observer := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
      (quittingStationaryProfile reward (quittingPureSetRoot exit)) observer -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward (quittingPureSetRoot exit)) observer = _
  rw [quittingContinuationBestResponseValue_pureSetRoot_eq
    reward exit observer hM hreward,
    quittingTerminalPayoff_pureSetRoot]

/-- Literal all-Never source of the passive-shear table. -/
def quittingFinThreePassiveShearSource :
    (quittingGame quittingFinThreePassiveShearReward).BehaviorProfile :=
  quittingStationaryProfile quittingFinThreePassiveShearReward
    (quittingPureSetRoot ∅)

/-- Literal endpoint at which exactly `mover` quits surely. -/
def quittingFinThreePassiveShearEndpoint (mover : Fin 3) :
    (quittingGame quittingFinThreePassiveShearReward).BehaviorProfile :=
  quittingStationaryProfile quittingFinThreePassiveShearReward
    (quittingPureSetRoot {mover})

theorem quittingFinThreePassiveShearEndpoint_eq_update_source
    (mover : Fin 3) :
    quittingFinThreePassiveShearEndpoint mover =
      Function.update quittingFinThreePassiveShearSource mover
        (quittingAlwaysQuitStrategy quittingFinThreePassiveShearReward mover) := by
  funext player time history
  by_cases hplayer : player = mover
  · subst player
    simp [quittingFinThreePassiveShearEndpoint,
      quittingFinThreePassiveShearSource, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile,
      quittingAlwaysQuitStrategy, quittingPureSetRoot, quittingSetAction]
    rfl
  · simp [quittingFinThreePassiveShearEndpoint,
      quittingFinThreePassiveShearSource, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile,
      quittingPureSetRoot, quittingSetAction, hplayer]

/-- The literal complete stopping-law mixture generating one passive-shear
ray.  It is Quit-now/always-Quit with probability `lambda` and Never with
probability `1-lambda`, reconstructed as a legal behavior strategy. -/
def quittingFinThreePassiveShearMixedProfile
    (mover : Fin 3) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingGame quittingFinThreePassiveShearReward).BehaviorProfile :=
  Function.update quittingFinThreePassiveShearSource mover
    (quittingStoppingLawMixtureBehaviorStrategy
      quittingFinThreePassiveShearReward mover
      (quittingFinThreePassiveShearSource mover)
      (quittingAlwaysQuitStrategy quittingFinThreePassiveShearReward mover)
      lambda hlambda0 hlambda1)

/-- Prescribed payoff on the literal reset ray: only the mover is paid, and
its payoff is exactly the mixture weight. -/
theorem quittingFinThreePassiveShearMixedProfile_payoff
    (mover observer : Fin 3) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalPayoff quittingFinThreePassiveShearReward
        (quittingFinThreePassiveShearMixedProfile mover lambda
          hlambda0 hlambda1) observer =
      if observer = mover then lambda else 0 := by
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    quittingFinThreePassiveShearReward quittingFinThreePassiveShearSource
      mover observer (quittingFinThreePassiveShearSource mover)
      (quittingAlwaysQuitStrategy quittingFinThreePassiveShearReward mover)
      lambda hlambda0 hlambda1
  rw [Function.update_eq_self,
    ← quittingFinThreePassiveShearEndpoint_eq_update_source] at haffine
  unfold quittingFinThreePassiveShearSource
    quittingFinThreePassiveShearEndpoint at haffine
  rw [quittingTerminalPayoff_pureSetRoot,
    quittingTerminalPayoff_pureSetRoot] at haffine
  change quittingTerminalPayoff quittingFinThreePassiveShearReward
      (quittingFinThreePassiveShearMixedProfile mover lambda
        hlambda0 hlambda1) observer = _ at haffine
  fin_cases mover <;> fin_cases observer <;>
    norm_num [quittingFinThreePassiveShearSource,
      quittingFinThreePassiveShearEndpoint, quittingSetReward,
      quittingFinThreePassiveShearReward,
      quittingFinThreeResetPredecessor] at haffine ⊢ <;>
    linarith

/-- Quitting immediately against the mixed mover law is worth one, plus the
cyclic predecessor bonus weighted by `lambda`. -/
theorem quittingFinThreePassiveShearMixedProfile_quitNow_payoff
    (mover observer : Fin 3) (hne : observer ≠ mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    let deviation := quittingPureTimeBehaviorStrategy
      quittingFinThreePassiveShearReward observer (some 0)
    quittingTerminalPayoff quittingFinThreePassiveShearReward
        (Function.update
          (quittingFinThreePassiveShearMixedProfile mover lambda
            hlambda0 hlambda1) observer deviation) observer =
      if observer = quittingFinThreeResetRecipient mover then
        1 + 2 * lambda else 1 := by
  dsimp only
  let deviation := quittingPureTimeBehaviorStrategy
    quittingFinThreePassiveShearReward observer (some 0)
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    quittingFinThreePassiveShearReward mover
    (quittingFinThreePassiveShearSource mover)
    (quittingAlwaysQuitStrategy quittingFinThreePassiveShearReward mover)
    lambda hlambda0 hlambda1
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    quittingFinThreePassiveShearReward
      (Function.update quittingFinThreePassiveShearSource observer deviation)
      mover observer (quittingFinThreePassiveShearSource mover)
      (quittingAlwaysQuitStrategy quittingFinThreePassiveShearReward mover)
      lambda hlambda0 hlambda1
  have hcommuteSource :
      Function.update
          (Function.update quittingFinThreePassiveShearSource observer deviation)
          mover (quittingFinThreePassiveShearSource mover) =
        Function.update quittingFinThreePassiveShearSource observer deviation := by
    rw [Function.update_comm hne]
    simp
  have hcommuteEndpoint :
      Function.update
          (Function.update quittingFinThreePassiveShearSource observer deviation)
          mover (quittingAlwaysQuitStrategy
            quittingFinThreePassiveShearReward mover) =
        Function.update (quittingFinThreePassiveShearEndpoint mover)
          observer deviation := by
    rw [Function.update_comm hne]
    rw [quittingFinThreePassiveShearEndpoint_eq_update_source]
  have hcommuteMixed :
      Function.update
          (Function.update quittingFinThreePassiveShearSource observer deviation)
          mover mixedStrategy =
        Function.update
          (quittingFinThreePassiveShearMixedProfile mover lambda
            hlambda0 hlambda1) observer deviation := by
    rw [Function.update_comm hne]
    rfl
  rw [hcommuteMixed, hcommuteSource, hcommuteEndpoint] at haffine
  dsimp only [deviation] at haffine
  unfold quittingFinThreePassiveShearSource
    quittingFinThreePassiveShearEndpoint at haffine
  rw [quittingTerminalPayoff_update_pureSetRoot_quitNow,
    quittingTerminalPayoff_update_pureSetRoot_quitNow] at haffine
  fin_cases mover <;> fin_cases observer <;>
    norm_num [Fin.ext_iff, quittingFinThreePassiveShearSource,
      quittingFinThreePassiveShearEndpoint, quittingFinThreeResetRecipient,
      quittingSetReward, quittingFinThreePassiveShearReward,
      quittingFinThreeResetPredecessor] at haffine ⊢ <;>
      linarith

/-- The cap-side object exposed by the positive-slope decoder can be
strictly positive without obstructing equilibrium.  In the passive-shear
table, let the cyclic recipient use the same Quit-now deviation at the
source and at the mover endpoint.  The mover's endpoint law raises that
deviation payoff by exactly two: the recipient receives the predecessor
bonus when both players quit together.

This is already a literal, state-matched root insertion effect.  The
zero-debt grand-coalition profile below shows that even this stronger
special case of a positive same-deviation terminal chord is strategically
benign unless some further counterexample-regime or minimum-fiber property
connects it to a contradiction. -/
theorem quittingFinThreePassiveShear_quitNowRectangle_eq_two
    (mover : Fin 3) :
    let observer := quittingFinThreeResetRecipient mover
    let deviation := quittingPureTimeBehaviorStrategy
      quittingFinThreePassiveShearReward observer (some 0)
    quittingTerminalPayoff quittingFinThreePassiveShearReward
          (Function.update (quittingFinThreePassiveShearEndpoint mover)
            observer deviation) observer -
        quittingTerminalPayoff quittingFinThreePassiveShearReward
          (Function.update quittingFinThreePassiveShearSource
            observer deviation) observer = 2 := by
  dsimp only
  unfold quittingFinThreePassiveShearEndpoint
    quittingFinThreePassiveShearSource
  rw [quittingTerminalPayoff_update_pureSetRoot_quitNow,
    quittingTerminalPayoff_update_pureSetRoot_quitNow]
  fin_cases mover <;>
    norm_num [Fin.ext_iff, quittingFinThreeResetRecipient,
      quittingSetReward, quittingFinThreePassiveShearReward,
      quittingFinThreeResetPredecessor]

/-- Every player has unit debt at the common minimum source. -/
def quittingFinThreeResetSourceDebt (_player : Fin 3) : ℝ := 1

/-- Endpoint debt after the mover's idealized complete-law deviation.
The mover is killed, the cyclic recipient rises from one to three, and the
third coordinate is unchanged. -/
def quittingFinThreeResetEndpointDebt
    (mover observer : Fin 3) : ℝ :=
  if observer = mover then 0
  else if observer = quittingFinThreeResetRecipient mover then 3
  else 1

/-- Debt at mixture weight `lambda` on one common-base reset ray. -/
def quittingFinThreeResetRayDebt
    (mover observer : Fin 3) (lambda : ℝ) : ℝ :=
  (1 - lambda) * quittingFinThreeResetSourceDebt observer +
    lambda * quittingFinThreeResetEndpointDebt mover observer

/-- The literal all-Never profile has exactly the abstract source debt
vector `(1,1,1)`. -/
theorem quittingFinThreePassiveShearSource_semanticDebt
    (observer : Fin 3) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair quittingFinThreePassiveShearReward
          quittingFinThreePassiveShearSource) observer =
      quittingFinThreeResetSourceDebt observer := by
  unfold quittingFinThreePassiveShearSource
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq
    quittingFinThreePassiveShearReward ∅ observer (by norm_num)
      abs_quittingFinThreePassiveShearReward_le_three]
  fin_cases observer <;>
    norm_num [quittingFinThreeResetSourceDebt,
      quittingSetReward, quittingFinThreePassiveShearReward,
      quittingFinThreeResetPredecessor]

/-- When exactly `mover` quits surely, the literal semantic debt vector is
the abstract endpoint: the mover has zero debt, its cyclic recipient has
debt three, and the remaining player has debt one. -/
theorem quittingFinThreePassiveShearEndpoint_semanticDebt
    (mover observer : Fin 3) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair quittingFinThreePassiveShearReward
          (quittingFinThreePassiveShearEndpoint mover)) observer =
      quittingFinThreeResetEndpointDebt mover observer := by
  unfold quittingFinThreePassiveShearEndpoint
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq
    quittingFinThreePassiveShearReward {mover} observer (by norm_num)
      abs_quittingFinThreePassiveShearReward_le_three]
  fin_cases mover <;> fin_cases observer <;>
    norm_num [Fin.ext_iff, quittingFinThreeResetEndpointDebt,
      quittingFinThreeResetRecipient, quittingSetReward,
      quittingFinThreePassiveShearReward,
      quittingFinThreeResetPredecessor]

/-- The entire literal stopping-law ray realizes the abstract affine debt
table exactly.  Thus passive shear is compatible with full behavioral
best-response envelopes, not merely with a formal chord inequality. -/
theorem quittingFinThreePassiveShearMixedProfile_semanticDebt
    (mover observer : Fin 3) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair quittingFinThreePassiveShearReward
          (quittingFinThreePassiveShearMixedProfile mover lambda
            hlambda0 hlambda1)) observer =
      quittingFinThreeResetRayDebt mover observer lambda := by
  have hupper := quittingTerminalSemanticDebt_stoppingLawMixture_le
    quittingFinThreePassiveShearReward quittingFinThreePassiveShearSource
      mover observer (quittingFinThreePassiveShearSource mover)
      (quittingAlwaysQuitStrategy quittingFinThreePassiveShearReward mover)
      lambda hlambda0 hlambda1 (by norm_num)
      abs_quittingFinThreePassiveShearReward_le_three
  rw [Function.update_eq_self,
    ← quittingFinThreePassiveShearEndpoint_eq_update_source] at hupper
  change quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair quittingFinThreePassiveShearReward
        (quittingFinThreePassiveShearMixedProfile mover lambda
          hlambda0 hlambda1)) observer ≤ _ at hupper
  rw [quittingFinThreePassiveShearSource_semanticDebt,
    quittingFinThreePassiveShearEndpoint_semanticDebt] at hupper
  by_cases hsame : observer = mover
  · subst observer
    have heq := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      quittingFinThreePassiveShearReward quittingFinThreePassiveShearSource
        mover (quittingFinThreePassiveShearSource mover)
        (quittingAlwaysQuitStrategy quittingFinThreePassiveShearReward mover)
        lambda hlambda0 hlambda1
    rw [Function.update_eq_self,
      ← quittingFinThreePassiveShearEndpoint_eq_update_source] at heq
    change quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair quittingFinThreePassiveShearReward
          (quittingFinThreePassiveShearMixedProfile mover lambda
            hlambda0 hlambda1)) mover = _ at heq
    rw [quittingFinThreePassiveShearSource_semanticDebt,
      quittingFinThreePassiveShearEndpoint_semanticDebt] at heq
    exact heq
  · let deviation := quittingPureTimeBehaviorStrategy
      quittingFinThreePassiveShearReward observer (some 0)
    have hdeviation :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        quittingFinThreePassiveShearReward
        (quittingFinThreePassiveShearMixedProfile mover lambda
          hlambda0 hlambda1) observer deviation (by norm_num)
          abs_quittingFinThreePassiveShearReward_le_three
    have hquit := quittingFinThreePassiveShearMixedProfile_quitNow_payoff
      mover observer hsame lambda hlambda0 hlambda1
    have hpayoff := quittingFinThreePassiveShearMixedProfile_payoff
      mover observer lambda hlambda0 hlambda1
    dsimp only [deviation] at hdeviation
    rw [hquit] at hdeviation
    rw [if_neg hsame] at hpayoff
    apply le_antisymm hupper
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    change quittingFinThreeResetRayDebt mover observer lambda ≤
      quittingContinuationBestResponseValue quittingFinThreePassiveShearReward
          (quittingFinThreePassiveShearMixedProfile mover lambda
            hlambda0 hlambda1) observer -
        quittingTerminalPayoff quittingFinThreePassiveShearReward
          (quittingFinThreePassiveShearMixedProfile mover lambda
            hlambda0 hlambda1) observer
    rw [hpayoff]
    fin_cases mover <;> fin_cases observer <;>
      norm_num [Fin.ext_iff, quittingFinThreeResetRayDebt,
        quittingFinThreeResetSourceDebt,
        quittingFinThreeResetEndpointDebt,
        quittingFinThreeResetRecipient] at hdeviation ⊢ <;>
      linarith

/-- The literal realization is intentionally not a quitting-game
counterexample: the grand-coalition sure-exit profile has zero debt in every
coordinate.  Hence the global minimum is zero even though the all-Never
source is a strict minimum along each selected reset ray. -/
theorem quittingFinThreePassiveShear_allQuit_semanticDebt_eq_zero
    (observer : Fin 3) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair quittingFinThreePassiveShearReward
          (quittingStationaryProfile quittingFinThreePassiveShearReward
            (quittingPureSetRoot Finset.univ))) observer = 0 := by
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq
    quittingFinThreePassiveShearReward Finset.univ observer (by norm_num)
      abs_quittingFinThreePassiveShearReward_le_three]
  fin_cases observer <;>
    norm_num [Fin.ext_iff, quittingSetReward,
      quittingFinThreePassiveShearReward,
      quittingFinThreeResetPredecessor]

/-- The half-law debt direction from the common source. -/
def quittingFinThreeHalfResetDirection
    (mover observer : Fin 3) : ℝ :=
  quittingFinThreeResetRayDebt mover observer (1 / 2) -
    quittingFinThreeResetSourceDebt observer

theorem quittingFinThreeResetRecipient_ne (mover : Fin 3) :
    quittingFinThreeResetRecipient mover ≠ mover := by
  fin_cases mover <;> simp [quittingFinThreeResetRecipient]

theorem quittingFinThreeResetEndpointDebt_nonneg
    (mover observer : Fin 3) :
    0 ≤ quittingFinThreeResetEndpointDebt mover observer := by
  unfold quittingFinThreeResetEndpointDebt
  split_ifs <;> norm_num

/-- The endpoint kills exactly the mover's debt coordinate. -/
theorem quittingFinThreeResetEndpointDebt_self (mover : Fin 3) :
    quittingFinThreeResetEndpointDebt mover mover = 0 := by
  simp [quittingFinThreeResetEndpointDebt]

/-- The half-reset target is literally the midpoint chord. -/
theorem quittingFinThreeResetRayDebt_half_eq_midpoint
    (mover observer : Fin 3) :
    quittingFinThreeResetRayDebt mover observer (1 / 2) =
      (1 / 2) * quittingFinThreeResetSourceDebt observer +
        (1 / 2) * quittingFinThreeResetEndpointDebt mover observer := by
  unfold quittingFinThreeResetRayDebt
  ring

/-- The mover loses one half unit of debt. -/
theorem quittingFinThreeHalfResetDirection_self (mover : Fin 3) :
    quittingFinThreeHalfResetDirection mover mover = -(1 / 2) := by
  simp [quittingFinThreeHalfResetDirection,
    quittingFinThreeResetRayDebt, quittingFinThreeResetSourceDebt,
    quittingFinThreeResetEndpointDebt]

/-- The named cyclic recipient gains one unit of debt. -/
theorem quittingFinThreeHalfResetDirection_recipient (mover : Fin 3) :
    quittingFinThreeHalfResetDirection mover
        (quittingFinThreeResetRecipient mover) = 1 := by
  have hne := quittingFinThreeResetRecipient_ne mover
  simp [quittingFinThreeHalfResetDirection,
    quittingFinThreeResetRayDebt, quittingFinThreeResetSourceDebt,
    quittingFinThreeResetEndpointDebt, hne]
  ring

/-- Every named recipient lies in the positive support of the common source. -/
theorem quittingFinThreeResetRecipient_sourceDebt_pos (mover : Fin 3) :
    0 < quittingFinThreeResetSourceDebt
      (quittingFinThreeResetRecipient mover) := by
  norm_num [quittingFinThreeResetSourceDebt]

/-- Each common-base half-reset has unavoidable passive excess `1/2`. -/
theorem sum_quittingFinThreeHalfResetDirection (mover : Fin 3) :
    (∑ observer : Fin 3,
      quittingFinThreeHalfResetDirection mover observer) = 1 / 2 := by
  fin_cases mover <;>
    simp [Fin.sum_univ_three, quittingFinThreeHalfResetDirection,
      quittingFinThreeResetRayDebt,
      quittingFinThreeResetSourceDebt, quittingFinThreeResetEndpointDebt,
      quittingFinThreeResetRecipient] <;>
    norm_num

/-- Along each individual reset ray, total debt is `3 + lambda`. -/
theorem sum_quittingFinThreeResetRayDebt
    (mover : Fin 3) (lambda : ℝ) :
    (∑ observer : Fin 3,
      quittingFinThreeResetRayDebt mover observer lambda) = 3 + lambda := by
  fin_cases mover <;>
    simp [Fin.sum_univ_three, quittingFinThreeResetRayDebt,
      quittingFinThreeResetSourceDebt, quittingFinThreeResetEndpointDebt,
      quittingFinThreeResetRecipient] <;>
    ring

/-- Hence the common source is an exact total-debt minimum on every
nonnegative common-base reset ray. -/
theorem quittingFinThreeResetSource_minimum_on_ray
    (mover : Fin 3) (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    (∑ observer : Fin 3,
        quittingFinThreeResetSourceDebt observer) ≤
      ∑ observer : Fin 3,
        quittingFinThreeResetRayDebt mover observer lambda := by
  rw [sum_quittingFinThreeResetRayDebt]
  simp [quittingFinThreeResetSourceDebt]
  linarith

/-- A nonnegative combination of the three reset directions has total
coordinate sum equal to one half of its total weight. -/
theorem sum_weighted_quittingFinThreeHalfResetDirection
    (weight : Fin 3 → ℝ) :
    (∑ observer : Fin 3,
        ∑ mover : Fin 3,
          weight mover * quittingFinThreeHalfResetDirection mover observer) =
      (1 / 2) * ∑ mover : Fin 3, weight mover := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_quittingFinThreeHalfResetDirection]
  rw [← Finset.sum_mul]
  ring

/-- **Passive-shear obstruction.**  No nonzero nonnegative combination of
the cyclic, support-contained half-reset directions can balance every debt
coordinate. -/
theorem not_balanced_quittingFinThreeHalfResetDirection
    (weight : Fin 3 → ℝ)
    (hweight : ∀ mover, 0 ≤ weight mover)
    (hpositive : ∃ mover, 0 < weight mover) :
    ¬ ∀ observer,
      (∑ mover : Fin 3,
        weight mover * quittingFinThreeHalfResetDirection mover observer) = 0 := by
  intro hbalanced
  have hsumPositive : 0 < ∑ mover : Fin 3, weight mover :=
    Finset.sum_pos' (fun mover _hmover => hweight mover)
      (by
        obtain ⟨mover, hmover⟩ := hpositive
        exact ⟨mover, Finset.mem_univ mover, hmover⟩)
  have hcoordinateSumZero :
      (∑ observer : Fin 3,
        ∑ mover : Fin 3,
          weight mover * quittingFinThreeHalfResetDirection mover observer) = 0 := by
    apply Finset.sum_eq_zero
    intro observer _hobserver
    exact hbalanced observer
  rw [sum_weighted_quittingFinThreeHalfResetDirection] at hcoordinateSumZero
  nlinarith

end GameTheory
