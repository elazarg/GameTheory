/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.GermNondegeneracy
import UniformEquilibrium.Quitting.Projective.AnalyticPacket
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler
import UniformEquilibrium.Quitting.Punishment.CompletedCycle
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticBellmanHierarchy

/-!
# The punishment-normalized auxiliary quitting game

This is the normalization layer used by the three-player existence theorem.
It is generic in the finite player type whenever no three-player fact is used.
The terminal table is translated by the vector

`min 0 (quittingPunishmentValue reward i)`.

The important point is that the translation is made simultaneously in every
terminal reward and in the continuation vector.  One-stage quitting payoffs,
fixed-point equations, and endpoint differences are then translated exactly.
-/

noncomputable section

namespace GameTheory

open Filter Set Topology
open StochasticGame Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Translate every absorbing payoff by a player-dependent live anchor. -/
def quittingRewardShift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : Payoff ι) : {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun S who => reward S who - anchor who

/-- Add an anchor to a continuation vector. -/
def quittingPayoffUnshift (anchor value : Payoff ι) : Payoff ι :=
  fun who => value who + anchor who

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingRewardShift_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : Payoff ι) (S : {S : Finset ι // S.Nonempty}) (who : ι) :
    quittingRewardShift reward anchor S who = reward S who - anchor who :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingPayoffUnshift_apply
    (anchor value : Payoff ι) (who : ι) :
    quittingPayoffUnshift anchor value who = value who + anchor who :=
  rfl

omit [DecidableEq ι] in
/-- A translated terminal table and translated continuation shift every pure
one-stage outcome by the same coordinate constant. -/
theorem quittingRootPayoff_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor value : Payoff ι) (action : ι → Bool) (who : ι) :
    quittingRootPayoff (quittingRewardShift reward anchor) value action who =
      quittingRootPayoff reward (quittingPayoffUnshift anchor value) action who -
        anchor who := by
  unfold quittingRootPayoff
  by_cases hquit : (quittingQuitters action).Nonempty
  · simp [hquit, quittingRewardShift]
  · simp [hquit, quittingPayoffUnshift]

omit [DecidableEq ι] in
/-- Expected one-stage payoffs obey the same translation law. -/
theorem quittingRootExpectedPayoff_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor value : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootExpectedPayoff (quittingRewardShift reward anchor) value root who =
      quittingRootExpectedPayoff reward (quittingPayoffUnshift anchor value)
          root who - anchor who := by
  unfold quittingRootExpectedPayoff
  have hpoint :
      (fun action =>
        quittingRootPayoff (quittingRewardShift reward anchor) value action who) =
      (fun action =>
        quittingRootPayoff reward (quittingPayoffUnshift anchor value) action who -
          anchor who) := by
    funext action
    exact quittingRootPayoff_shift reward anchor value action who
  rw [hpoint, expect_sub, expect_const]

omit [DecidableEq ι] in
/-- Vector form of the translated successor identity. -/
theorem quittingRootSuccessorPayoff_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor value : Payoff ι) (root : ι → PMF Bool) :
    quittingRootSuccessorPayoff (quittingRewardShift reward anchor) value root =
      fun who =>
        quittingRootSuccessorPayoff reward
            (quittingPayoffUnshift anchor value) root who - anchor who := by
  funext who
  exact quittingRootExpectedPayoff_shift reward anchor value root who

/-- Pure-Quit endpoints translate exactly. -/
theorem quittingRootQuitPayoff_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor value : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff (quittingRewardShift reward anchor) value root who =
      quittingRootQuitPayoff reward (quittingPayoffUnshift anchor value) root who -
        anchor who := by
  exact quittingRootExpectedPayoff_shift reward anchor value
    (Function.update root who (PMF.pure true)) who

/-- Pure-Continue endpoints translate exactly. -/
theorem quittingRootContinuePayoff_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor value : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff (quittingRewardShift reward anchor) value root who =
      quittingRootContinuePayoff reward
          (quittingPayoffUnshift anchor value) root who - anchor who := by
  exact quittingRootExpectedPayoff_shift reward anchor value
    (Function.update root who (PMF.pure false)) who

/-- Endpoint differences are invariant under simultaneous translation. -/
theorem quittingRootEndpointDifference_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor value : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference (quittingRewardShift reward anchor) value root who =
      quittingRootEndpointDifference reward
        (quittingPayoffUnshift anchor value) root who := by
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_shift, quittingRootContinuePayoff_shift]
  ring

/-- Exact endpoint Nash is invariant under simultaneous translation. -/
theorem isεQuittingRootEndpointNash_zero_shift_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor value : Payoff ι) (root : ι → PMF Bool) :
    IsεQuittingRootEndpointNash (quittingRewardShift reward anchor) value 0 root ↔
      IsεQuittingRootEndpointNash reward
        (quittingPayoffUnshift anchor value) 0 root := by
  unfold IsεQuittingRootEndpointNash
  simp_rw [quittingRootEndpointDifference_shift]

omit [DecidableEq ι] in
/-- A shifted fixed point is an original fixed point after adding the anchor. -/
theorem quittingRootFixedPoint_unshift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor value : Payoff ι) (root : ι → PMF Bool)
    (hfixed : value =
      quittingRootSuccessorPayoff (quittingRewardShift reward anchor) value root) :
    quittingPayoffUnshift anchor value =
      quittingRootSuccessorPayoff reward
        (quittingPayoffUnshift anchor value) root := by
  funext who
  have hwho := congrFun hfixed who
  rw [quittingRootSuccessorPayoff_shift] at hwho
  simp only [quittingPayoffUnshift_apply]
  linarith

/-! ## Endpoint dictionary at `t = 0` -/

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Analytic pinning on the punctured germ extends to every absorbed endpoint
coordinate by continuity. -/
theorem quittingGerm_assignment_val_some_zero
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (S : {S : Finset ι // S.Nonempty}) (who : ι) :
    g.assignment 0 (BellmanVar.val (some S) who) = reward S who := by
  have hcurve : Tendsto
      (fun t : ℝ => g.assignment t (BellmanVar.val (some S) who))
      (𝓝[>] (0 : ℝ))
      (𝓝 (g.assignment 0 (BellmanVar.val (some S) who))) :=
    (g.analytic_coordinate (BellmanVar.val (some S) who)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hconstant : Tendsto (fun _ : ℝ => reward S who)
      (𝓝[>] (0 : ℝ)) (𝓝 (reward S who)) := tendsto_const_nhds
  have heventually :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        g.assignment t (BellmanVar.val (some S) who) = reward S who := by
    filter_upwards [eventually_mem_Ioo_radius g] with t ht
    exact quittingGerm_assignment_val_some g ht S who
  have hsame : Tendsto
      (fun t : ℝ => g.assignment t (BellmanVar.val (some S) who))
      (𝓝[>] (0 : ℝ)) (𝓝 (reward S who)) :=
    hconstant.congr' (Filter.EventuallyEq.symm heventually)
  exact tendsto_nhds_unique hcurve hsame

/-- The endpoint decoder still carries the actual absorbed reward table. -/
theorem quittingGerm_endpointDecodeValue_some_eq
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    (fun S => g.endpointValue (some S)) = reward := by
  funext S who
  exact quittingGerm_assignment_val_some_zero g S who

/-- The endpoint root's quit mass is the quit-rate germ evaluated at zero. -/
theorem quittingGerm_endpointProfile_apply_true_toReal
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) :
    ((g.endpointProfile none who) true).toReal = quittingGermQuitRate g who 0 := by
  simpa [StochasticGame.AnalyticBellmanGerm.endpointProfile,
    StochasticGame.AnalyticBellmanGerm.endpoint,
    quittingGermQuitRate] using
    ((quittingGame reward).bellmanDecodeProfile_apply_toReal
      g.endpoint_isPolynomialBellmanSolution none who true)

/-- The active endpoint value is `quittingGermValue g 0`. -/
@[simp] theorem quittingGerm_endpointValue_none
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    g.endpointValue none = quittingGermValue g 0 :=
  rfl

/-- At the analytic endpoint, the active value and endpoint profile solve the
undiscounted quitting successor equation with the pinned reward table. -/
theorem quittingGerm_endpoint_fixedPoint
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    quittingGermValue g 0 =
      quittingRootSuccessorPayoff reward (quittingGermValue g 0)
        (g.endpointProfile none) := by
  have hvalue := g.isDiscountedStationaryBellmanEq_endpoint.2 none
  funext who
  have hwho := hvalue who
  rw [discountedAuxEU_quittingGame_none,
    quittingGerm_endpointDecodeValue_some_eq] at hwho
  simpa [quittingRootSuccessorPayoff] using hwho.symm

/-- The endpoint profile is an exact quitting root equilibrium against its
active endpoint value. -/
theorem quittingGerm_endpoint_endpointNash
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    IsεQuittingRootEndpointNash reward (quittingGermValue g 0) 0
      (g.endpointProfile none) := by
  have hrec : ∀ who,
      quittingGermValue g 0 who =
        1 * quittingRootSuccessorPayoff reward (quittingGermValue g 0)
          (g.endpointProfile none) who := by
    intro who
    simpa using congrFun (quittingGerm_endpoint_fixedPoint g) who
  apply (isεQuittingRootEndpointNash_zero_iff_of_rootRecursion reward 1
    (by norm_num) (quittingGermValue g 0) (g.endpointProfile none) hrec).2
  intro who
  have hEq := g.isDiscountedStationaryBellmanEq_endpoint
  have hon := hEq.2 none who
  have hquit := hEq.1 none who (PMF.pure true)
  have hcontinue := hEq.1 none who (PMF.pure false)
  rw [hon] at hquit hcontinue
  rw [discountedAuxEU_quittingGame_none,
    quittingGerm_endpointDecodeValue_some_eq] at hquit hcontinue
  simp only [quittingGerm_endpointValue_none] at hquit hcontinue
  have heta : (fun j : ι => quittingGermValue g 0 j) =
      quittingGermValue g 0 := by
    funext j
    rfl
  rw [heta] at hquit hcontinue
  constructor
  · convert hquit using 1
    · simp only [one_mul, quittingRootQuitPayoff]
      apply congrArg (fun root : ι → PMF Bool =>
        quittingRootExpectedPayoff reward (quittingGermValue g 0) root who)
      funext player
      by_cases hp : player = who
      · subst player
        simp only [Function.update_self]
        with_unfolding_all
          rfl
      · simp [Function.update_of_ne hp]
  · convert hcontinue using 1
    · simp only [one_mul, quittingRootContinuePayoff]
      apply congrArg (fun root : ι → PMF Bool =>
        quittingRootExpectedPayoff reward (quittingGermValue g 0) root who)
      funext player
      by_cases hp : player = who
      · subst player
        simp only [Function.update_self]
        with_unfolding_all
          rfl
      · simp [Function.update_of_ne hp]

/-! ## Punishment normalization -/

/-- The exact punishment value of the original table. -/
def quittingAuxiliaryPunishment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Payoff ι :=
  fun who => quittingPunishmentValue reward who

/-- Solan's live anchor, clipped at zero. -/
def quittingAuxiliaryLive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Payoff ι :=
  fun who => min 0 (quittingAuxiliaryPunishment reward who)

/-- The zero-live auxiliary quitting table. -/
def quittingAuxiliaryReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  quittingRewardShift reward (quittingAuxiliaryLive reward)

/-- Convert a shifted endpoint value back to original reward coordinates. -/
def quittingAuxiliaryTarget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) : Payoff ι :=
  quittingPayoffUnshift (quittingAuxiliaryLive reward) value

@[simp] theorem quittingAuxiliaryLive_eq_punishment_of_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (hchi : quittingPunishmentValue reward who ≤ 0) :
    quittingAuxiliaryLive reward who = quittingPunishmentValue reward who := by
  simp [quittingAuxiliaryLive, quittingAuxiliaryPunishment, min_eq_right hchi]

@[simp] theorem quittingAuxiliaryLive_eq_zero_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (hchi : 0 < quittingPunishmentValue reward who) :
    quittingAuxiliaryLive reward who = 0 := by
  simp [quittingAuxiliaryLive, quittingAuxiliaryPunishment,
    min_eq_left hchi.le]

theorem quittingAuxiliaryLive_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingAuxiliaryLive reward who ≤ 0 :=
  min_le_left _ _

/-! ## The punctured nonnegativity lemma -/

/-- The original pure-Quit stationary endpoint is the original root's
fixed-opponents quit value. -/
theorem quittingRootQuitPayoff_eq_stationaryFixedOpponentsQuitValue'
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward value root who =
      quittingStationaryFixedOpponentsQuitValue reward root who := by
  simpa [quittingStationaryFixedOpponentsQuitValue] using
    (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (fun _ => root) who value 0)

/-- The original pure-Continue endpoint splits into the opponent absorption
reward and the opponent continuation coefficient. -/
theorem quittingRootContinuePayoff_eq_stationaryFixedOpponents'
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff reward value root who =
      quittingStationaryFixedOpponentsContinueReward reward root who +
        quittingStationaryFixedOpponentsContinueMass root who * value who := by
  simpa [quittingStationaryFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass] using
    (quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who value 0)

/-- If all opponents continue surely, quitting now yields exactly the solo
terminal reward. -/
theorem quittingStationaryFixedOpponentsQuitValue_eq_solo_of_mass_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hmass : quittingStationaryFixedOpponentsContinueMass root who = 1) :
    quittingStationaryFixedOpponentsQuitValue reward root who =
      reward (quittingSingletonTerminal who) who := by
  have hopponents :=
    opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
      root who hmass
  have hroot : Function.update root who (PMF.pure true) =
      quittingPureSetRoot ({who} : Finset ι) := by
    funext player
    by_cases hp : player = who
    · subst player
      simp [quittingPureSetRoot, quittingSetAction]
    · rw [Function.update_of_ne hp, hopponents player hp]
      simp [quittingPureSetRoot, quittingSetAction, hp]
  change quittingRootAbsorbingContribution reward
      (Function.update root who (PMF.pure true)) who = _
  rw [hroot, quittingRootAbsorbingContribution_pureSetRoot]
  rw [quittingSetReward_of_nonempty reward (Finset.singleton_nonempty who)]
  rfl

/-- If a player's original punishment value is nonpositive, every genuine
discounted point of the auxiliary analytic germ has a nonnegative value in
that coordinate. -/
theorem quittingAuxiliaryGermValue_nonneg_of_punishment_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1)
    (who : ι) (hchi : quittingPunishmentValue reward who ≤ 0) :
    0 ≤ quittingGermValue g t who := by
  let root := quittingGermRoot g ht
  let W := quittingGermValue g t
  let chi := quittingPunishmentValue reward who
  let live := quittingAuxiliaryLive reward
  let c := quittingStationaryFixedOpponentsContinueMass root who
  let S := quittingStationaryFixedOpponentsQuitValue reward root who
  let H := quittingStationaryFixedOpponentsContinueReward reward root who
  let beta := 1 - t ^ g.ramification
  have hbeta : 0 < beta := quittingGerm_discountFactor_pos g ht ht1
  have hbeta_le : beta ≤ 1 := by
    dsimp only [beta]
    exact sub_le_self _ (pow_nonneg ht.1.le _)
  have hc0 : 0 ≤ c :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root who
  have hc1 : c ≤ 1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hchiCap : chi ≤ quittingStationaryUnilateralCap reward root who :=
    quittingPunishmentValue_le_stationaryUnilateralCap reward who root
  have hlive : live who = chi := by
    exact quittingAuxiliaryLive_eq_punishment_of_nonpos reward who hchi
  by_cases hcontract : c < 1
  · rw [quittingStationaryUnilateralCap_eq_max_div] at hchiCap
    by_cases hbranch : S ≤ H / (1 - c)
    · have hH : 0 ≤ H - (1 - c) * chi := by
        have hden : 0 < 1 - c := sub_pos.mpr hcontract
        rw [max_eq_right hbranch] at hchiCap
        rw [le_div_iff₀ hden] at hchiCap
        linarith
      have hcontinue := quittingGerm_bestResponse_continue g ht who
      have hshift := quittingRootContinuePayoff_shift reward live W root who
      have horiginal :=
        quittingRootContinuePayoff_eq_stationaryFixedOpponents'
          reward (quittingPayoffUnshift live W) root who
      change beta *
          quittingRootContinuePayoff (quittingAuxiliaryReward reward) W root who ≤
        W who at hcontinue
      change beta *
          quittingRootContinuePayoff (quittingRewardShift reward live) W root who ≤
        W who at hcontinue
      rw [hshift, horiginal] at hcontinue
      simp only [quittingPayoffUnshift_apply, hlive] at hcontinue
      have hcoef : 0 < 1 - beta * c := by
        have hbc : beta * c ≤ c := by
          simpa using mul_le_mul_of_nonneg_right hbeta_le hc0
        exact sub_pos.mpr (lt_of_le_of_lt hbc hcontract)
      have hrhs : 0 ≤ beta * (H - (1 - c) * chi) :=
        mul_nonneg hbeta.le hH
      have hkey : beta * (H - (1 - c) * chi) ≤
          (1 - beta * c) * W who := by
        dsimp only [W, root, live, c, H, beta, chi] at *
        linarith
      exact nonneg_of_mul_nonneg_right (le_trans hrhs hkey) hcoef
    · have hS : 0 ≤ S - chi := by
        rw [max_eq_left (le_of_not_ge hbranch)] at hchiCap
        linarith
      have hquit := quittingGerm_bestResponse_quit g ht who
      have hshift := quittingRootQuitPayoff_shift reward live W root who
      have horiginal :=
        quittingRootQuitPayoff_eq_stationaryFixedOpponentsQuitValue'
          reward (quittingPayoffUnshift live W) root who
      change beta *
          quittingRootQuitPayoff (quittingAuxiliaryReward reward) W root who ≤
        W who at hquit
      change beta *
          quittingRootQuitPayoff (quittingRewardShift reward live) W root who ≤
        W who at hquit
      rw [hshift, horiginal] at hquit
      simp only [hlive] at hquit
      exact le_trans (mul_nonneg hbeta.le hS) hquit
  · have hc : c = 1 := le_antisymm hc1 (not_lt.mp hcontract)
    have hH : H = 0 := by
      exact quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
        reward hc
    have hcontinue := quittingGerm_bestResponse_continue g ht who
    have hshift := quittingRootContinuePayoff_shift reward live W root who
    have horiginal :=
      quittingRootContinuePayoff_eq_stationaryFixedOpponents'
        reward (quittingPayoffUnshift live W) root who
    change beta *
        quittingRootContinuePayoff (quittingAuxiliaryReward reward) W root who ≤
      W who at hcontinue
    change beta *
        quittingRootContinuePayoff (quittingRewardShift reward live) W root who ≤
      W who at hcontinue
    rw [hshift, horiginal] at hcontinue
    have hc' : quittingStationaryFixedOpponentsContinueMass root who = 1 := hc
    have hH' : quittingStationaryFixedOpponentsContinueReward reward root who = 0 := hH
    simp only [quittingPayoffUnshift_apply, hlive] at hcontinue
    rw [hc', hH'] at hcontinue
    ring_nf at hcontinue
    have hgap : 0 < 1 - beta := by
      dsimp only [beta]
      simpa using pow_pos ht.1 g.ramification
    nlinarith

/-- The punctured nonnegativity passes to the analytic endpoint. -/
theorem quittingAuxiliaryGermValue_zero_nonneg_of_punishment_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    (who : ι) (hchi : quittingPunishmentValue reward who ≤ 0) :
    0 ≤ quittingGermValue g 0 who := by
  have hvalue := quittingGermValue_tendsto_zero g who
  have heventually :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ quittingGermValue g t who := by
    have hltOne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
        Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
          nhdsWithin_le_nhds
    filter_upwards [eventually_mem_Ioo_radius g, hltOne] with t ht ht1
    exact quittingAuxiliaryGermValue_nonneg_of_punishment_nonpos
      reward g ht ht1 who hchi
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hvalue heventually

/-- In the nonpositive-punishment regime, the original target reconstructed
from an auxiliary endpoint dominates the punishment value. -/
theorem quittingPunishmentValue_le_auxiliaryTarget_of_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    (who : ι) (hchi : quittingPunishmentValue reward who ≤ 0) :
    quittingPunishmentValue reward who ≤
      quittingAuxiliaryTarget reward (quittingGermValue g 0) who := by
  have hW :=
    quittingAuxiliaryGermValue_zero_nonneg_of_punishment_nonpos reward g who hchi
  simp only [quittingAuxiliaryTarget, quittingPayoffUnshift_apply,
    quittingAuxiliaryLive_eq_punishment_of_nonpos reward who hchi]
  linarith

/-! ## Endpoint target floor and absorbing endpoint compiler -/

/-- The auxiliary endpoint translated to the original table dominates every
player's exact quitting punishment value. -/
theorem quittingPunishmentValue_le_auxiliaryEndpointTarget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    (who : ι) :
    quittingPunishmentValue reward who ≤
      quittingAuxiliaryTarget reward (quittingGermValue g 0) who := by
  by_cases hchi : quittingPunishmentValue reward who ≤ 0
  · exact quittingPunishmentValue_le_auxiliaryTarget_of_nonpos
      reward g who hchi
  · have hchipos : 0 < quittingPunishmentValue reward who := lt_of_not_ge hchi
    have hlive := quittingAuxiliaryLive_eq_zero_of_pos reward who hchipos
    let root : ι → PMF Bool := g.endpointProfile none
    let W := quittingGermValue g 0
    have hfixed := quittingGerm_endpoint_fixedPoint g
    have hnash := quittingGerm_endpoint_endpointNash g
    by_cases hcontract :
        quittingStationaryFixedOpponentsContinueMass root who < 1
    · have hrootNash : IsεQuittingRootNash
          (quittingAuxiliaryReward reward) W 0 root :=
        (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          (quittingAuxiliaryReward reward) W root).mp hnash
      obtain ⟨hquitShift, hcontinueShift⟩ :=
        quittingStationaryEndpointBounds_of_fixedPoint_rootNash
          (quittingAuxiliaryReward reward) root W hfixed hrootNash who
      let target := quittingPayoffUnshift (quittingAuxiliaryLive reward) W
      have hquitTranslate := quittingRootQuitPayoff_shift reward
        (quittingAuxiliaryLive reward) W root who
      have hcontinueTranslate := quittingRootContinuePayoff_shift reward
        (quittingAuxiliaryLive reward) W root who
      have hS :
          quittingStationaryFixedOpponentsQuitValue
              (quittingAuxiliaryReward reward) root who =
            quittingStationaryFixedOpponentsQuitValue reward root who := by
        rw [← quittingRootQuitPayoff_eq_stationaryFixedOpponentsQuitValue'
          (quittingAuxiliaryReward reward) W root who,
          ← quittingRootQuitPayoff_eq_stationaryFixedOpponentsQuitValue'
            reward target root who]
        simpa [quittingAuxiliaryReward, target, hlive] using hquitTranslate
      have hH :
          quittingStationaryFixedOpponentsContinueReward
              (quittingAuxiliaryReward reward) root who =
            quittingStationaryFixedOpponentsContinueReward reward root who := by
        have haux := quittingRootContinuePayoff_eq_stationaryFixedOpponents'
          (quittingAuxiliaryReward reward) W root who
        have horiginal := quittingRootContinuePayoff_eq_stationaryFixedOpponents'
          reward target root who
        change quittingRootContinuePayoff (quittingAuxiliaryReward reward) W root who =
          quittingRootContinuePayoff reward target root who -
            quittingAuxiliaryLive reward who at hcontinueTranslate
        rw [haux, horiginal] at hcontinueTranslate
        simp only [target, quittingPayoffUnshift_apply, hlive, add_zero,
          sub_zero] at hcontinueTranslate
        linarith
      rw [hS] at hquitShift
      rw [hH] at hcontinueShift
      have hcap : quittingStationaryUnilateralCap reward root who ≤ W who := by
        simpa [quittingStationaryUnilateralCap] using
          quittingStationarySelectedCap_le_of_endpointBounds
            hcontract hquitShift hcontinueShift
      have hchiCap :=
        quittingPunishmentValue_le_stationaryUnilateralCap reward who root
      simp only [quittingAuxiliaryTarget, quittingPayoffUnshift_apply, hlive,
        add_zero]
      exact le_trans hchiCap hcap
    · have hmassLe :=
        quittingStationaryFixedOpponentsContinueMass_le_one root who
      have hmass : quittingStationaryFixedOpponentsContinueMass root who = 1 :=
        le_antisymm hmassLe (not_lt.mp hcontract)
      have hpure := opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
        root who hmass
      have hsoloBound := quittingPunishmentValue_le_max_solo reward who
      have hsoloPos : 0 < reward (quittingSingletonTerminal who) who := by
        by_contra hnot
        have : reward (quittingSingletonTerminal who) who ≤ 0 := not_lt.mp hnot
        have hmax : max (quittingSetReward reward ({who} : Finset ι) who) 0 = 0 := by
          have hset : quittingSetReward reward ({who} : Finset ι) who =
              reward (quittingSingletonTerminal who) who := by
            rw [quittingSetReward_of_nonempty reward (Finset.singleton_nonempty who)]
            rfl
          rw [hset, max_eq_right this]
        rw [hmax] at hsoloBound
        linarith
      have hsoloLe :
          reward (quittingSingletonTerminal who) who ≤ W who := by
        have hrootNash :=
          (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
            (quittingAuxiliaryReward reward) W root).mp hnash
        have hquit := hrootNash who (PMF.pure true)
        change quittingRootQuitPayoff (quittingAuxiliaryReward reward) W root who ≤
          quittingRootSuccessorPayoff (quittingAuxiliaryReward reward) W root who + 0
            at hquit
        simp only [add_zero] at hquit
        rw [← congrFun hfixed who] at hquit
        have hquitEq := quittingRootQuitPayoff_eq_stationaryFixedOpponentsQuitValue'
          (quittingAuxiliaryReward reward) W root who
        rw [hquitEq] at hquit
        have hsoloToQuit :=
          quittingSetReward_singleton_sub_le_fixedOpponentsQuitValue
            (quittingAuxiliaryReward reward) root who
        rw [hmass] at hsoloToQuit
        norm_num at hsoloToQuit
        have hset :
            quittingSetReward (quittingAuxiliaryReward reward)
                ({who} : Finset ι) who =
              (quittingAuxiliaryReward reward)
                (quittingSingletonTerminal who) who := by
          rw [quittingSetReward_of_nonempty _ (Finset.singleton_nonempty who)]
          rfl
        have hauxSolo :
            (quittingAuxiliaryReward reward)
                (quittingSingletonTerminal who) who ≤
              quittingStationaryFixedOpponentsQuitValue
                (quittingAuxiliaryReward reward) root who := by
          rwa [← hset]
        have horiginalSolo :
            (quittingAuxiliaryReward reward)
                (quittingSingletonTerminal who) who =
              reward (quittingSingletonTerminal who) who := by
          simp [quittingAuxiliaryReward, quittingRewardShift, hlive]
        rw [horiginalSolo] at hauxSolo
        exact le_trans hauxSolo hquit
      simp only [quittingAuxiliaryTarget, quittingPayoffUnshift_apply, hlive,
        add_zero]
      exact le_trans (by
        have hset : quittingSetReward reward ({who} : Finset ι) who =
            reward (quittingSingletonTerminal who) who := by
          rw [quittingSetReward_of_nonempty reward (Finset.singleton_nonempty who)]
          rfl
        rw [hset, max_eq_left hsoloPos.le] at hsoloBound
        exact hsoloBound) hsoloLe

/-- Every coordinate of the normalized analytic endpoint is nonnegative. -/
theorem quittingAuxiliaryGermValue_zero_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    (who : ι) :
    0 ≤ quittingGermValue g 0 who := by
  by_cases hchi : quittingPunishmentValue reward who ≤ 0
  · exact quittingAuxiliaryGermValue_zero_nonneg_of_punishment_nonpos
      reward g who hchi
  · have hchipos : 0 < quittingPunishmentValue reward who := lt_of_not_ge hchi
    have hfloor := quittingPunishmentValue_le_auxiliaryEndpointTarget reward g who
    simp only [quittingAuxiliaryTarget, quittingPayoffUnshift_apply,
      quittingAuxiliaryLive_eq_zero_of_pos reward who hchipos, add_zero] at hfloor
    exact le_trans hchipos.le hfloor

omit [DecidableEq ι] in
/-- A product root with unit all-Continue mass is the pure all-Continue root. -/
theorem quittingRoot_eq_allContinue_of_continueMass_eq_one
    (root : ι → PMF Bool)
    (hmass : quittingStationaryContinueMass root = 1) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  funext who
  exact eq_pure_false_of_quittingStationaryContinueMass_eq_one hmass who

/-- On an all-Continue auxiliary endpoint, every original solo payoff is
below the translated original target. -/
theorem quittingSolo_le_auxiliaryEndpointTarget_of_continueMass_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    (hmass : quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (who : ι) :
    reward (quittingSingletonTerminal who) who ≤
      quittingAuxiliaryTarget reward (quittingGermValue g 0) who := by
  let root : ι → PMF Bool := g.endpointProfile none
  let W := quittingGermValue g 0
  let live := quittingAuxiliaryLive reward
  let target := quittingAuxiliaryTarget reward W
  have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) :=
    quittingRoot_eq_allContinue_of_continueMass_eq_one root hmass
  have hnashShift := quittingGerm_endpoint_endpointNash g
  have hnash : IsεQuittingRootEndpointNash reward target 0 root :=
    (isεQuittingRootEndpointNash_zero_shift_iff reward live W root).mp hnashShift
  have hwho := (hnash who).1
  rw [hroot, quittingRootEndpointDifference_allContinueRoot] at hwho
  simpa [quittingAllContinueRoot] using hwho

/-- If the auxiliary shifted table is zero-solo, then so is the original
table, because every live anchor is nonpositive. -/
theorem isQuittingZeroSolo_of_auxiliaryReward_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hzero : IsQuittingZeroSolo (quittingAuxiliaryReward reward)) :
    IsQuittingZeroSolo reward := by
  intro who
  have h := hzero who
  have hlive := quittingAuxiliaryLive_nonpos reward who
  change reward (quittingSingletonTerminal who) who -
      quittingAuxiliaryLive reward who ≤ 0 at h
  linarith

/-- A jointly absorbing endpoint of the auxiliary germ compiles, after
translation, to a uniform-equilibrium payoff of the original quitting game. -/
theorem isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    (habsorbs : quittingStationaryContinueMass (g.endpointProfile none) < 1) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingAuxiliaryTarget reward (quittingGermValue g 0)) := by
  let root : ι → PMF Bool := g.endpointProfile none
  let W := quittingGermValue g 0
  let live := quittingAuxiliaryLive reward
  let target := quittingAuxiliaryTarget reward W
  have hfixedShift := quittingGerm_endpoint_fixedPoint g
  have hfixed : target = quittingRootSuccessorPayoff reward target root := by
    exact quittingRootFixedPoint_unshift reward live W root hfixedShift
  have hnashShift := quittingGerm_endpoint_endpointNash g
  have hnashEndpoint : IsεQuittingRootEndpointNash reward target 0 root := by
    exact (isεQuittingRootEndpointNash_zero_shift_iff reward live W root).mp
      hnashShift
  have hnash : IsεQuittingRootNash reward target 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward target root).mp hnashEndpoint
  let cycle : Fin 1 → ι → PMF Bool := fun _ => root
  let value : Fin 1 → Payoff ι := fun _ => target
  apply isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle
    reward cycle value 0
  · intro phase
    simpa [cycle, value, finRotate] using hfixed
  · intro phase
    simpa [cycle, value, finRotate] using hnash
  · simpa [cycle] using habsorbs
  · intro who
    by_cases hcontract :
        quittingStationaryFixedOpponentsContinueMass root who < 1
    · left
      simpa [cycle] using hcontract
    · right
      have hmassLe :=
        quittingStationaryFixedOpponentsContinueMass_le_one root who
      have hmass : quittingStationaryFixedOpponentsContinueMass root who = 1 :=
        le_antisymm hmassLe (not_lt.mp hcontract)
      have hopponents :=
        opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
          root who hmass
      have hrootQuit : 0 < ((root who) true).toReal := by
        by_contra hnot
        have hzero : ((root who) true).toReal = 0 :=
          le_antisymm (not_lt.mp hnot) ENNReal.toReal_nonneg
        have hcontinue : ((root who) false).toReal = 1 := by
          have hsum := quittingRoot_continueProbability_add_quitProbability root who
          linarith
        have hall : root = (quittingAllContinueRoot : ι → PMF Bool) := by
          funext player
          by_cases hp : player = who
          · subst player
            exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ hzero
          · exact hopponents player hp
        change quittingStationaryContinueMass root < 1 at habsorbs
        rw [hall, quittingStationaryContinueMass_eq_prod] at habsorbs
        simp [quittingAllContinueRoot] at habsorbs
      have hsolo : target who = reward (quittingSingletonTerminal who) who := by
        have hquitEq := quittingRootQuitPayoff_eq_stationaryFixedOpponentsQuitValue'
          reward target root who
        have hcontEq := quittingRootContinuePayoff_eq_stationaryFixedOpponents'
          reward target root who
        have hH := quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
          reward hmass
        have hS : quittingStationaryFixedOpponentsQuitValue reward root who =
            reward (quittingSingletonTerminal who) who :=
          quittingStationaryFixedOpponentsQuitValue_eq_solo_of_mass_eq_one
            reward root who hmass
        have htargetFixed := congrFun hfixed who
        rw [quittingRootSuccessorPayoff_eq_endpointMix] at htargetFixed
        rw [hquitEq, hcontEq, hH, hmass, hS] at htargetFixed
        simp only [zero_add, one_mul] at htargetFixed
        have hsum := quittingRoot_continueProbability_add_quitProbability root who
        have hq : ((root who) true).toReal =
            1 - ((root who) false).toReal := by
          linarith
        have hproduct : ((root who) true).toReal *
            (target who - reward (quittingSingletonTerminal who) who) = 0 := by
          calc
            ((root who) true).toReal *
                  (target who - reward (quittingSingletonTerminal who) who) =
                (1 - ((root who) false).toReal) *
                  (target who - reward (quittingSingletonTerminal who) who) := by
                    rw [hq]
            _ = target who -
                ((1 - ((root who) false).toReal) *
                    reward (quittingSingletonTerminal who) who +
                  ((root who) false).toReal * target who) := by ring
            _ = target who -
                (((root who) true).toReal *
                    reward (quittingSingletonTerminal who) who +
                  ((root who) false).toReal * target who) := by rw [← hq]
            _ = 0 := by rw [← htargetFixed]; ring
        have hdiff := (mul_eq_zero.mp hproduct).resolve_left hrootQuit.ne'
        linarith
      rw [← hsolo]
      exact quittingPunishmentValue_le_auxiliaryEndpointTarget reward g who

end GameTheory
