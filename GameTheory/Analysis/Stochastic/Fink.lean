/-
# General-sum discounted stationary Bellman equilibria

The fixed-point construction uses the canonical `FinDist`, `UtilityGame`,
mixed Nash predicate, profile update, simplex bridge, and one-way analytic
fixed-point dependency.

Primary reference: A. M. Fink, “Equilibrium in a Stochastic n-Person Game,”
*Journal of Science of the Hiroshima University, Series A-I* 28 (1964).
-/

import GameTheory.Analysis.Nash
import GameTheory.Core.MixedImprovement
import GameTheory.Stochastic.Basic
import GameTheory.Math.PositivePartFixedPoint

noncomputable section

open scoped BigOperators

namespace GameTheory.Stochastic.Game

open GameTheory.Math.Probability

universe uι us ua

variable {ι : Type uι} (G : Game.{uι, us, ua} ι)

/-- A state-dependent mixed action profile. -/
abbrev StationaryMixedProfile : Type _ :=
  G.State → ∀ player, FinDist (G.Action player)

/-- The one-stage simultaneous-action signature of a stochastic game. -/
abbrev actionSignature : GameSignature ι where
  Strategy := G.Action
  Outcome := ∀ player, G.Action player

/-- Pure joint actions evaluate to themselves. -/
abbrev actionForm : GameForm ι where
  sig := G.actionSignature
  play joint := FinDist.pure joint

/-- The normalized one-step utility with continuation value `value`. -/
def discountedAuxUtility (β : ℝ) (value : G.State → ι → ℝ)
    (state : G.State) (joint : ∀ player, G.Action player)
    (who : ι) : ℝ :=
  (1 - β) * G.stageUtility state joint who +
    β * (G.transition state joint).expect (fun next => value next who)

/-- The finite auxiliary normal-form game at one state. -/
abbrev discountedAuxGame (β : ℝ) (value : G.State → ι → ℝ)
    (state : G.State) : UtilityGame ι where
  form := G.actionForm
  utility := G.discountedAuxUtility β value state

/-- State-player agents index the action simplices in Fink's domain. -/
abbrev FinkAgent := G.State × ι

/-- One action carrier for each state-player agent. -/
abbrev finkSignature : GameSignature.{max us uι, ua, 0} G.FinkAgent where
  Strategy agent := G.Action agent.2
  Outcome := PUnit

/-- Ambient strategy weights and state-contingent continuation values. -/
abbrev FinkAmbient : Type _ :=
  Profile G.finkSignature.weights × (G.State → ι → ℝ)

/-- Product of the stationary mixed-action polytope and a bounded value cube. -/
def finkDomain [Fintype G.State] [Fintype ι]
    [∀ player, Fintype (G.Action player)] (bound : ℝ) : Set G.FinkAmbient :=
  mixedPolytope G.finkSignature ×ˢ
    Set.Icc (fun _ _ => -bound) (fun _ _ => bound)

theorem convex_finkDomain [Fintype G.State] [Fintype ι]
    [∀ player, Fintype (G.Action player)] (bound : ℝ) :
    Convex ℝ (G.finkDomain bound) :=
  (convex_mixedPolytope G.finkSignature).prod
    (convex_Icc (fun _ : G.State => fun _ : ι => -bound)
      (fun _ => fun _ => bound))

theorem isCompact_finkDomain [Fintype G.State] [Fintype ι]
    [∀ player, Fintype (G.Action player)] (bound : ℝ) :
    IsCompact (G.finkDomain bound) :=
  (isCompact_mixedPolytope G.finkSignature).prod isCompact_Icc

theorem nonempty_finkDomain [Fintype G.State] [Fintype ι]
    [∀ player, Fintype (G.Action player)]
    [∀ player, Nonempty (G.Action player)] {bound : ℝ}
    (hbound : 0 ≤ bound) : (G.finkDomain bound).Nonempty := by
  refine ⟨(probs G.finkSignature fun agent =>
      FinDist.pure (Classical.arbitrary (G.Action agent.2)), 0), ?_, ?_⟩
  · exact probs_mem_mixedPolytope G.finkSignature _
  · constructor <;> intro state who <;> simp [hbound]

/-- The real action weights at one state. -/
def finkStateWeights [Fintype G.State] [Fintype ι]
    [∀ player, Fintype (G.Action player)] {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) :
    Profile G.actionSignature.weights :=
  fun player => point.1.1 (state, player)

theorem finkStateWeights_mem [Fintype G.State] [Fintype ι]
    [∀ player, Fintype (G.Action player)] {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) :
    G.finkStateWeights point state ∈ mixedPolytope G.actionSignature := by
  rw [mem_mixedPolytope]
  intro player
  exact (mem_mixedPolytope G.finkSignature).1 point.2.1 (state, player)

/-- Decode the stationary mixed profile represented by a domain point. -/
def finkProfile [Fintype G.State] [Fintype ι]
    [∀ player, Fintype (G.Action player)] {bound : ℝ}
    (point : G.finkDomain bound) : G.StationaryMixedProfile :=
  fun state => ofPolytope G.actionSignature (G.finkStateWeights_mem point state)

@[simp]
theorem finkProfile_prob [Fintype G.State] [Fintype ι]
    [∀ player, Fintype (G.Action player)] {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι) :
    (G.finkProfile point state who).prob =
      G.finkStateWeights point state who := by
  exact congrFun (probs_ofPolytope G.actionSignature
    (G.finkStateWeights_mem point state)) who

/-- Decode the continuation-value coordinate. -/
def finkValue [Fintype G.State] [Fintype ι]
    [∀ player, Fintype (G.Action player)] {bound : ℝ}
    (point : G.finkDomain bound) : G.State → ι → ℝ :=
  point.1.2

/-- The on-profile auxiliary expected payoff in real simplex coordinates. -/
def finkAuxPayoff [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι) : ℝ :=
  payoff G.actionForm
    (G.discountedAuxUtility β (G.finkValue point) state) who
    (G.finkStateWeights point state)

/-- The auxiliary payoff after one pure deviation, in finite coordinates. -/
def finkDeviationPayoff [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι)
    (action : G.Action who) : ℝ :=
  ∑ joint : ∀ player, G.Action player,
    (FinDist.pure action).prob (joint who) *
      ((∏ player ∈ Finset.univ.erase who,
          G.finkStateWeights point state player (joint player)) *
        G.discountedAuxUtility β (G.finkValue point) state joint who)

theorem finkDeviationPayoff_eq_payoff_update [Fintype G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι)
    (action : G.Action who) :
    G.finkDeviationPayoff β point state who action =
      payoff G.actionForm
        (G.discountedAuxUtility β (G.finkValue point) state) who
        (Profile.update (G.finkStateWeights point state) who
          (FinDist.pure action).prob) := by
  rw [payoff_update]
  unfold finkDeviationPayoff actionForm expectedUtility
  simp

theorem finkAuxPayoff_eq_expectedUtility [Fintype G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι) :
    G.finkAuxPayoff β point state who =
      expectedUtility (G.discountedAuxGame β (G.finkValue point) state).utility who
        ((G.discountedAuxGame β (G.finkValue point) state).form.mixed.play
          (G.finkProfile point state)) := by
  unfold finkAuxPayoff discountedAuxGame
  rw [← payoff_probs]
  congr 1
  exact (probs_ofPolytope G.actionSignature
    (G.finkStateWeights_mem point state)).symm

theorem finkDeviationPayoff_eq_expectedUtility [Fintype G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι)
    (action : G.Action who) :
    G.finkDeviationPayoff β point state who action =
      expectedUtility (G.discountedAuxGame β (G.finkValue point) state).utility who
        ((G.discountedAuxGame β (G.finkValue point) state).form.mixed.play
          (Profile.update (G.finkProfile point state) who
            (FinDist.pure action))) := by
  rw [G.finkDeviationPayoff_eq_payoff_update]
  unfold discountedAuxGame
  rw [← payoff_probs, probs_update]
  congr 1
  exact congrArg (fun weights =>
    Profile.update weights who (FinDist.pure action).prob)
    (probs_ofPolytope G.actionSignature
      (G.finkStateWeights_mem point state)).symm

/-- Pure one-step gain in Fink's auxiliary game. -/
def finkGain [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι)
    (action : G.Action who) : ℝ :=
  G.finkDeviationPayoff β point state who action -
    G.finkAuxPayoff β point state who

theorem finkGain_eq_mixedGain [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (point : G.finkDomain bound)
    (state : G.State) (who : ι) (action : G.Action who) :
    G.finkGain β point state who action =
      (G.discountedAuxGame β (G.finkValue point) state).mixedGain
        (G.finkProfile point state) who action := by
  unfold finkGain UtilityGame.mixedGain
  rw [G.finkDeviationPayoff_eq_expectedUtility,
    G.finkAuxPayoff_eq_expectedUtility]

/-- Total positive auxiliary gain for one state-player agent. -/
def finkGainSum [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι) : ℝ :=
  ∑ action, max (G.finkGain β point state who action) 0

theorem finkGainSum_nonneg [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (point : G.finkDomain bound)
    (state : G.State) (who : ι) :
    0 ≤ G.finkGainSum β point state who :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- One coordinate of Nash's positive-gain adjustment. -/
def finkStrategyWeightUpdate [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (point : G.finkDomain bound)
    (state : G.State) (who : ι) (action : G.Action who) : ℝ :=
  (G.finkStateWeights point state who action +
      max (G.finkGain β point state who action) 0) /
    (1 + G.finkGainSum β point state who)

theorem finkStrategyUpdate_mem [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (point : G.finkDomain bound)
    (state : G.State) (who : ι) :
    (fun action => G.finkStrategyWeightUpdate β point state who action) ∈
      stdSimplex ℝ (G.Action who) := by
  constructor
  · intro action
    apply div_nonneg
    · exact add_nonneg
        (((mem_mixedPolytope G.actionSignature).1
          (G.finkStateWeights_mem point state) who).1 action)
        (le_max_right _ _)
    · linarith [G.finkGainSum_nonneg β point state who]
  · have hden : 1 + G.finkGainSum β point state who ≠ 0 := by
      linarith [G.finkGainSum_nonneg β point state who]
    simp only [finkStrategyWeightUpdate]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [show ∑ action : G.Action who,
        G.finkStateWeights point state who action = 1 by
      exact ((mem_mixedPolytope G.actionSignature).1
        (G.finkStateWeights_mem point state) who).2]
    exact div_self hden

theorem continuous_finkAuxPayoff [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (state : G.State) (who : ι) :
    Continuous (fun point : G.finkDomain bound =>
      G.finkAuxPayoff β point state who) := by
  unfold finkAuxPayoff payoff actionForm expectedUtility
    discountedAuxUtility finkStateWeights finkValue
  simp_rw [FinDist.expect_pure, FinDist.expect_eq_sum]
  fun_prop

theorem continuous_finkDeviationPayoff [Fintype G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (state : G.State) (who : ι) (action : G.Action who) :
    Continuous (fun point : G.finkDomain bound =>
      G.finkDeviationPayoff β point state who action) := by
  unfold finkDeviationPayoff discountedAuxUtility finkStateWeights finkValue
  simp_rw [FinDist.expect_eq_sum]
  fun_prop

theorem continuous_finkGain [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (state : G.State) (who : ι)
    (action : G.Action who) :
    Continuous (fun point : G.finkDomain bound =>
      G.finkGain β point state who action) :=
  (G.continuous_finkDeviationPayoff β state who action).sub
    (G.continuous_finkAuxPayoff β state who)

theorem continuous_finkGainSum [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (state : G.State) (who : ι) :
    Continuous (fun point : G.finkDomain bound =>
      G.finkGainSum β point state who) := by
  unfold finkGainSum
  exact continuous_finsetSum _ fun action _ =>
    (G.continuous_finkGain β state who action).max continuous_const

theorem continuous_finkStrategyWeightUpdate [Fintype G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (state : G.State) (who : ι) (action : G.Action who) :
    Continuous (fun point : G.finkDomain bound =>
      G.finkStrategyWeightUpdate β point state who action) := by
  unfold finkStrategyWeightUpdate
  have hweight : Continuous (fun point : G.finkDomain bound =>
      G.finkStateWeights point state who action) := by
    unfold finkStateWeights
    fun_prop
  exact (hweight.add
      ((G.continuous_finkGain β state who action).max continuous_const)).div
    (continuous_const.add (G.continuous_finkGainSum β state who))
    (fun point => by
      linarith [G.finkGainSum_nonneg β point state who])

theorem abs_discountedAuxUtility_le (β bound : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound)
    (value : G.State → ι → ℝ)
    (hvalue : ∀ state who, |value state who| ≤ bound)
    (state : G.State) (joint : ∀ player, G.Action player) (who : ι) :
    |G.discountedAuxUtility β value state joint who| ≤ bound := by
  have hweight : 0 ≤ 1 - β := sub_nonneg.mpr hβ1
  have hexpect :
      |(G.transition state joint).expect (fun next => value next who)| ≤ bound :=
    FinDist.abs_expect_le_of_abs_bound _ _
      (fun next _ => hvalue next who)
  calc
    |G.discountedAuxUtility β value state joint who| ≤
        |(1 - β) * G.stageUtility state joint who| +
          |β * (G.transition state joint).expect
            (fun next => value next who)| := abs_add_le _ _
    _ = (1 - β) * |G.stageUtility state joint who| +
          β * |(G.transition state joint).expect
            (fun next => value next who)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hweight, abs_of_nonneg hβ0]
    _ ≤ (1 - β) * bound + β * bound :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hstage state joint who) hweight)
        (mul_le_mul_of_nonneg_left hexpect hβ0)
    _ = bound := by ring

theorem abs_finkAuxPayoff_le [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β bound : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound)
    (point : G.finkDomain bound) (state : G.State) (who : ι) :
    |G.finkAuxPayoff β point state who| ≤ bound := by
  rw [G.finkAuxPayoff_eq_expectedUtility]
  unfold expectedUtility
  apply FinDist.abs_expect_le_of_abs_bound
  intro joint _
  exact G.abs_discountedAuxUtility_le β bound hβ0 hβ1 hstage
    (G.finkValue point)
    (fun next player => abs_le.mpr
      ⟨point.2.2.1 next player, point.2.2.2 next player⟩)
    state joint who

/-- The ambient-coordinate formula for Fink's joint strategy/value map. -/
def finkAmbientUpdate [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) : G.FinkAmbient :=
  (fun agent action =>
      G.finkStrategyWeightUpdate β point agent.1 agent.2 action,
    fun state who => G.finkAuxPayoff β point state who)

theorem finkAmbientUpdate_mem [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β bound : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound)
    (point : G.finkDomain bound) :
    G.finkAmbientUpdate β point ∈ G.finkDomain bound := by
  constructor
  · rw [mem_mixedPolytope]
    intro agent
    exact G.finkStrategyUpdate_mem β point agent.1 agent.2
  · constructor <;> intro state who
    · exact (abs_le.mp
        (G.abs_finkAuxPayoff_le β bound hβ0 hβ1 hstage point state who)).1
    · exact (abs_le.mp
        (G.abs_finkAuxPayoff_le β bound hβ0 hβ1 hstage point state who)).2

/-- Fink's continuous self-map of the compact strategy/value domain. -/
def finkMap [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)]
    (β bound : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound) :
    G.finkDomain bound → G.finkDomain bound :=
  fun point => ⟨G.finkAmbientUpdate β point,
    G.finkAmbientUpdate_mem β bound hβ0 hβ1 hstage point⟩

theorem continuous_finkMap [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β bound : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound) :
    Continuous (G.finkMap β bound hβ0 hβ1 hstage) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_pi fun agent => continuous_pi fun action =>
      G.continuous_finkStrategyWeightUpdate β agent.1 agent.2 action
  · exact continuous_pi fun state => continuous_pi fun who =>
      G.continuous_finkAuxPayoff β state who

theorem exists_finkMap_fixedPoint [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    [∀ player, Nonempty (G.Action player)]
    (β bound : ℝ) (hbound : 0 ≤ bound) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound) :
    ∃ point : G.finkDomain bound,
      G.finkMap β bound hβ0 hβ1 hstage point = point := by
  let map : C(G.finkDomain bound, G.finkDomain bound) :=
    ⟨G.finkMap β bound hβ0 hβ1 hstage,
      G.continuous_finkMap β bound hβ0 hβ1 hstage⟩
  exact _root_.brouwer_fixed_point (G.finkDomain bound)
    (G.convex_finkDomain bound) (G.isCompact_finkDomain bound)
    (G.nonempty_finkDomain hbound) map

/-- A stationary profile is Nash in every discounted auxiliary game and its
continuation values satisfy the corresponding Bellman equations. -/
def IsDiscountedStationaryBellmanEq [Fintype ι] [DecidableEq ι]
    (β : ℝ) (profile : G.StationaryMixedProfile)
    (value : G.State → ι → ℝ) : Prop :=
  (∀ state,
    IsNash (G.discountedAuxGame β value state).form.mixed
      (euPreference (G.discountedAuxGame β value state).utility)
      (profile state)) ∧
  ∀ state who,
    expectedUtility (G.discountedAuxGame β value state).utility who
      ((G.discountedAuxGame β value state).form.mixed.play
        (profile state)) = value state who

theorem isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)]
    (β bound : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound)
    (point : G.finkDomain bound)
    (hfixed : G.finkMap β bound hβ0 hβ1 hstage point = point) :
    G.IsDiscountedStationaryBellmanEq β (G.finkProfile point)
      (G.finkValue point) := by
  constructor
  · intro state
    rw [(G.discountedAuxGame β (G.finkValue point) state).isNash_iff_mixedGain_nonpos]
    intro who action
    rw [← G.finkGain_eq_mixedGain β point state who action]
    apply GameTheory.Math.all_nonpos_of_weighted_positivePart_fixedPoint
      (weight := fun candidate => (G.finkProfile point state who).prob candidate)
      (gain := fun candidate => G.finkGain β point state who candidate)
    · intro candidate
      have hcoordinate := congrArg
        (fun result : G.finkDomain bound => result.1.1 (state, who) candidate)
        hfixed
      have hden : 1 + G.finkGainSum β point state who ≠ 0 := by
        linarith [G.finkGainSum_nonneg β point state who]
      have hdivision :
          (G.finkStateWeights point state who candidate +
              max (G.finkGain β point state who candidate) 0) /
            (1 + G.finkGainSum β point state who) =
              G.finkStateWeights point state who candidate := by
        simpa [finkMap, finkAmbientUpdate, finkStrategyWeightUpdate,
          finkStateWeights] using hcoordinate
      rw [G.finkProfile_prob]
      exact (div_eq_iff hden).mp hdivision |>.symm
    · have hmean :=
        (G.discountedAuxGame β (G.finkValue point) state).expect_mixedGain_self_zero
          (G.finkProfile point state) who
      rw [FinDist.expect_eq_sum] at hmean
      calc
        ∑ candidate, (G.finkProfile point state who).prob candidate *
            G.finkGain β point state who candidate =
            ∑ candidate, (G.finkProfile point state who).prob candidate *
              (G.discountedAuxGame β (G.finkValue point) state).mixedGain
                (G.finkProfile point state) who candidate := by
          exact Finset.sum_congr rfl fun candidate _ => by
            rw [G.finkGain_eq_mixedGain]
        _ = 0 := hmean
  · intro state who
    have hcoordinate := congrArg
      (fun result : G.finkDomain bound => result.1.2 state who) hfixed
    rw [← G.finkAuxPayoff_eq_expectedUtility]
    simpa [finkMap, finkAmbientUpdate, finkValue] using hcoordinate

/-- A finite stochastic game admits a bounded stationary profile and value
function satisfying the statewise mixed-Nash and Bellman equations. This is the
stationary Bellman fixed-point conclusion; equilibrium against arbitrary
history-dependent deviations requires a separate one-shot-deviation theorem. -/
theorem exists_isDiscountedStationaryBellmanEq_bounded
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)]
    [∀ player, Nonempty (G.Action player)]
    (β bound : ℝ) (hbound : 0 ≤ bound) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound) :
    ∃ (profile : G.StationaryMixedProfile) (value : G.State → ι → ℝ),
      G.IsDiscountedStationaryBellmanEq β profile value ∧
        ∀ state who, |value state who| ≤ bound := by
  obtain ⟨point, hfixed⟩ :=
    G.exists_finkMap_fixedPoint β bound hbound hβ0 hβ1 hstage
  exact ⟨G.finkProfile point, G.finkValue point,
    G.isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
      β bound hβ0 hβ1 hstage point hfixed,
    fun state who => abs_le.mpr
      ⟨point.2.2.1 state who, point.2.2.2 state who⟩⟩

end GameTheory.Stochastic.Game
