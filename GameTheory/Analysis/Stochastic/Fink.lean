/-
# General-sum discounted stationary Bellman equilibria

The fixed-point construction uses the canonical `PMF`, `UtilityGame`,
mixed Nash predicate, profile update, simplex bridge, and one-way analytic
fixed-point dependency.

Primary reference: A. M. Fink, “Equilibrium in a Stochastic n-Person Game,”
*Journal of Science of the Hiroshima University, Series A-I* 28 (1964).
-/

import GameTheory.Analysis.Nash
import GameTheory.Core.MixedImprovement
import GameTheory.Stochastic.Basic
import GameTheory.Stochastic.OneStep
import GameTheory.Math.PositivePartFixedPoint

noncomputable section

open scoped BigOperators

namespace GameTheory.Stochastic.Game

open GameTheory.Math.Probability

universe uι us ua

variable {ι : Type uι} (G : Game.{uι, us, ua} ι)

/-- The normalized one-step utility with continuation value `value`. -/
def discountedAuxUtility (β : ℝ) (value : G.State → ι → ℝ)
    (state : G.State) (joint : ∀ player, G.Action player)
    (who : ι)
    (hintegrable : PayoffIntegrable (G.transition state joint)
      (fun next => value next who)) : ℝ :=
  G.normalizedOneStepUtility β (fun next => value next who)
    state joint who hintegrable

/-- A finite next-state carrier integrates each pure one-step law; the
joint-action outcome carrier itself need not be finite. -/
theorem discountedAuxIntegrable [Finite G.State] (β : ℝ)
    (value : G.State → ι → ℝ) (state : G.State) :
    (G.oneStepForm state).HasIntegrableUtility
      (G.discountedAuxGame β value state).utility := by
  intro who joint
  exact G.oneStepUtility_pure_integrable β value state joint who
    (payoffIntegrable_of_finite _ _)

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
def finkDomain (bound : ℝ) : Set G.FinkAmbient :=
  mixedPolytope G.finkSignature ×ˢ
    Set.Icc (fun _ _ => -bound) (fun _ _ => bound)

theorem convex_finkDomain
    [∀ player, Fintype (G.Action player)] (bound : ℝ) :
    Convex ℝ (G.finkDomain bound) :=
  (convex_mixedPolytope G.finkSignature).prod
    (convex_Icc (fun _ : G.State => fun _ : ι => -bound)
      (fun _ => fun _ => bound))

theorem isCompact_finkDomain
    [∀ player, Fintype (G.Action player)] (bound : ℝ) :
    IsCompact (G.finkDomain bound) :=
  (isCompact_mixedPolytope G.finkSignature).prod isCompact_Icc

theorem nonempty_finkDomain
    [∀ player, Fintype (G.Action player)]
    [∀ player, Nonempty (G.Action player)] {bound : ℝ}
    (hbound : 0 ≤ bound) : (G.finkDomain bound).Nonempty := by
  refine ⟨(probs G.finkSignature fun agent =>
      PMF.pure (Classical.arbitrary (G.Action agent.2)), 0), ?_, ?_⟩
  · exact probs_mem_mixedPolytope G.finkSignature _
  · constructor <;> intro state who <;> simp [hbound]

/-- The real action weights at one state. -/
def finkStateWeights {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) :
    Profile G.oneStepSignature.weights :=
  fun player => point.1.1 (state, player)

theorem finkStateWeights_mem {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) :
    G.finkStateWeights point state ∈ mixedPolytope G.oneStepSignature := by
  rw [mem_mixedPolytope]
  intro player
  exact (mem_mixedPolytope G.finkSignature).1 point.2.1 (state, player)

/-- Decode the stationary mixed profile represented by a domain point. -/
def finkProfile
    [∀ player, Fintype (G.Action player)] {bound : ℝ}
    (point : G.finkDomain bound) : G.StationaryMixedProfile :=
  fun state => ofPolytope G.oneStepSignature (G.finkStateWeights_mem point state)

@[simp]
theorem finkProfile_toReal
    [∀ player, Fintype (G.Action player)] {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι)
    (action : G.Action who) :
    (G.finkProfile point state who action).toReal =
      G.finkStateWeights point state who action := by
  exact congrFun (congrFun (probs_ofPolytope G.oneStepSignature
    (G.finkStateWeights_mem point state)) who) action

/-- Decode the continuation-value coordinate. -/
def finkValue {bound : ℝ}
    (point : G.finkDomain bound) : G.State → ι → ℝ :=
  point.1.2

variable [Fintype G.State]

/-- Finite actions and states integrate every mixed one-step outcome law. -/
theorem discountedAuxMixedIntegrable [Fintype ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ)
    (value : G.State → ι → ℝ) (state : G.State) (who : ι)
    (profile : Profile G.oneStepSignature.mixed) :
    UtilityIntegrable (G.discountedAuxGame β value state).utility who
      ((G.discountedAuxGame β value state).form.mixed.play profile) :=
  (GameForm.HasIntegrableUtility.mixed_of_finite
    (G.discountedAuxIntegrable β value state)) who profile

omit [Fintype G.State] in
/-- Fink's finite coordinates use the scalar expectation of the actual
stochastic pure outcome law. -/
theorem discountedAuxPurePayoff_eq_scalar [Finite G.State] (β : ℝ)
    (value : G.State → ι → ℝ) (state : G.State)
    (joint : ∀ player, G.Action player) (who : ι) :
    expectedUtility (G.discountedAuxGame β value state).utility who
        ((G.discountedAuxGame β value state).form.play joint)
        (G.discountedAuxIntegrable β value state who joint) =
      G.discountedAuxUtility β value state joint who
        (payoffIntegrable_of_finite _ _) :=
  G.oneStepUtility_pure_expected β value state joint who
    (payoffIntegrable_of_finite _ _) _

/-- The on-profile auxiliary expected payoff in real simplex coordinates. -/
def finkAuxPayoff [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι) : ℝ :=
  payoff (G.oneStepForm state)
    (G.discountedAuxGame β (G.finkValue point) state).utility
    (G.discountedAuxIntegrable β (G.finkValue point) state) who
    (G.finkStateWeights point state)

/-- The auxiliary payoff after one pure deviation, in finite coordinates. -/
def finkDeviationPayoff [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι)
    (action : G.Action who) : ℝ :=
  ∑ joint : ∀ player, G.Action player,
    ((PMF.pure action) (joint who)).toReal *
      ((∏ player ∈ Finset.univ.erase who,
          G.finkStateWeights point state player (joint player)) *
        G.discountedAuxUtility β (G.finkValue point) state joint who
          (payoffIntegrable_of_finite _ _))

theorem finkDeviationPayoff_eq_payoff_update
    [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι)
    (action : G.Action who) :
    G.finkDeviationPayoff β point state who action =
      payoff (G.oneStepForm state)
        (G.discountedAuxGame β (G.finkValue point) state).utility
        (G.discountedAuxIntegrable β (G.finkValue point) state) who
        (Profile.update (G.finkStateWeights point state) who
          (fun candidate => ((PMF.pure action) candidate).toReal)) := by
  rw [payoff_update]
  unfold finkDeviationPayoff
  apply Finset.sum_congr rfl
  intro joint _
  rw [G.discountedAuxPurePayoff_eq_scalar]

theorem finkAuxPayoff_eq_expectedUtility
    [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι) :
    G.finkAuxPayoff β point state who =
      expectedUtility (G.discountedAuxGame β (G.finkValue point) state).utility who
        ((G.discountedAuxGame β (G.finkValue point) state).form.mixed.play
          (G.finkProfile point state))
        (G.discountedAuxMixedIntegrable β (G.finkValue point) state who
          (G.finkProfile point state)) := by
  unfold finkAuxPayoff
  rw [← payoff_probs (F := G.oneStepForm state)
    (pureIntegrable := G.discountedAuxIntegrable β
      (G.finkValue point) state)]
  congr 1
  exact (probs_ofPolytope G.oneStepSignature
    (G.finkStateWeights_mem point state)).symm

theorem finkDeviationPayoff_eq_expectedUtility
    [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι)
    (action : G.Action who) :
    G.finkDeviationPayoff β point state who action =
      expectedUtility (G.discountedAuxGame β (G.finkValue point) state).utility who
        ((G.discountedAuxGame β (G.finkValue point) state).form.mixed.play
          (Profile.update (G.finkProfile point state) who
            (PMF.pure action)))
        (G.discountedAuxMixedIntegrable β (G.finkValue point) state who
          (Profile.update (G.finkProfile point state) who
            (PMF.pure action))) := by
  rw [G.finkDeviationPayoff_eq_payoff_update]
  rw [← payoff_probs (F := G.oneStepForm state)
    (pureIntegrable := G.discountedAuxIntegrable β
      (G.finkValue point) state), probs_update]
  congr 1
  exact congrArg (fun weights =>
    Profile.update weights who
      (fun candidate => ((PMF.pure action) candidate).toReal))
    (probs_ofPolytope G.oneStepSignature
      (G.finkStateWeights_mem point state)).symm

/-- Pure one-step gain in Fink's auxiliary game. -/
def finkGain [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι)
    (action : G.Action who) : ℝ :=
  G.finkDeviationPayoff β point state who action -
    G.finkAuxPayoff β point state who

theorem finkGain_eq_mixedGain [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (point : G.finkDomain bound)
    (state : G.State) (who : ι) (action : G.Action who) :
    G.finkGain β point state who action =
      (G.discountedAuxGame β (G.finkValue point) state).mixedGain
        (G.finkProfile point state) who action
        (G.discountedAuxMixedIntegrable β (G.finkValue point) state who
          (G.finkProfile point state))
        (G.discountedAuxMixedIntegrable β (G.finkValue point) state who
          (Profile.update (G.finkProfile point state) who
            (PMF.pure action))) := by
  unfold finkGain UtilityGame.mixedGain
  rw [G.finkDeviationPayoff_eq_expectedUtility,
    G.finkAuxPayoff_eq_expectedUtility]

/-- Total positive auxiliary gain for one state-player agent. -/
def finkGainSum [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) (state : G.State) (who : ι) : ℝ :=
  ∑ action, max (G.finkGain β point state who action) 0

theorem finkGainSum_nonneg [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (point : G.finkDomain bound)
    (state : G.State) (who : ι) :
    0 ≤ G.finkGainSum β point state who :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- One coordinate of Nash's positive-gain adjustment. -/
def finkStrategyWeightUpdate [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (point : G.finkDomain bound)
    (state : G.State) (who : ι) (action : G.Action who) : ℝ :=
  (G.finkStateWeights point state who action +
      max (G.finkGain β point state who action) 0) /
    (1 + G.finkGainSum β point state who)

theorem finkStrategyUpdate_mem [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (point : G.finkDomain bound)
    (state : G.State) (who : ι) :
    (fun action => G.finkStrategyWeightUpdate β point state who action) ∈
      simplexWeights (G.Action who) := by
  rw [mem_simplexWeights]
  constructor
  · intro action
    apply div_nonneg
    · exact add_nonneg
        ((mem_simplexWeights.mp ((mem_mixedPolytope G.oneStepSignature).1
          (G.finkStateWeights_mem point state) who)).1 action)
        (le_max_right _ _)
    · linarith [G.finkGainSum_nonneg β point state who]
  · have hden : 1 + G.finkGainSum β point state who ≠ 0 := by
      linarith [G.finkGainSum_nonneg β point state who]
    simp only [finkStrategyWeightUpdate]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [show ∑ action : G.Action who,
        G.finkStateWeights point state who action = 1 by
      exact (mem_simplexWeights.mp ((mem_mixedPolytope G.oneStepSignature).1
        (G.finkStateWeights_mem point state) who)).2]
    exact div_self hden

theorem continuous_finkAuxPayoff [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (state : G.State) (who : ι) :
    Continuous (fun point : G.finkDomain bound =>
      G.finkAuxPayoff β point state who) := by
  unfold finkAuxPayoff payoff
  simp_rw [G.discountedAuxPurePayoff_eq_scalar]
  unfold discountedAuxUtility normalizedOneStepUtility
    finkStateWeights finkValue
  simp_rw [expect_eq_sum]
  fun_prop

theorem continuous_finkDeviationPayoff [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (state : G.State) (who : ι) (action : G.Action who) :
    Continuous (fun point : G.finkDomain bound =>
      G.finkDeviationPayoff β point state who action) := by
  unfold finkDeviationPayoff discountedAuxUtility
    normalizedOneStepUtility finkStateWeights
  simp_rw [expect_eq_sum]
  unfold finkValue
  fun_prop

theorem continuous_finkGain [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (state : G.State) (who : ι)
    (action : G.Action who) :
    Continuous (fun point : G.finkDomain bound =>
      G.finkGain β point state who action) :=
  (G.continuous_finkDeviationPayoff β state who action).sub
    (G.continuous_finkAuxPayoff β state who)

theorem continuous_finkGainSum [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β : ℝ) {bound : ℝ} (state : G.State) (who : ι) :
    Continuous (fun point : G.finkDomain bound =>
      G.finkGainSum β point state who) := by
  unfold finkGainSum
  exact continuous_finsetSum _ fun action _ =>
    (G.continuous_finkGain β state who action).max continuous_const

theorem continuous_finkStrategyWeightUpdate [Fintype ι] [DecidableEq ι]
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

omit [Fintype G.State] in
theorem abs_discountedAuxUtility_le (β bound : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound)
    (value : G.State → ι → ℝ)
    (hvalue : ∀ state who, |value state who| ≤ bound)
    (state : G.State) (joint : ∀ player, G.Action player) (who : ι)
    (hintegrable : PayoffIntegrable (G.transition state joint)
      (fun next => value next who)) :
    |G.discountedAuxUtility β value state joint who hintegrable| ≤ bound := by
  have hweight : 0 ≤ 1 - β := sub_nonneg.mpr hβ1
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg _).trans (hstage state joint who)
  have hexpect :
      |expect (G.transition state joint) (fun next => value next who)
        hintegrable| ≤ bound :=
    expect_abs_le_of_bounded hbound0 (fun next => hvalue next who)
      hintegrable
  calc
    |G.discountedAuxUtility β value state joint who hintegrable| ≤
        |(1 - β) * G.stageUtility state joint who| +
          |β * expect (G.transition state joint)
            (fun next => value next who) hintegrable| := by
      exact abs_add_le _ _
    _ = (1 - β) * |G.stageUtility state joint who| +
          β * |expect (G.transition state joint)
            (fun next => value next who) hintegrable| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hweight, abs_of_nonneg hβ0]
    _ ≤ (1 - β) * bound + β * bound :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hstage state joint who) hweight)
        (mul_le_mul_of_nonneg_left hexpect hβ0)
    _ = bound := by ring

theorem abs_finkAuxPayoff_le [Fintype ι]
    [DecidableEq ι] [∀ player, Fintype (G.Action player)]
    (β bound : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound)
    (point : G.finkDomain bound) (state : G.State) (who : ι) :
    |G.finkAuxPayoff β point state who| ≤ bound := by
  rw [G.finkAuxPayoff_eq_expectedUtility]
  unfold expectedUtility
  have hbound0 : 0 ≤ bound := by
    let joint : ∀ player, G.Action player := fun player =>
      ((G.finkProfile point state player).support_nonempty).choose
    exact (abs_nonneg _).trans (hstage state joint who)
  apply expect_abs_le_of_bounded hbound0
  intro outcome
  have hweight : 0 ≤ 1 - β := sub_nonneg.mpr hβ1
  have hvalue : |G.finkValue point outcome.2 who| ≤ bound :=
    abs_le.mpr ⟨point.2.2.1 outcome.2 who,
      point.2.2.2 outcome.2 who⟩
  calc
    |(G.discountedAuxGame β (G.finkValue point) state).utility outcome who| ≤
        |(1 - β) * G.stageUtility state outcome.1 who| +
          |β * G.finkValue point outcome.2 who| := by
      exact abs_add_le _ _
    _ = (1 - β) * |G.stageUtility state outcome.1 who| +
          β * |G.finkValue point outcome.2 who| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hweight, abs_of_nonneg hβ0]
    _ ≤ (1 - β) * bound + β * bound :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hstage state outcome.1 who) hweight)
        (mul_le_mul_of_nonneg_left hvalue hβ0)
    _ = bound := by ring

/-- The ambient-coordinate formula for Fink's joint strategy/value map. -/
def finkAmbientUpdate [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)] (β : ℝ) {bound : ℝ}
    (point : G.finkDomain bound) : G.FinkAmbient :=
  (fun agent action =>
      G.finkStrategyWeightUpdate β point agent.1 agent.2 action,
    fun state who => G.finkAuxPayoff β point state who)

theorem finkAmbientUpdate_mem [Fintype ι]
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
def finkMap [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)]
    (β bound : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound) :
    G.finkDomain bound → G.finkDomain bound :=
  fun point => ⟨G.finkAmbientUpdate β point,
    G.finkAmbientUpdate_mem β bound hβ0 hβ1 hstage point⟩

theorem continuous_finkMap [Fintype ι]
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

theorem exists_finkMap_fixedPoint [Fintype ι]
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

theorem isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
    [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Action player)]
    (β bound : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hstage : ∀ state joint who, |G.stageUtility state joint who| ≤ bound)
    (point : G.finkDomain bound)
    (hfixed : G.finkMap β bound hβ0 hβ1 hstage point = point) :
    G.IsDiscountedStationaryBellmanEq β (G.finkProfile point)
      (G.finkValue point) := by
  constructor
  · intro state
    let H := G.discountedAuxGame β (G.finkValue point) state
    let p := G.finkProfile point state
    let hbase := fun who => G.discountedAuxMixedIntegrable β
      (G.finkValue point) state who p
    let hdeviation := fun who replacement =>
      G.discountedAuxMixedIntegrable β (G.finkValue point) state who
        (Profile.update p who replacement)
    rw [H.isNash_iff_mixedGain_nonpos p hbase hdeviation]
    intro who action
    rw [← G.finkGain_eq_mixedGain β point state who action]
    apply GameTheory.Math.all_nonpos_of_weighted_positivePart_fixedPoint
      (weight := fun candidate => (G.finkProfile point state who candidate).toReal)
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
      rw [G.finkProfile_toReal]
      exact (div_eq_iff hden).mp hdivision |>.symm
    · have hmean :=
        (G.discountedAuxGame β (G.finkValue point) state).expect_mixedGain_self_zero
          (G.finkProfile point state) who (hbase who)
          (fun action => hdeviation who (PMF.pure action))
      rw [expect_eq_sum] at hmean
      calc
        ∑ candidate, (G.finkProfile point state who candidate).toReal *
            G.finkGain β point state who candidate =
            ∑ candidate, (G.finkProfile point state who candidate).toReal *
              (G.discountedAuxGame β (G.finkValue point) state).mixedGain
                (G.finkProfile point state) who candidate
                (hbase who) (hdeviation who (PMF.pure candidate)) := by
          exact Finset.sum_congr rfl fun candidate _ => by
            rw [G.finkGain_eq_mixedGain]
        _ = 0 := hmean
  · intro state who
    refine ⟨G.discountedAuxMixedIntegrable β (G.finkValue point) state who
      (G.finkProfile point state), ?_⟩
    have hcoordinate := congrArg
      (fun result : G.finkDomain bound => result.1.2 state who) hfixed
    rw [← G.finkAuxPayoff_eq_expectedUtility]
    simpa [finkMap, finkAmbientUpdate, finkValue] using hcoordinate

/-- A finite stochastic game admits a bounded stationary profile and value
function satisfying the statewise mixed-Nash and Bellman equations. This is the
stationary Bellman fixed-point conclusion; equilibrium against arbitrary
history-dependent deviations requires a separate one-shot-deviation theorem. -/
theorem exists_isDiscountedStationaryBellmanEq_bounded
    [Fintype ι] [DecidableEq ι]
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
