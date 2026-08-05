/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicStagePayoffInnovation

/-!
# Public action-frequency innovations under behavior deviations

A fixed analytic stage response supplies a selected player and action. Its
public action-frequency score is already centered and bounded at one stage.
This file carries that score through arbitrary finite public histories.

The resulting cumulative statistic has three exact descriptions:

* its conditional mean is the selected action's probability excess;
* its expectation under any history-dependent comparison behavior is the
  expectation of the predictable cumulative excess;
* pathwise it is that compensator minus a centered adverse-noise term.

This is the maximal behavioral activation datum implied by the fixed public
score. It supplies the algebraic `comparisonLower` field of the horizon-free
detector without assuming that the comparison is stationary or pure.
Constructing the common measurable martingale realization and choosing a
credible target-preserving continuation remain separate play-law and
strategic obligations.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.OnlineLearning Math.PMFProduct Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}

/-- The selected-action innovation after a concrete public history. -/
def historySelectedActionInnovation
    [Fintype ι]
    (prescribed : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    {t : ℕ} (history : G.Hist t)
    (jointAction : G.JointAct) : ℝ :=
  G.publicActionFrequencyScore owner
    (prescribed owner t history) selected jointAction

/-- Prescribed behavior centers the selected-action innovation after every
public history. -/
theorem expect_historySelectedActionInnovation_prescribed_eq_zero
    [Fintype ι] [∀ i, Finite (G.Act i)]
    (prescribed : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    {t : ℕ} (history : G.Hist t) :
    expect (G.stageActionDist prescribed history)
        (G.historySelectedActionInnovation
          prescribed owner selected history) = 0 := by
  unfold historySelectedActionInnovation stageActionDist
  exact G.expect_publicActionFrequencyScore_baseline_eq_zero
    owner (fun i => prescribed i t history) selected

/-- Under arbitrary comparison behavior, the conditional mean is exactly
the selected action's probability shift. -/
theorem expect_historySelectedActionInnovation_eq_probabilityDifference
    [Fintype ι] [∀ i, Finite (G.Act i)]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    {t : ℕ} (history : G.Hist t) :
    expect (G.stageActionDist comparison history)
        (G.historySelectedActionInnovation
          prescribed owner selected history) =
      (comparison owner t history selected).toReal -
        (prescribed owner t history selected).toReal := by
  unfold historySelectedActionInnovation stageActionDist
  exact G.expect_publicActionFrequencyScore_eq_difference
    owner (fun i => comparison i t history)
      (prescribed owner t history) selected

/-- The probability-shift identity applies directly to every
history-dependent unilateral deviation. -/
theorem
    expect_historySelectedActionInnovation_eq_behaviorDeviationDifference
    [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)]
    (prescribed : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    (deviation : G.BehaviorStrategy owner)
    {t : ℕ} (history : G.Hist t) :
    expect
        (G.stageActionDist
          (Function.update prescribed owner deviation) history)
        (G.historySelectedActionInnovation
          prescribed owner selected history) =
      (deviation t history selected).toReal -
        (prescribed owner t history selected).toReal := by
  rw [
    G.expect_historySelectedActionInnovation_eq_probabilityDifference
  ]
  simp

/-- The history-selected frequency innovation is pointwise bounded by one. -/
theorem abs_historySelectedActionInnovation_le_one
    [Fintype ι]
    (prescribed : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    {t : ℕ} (history : G.Hist t)
    (jointAction : G.JointAct) :
    |G.historySelectedActionInnovation
        prescribed owner selected history jointAction| ≤ 1 := by
  exact G.abs_publicActionFrequencyScore_le_one
    owner (prescribed owner t history) selected jointAction

/-! ## Cumulative compensator -/

/-- Realized cumulative selected-action innovation along a public history. -/
def cumulativeSelectedActionInnovation
    [Fintype ι]
    (prescribed : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    {T : ℕ} (history : G.Hist T) : ℝ :=
  ∑ stage,
    G.historySelectedActionInnovation prescribed owner selected
      (G.historyBeforeStage history stage)
      (history.1 stage).2

/-- Predictable cumulative selected-action probability excess under a
comparison behavior profile. -/
def cumulativeSelectedActionExcess
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (selected : G.Act owner)
    {T : ℕ} (history : G.Hist T) : ℝ :=
  ∑ stage : Fin T,
    ((comparison owner stage.1
          (G.historyBeforeStage history stage) selected).toReal -
      (prescribed owner stage.1
          (G.historyBeforeStage history stage) selected).toReal)

@[simp]
theorem cumulativeSelectedActionInnovation_zero
    [Fintype ι]
    (prescribed : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    (history : G.Hist 0) :
    G.cumulativeSelectedActionInnovation
      prescribed owner selected history = 0 := by
  simp [cumulativeSelectedActionInnovation]

@[simp]
theorem cumulativeSelectedActionExcess_zero
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (selected : G.Act owner)
    (history : G.Hist 0) :
    G.cumulativeSelectedActionExcess
      prescribed comparison owner selected history = 0 := by
  simp [cumulativeSelectedActionExcess]

@[simp]
theorem cumulativeSelectedActionInnovation_snoc
    [Fintype ι]
    (prescribed : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State) :
    G.cumulativeSelectedActionInnovation prescribed owner selected
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1)) =
      G.cumulativeSelectedActionInnovation
          prescribed owner selected history +
        G.historySelectedActionInnovation
          prescribed owner selected history jointAction := by
  rw [cumulativeSelectedActionInnovation, Fin.sum_univ_castSucc]
  simp only [historyBeforeStage_snoc_castSucc,
    historyBeforeStage_snoc_last, Fin.snoc_castSucc,
    Fin.snoc_last]
  rfl

@[simp]
theorem cumulativeSelectedActionExcess_snoc
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (selected : G.Act owner)
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State) :
    G.cumulativeSelectedActionExcess prescribed comparison owner selected
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1)) =
      G.cumulativeSelectedActionExcess
          prescribed comparison owner selected history +
        ((comparison owner T history selected).toReal -
          (prescribed owner T history selected).toReal) := by
  rw [cumulativeSelectedActionExcess, Fin.sum_univ_castSucc]
  simp only [historyBeforeStage_snoc_castSucc,
    historyBeforeStage_snoc_last]
  rfl

/-- Under arbitrary history-dependent comparison behavior, expected
cumulative selected-action innovation is exactly expected predictable
selected-action excess. -/
theorem expect_cumulativeSelectedActionInnovation_eq_excess
    [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    (s₀ : G.State) (T : ℕ) :
    expect (G.histDist comparison s₀ T)
        (G.cumulativeSelectedActionInnovation
          prescribed owner selected) =
      expect (G.histDist comparison s₀ T)
        (G.cumulativeSelectedActionExcess
          prescribed comparison owner selected) := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [G.histDist_succ, expect_bind, expect_bind]
      have hinnovation :
          (fun history : G.Hist T =>
            expect
              ((G.stageActionDist comparison history).bind
                fun jointAction =>
                  (G.transition history.2 jointAction).bind
                    fun nextState =>
                      PMF.pure
                        ((Fin.snoc history.1
                            (history.2, jointAction), nextState) :
                          G.Hist (T + 1)))
              (G.cumulativeSelectedActionInnovation
                prescribed owner selected)) =
            fun history =>
              G.cumulativeSelectedActionInnovation
                  prescribed owner selected history +
                ((comparison owner T history selected).toReal -
                  (prescribed owner T history selected).toReal) := by
        funext history
        rw [expect_bind]
        have haction (jointAction : G.JointAct) :
            expect
                ((G.transition history.2 jointAction).bind
                  fun nextState =>
                    PMF.pure
                      ((Fin.snoc history.1
                          (history.2, jointAction), nextState) :
                        G.Hist (T + 1)))
                (G.cumulativeSelectedActionInnovation
                  prescribed owner selected) =
              G.cumulativeSelectedActionInnovation
                  prescribed owner selected history +
                G.historySelectedActionInnovation
                  prescribed owner selected history jointAction := by
          rw [expect_bind]
          simp only [expect_pure,
            cumulativeSelectedActionInnovation_snoc]
          exact expect_const _ _
        simp_rw [haction]
        rw [expect_add, expect_const,
          G.expect_historySelectedActionInnovation_eq_probabilityDifference]
      have hexcess :
          (fun history : G.Hist T =>
            expect
              ((G.stageActionDist comparison history).bind
                fun jointAction =>
                  (G.transition history.2 jointAction).bind
                    fun nextState =>
                      PMF.pure
                        ((Fin.snoc history.1
                            (history.2, jointAction), nextState) :
                          G.Hist (T + 1)))
              (G.cumulativeSelectedActionExcess
                prescribed comparison owner selected)) =
            fun history =>
              G.cumulativeSelectedActionExcess
                  prescribed comparison owner selected history +
                ((comparison owner T history selected).toReal -
                  (prescribed owner T history selected).toReal) := by
        funext history
        rw [expect_bind]
        have haction (jointAction : G.JointAct) :
            expect
                ((G.transition history.2 jointAction).bind
                  fun nextState =>
                    PMF.pure
                      ((Fin.snoc history.1
                          (history.2, jointAction), nextState) :
                        G.Hist (T + 1)))
                (G.cumulativeSelectedActionExcess
                  prescribed comparison owner selected) =
              G.cumulativeSelectedActionExcess
                  prescribed comparison owner selected history +
                ((comparison owner T history selected).toReal -
                  (prescribed owner T history selected).toReal) := by
          rw [expect_bind]
          simp only [expect_pure,
            cumulativeSelectedActionExcess_snoc]
          exact expect_const _ _
        simp_rw [haction]
        exact expect_const _ _
      rw [hinnovation, hexcess, expect_add, expect_add, ih]

/-- Specialization of the cumulative identity to any history-dependent
unilateral deviation. -/
theorem
    expect_cumulativeSelectedActionInnovation_eq_behaviorDeviationExcess
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    (deviation : G.BehaviorStrategy owner)
    (s₀ : G.State) (T : ℕ) :
    expect
        (G.histDist
          (Function.update prescribed owner deviation) s₀ T)
        (G.cumulativeSelectedActionInnovation
          prescribed owner selected) =
      expect
        (G.histDist
          (Function.update prescribed owner deviation) s₀ T)
        (G.cumulativeSelectedActionExcess prescribed
          (Function.update prescribed owner deviation)
          owner selected) :=
  G.expect_cumulativeSelectedActionInnovation_eq_excess
    prescribed (Function.update prescribed owner deviation)
    owner selected s₀ T

/-- Adverse noise is predictable selected-action excess minus the realized
public innovation. -/
def selectedActionInnovationAdverseNoise
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    {T : ℕ} (history : G.Hist T) : ℝ :=
  G.cumulativeSelectedActionExcess
      prescribed comparison owner selected history -
    G.cumulativeSelectedActionInnovation
      prescribed owner selected history

/-- Exact pathwise decomposition consumed by the comparison side of the
horizon-free detector. -/
theorem cumulativeSelectedActionInnovation_eq_excess_sub_adverseNoise
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    {T : ℕ} (history : G.Hist T) :
    G.cumulativeSelectedActionInnovation
        prescribed owner selected history =
      G.cumulativeSelectedActionExcess
          prescribed comparison owner selected history -
        G.selectedActionInnovationAdverseNoise
          prescribed comparison owner selected history := by
  rw [selectedActionInnovationAdverseNoise]
  ring

/-- Any deterministic lower bound on cumulative probability excess supplies
the detector's comparison lower bound. -/
theorem signal_sub_selectedActionAdverseNoise_le_innovation
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    {T : ℕ} (history : G.Hist T)
    (signal : ℝ)
    (hsignal :
      signal ≤
        G.cumulativeSelectedActionExcess
          prescribed comparison owner selected history) :
    signal -
        G.selectedActionInnovationAdverseNoise
          prescribed comparison owner selected history ≤
      G.cumulativeSelectedActionInnovation
        prescribed owner selected history := by
  rw [
    G.cumulativeSelectedActionInnovation_eq_excess_sub_adverseNoise
      prescribed comparison owner selected history
  ]
  exact sub_le_sub_right hsignal _

/-! ## Fixed analytic response at one universal-calendar epoch -/

namespace AnalyticFinkStagePublicResponse

/-- Freeze the selected response's Fink mixed profile during one detector
epoch. This is an actual behavior profile, not an existential phase or
punishment predicate. -/
def epochBaselineBehavior
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
    {germ : G.AnalyticBellmanGerm}
    {response : Σ owner : ι, G.State × G.Act owner}
    (_R : AnalyticFinkStagePublicResponse germ response)
    {scale : ℝ} (hscale : scale ∈ Ioo (0 : ℝ) germ.radius) :
    G.BehaviorProfile :=
  G.stationaryBehaviorProfile
    (G.finkProfile (germ.finkPointAt hscale) response.2.1)

/-- The concrete comparison behavior that always uses the selected action
during the same epoch. -/
def epochPureResponseBehavior
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
    {germ : G.AnalyticBellmanGerm}
    {response : Σ owner : ι, G.State × G.Act owner}
    (R : AnalyticFinkStagePublicResponse germ response)
    {scale : ℝ} (hscale : scale ∈ Ioo (0 : ℝ) germ.radius) :
    G.BehaviorProfile :=
  Function.update (epochBaselineBehavior R hscale) response.1
    (fun _ _ => PMF.pure response.2.2)

/-- At every sufficiently late valid universal-calendar epoch, the fixed
pure response creates a deterministic cumulative probability-excess signal.
It grows linearly in the number of stages, with the analytic power-law
margin exposed by the response.

This is the strongest calendar-level behavioral activation statement that
does not assume a path-space martingale compiler or a punishment strategy. -/
theorem eventually_cumulativePureResponseExcess_ge
    [Fintype G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
    {germ : G.AnalyticBellmanGerm}
    {response : Σ owner : ι, G.State × G.Act owner}
    (R : AnalyticFinkStagePublicResponse germ response)
    {U : ℝ} (hU : 0 < U)
    (hpay : ∀ s a owner, |G.stagePayoff s a owner| ≤ U) :
    ∀ᶠ k : ℕ in atTop,
      ∀ hk :
          universalEpochScale k ∈
            Ioo (0 : ℝ) germ.radius,
        ∀ (T : ℕ) (history : G.Hist T),
          (T : ℝ) *
                (R.margin / (2 * U) *
                  universalEpochScale k ^ R.order) ≤
            G.cumulativeSelectedActionExcess
              (epochBaselineBehavior R hk)
              (epochPureResponseBehavior R hk)
              response.1 response.2.2 history := by
  filter_upwards
      [R.eventually_universalEpochActionFrequencyDetector hU hpay] with
      k hdetector
  intro hk T history
  have hmargin := (hdetector hk).2.1
  rw [
    G.expect_publicActionFrequencyScore_pureComparison_eq_missingMass
  ] at hmargin
  have hexcess :
      G.cumulativeSelectedActionExcess
          (epochBaselineBehavior R hk)
          (epochPureResponseBehavior R hk)
          response.1 response.2.2 history =
        (T : ℝ) *
          (1 -
            ((G.finkProfile
              (germ.finkPointAt hk) response.2.1 response.1)
                response.2.2).toReal) := by
    rw [cumulativeSelectedActionExcess]
    have hterm (stage : Fin T) :
        (((epochPureResponseBehavior R hk)
              response.1 stage.1
              (G.historyBeforeStage history stage)
              response.2.2).toReal -
            ((epochBaselineBehavior R hk)
              response.1 stage.1
              (G.historyBeforeStage history stage)
              response.2.2).toReal) =
          1 -
            ((G.finkProfile
              (germ.finkPointAt hk) response.2.1 response.1)
                response.2.2).toReal := by
      simp [epochPureResponseBehavior, epochBaselineBehavior,
        stationaryBehaviorProfile]
    simp_rw [hterm]
    simp
    ring
  rw [hexcess]
  exact mul_le_mul_of_nonneg_left hmargin (Nat.cast_nonneg T)

end AnalyticFinkStagePublicResponse

end StochasticGame
end GameTheory
