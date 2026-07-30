/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicStagePayoffInnovation

/-!
# Public Bellman innovation scores

A completed public stage reveals both the joint action and the successor
state.  For a fixed state potential, subtract the prescribed conditional
expectation of

`stage payoff + successor potential`

from its realized value.  The resulting score is centered under prescribed
play.  Under an arbitrary comparison behavior profile, its conditional mean
is exactly the comparison's stage-payoff gain plus its transition-potential
drift.

This is the canonical one-step statistical interface for a Bellman response.
It detects a supplied profitable comparison; it does not select a punishment
continuation or prove that the comparison remains profitable after a phase
change.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- Public outcome of one completed stage: joint action and successor state. -/
abbrev PublicStageOutcome (G : StochasticGame ι) :=
  G.JointAct × G.State

/-- Conditional law of the next public stage outcome. -/
def publicStageOutcomeDist
    [Fintype ι]
    (profile : G.BehaviorProfile)
    {t : ℕ} (history : G.Hist t) :
    PMF G.PublicStageOutcome :=
  (G.stageActionDist profile history).bind fun jointAction =>
    (G.transition history.2 jointAction).bind fun nextState =>
      PMF.pure (jointAction, nextState)

/-- Expected successor value of a fixed state potential after one history. -/
def statePotentialEUAt
    [Fintype ι]
    (profile : G.BehaviorProfile)
    (potential : G.State → ℝ)
    {t : ℕ} (history : G.Hist t) : ℝ :=
  expect (G.stageActionDist profile history) fun jointAction =>
    expect (G.transition history.2 jointAction) potential

/-- Prescribed conditional expectation of stage payoff plus successor
potential. -/
def stageBellmanEUAt
    [Fintype ι]
    (profile : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {t : ℕ} (history : G.Hist t) : ℝ :=
  G.stageEUAt profile history owner +
    G.statePotentialEUAt profile potential history

/-- Realized payoff-plus-potential innovation, centered under the prescribed
behavior profile. -/
def historyBellmanInnovation
    [Fintype ι]
    (prescribed : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {t : ℕ} (history : G.Hist t)
    (outcome : G.PublicStageOutcome) : ℝ :=
  G.stagePayoff history.2 outcome.1 owner +
      potential outcome.2 -
    G.stageBellmanEUAt prescribed owner potential history

/-- Expectation over the public outcome law is the corresponding nested
action/transition expectation. -/
theorem expect_publicStageOutcomeDist
    [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (profile : G.BehaviorProfile)
    {t : ℕ} (history : G.Hist t)
    (f : G.PublicStageOutcome → ℝ) :
    expect (G.publicStageOutcomeDist profile history) f =
      expect (G.stageActionDist profile history) fun jointAction =>
        expect (G.transition history.2 jointAction) fun nextState =>
          f (jointAction, nextState) := by
  rw [publicStageOutcomeDist, expect_bind]
  apply congrArg (expect (G.stageActionDist profile history))
  funext jointAction
  rw [expect_bind]
  simp

/-- The public Bellman innovation is centered under prescribed play. -/
theorem expect_historyBellmanInnovation_prescribed_eq_zero
    [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {t : ℕ} (history : G.Hist t) :
    expect (G.publicStageOutcomeDist prescribed history)
        (G.historyBellmanInnovation
          prescribed owner potential history) = 0 := by
  rw [G.expect_publicStageOutcomeDist]
  have hinner (jointAction : G.JointAct) :
      expect (G.transition history.2 jointAction)
          (fun nextState =>
            G.historyBellmanInnovation prescribed owner potential
              history (jointAction, nextState)) =
        G.stagePayoff history.2 jointAction owner +
            expect (G.transition history.2 jointAction) potential -
          G.stageBellmanEUAt
            prescribed owner potential history := by
    unfold historyBellmanInnovation
    change
      expect (G.transition history.2 jointAction)
          (fun nextState =>
            G.stagePayoff history.2 jointAction owner +
                potential nextState -
              G.stageBellmanEUAt
                prescribed owner potential history) =
        _
    rw [expect_sub, expect_const, expect_add, expect_const]
  simp_rw [hinner, expect_sub, expect_const, expect_add]
  exact sub_self _

/-- Under any comparison profile, the conditional mean is exactly its stage
gain plus its transition-potential drift relative to prescribed play. -/
theorem expect_historyBellmanInnovation_eq_gain_add_drift
    [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {t : ℕ} (history : G.Hist t) :
    expect (G.publicStageOutcomeDist comparison history)
        (G.historyBellmanInnovation
          prescribed owner potential history) =
      (G.stageEUAt comparison history owner -
          G.stageEUAt prescribed history owner) +
        (G.statePotentialEUAt comparison potential history -
          G.statePotentialEUAt prescribed potential history) := by
  rw [G.expect_publicStageOutcomeDist]
  have hinner (jointAction : G.JointAct) :
      expect (G.transition history.2 jointAction)
          (fun nextState =>
            G.historyBellmanInnovation prescribed owner potential
              history (jointAction, nextState)) =
        G.stagePayoff history.2 jointAction owner +
            expect (G.transition history.2 jointAction) potential -
          G.stageBellmanEUAt
            prescribed owner potential history := by
    unfold historyBellmanInnovation
    change
      expect (G.transition history.2 jointAction)
          (fun nextState =>
            G.stagePayoff history.2 jointAction owner +
                potential nextState -
              G.stageBellmanEUAt
                prescribed owner potential history) =
        _
    rw [expect_sub, expect_const, expect_add, expect_const]
  simp_rw [hinner, expect_sub, expect_const, expect_add]
  unfold stageBellmanEUAt statePotentialEUAt stageEUAt
  ring

/-- Arbitrary history-dependent unilateral behavior deviations are covered
without selecting a pure comparator. -/
theorem expect_historyBellmanInnovation_eq_behaviorDeviationGain
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed : G.BehaviorProfile)
    (owner : ι) (deviation : G.BehaviorStrategy owner)
    (potential : G.State → ℝ)
    {t : ℕ} (history : G.Hist t) :
    expect
        (G.publicStageOutcomeDist
          (Function.update prescribed owner deviation) history)
        (G.historyBellmanInnovation
          prescribed owner potential history) =
      (G.stageEUAt
          (Function.update prescribed owner deviation)
          history owner -
        G.stageEUAt prescribed history owner) +
      (G.statePotentialEUAt
          (Function.update prescribed owner deviation)
          potential history -
        G.statePotentialEUAt prescribed potential history) :=
  G.expect_historyBellmanInnovation_eq_gain_add_drift
    prescribed (Function.update prescribed owner deviation)
    owner potential history

/-- A payoff bound `U` and a potential bound `B` give the public innovation
bound `2 * (U + B)`. -/
theorem abs_historyBellmanInnovation_le_two_mul
    [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    {U B : ℝ}
    (hpay : ∀ s a owner, |G.stagePayoff s a owner| ≤ U)
    (prescribed : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    (hpotential : ∀ s, |potential s| ≤ B)
    {t : ℕ} (history : G.Hist t)
    (outcome : G.PublicStageOutcome) :
    |G.historyBellmanInnovation
        prescribed owner potential history outcome| ≤
      2 * (U + B) := by
  have hstageMean :
      |G.stageEUAt prescribed history owner| ≤ U := by
    exact abs_expect_le_of_abs_le _ _ fun action =>
      hpay history.2 action owner
  have hpotentialMean :
      |G.statePotentialEUAt
          prescribed potential history| ≤ B := by
    unfold statePotentialEUAt
    apply abs_expect_le_of_abs_le
    intro action
    exact abs_expect_le_of_abs_le _ _ hpotential
  have hrealized :
      |G.stagePayoff history.2 outcome.1 owner +
          potential outcome.2| ≤ U + B := by
    exact (abs_add_le _ _).trans
      (add_le_add
        (hpay history.2 outcome.1 owner)
        (hpotential outcome.2))
  have hbaseline :
      |G.stageBellmanEUAt
          prescribed owner potential history| ≤ U + B := by
    unfold stageBellmanEUAt
    exact (abs_add_le _ _).trans
      (add_le_add hstageMean hpotentialMean)
  unfold historyBellmanInnovation
  exact (abs_sub _ _).trans <| by
    linarith

/-- A positive Bellman compensator is therefore a positive conditional mean
of one bounded public score. -/
theorem signal_le_expect_historyBellmanInnovation
    [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {t : ℕ} (history : G.Hist t) (signal : ℝ)
    (hsignal :
      signal ≤
        (G.stageEUAt comparison history owner -
            G.stageEUAt prescribed history owner) +
          (G.statePotentialEUAt comparison potential history -
            G.statePotentialEUAt prescribed potential history)) :
    signal ≤
      expect (G.publicStageOutcomeDist comparison history)
        (G.historyBellmanInnovation
          prescribed owner potential history) := by
  rw [
    G.expect_historyBellmanInnovation_eq_gain_add_drift
      prescribed comparison owner potential history
  ]
  exact hsignal

/-! ## Finite-horizon Bellman compensators -/

/-- The state path of a completed history, including its final state. -/
def historyStatePath
    {T : ℕ} (history : G.Hist T) : Fin (T + 1) → G.State :=
  Fin.snoc (fun stage => (history.1 stage).1) history.2

/-- Extending a history appends exactly its new final state to the state
path. -/
@[simp]
theorem historyStatePath_snoc
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State) :
    G.historyStatePath
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1)) =
      Fin.snoc (G.historyStatePath history) nextState := by
  funext stage
  refine Fin.lastCases ?_ (fun earlier => ?_) stage
  · simp [historyStatePath]
  · refine Fin.lastCases ?_ (fun prior => ?_) earlier
    · simp [historyStatePath]
    · simp [historyStatePath]

/-- Successor state observed after a completed stage. -/
def stateAfterStage
    {T : ℕ} (history : G.Hist T) (stage : Fin T) : G.State :=
  G.historyStatePath history stage.succ

@[simp]
theorem stateAfterStage_snoc_castSucc
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State)
    (stage : Fin T) :
    G.stateAfterStage
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1))
        stage.castSucc =
      G.stateAfterStage history stage := by
  unfold stateAfterStage
  rw [historyStatePath_snoc]
  have hindex :
      stage.castSucc.succ = stage.succ.castSucc :=
    Fin.ext rfl
  rw [hindex, Fin.snoc_castSucc]

@[simp]
theorem stateAfterStage_snoc_last
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State) :
    G.stateAfterStage
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1))
        (Fin.last T) =
      nextState := by
  unfold stateAfterStage
  rw [historyStatePath_snoc]
  have hindex :
      (Fin.last T).succ = Fin.last (T + 1) :=
    Fin.ext rfl
  rw [hindex, Fin.snoc_last]

/-- Cumulative realized public Bellman innovation along a full history. -/
def cumulativeBellmanInnovation
    [Fintype ι]
    (prescribed : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {T : ℕ} (history : G.Hist T) : ℝ :=
  ∑ stage,
    G.historyBellmanInnovation prescribed owner potential
      (G.historyBeforeStage history stage)
      ((history.1 stage).2, G.stateAfterStage history stage)

/-- Predictable sum of stage-payoff gains and transition-potential drifts
under a comparison behavior profile. -/
def cumulativeBellmanCompensator
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {T : ℕ} (history : G.Hist T) : ℝ :=
  ∑ stage,
    ((G.stageEUAt comparison
          (G.historyBeforeStage history stage) owner -
        G.stageEUAt prescribed
          (G.historyBeforeStage history stage) owner) +
      (G.statePotentialEUAt comparison potential
          (G.historyBeforeStage history stage) -
        G.statePotentialEUAt prescribed potential
          (G.historyBeforeStage history stage)))

@[simp]
theorem cumulativeBellmanInnovation_zero
    [Fintype ι]
    (prescribed : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    (history : G.Hist 0) :
    G.cumulativeBellmanInnovation
      prescribed owner potential history = 0 := by
  simp [cumulativeBellmanInnovation]

@[simp]
theorem cumulativeBellmanCompensator_zero
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    (history : G.Hist 0) :
    G.cumulativeBellmanCompensator
      prescribed comparison owner potential history = 0 := by
  simp [cumulativeBellmanCompensator]

@[simp]
theorem cumulativeBellmanInnovation_snoc
    [Fintype ι]
    (prescribed : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State) :
    G.cumulativeBellmanInnovation prescribed owner potential
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1)) =
      G.cumulativeBellmanInnovation
          prescribed owner potential history +
        G.historyBellmanInnovation prescribed owner potential
          history (jointAction, nextState) := by
  rw [cumulativeBellmanInnovation, Fin.sum_univ_castSucc]
  simp only [historyBeforeStage_snoc_castSucc,
    historyBeforeStage_snoc_last, Fin.snoc_castSucc,
    Fin.snoc_last, stateAfterStage_snoc_castSucc,
    stateAfterStage_snoc_last]
  rfl

@[simp]
theorem cumulativeBellmanCompensator_snoc
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State) :
    G.cumulativeBellmanCompensator
        prescribed comparison owner potential
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1)) =
      G.cumulativeBellmanCompensator
          prescribed comparison owner potential history +
        ((G.stageEUAt comparison history owner -
            G.stageEUAt prescribed history owner) +
          (G.statePotentialEUAt comparison potential history -
            G.statePotentialEUAt
              prescribed potential history)) := by
  rw [cumulativeBellmanCompensator, Fin.sum_univ_castSucc]
  simp only [historyBeforeStage_snoc_castSucc,
    historyBeforeStage_snoc_last]
  rfl

/-- Under any comparison behavior, expected cumulative public Bellman
innovation equals its expected predictable gain-and-drift compensator. -/
theorem expect_cumulativeBellmanInnovation_eq_compensator
    [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed comparison : G.BehaviorProfile)
    (s₀ : G.State) (owner : ι)
    (potential : G.State → ℝ) (T : ℕ) :
    expect (G.histDist comparison s₀ T)
        (G.cumulativeBellmanInnovation
          prescribed owner potential) =
      expect (G.histDist comparison s₀ T)
        (G.cumulativeBellmanCompensator
          prescribed comparison owner potential) := by
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
              (G.cumulativeBellmanInnovation
                prescribed owner potential)) =
            fun history =>
              G.cumulativeBellmanInnovation
                  prescribed owner potential history +
                ((G.stageEUAt comparison history owner -
                    G.stageEUAt prescribed history owner) +
                  (G.statePotentialEUAt
                      comparison potential history -
                    G.statePotentialEUAt
                      prescribed potential history)) := by
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
                (G.cumulativeBellmanInnovation
                  prescribed owner potential) =
              G.cumulativeBellmanInnovation
                  prescribed owner potential history +
                expect (G.transition history.2 jointAction)
                  (fun nextState =>
                    G.historyBellmanInnovation
                      prescribed owner potential history
                      (jointAction, nextState)) := by
          rw [expect_bind]
          simp_rw [expect_pure,
            cumulativeBellmanInnovation_snoc]
          rw [expect_add, expect_const]
        simp_rw [haction]
        rw [expect_add, expect_const]
        rw [← G.expect_publicStageOutcomeDist comparison history]
        rw [
          G.expect_historyBellmanInnovation_eq_gain_add_drift
            prescribed comparison owner potential history
        ]
      have hcompensator :
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
              (G.cumulativeBellmanCompensator
                prescribed comparison owner potential)) =
            fun history =>
              G.cumulativeBellmanCompensator
                  prescribed comparison owner potential history +
                ((G.stageEUAt comparison history owner -
                    G.stageEUAt prescribed history owner) +
                  (G.statePotentialEUAt
                      comparison potential history -
                    G.statePotentialEUAt
                      prescribed potential history)) := by
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
                (G.cumulativeBellmanCompensator
                  prescribed comparison owner potential) =
              G.cumulativeBellmanCompensator
                  prescribed comparison owner potential history +
                ((G.stageEUAt comparison history owner -
                    G.stageEUAt prescribed history owner) +
                  (G.statePotentialEUAt
                      comparison potential history -
                    G.statePotentialEUAt
                      prescribed potential history)) := by
          rw [expect_bind]
          simp only [expect_pure,
            cumulativeBellmanCompensator_snoc]
          exact expect_const _ _
        simp_rw [haction]
        exact expect_const _ _
      rw [hinnovation, hcompensator]
      simp_rw [expect_add]
      rw [ih]

/-- Cumulative specialization to an arbitrary unilateral behavior
deviation. -/
theorem expect_cumulativeBellmanInnovation_eq_behaviorDeviationCompensator
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed : G.BehaviorProfile)
    (owner : ι) (deviation : G.BehaviorStrategy owner)
    (potential : G.State → ℝ)
    (s₀ : G.State) (T : ℕ) :
    expect
        (G.histDist
          (Function.update prescribed owner deviation) s₀ T)
        (G.cumulativeBellmanInnovation
          prescribed owner potential) =
      expect
        (G.histDist
          (Function.update prescribed owner deviation) s₀ T)
        (G.cumulativeBellmanCompensator prescribed
          (Function.update prescribed owner deviation)
          owner potential) :=
  G.expect_cumulativeBellmanInnovation_eq_compensator
    prescribed (Function.update prescribed owner deviation)
    s₀ owner potential T

/-- Adverse noise is predictable Bellman gain-and-drift minus realized
public Bellman innovation. -/
def bellmanInnovationAdverseNoise
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {T : ℕ} (history : G.Hist T) : ℝ :=
  G.cumulativeBellmanCompensator
      prescribed comparison owner potential history -
    G.cumulativeBellmanInnovation
      prescribed owner potential history

/-- Exact pathwise decomposition used by the comparison side of the
horizon-free detector interface. -/
theorem cumulativeBellmanInnovation_eq_compensator_sub_adverseNoise
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {T : ℕ} (history : G.Hist T) :
    G.cumulativeBellmanInnovation
        prescribed owner potential history =
      G.cumulativeBellmanCompensator
          prescribed comparison owner potential history -
        G.bellmanInnovationAdverseNoise
          prescribed comparison owner potential history := by
  rw [bellmanInnovationAdverseNoise]
  ring

/-- A deterministic lower signal for the cumulative Bellman compensator
supplies the detector's pathwise `comparisonLower` inequality. -/
theorem signal_sub_adverseNoise_le_cumulativeBellmanInnovation
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (potential : G.State → ℝ)
    {T : ℕ} (history : G.Hist T)
    (signal : ℝ)
    (hsignal :
      signal ≤
        G.cumulativeBellmanCompensator
          prescribed comparison owner potential history) :
    signal -
        G.bellmanInnovationAdverseNoise
          prescribed comparison owner potential history ≤
      G.cumulativeBellmanInnovation
        prescribed owner potential history := by
  rw [
    G.cumulativeBellmanInnovation_eq_compensator_sub_adverseNoise
      prescribed comparison owner potential history
  ]
  exact sub_le_sub_right hsignal _

end StochasticGame
end GameTheory
