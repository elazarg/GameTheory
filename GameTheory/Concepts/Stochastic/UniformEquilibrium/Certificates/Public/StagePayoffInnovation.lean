/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticActionFrequencyActivation

/-!
# Public stage-payoff innovation scores

The realized public joint action reveals every player's realized stage
payoff. Subtracting its expectation under prescribed mixed play gives a
single bounded public innovation score. Unlike an action-frequency score,
this detector needs no fixed pure comparator:

* it is centered under prescribed joint play;
* under any comparison mixed profile, its expectation is exactly the
  comparison's one-stage payoff gain;
* under an arbitrary behavior deviation, its historywise conditional mean
  is exactly the deviation's historywise stage-payoff gain.

The final section sums these identities along stochastic-game histories.
The cumulative innovation has expected value equal to its predictable
stage-gain compensator. Pathwise it is the compensator minus an adverse
noise term, which is precisely the algebraic `comparisonLower` input used by
`HorizonFreePublicDetector`. Establishing a common measurable martingale
realization for that adverse noise belongs to the concrete play-law
compiler; no punishment closure is asserted here.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- Public realized stage payoff minus its expectation under the prescribed
independent mixed profile. -/
def publicStagePayoffInnovation
    [Fintype ι]
    (s : G.State) (prescribed : ∀ i, PMF (G.Act i))
    (owner : ι) (jointAction : G.JointAct) : ℝ :=
  G.stagePayoff s jointAction owner -
    G.mixedStageEU s prescribed owner

/-- The innovation score is exactly centered under prescribed joint play. -/
theorem expect_publicStagePayoffInnovation_eq_zero
    [Fintype ι] [∀ i, Finite (G.Act i)]
    (s : G.State) (prescribed : ∀ i, PMF (G.Act i))
    (owner : ι) :
    expect (pmfPi prescribed)
        (G.publicStagePayoffInnovation s prescribed owner) = 0 := by
  unfold publicStagePayoffInnovation
  rw [expect_sub, expect_const]
  exact sub_self _

/-- Under an arbitrary comparison mixed profile, expected innovation is
exactly its one-stage payoff gain over prescribed play. -/
theorem expect_publicStagePayoffInnovation_eq_mixedStageGain
    [Fintype ι] [∀ i, Finite (G.Act i)]
    (s : G.State)
    (prescribed comparison : ∀ i, PMF (G.Act i))
    (owner : ι) :
    expect (pmfPi comparison)
        (G.publicStagePayoffInnovation s prescribed owner) =
      G.mixedStageEU s comparison owner -
        G.mixedStageEU s prescribed owner := by
  unfold publicStagePayoffInnovation
  rw [expect_sub, expect_const]
  rfl

/-- In particular, this identity applies to every unilateral mixed
deviation, not just a selected pure action. -/
theorem expect_publicStagePayoffInnovation_eq_unilateralMixedStageGain
    [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)]
    (s : G.State) (prescribed : ∀ i, PMF (G.Act i))
    (owner : ι) (deviation : PMF (G.Act owner)) :
    expect
        (pmfPi
          (Function.update prescribed owner deviation))
        (G.publicStagePayoffInnovation s prescribed owner) =
      G.mixedStageEU s
          (Function.update prescribed owner deviation) owner -
        G.mixedStageEU s prescribed owner :=
  G.expect_publicStagePayoffInnovation_eq_mixedStageGain
    s prescribed (Function.update prescribed owner deviation) owner

/-- A payoff bound `U` bounds the public payoff innovation by `2 * U`. -/
theorem abs_publicStagePayoffInnovation_le_two_mul
    [Fintype ι] [∀ i, Finite (G.Act i)]
    {U : ℝ}
    (hpay : ∀ s a owner, |G.stagePayoff s a owner| ≤ U)
    (s : G.State) (prescribed : ∀ i, PMF (G.Act i))
    (owner : ι) (jointAction : G.JointAct) :
    |G.publicStagePayoffInnovation
        s prescribed owner jointAction| ≤ 2 * U := by
  have hmean :
      |G.mixedStageEU s prescribed owner| ≤ U :=
    abs_expect_le_of_abs_le _ _ fun action =>
      hpay s action owner
  have hsub :=
    abs_sub
      (G.stagePayoff s jointAction owner)
      (G.mixedStageEU s prescribed owner)
  exact hsub.trans (by
    have hrealized := hpay s jointAction owner
    linarith)

/-! ## Historywise innovations -/

/-- Public payoff innovation selected after a concrete game history. -/
def historyStagePayoffInnovation
    [Fintype ι]
    (prescribed : G.BehaviorProfile) (owner : ι)
    {t : ℕ} (history : G.Hist t)
    (jointAction : G.JointAct) : ℝ :=
  G.stagePayoff history.2 jointAction owner -
    G.stageEUAt prescribed history owner

/-- Prescribed behavior centers the history-selected innovation score at
every public history. -/
theorem expect_historyStagePayoffInnovation_prescribed_eq_zero
    [Fintype ι] [∀ i, Finite (G.Act i)]
    (prescribed : G.BehaviorProfile) (owner : ι)
    {t : ℕ} (history : G.Hist t) :
    expect (G.stageActionDist prescribed history)
        (G.historyStagePayoffInnovation
          prescribed owner history) = 0 := by
  unfold historyStagePayoffInnovation
  rw [expect_sub, expect_const]
  exact sub_self _

/-- Under any comparison behavior profile, the historywise conditional mean
is exactly its stage-payoff gain. -/
theorem expect_historyStagePayoffInnovation_eq_stageEUAt_sub
    [Fintype ι] [∀ i, Finite (G.Act i)]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) {t : ℕ} (history : G.Hist t) :
    expect (G.stageActionDist comparison history)
        (G.historyStagePayoffInnovation
          prescribed owner history) =
      G.stageEUAt comparison history owner -
        G.stageEUAt prescribed history owner := by
  unfold historyStagePayoffInnovation
  rw [expect_sub, expect_const]
  rfl

/-- History-dependent unilateral behavior deviations are covered directly. -/
theorem expect_historyStagePayoffInnovation_eq_behaviorDeviationGain
    [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)]
    (prescribed : G.BehaviorProfile) (owner : ι)
    (deviation : G.BehaviorStrategy owner)
    {t : ℕ} (history : G.Hist t) :
    expect
        (G.stageActionDist
          (Function.update prescribed owner deviation) history)
        (G.historyStagePayoffInnovation
          prescribed owner history) =
      G.stageEUAt
          (Function.update prescribed owner deviation)
          history owner -
        G.stageEUAt prescribed history owner :=
  G.expect_historyStagePayoffInnovation_eq_stageEUAt_sub
    prescribed (Function.update prescribed owner deviation)
    owner history

/-- The history-selected innovation retains the same `2 * U` bound. -/
theorem abs_historyStagePayoffInnovation_le_two_mul
    [Fintype ι] [∀ i, Finite (G.Act i)]
    {U : ℝ}
    (hpay : ∀ s a owner, |G.stagePayoff s a owner| ≤ U)
    (prescribed : G.BehaviorProfile) (owner : ι)
    {t : ℕ} (history : G.Hist t)
    (jointAction : G.JointAct) :
    |G.historyStagePayoffInnovation
        prescribed owner history jointAction| ≤ 2 * U := by
  have hmean :
      |G.stageEUAt prescribed history owner| ≤ U :=
    abs_expect_le_of_abs_le _ _ fun action =>
      hpay history.2 action owner
  have hsub :=
    abs_sub
      (G.stagePayoff history.2 jointAction owner)
      (G.stageEUAt prescribed history owner)
  exact hsub.trans (by
    have hrealized := hpay history.2 jointAction owner
    linarith)

/-! ## Cumulative compensator -/

/-- Prefix ending immediately before a completed stage of a full history. -/
def historyBeforeStage
    {T : ℕ} (history : G.Hist T) (stage : Fin T) :
    G.Hist stage :=
  (fun earlier =>
    history.1
      (Fin.castLE (Nat.le_of_lt stage.isLt) earlier),
    (history.1 stage).1)

/-- Realized cumulative public payoff innovation along a full game history. -/
def cumulativeStagePayoffInnovation
    [Fintype ι]
    (prescribed : G.BehaviorProfile) (owner : ι)
    {T : ℕ} (history : G.Hist T) : ℝ :=
  ∑ stage,
    G.historyStagePayoffInnovation prescribed owner
      (G.historyBeforeStage history stage)
      (history.1 stage).2

/-- Predictable cumulative conditional mean of the same score under a
comparison behavior profile. -/
def cumulativeStageGainCompensator
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) {T : ℕ} (history : G.Hist T) : ℝ :=
  ∑ stage,
    (G.stageEUAt comparison
        (G.historyBeforeStage history stage) owner -
      G.stageEUAt prescribed
        (G.historyBeforeStage history stage) owner)

@[simp]
theorem historyBeforeStage_snoc_castSucc
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State)
    (stage : Fin T) :
    G.historyBeforeStage
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1))
        stage.castSucc =
      G.historyBeforeStage history stage := by
  apply Prod.ext
  · funext earlier
    change
      (Fin.snoc history.1 (history.2, jointAction) :
          Fin (T + 1) → G.State × G.JointAct)
          (Fin.castLE
            (Nat.le_of_lt stage.castSucc.isLt) earlier) =
        history.1
          (Fin.castLE (Nat.le_of_lt stage.isLt) earlier)
    have hcast :
        Fin.castLE
            (Nat.le_of_lt stage.castSucc.isLt) earlier =
          Fin.castSucc
            (Fin.castLE (Nat.le_of_lt stage.isLt) earlier) :=
      Fin.ext rfl
    rw [hcast, Fin.snoc_castSucc]
  · change
      ((Fin.snoc history.1 (history.2, jointAction) :
          Fin (T + 1) → G.State × G.JointAct)
          stage.castSucc).1 =
        (history.1 stage).1
    rw [Fin.snoc_castSucc]

@[simp]
theorem historyBeforeStage_snoc_last
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State) :
    G.historyBeforeStage
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1))
        (Fin.last T) =
      history := by
  apply Prod.ext
  · funext earlier
    let earlierT : Fin T :=
      ⟨earlier.val, earlier.isLt⟩
    have hcast :
        Fin.castLE
            (Nat.le_of_lt (Fin.last T).isLt) earlier =
          Fin.castSucc earlierT :=
      Fin.ext rfl
    change
      (Fin.snoc history.1 (history.2, jointAction) :
          Fin (T + 1) → G.State × G.JointAct)
          (Fin.castLE
            (Nat.le_of_lt (Fin.last T).isLt) earlier) =
        history.1 earlier
    rw [hcast, Fin.snoc_castSucc]
    congr
  · change
      ((Fin.snoc history.1 (history.2, jointAction) :
          Fin (T + 1) → G.State × G.JointAct)
          (Fin.last T)).1 =
        history.2
    rw [Fin.snoc_last]

@[simp]
theorem cumulativeStagePayoffInnovation_zero
    [Fintype ι]
    (prescribed : G.BehaviorProfile) (owner : ι)
    (history : G.Hist 0) :
    G.cumulativeStagePayoffInnovation
      prescribed owner history = 0 := by
  simp [cumulativeStagePayoffInnovation]

@[simp]
theorem cumulativeStageGainCompensator_zero
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) (history : G.Hist 0) :
    G.cumulativeStageGainCompensator
      prescribed comparison owner history = 0 := by
  simp [cumulativeStageGainCompensator]

@[simp]
theorem cumulativeStagePayoffInnovation_snoc
    [Fintype ι]
    (prescribed : G.BehaviorProfile) (owner : ι)
    {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State) :
    G.cumulativeStagePayoffInnovation prescribed owner
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1)) =
      G.cumulativeStagePayoffInnovation prescribed owner history +
        G.historyStagePayoffInnovation
          prescribed owner history jointAction := by
  rw [cumulativeStagePayoffInnovation, Fin.sum_univ_castSucc]
  simp only [historyBeforeStage_snoc_castSucc,
    historyBeforeStage_snoc_last, Fin.snoc_castSucc,
    Fin.snoc_last]
  rfl

@[simp]
theorem cumulativeStageGainCompensator_snoc
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) {T : ℕ} (history : G.Hist T)
    (jointAction : G.JointAct) (nextState : G.State) :
    G.cumulativeStageGainCompensator
        prescribed comparison owner
        ((Fin.snoc history.1 (history.2, jointAction), nextState) :
          G.Hist (T + 1)) =
      G.cumulativeStageGainCompensator
          prescribed comparison owner history +
        (G.stageEUAt comparison history owner -
          G.stageEUAt prescribed history owner) := by
  rw [cumulativeStageGainCompensator, Fin.sum_univ_castSucc]
  simp only [historyBeforeStage_snoc_castSucc,
    historyBeforeStage_snoc_last]
  rfl

/-- Finite-horizon compensator identity for arbitrary comparison behavior:
expected cumulative public innovation equals the expected predictable sum
of historywise stage-payoff gains. -/
theorem expect_cumulativeStagePayoffInnovation_eq_compensator
    [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed comparison : G.BehaviorProfile)
    (s₀ : G.State) (owner : ι) (T : ℕ) :
    expect (G.histDist comparison s₀ T)
        (G.cumulativeStagePayoffInnovation
          prescribed owner) =
      expect (G.histDist comparison s₀ T)
        (G.cumulativeStageGainCompensator
          prescribed comparison owner) := by
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
              (G.cumulativeStagePayoffInnovation
                prescribed owner)) =
            fun history =>
              G.cumulativeStagePayoffInnovation
                  prescribed owner history +
                (G.stageEUAt comparison history owner -
                  G.stageEUAt prescribed history owner) := by
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
                (G.cumulativeStagePayoffInnovation
                  prescribed owner) =
              G.cumulativeStagePayoffInnovation
                  prescribed owner history +
                G.historyStagePayoffInnovation
                  prescribed owner history jointAction := by
          rw [expect_bind]
          simp only [expect_pure,
            cumulativeStagePayoffInnovation_snoc]
          exact expect_const _ _
        simp_rw [haction]
        rw [expect_add, expect_const,
          G.expect_historyStagePayoffInnovation_eq_stageEUAt_sub]
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
              (G.cumulativeStageGainCompensator
                prescribed comparison owner)) =
            fun history =>
              G.cumulativeStageGainCompensator
                  prescribed comparison owner history +
                (G.stageEUAt comparison history owner -
                  G.stageEUAt prescribed history owner) := by
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
                (G.cumulativeStageGainCompensator
                  prescribed comparison owner) =
              G.cumulativeStageGainCompensator
                  prescribed comparison owner history +
                (G.stageEUAt comparison history owner -
                  G.stageEUAt prescribed history owner) := by
          rw [expect_bind]
          simp only [expect_pure,
            cumulativeStageGainCompensator_snoc]
          exact expect_const _ _
        simp_rw [haction]
        exact expect_const _ _
      rw [hinnovation, hcompensator,
        expect_add, expect_add, ih]

/-- Specialization of the cumulative compensator identity to an arbitrary
unilateral behavior deviation. -/
theorem expect_cumulativeStagePayoffInnovation_eq_behaviorDeviationCompensator
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (prescribed : G.BehaviorProfile) (owner : ι)
    (deviation : G.BehaviorStrategy owner)
    (s₀ : G.State) (T : ℕ) :
    expect
        (G.histDist
          (Function.update prescribed owner deviation) s₀ T)
        (G.cumulativeStagePayoffInnovation
          prescribed owner) =
      expect
        (G.histDist
          (Function.update prescribed owner deviation) s₀ T)
        (G.cumulativeStageGainCompensator
          prescribed
          (Function.update prescribed owner deviation)
          owner) :=
  G.expect_cumulativeStagePayoffInnovation_eq_compensator
    prescribed (Function.update prescribed owner deviation)
    s₀ owner T

/-- Adverse noise is the predictable gain compensator minus realized public
innovation. -/
def stagePayoffInnovationAdverseNoise
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) {T : ℕ} (history : G.Hist T) : ℝ :=
  G.cumulativeStageGainCompensator
      prescribed comparison owner history -
    G.cumulativeStagePayoffInnovation
      prescribed owner history

/-- Exact pathwise decomposition consumed by the comparison side of
`HorizonFreePublicDetector`. -/
theorem cumulativeStagePayoffInnovation_eq_compensator_sub_adverseNoise
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) {T : ℕ} (history : G.Hist T) :
    G.cumulativeStagePayoffInnovation prescribed owner history =
      G.cumulativeStageGainCompensator
          prescribed comparison owner history -
        G.stagePayoffInnovationAdverseNoise
          prescribed comparison owner history := by
  rw [stagePayoffInnovationAdverseNoise]
  ring

/-- Any deterministic lower signal for the cumulative stage-gain
compensator supplies the `comparisonLower` inequality required by the
horizon-free detector interface. Martingale and measurable-process fields
remain separate concrete play-law obligations. -/
theorem signal_sub_adverseNoise_le_cumulativeStagePayoffInnovation
    [Fintype ι]
    (prescribed comparison : G.BehaviorProfile)
    (owner : ι) {T : ℕ} (history : G.Hist T)
    (signal : ℝ)
    (hsignal :
      signal ≤
        G.cumulativeStageGainCompensator
          prescribed comparison owner history) :
    signal -
        G.stagePayoffInnovationAdverseNoise
          prescribed comparison owner history ≤
      G.cumulativeStagePayoffInnovation
        prescribed owner history := by
  rw [
    G.cumulativeStagePayoffInnovation_eq_compensator_sub_adverseNoise
      prescribed comparison owner history
  ]
  exact sub_le_sub_right hsignal _

end StochasticGame
end GameTheory
