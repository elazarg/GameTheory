/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FinkObstruction
import Math.OnlineLearning.AnytimeMultiplicativeWeights
import Math.Probability.Adaptive

/-!
# Anytime public monitors for Fink transition obstructions

The fixed coordinate-test family from `FinkObstruction` is used as the action set of the
horizon-independent signed multiplicative-weights learner. For any realized successor-state
stream, the learner captures the cumulative score of every destination/sign monitor up to
vanishing average regret.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability
open Filter

/-- The finite monitor family: a destination state and one of its two score orientations. -/
abbrev PMFCoordinateMonitor (Ω : Type) := Ω × Bool

/-- Public score obtained by mixing the destination/sign tests with an arbitrary monitor
    distribution. In a sequential construction the distribution may be chosen from the public
    history before the next outcome is observed. -/
def weightedPMFCoordinateMonitorScore {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω) (monitorDist : PMF (PMFCoordinateMonitor Ω)) (x : Ω) : ℝ :=
  expect monitorDist (fun monitor =>
    pmfCoordinateTestScore baseline monitor.1 monitor.2 x)

theorem abs_weightedPMFCoordinateMonitorScore_le_one
    {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω) (monitorDist : PMF (PMFCoordinateMonitor Ω)) (x : Ω) :
    |weightedPMFCoordinateMonitorScore baseline monitorDist x| ≤ 1 := by
  exact abs_expect_le_of_abs_le monitorDist _ fun monitor =>
    abs_pmfCoordinateTestScore_le_one baseline monitor.1 monitor.2 x

theorem weightedPMFCoordinateMonitorScore_mem_Icc
    {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω) (monitorDist : PMF (PMFCoordinateMonitor Ω)) (x : Ω) :
    weightedPMFCoordinateMonitorScore baseline monitorDist x ∈
      Set.Icc (-1 : ℝ) 1 :=
  abs_le.mp (abs_weightedPMFCoordinateMonitorScore_le_one baseline monitorDist x)

/-- Every predictable mixture of the coordinate monitors remains exactly centered under the
    baseline kernel. This is the one-step conditional-centering interface for a public account. -/
theorem expect_weightedPMFCoordinateMonitorScore_baseline
    {Ω : Type} [Finite Ω] [DecidableEq Ω]
    (baseline : PMF Ω) (monitorDist : PMF (PMFCoordinateMonitor Ω)) :
    expect baseline (weightedPMFCoordinateMonitorScore baseline monitorDist) = 0 := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  rw [show weightedPMFCoordinateMonitorScore baseline monitorDist = fun x =>
      ∑ monitor, (monitorDist monitor).toReal *
        pmfCoordinateTestScore baseline monitor.1 monitor.2 x by
    funext x
    exact expect_eq_sum _ _]
  rw [← expect_sum_comm]
  apply Finset.sum_eq_zero
  intro monitor _
  rw [expect_const_mul, expect_pmfCoordinateTestScore_baseline, mul_zero]

/-- Fubini formula for the expectation of a weighted coordinate-monitor score. -/
theorem expect_weightedPMFCoordinateMonitorScore
    {Ω : Type} [Finite Ω] [DecidableEq Ω]
    (baseline comparison : PMF Ω)
    (monitorDist : PMF (PMFCoordinateMonitor Ω)) :
    expect comparison (weightedPMFCoordinateMonitorScore baseline monitorDist) =
      expect monitorDist (fun monitor =>
        expect comparison
          (pmfCoordinateTestScore baseline monitor.1 monitor.2)) := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  rw [show weightedPMFCoordinateMonitorScore baseline monitorDist = fun x =>
      ∑ monitor, (monitorDist monitor).toReal *
        pmfCoordinateTestScore baseline monitor.1 monitor.2 x by
    funext x
    exact expect_eq_sum _ _]
  rw [← expect_sum_comm, expect_eq_sum]
  exact Finset.sum_congr rfl fun monitor _ => by
    rw [expect_const_mul]

/-- Under a comparison kernel, the weighted score is the monitor-distribution average of the
    oriented destination-probability differences. -/
theorem expect_weightedPMFCoordinateMonitorScore_eq_difference
    {Ω : Type} [Finite Ω] [DecidableEq Ω]
    (baseline comparison : PMF Ω)
    (monitorDist : PMF (PMFCoordinateMonitor Ω)) :
    expect comparison (weightedPMFCoordinateMonitorScore baseline monitorDist) =
      expect monitorDist (fun monitor =>
        (if monitor.2 then 1 else -1) *
          ((comparison monitor.1).toReal - (baseline monitor.1).toReal)) := by
  rw [expect_weightedPMFCoordinateMonitorScore]
  congr 1
  funext monitor
  exact expect_pmfCoordinateTestScore baseline comparison monitor.1 monitor.2

/-- Predictable weighted score selected from a finite public outcome history. -/
def predictablePMFCoordinateMonitorScore {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω)
    (monitorChoice : ∀ n, (Fin n → Ω) → PMF (PMFCoordinateMonitor Ω))
    (n : ℕ) (history : Fin n → Ω) (x : Ω) : ℝ :=
  weightedPMFCoordinateMonitorScore baseline (monitorChoice n history) x

theorem abs_predictablePMFCoordinateMonitorScore_le_one
    {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω)
    (monitorChoice : ∀ n, (Fin n → Ω) → PMF (PMFCoordinateMonitor Ω))
    (n : ℕ) (history : Fin n → Ω) (x : Ω) :
    |predictablePMFCoordinateMonitorScore baseline monitorChoice n history x| ≤ 1 :=
  abs_weightedPMFCoordinateMonitorScore_le_one baseline (monitorChoice n history) x

/-- Law of the first `T` public outcomes when every conditional next-outcome kernel is the fixed
    baseline PMF. -/
def baselinePMFHistoryLaw {Ω : Type} (baseline : PMF Ω) (T : ℕ) :
    PMF (Fin T → Ω) :=
  adaptiveHistoryLaw (fun _ _ => baseline) T

/-- Cumulative score generated by predictable monitor choices along a public outcome history. -/
def predictablePMFCoordinateMonitorCumulativeScore
    {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω)
    (monitorChoice : ∀ n, (Fin n → Ω) → PMF (PMFCoordinateMonitor Ω))
    (T : ℕ) (history : Fin T → Ω) : ℝ :=
  predictableScoreSum
    (predictablePMFCoordinateMonitorScore baseline monitorChoice) T history

/-- Exact finite-horizon martingale identity: under the baseline history law, every sequence of
    monitor mixtures chosen from the prior public outcomes has zero expected cumulative score. -/
theorem expect_predictablePMFCoordinateMonitorCumulativeScore_baseline_eq_zero
    {Ω : Type} [Finite Ω] [DecidableEq Ω]
    (baseline : PMF Ω)
    (monitorChoice : ∀ n, (Fin n → Ω) → PMF (PMFCoordinateMonitor Ω))
    (T : ℕ) :
    expect (baselinePMFHistoryLaw baseline T)
        (predictablePMFCoordinateMonitorCumulativeScore baseline monitorChoice T) = 0 := by
  exact expect_predictableScoreSum_eq_zero
    (fun _ _ => baseline)
    (predictablePMFCoordinateMonitorScore baseline monitorChoice)
    (fun n history =>
      expect_weightedPMFCoordinateMonitorScore_baseline baseline
        (monitorChoice n history))
    T

/-- Cumulative conditional drift of the predictable weighted monitor under a history-dependent
    comparison kernel. -/
def predictablePMFCoordinateMonitorConditionalDriftSum
    {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω)
    (comparison : ∀ n, (Fin n → Ω) → PMF Ω)
    (monitorChoice : ∀ n, (Fin n → Ω) → PMF (PMFCoordinateMonitor Ω))
    (T : ℕ) (history : Fin T → Ω) : ℝ :=
  predictableConditionalMeanSum comparison
    (predictablePMFCoordinateMonitorScore baseline monitorChoice) T history

@[simp] theorem predictablePMFCoordinateMonitorConditionalDriftSum_snoc
    {Ω : Type} [Finite Ω] [DecidableEq Ω]
    (baseline : PMF Ω)
    (comparison : ∀ n, (Fin n → Ω) → PMF Ω)
    (monitorChoice : ∀ n, (Fin n → Ω) → PMF (PMFCoordinateMonitor Ω))
    (n : ℕ) (history : Fin n → Ω) (x : Ω) :
    predictablePMFCoordinateMonitorConditionalDriftSum
        baseline comparison monitorChoice (n + 1) (Fin.snoc history x) =
      predictablePMFCoordinateMonitorConditionalDriftSum
          baseline comparison monitorChoice n history +
        expect (monitorChoice n history) (fun monitor =>
          (if monitor.2 then 1 else -1) *
            (((comparison n history) monitor.1).toReal -
              (baseline monitor.1).toReal)) := by
  rw [predictablePMFCoordinateMonitorConditionalDriftSum,
    predictableConditionalMeanSum_snoc]
  change _ + expect (comparison n history)
      (weightedPMFCoordinateMonitorScore baseline (monitorChoice n history)) = _
  rw [expect_weightedPMFCoordinateMonitorScore_eq_difference]
  rfl

/-- Expected cumulative score under an arbitrary adaptive comparison law equals its expected
    cumulative oriented coordinate drift. -/
theorem expect_predictablePMFCoordinateMonitorCumulativeScore_eq_drift
    {Ω : Type} [Finite Ω] [DecidableEq Ω]
    (baseline : PMF Ω)
    (comparison : ∀ n, (Fin n → Ω) → PMF Ω)
    (monitorChoice : ∀ n, (Fin n → Ω) → PMF (PMFCoordinateMonitor Ω))
    (T : ℕ) :
    expect (adaptiveHistoryLaw comparison T)
        (predictablePMFCoordinateMonitorCumulativeScore baseline monitorChoice T) =
      expect (adaptiveHistoryLaw comparison T)
        (predictablePMFCoordinateMonitorConditionalDriftSum
          baseline comparison monitorChoice T) := by
  exact expect_predictableScoreSum_eq_expect_conditionalMeanSum comparison
    (predictablePMFCoordinateMonitorScore baseline monitorChoice) T

/-- Realized signed gain of a coordinate monitor on an observed outcome stream. -/
def pmfCoordinateMonitorGain {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω)
    (round : ℕ) (monitor : PMFCoordinateMonitor Ω) : ℝ :=
  pmfCoordinateTestScore baseline monitor.1 monitor.2 (observation round)

theorem pmfCoordinateMonitorGain_mem_Icc {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω) :
    ∀ round monitor,
      pmfCoordinateMonitorGain baseline observation round monitor ∈
        Set.Icc (-1 : ℝ) 1 := by
  intro round monitor
  exact abs_le.mp
    (abs_pmfCoordinateTestScore_le_one baseline monitor.1 monitor.2 (observation round))

/-- Total weighted score of the fixed anytime learner on the coordinate-monitor family. -/
def anytimePMFCoordinateMonitorAlgGain {Ω : Type} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (baseline : PMF Ω) (observation : ℕ → Ω) (T : ℕ) : ℝ :=
  Math.OnlineLearning.anytimeSignedAlgGain
    (pmfCoordinateMonitorGain baseline observation) T

/-- Coordinate-monitor distribution played at absolute round `t`. -/
def anytimePMFCoordinateMonitorDist {Ω : Type} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (baseline : PMF Ω) (observation : ℕ → Ω) (t : ℕ) :
    PMF (PMFCoordinateMonitor Ω) :=
  Math.OnlineLearning.anytimeSignedMWDist
    (pmfCoordinateMonitorGain baseline observation) t

/-- The coordinate-monitor algorithm gain is exactly its cumulative realized weighted public
    score. -/
theorem anytimePMFCoordinateMonitorAlgGain_eq_sum_weightedScore
    {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω) (T : ℕ) :
    anytimePMFCoordinateMonitorAlgGain baseline observation T =
      ∑ t ∈ Finset.range T,
        weightedPMFCoordinateMonitorScore baseline
          (anytimePMFCoordinateMonitorDist baseline observation t) (observation t) := by
  rw [anytimePMFCoordinateMonitorAlgGain,
    Math.OnlineLearning.anytimeSignedAlgGain_eq_sum]
  rfl

/-- Gain stream obtained from a finite public history. Values at rounds outside the history are
    set to zero; causality ensures that this arbitrary continuation does not affect earlier
    monitor choices. -/
def pmfCoordinateMonitorFinHistoryGain
    {Ω : Type} [DecidableEq Ω] {n : ℕ} (baseline : PMF Ω)
    (history : Fin n → Ω) (round : ℕ) (monitor : PMFCoordinateMonitor Ω) : ℝ :=
  if hround : round < n then
    pmfCoordinateTestScore baseline monitor.1 monitor.2
      (history ⟨round, hround⟩)
  else 0

/-- Anytime coordinate-monitor choice determined by exactly the preceding finite public
    history. -/
def predictableAnytimePMFCoordinateMonitorChoice
    {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (baseline : PMF Ω) (n : ℕ) (history : Fin n → Ω) :
    PMF (PMFCoordinateMonitor Ω) :=
  Math.OnlineLearning.anytimeSignedMWDist
    (pmfCoordinateMonitorFinHistoryGain baseline history) n

/-- Causality of the public monitor: evaluating the finite-history choice on the prefix of any
    full observation stream gives exactly the absolute-time monitor distribution for that stream. -/
theorem predictableAnytimePMFCoordinateMonitorChoice_prefix
    {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω) (n : ℕ) :
    predictableAnytimePMFCoordinateMonitorChoice baseline n
        (fun i => observation i) =
      anytimePMFCoordinateMonitorDist baseline observation n := by
  apply Math.OnlineLearning.anytimeSignedMWDist_congr_of_forall_lt
  intro s hs
  funext monitor
  simp [pmfCoordinateMonitorFinHistoryGain, pmfCoordinateMonitorGain, hs]

/-- The actual causal anytime monitor has zero expected cumulative score under the baseline
    public-history law at every horizon. -/
theorem expect_predictableAnytimePMFCoordinateMonitorCumulativeScore_baseline_eq_zero
    {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (baseline : PMF Ω) (T : ℕ) :
    expect (baselinePMFHistoryLaw baseline T)
        (predictablePMFCoordinateMonitorCumulativeScore baseline
          (predictableAnytimePMFCoordinateMonitorChoice baseline) T) = 0 := by
  exact expect_predictablePMFCoordinateMonitorCumulativeScore_baseline_eq_zero
    baseline (predictableAnytimePMFCoordinateMonitorChoice baseline) T

/-- Under an adaptive comparison law, the actual causal anytime monitor's expected cumulative
    score equals its expected cumulative oriented coordinate drift. -/
theorem expect_predictableAnytimePMFCoordinateMonitorCumulativeScore_eq_drift
    {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (baseline : PMF Ω)
    (comparison : ∀ n, (Fin n → Ω) → PMF Ω)
    (T : ℕ) :
    expect (adaptiveHistoryLaw comparison T)
        (predictablePMFCoordinateMonitorCumulativeScore baseline
          (predictableAnytimePMFCoordinateMonitorChoice baseline) T) =
      expect (adaptiveHistoryLaw comparison T)
        (predictablePMFCoordinateMonitorConditionalDriftSum baseline comparison
          (predictableAnytimePMFCoordinateMonitorChoice baseline) T) := by
  exact expect_predictablePMFCoordinateMonitorCumulativeScore_eq_drift
    baseline comparison (predictableAnytimePMFCoordinateMonitorChoice baseline) T

/-- Every fixed coordinate monitor has vanishing positive average regret against the one
    horizon-independent weighted monitor. This statement is pathwise in the observed outcomes. -/
theorem eventually_anytimePMFCoordinateMonitor_regret_div_lt
    {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ monitor : PMFCoordinateMonitor Ω,
      (Math.OnlineLearning.cumGain
          (pmfCoordinateMonitorGain baseline observation) T monitor
          - anytimePMFCoordinateMonitorAlgGain baseline observation T) / T < ε := by
  exact Math.OnlineLearning.eventually_anytimeSigned_fixedActionRegret_div_lt
    (pmfCoordinateMonitorGain_mem_Icc baseline observation) hε

/-- Equivalent capture form: every fixed monitor's average realized score is eventually below
    the learner's average weighted score plus any positive tolerance. -/
theorem eventually_pmfCoordinateMonitor_cumGain_div_lt_algGain_div_add
    {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ monitor : PMFCoordinateMonitor Ω,
      Math.OnlineLearning.cumGain
          (pmfCoordinateMonitorGain baseline observation) T monitor / T
        < anytimePMFCoordinateMonitorAlgGain baseline observation T / T + ε := by
  filter_upwards [
    eventually_anytimePMFCoordinateMonitor_regret_div_lt baseline observation hε
  ] with T hT
  intro monitor
  have hmonitor := hT monitor
  rw [sub_div] at hmonitor
  linarith

namespace NormalizedFinkSupportTangentObstructionFlow

/-- Pair-valued form of the transition-visible monitor certificate, matching the action type of
    the anytime coordinate-monitor learner. -/
theorem exists_pureDeviationCoordinateMonitor_spec
    (G : StochasticGame ι)
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who)
    (hkernel :
      G.finkPureDeviationStateKernel z s who d ≠
        G.finkStateKernel z s) :
    ∃ monitor : PMFCoordinateMonitor G.State,
      expect (G.finkStateKernel z s)
          (pmfCoordinateTestScore
            (G.finkStateKernel z s) monitor.1 monitor.2) = 0 ∧
        0 <
          expect (G.finkPureDeviationStateKernel z s who d)
            (pmfCoordinateTestScore
              (G.finkStateKernel z s) monitor.1 monitor.2) ∧
        ∀ x,
          |pmfCoordinateTestScore
            (G.finkStateKernel z s) monitor.1 monitor.2 x| ≤ 1 := by
  obtain ⟨t, positive, hbaseline, hpositive, hbound⟩ :=
    exists_pureDeviationCoordinateTestScore_spec G z s who d hkernel
  exact ⟨(t, positive), hbaseline, hpositive, hbound⟩

end NormalizedFinkSupportTangentObstructionFlow

end StochasticGame
end GameTheory
