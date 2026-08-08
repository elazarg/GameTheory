/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Equilibrium.Uniform
import GameTheory.Concepts.Stochastic.Core.StageGame
import Math.PMFIter
import Math.MeanErgodic

/-!
# Uniform Equilibria under Action-Independent Transitions

Proved special case of the uniform equilibrium existence problem
(`StochasticGame.exists_uniformEquilibriumPayoff`): if the transition kernel
does not depend on the chosen actions — a "no control" game — then no player
can influence the state process, so the Markov profile that plays a mixed
Nash equilibrium of the current stage game at every state is an *exact* Nash
equilibrium of the `T`-stage game for every horizon `T`.  A single profile
is therefore a uniform ε-equilibrium for every `ε > 0` simultaneously, and
its average payoffs converge by the mean ergodic theorem for finite Markov
chains (`Math.MeanErgodic.tendsto_cesaro_expect_iter`), giving a full
uniform equilibrium payoff.

The formal content of "no control" is that the state marginal of the
history distribution is the iterated kernel (`Math.PMFIter.iter`), for
*every* behavior profile.

## Main results

* `StochasticGame.map_snd_histDist_of_forall_transition_eq` — under
  action-independent transitions the state marginal is the iterated kernel,
  for every profile
* `StochasticGame.isεHorizonNash_markovBehaviorProfile` — per-state
  stage-Nash Markov play is an ε-Nash equilibrium at every horizon, every
  `ε ≥ 0`
* `StochasticGame.exists_forall_isUniformεEquilibrium_of_isActionIndependent`
  — one profile that is a uniform ε-equilibrium for every `ε > 0`
* `StochasticGame.exists_uniformEquilibriumPayoff_of_isActionIndependent`
  — action-independent games have uniform equilibrium payoffs
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace StochasticGame

open Filter Math.Probability Math.PMFProduct

variable {ι : Type}

/-- The transitions of `G` do not depend on the chosen actions: the state
process is an autonomous Markov chain. -/
def IsActionIndependent (G : StochasticGame ι) : Prop :=
  ∀ (s : G.State) (a a' : G.JointAct), G.transition s a = G.transition s a'

-- ============================================================================
-- The state marginal under action-independent transitions
-- ============================================================================

/-- Under action-independent transitions the state marginal of the history
distribution is the iterated kernel — regardless of the behavior profile.
The autonomous kernel is supplied as any `κ` agreeing with the
transitions. -/
theorem map_snd_histDist_of_forall_transition_eq
    (G : StochasticGame ι) [Fintype ι]
    {κ : G.State → PMF G.State} (hκ : ∀ s a, G.transition s a = κ s)
    (σ : G.BehaviorProfile) (s₀ : G.State) :
    ∀ t : ℕ,
      (G.histDist σ s₀ t).map Prod.snd = Math.PMFIter.iter κ t s₀ := by
  intro t
  induction t with
  | zero => simp [emptyHist, PMF.pure_map]
  | succ t ih =>
    rw [Math.PMFIter.iter_succ', ← ih, histDist_succ, PMF.bind_map]
    simp only [PMF.map_bind, PMF.pure_map, PMF.bind_pure]
    congr 1
    funext h
    simp only [Function.comp_apply, hκ]
    exact PMF.bind_const _ _

/-- Expectations of state functions along play depend only on the iterated
kernel, not on the behavior profile. -/
theorem expect_snd_histDist_of_forall_transition_eq
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    {κ : G.State → PMF G.State} (hκ : ∀ s a, G.transition s a = κ s)
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) (w : G.State → ℝ) :
    expect (G.histDist σ s₀ t) (fun h => w h.2) =
      expect (Math.PMFIter.iter κ t s₀) w := by
  letI : Fintype G.State := Fintype.ofFinite G.State
  rw [← G.map_snd_histDist_of_forall_transition_eq hκ σ s₀ t,
    Math.Probability.expect_map_fintype_target]

/-- Under action-independent transitions, the expected total payoff of
Markov play is the sum of the expected stage values along the autonomous
state chain. -/
theorem expect_totalPayoff_markovBehaviorProfile
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    {κ : G.State → PMF G.State} (hκ : ∀ s a, G.transition s a = κ s)
    (x : (s : G.State) → ∀ i, PMF (G.Act i)) (s₀ : G.State) (who : ι) :
    ∀ T : ℕ,
      expect (G.histDist (G.markovBehaviorProfile x) s₀ T)
          (fun h => G.totalPayoff who h) =
        ∑ t ∈ Finset.range T,
          expect (Math.PMFIter.iter κ t s₀)
            (fun s => G.mixedStageEU s (x s) who) := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
    rw [G.expect_totalPayoff_succ, ih, Finset.sum_range_succ]
    congr 1
    calc expect (G.histDist (G.markovBehaviorProfile x) s₀ T)
          (fun h => G.stageEUAt (G.markovBehaviorProfile x) h who)
        = expect (G.histDist (G.markovBehaviorProfile x) s₀ T)
            (fun h => G.mixedStageEU h.2 (x h.2) who) := rfl
      _ = expect (Math.PMFIter.iter κ T s₀)
            (fun s => G.mixedStageEU s (x s) who) :=
          G.expect_snd_histDist_of_forall_transition_eq hκ
            (G.markovBehaviorProfile x) s₀ T
            (fun s => G.mixedStageEU s (x s) who)

/-- Average-payoff version of `expect_totalPayoff_markovBehaviorProfile`. -/
theorem finiteAveragePayoff_markovBehaviorProfile
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    {κ : G.State → PMF G.State} (hκ : ∀ s a, G.transition s a = κ s)
    (x : (s : G.State) → ∀ i, PMF (G.Act i)) (s₀ : G.State) (who : ι)
    (T : ℕ) :
    G.finiteAveragePayoff s₀ T (G.markovBehaviorProfile x) who =
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        expect (Math.PMFIter.iter κ t s₀)
          (fun s => G.mixedStageEU s (x s) who) := by
  rw [finiteAveragePayoff,
    G.expect_totalPayoff_markovBehaviorProfile hκ x s₀ who T]

-- ============================================================================
-- Per-state stage-Nash Markov play is an equilibrium at every horizon
-- ============================================================================

/-- Under action-independent transitions, Markov play of per-state mixed
stage Nash equilibria is an ε-Nash equilibrium of the `T`-stage game for
every horizon `T` and every `ε ≥ 0` — an exact equilibrium of every finite
truncation. -/
theorem isεHorizonNash_markovBehaviorProfile
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    {κ : G.State → PMF G.State} (hκ : ∀ s a, G.transition s a = κ s)
    {x : (s : G.State) → ∀ i, PMF (G.Act i)} (hx : G.IsMixedStageNash x)
    (s₀ : G.State) (T : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    G.IsεHorizonNash s₀ T ε (G.markovBehaviorProfile x) := by
  intro who dev
  -- On the equilibrium path the expected total payoff is the sum of the
  -- expected stage-Nash values along the autonomous state chain.
  have hOn := G.expect_totalPayoff_markovBehaviorProfile hκ x s₀ who
  -- Against any unilateral deviation, every stage contributes at most the
  -- stage-Nash value of the current state; the state chain is unchanged.
  have hOff : ∀ T : ℕ,
      expect
          (G.histDist
            (Function.update (G.markovBehaviorProfile x) who dev) s₀ T)
          (fun h => G.totalPayoff who h) ≤
        ∑ t ∈ Finset.range T,
          expect (Math.PMFIter.iter κ t s₀)
            (fun s => G.mixedStageEU s (x s) who) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [G.expect_totalPayoff_succ, Finset.sum_range_succ]
      have hstage :
          expect
              (G.histDist
                (Function.update (G.markovBehaviorProfile x) who dev) s₀ T)
              (fun h =>
                G.stageEUAt
                  (Function.update (G.markovBehaviorProfile x) who dev)
                  h who) ≤
            expect (Math.PMFIter.iter κ T s₀)
              (fun s => G.mixedStageEU s (x s) who) := by
        rw [← G.expect_snd_histDist_of_forall_transition_eq hκ
          (Function.update (G.markovBehaviorProfile x) who dev) s₀ T
          (fun s => G.mixedStageEU s (x s) who)]
        apply expect_mono
        intro h
        unfold stageEUAt
        rw [G.stageActionDist_update_markovBehaviorProfile]
        exact hx h.2 who (dev T h)
      linarith
  -- Divide by the horizon.
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    simpa using hε
  · have hTnn : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
    have h1 := mul_le_mul_of_nonneg_left (hOff T) hTnn
    unfold finiteAveragePayoff
    rw [hOn T]
    linarith

/-- **Action-independent ("no control") games admit uniform ε-equilibria for
every ε simultaneously**: one Markov profile of per-state stage-Nash mixed
actions is an exact Nash equilibrium of every finite-horizon game. -/
theorem exists_forall_isUniformεEquilibrium_of_isActionIndependent
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (hAI : G.IsActionIndependent) (s₀ : G.State) :
    ∃ σ : G.BehaviorProfile,
      ∀ ε : ℝ, 0 < ε → G.IsUniformεEquilibrium s₀ ε σ := by
  obtain ⟨x, hx⟩ := G.exists_isMixedStageNash
  have hκ : ∀ s a, G.transition s a =
      (fun s' => G.transition s' (Classical.arbitrary G.JointAct)) s :=
    fun s a => hAI s a (Classical.arbitrary G.JointAct)
  exact ⟨G.markovBehaviorProfile x, fun ε hε =>
    ⟨0, fun T _ =>
      G.isεHorizonNash_markovBehaviorProfile hκ hx s₀ T hε.le⟩⟩

/-- **Action-independent games have uniform equilibrium payoffs**: with an
autonomous state process, Markov stage-Nash play is an exact equilibrium of
every horizon, and its average payoffs converge by the mean ergodic theorem
for finite Markov chains (`Math.MeanErgodic.tendsto_cesaro_expect_iter`).
This settles the action-independent special case of
`exists_uniformEquilibriumPayoff`. -/
theorem exists_uniformEquilibriumPayoff_of_isActionIndependent
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (hAI : G.IsActionIndependent) (s₀ : G.State) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  obtain ⟨x, hx⟩ := G.exists_isMixedStageNash
  have hκ : ∀ s a, G.transition s a =
      (fun s' => G.transition s' (Classical.arbitrary G.JointAct)) s :=
    fun s a => hAI s a (Classical.arbitrary G.JointAct)
  -- Average payoffs of the Markov profile converge, per player.
  have hconv : ∀ who : ι, ∃ v : ℝ, Tendsto
      (fun T : ℕ =>
        G.finiteAveragePayoff s₀ T (G.markovBehaviorProfile x) who)
      atTop (nhds v) := by
    intro who
    obtain ⟨v, hv⟩ := Math.MeanErgodic.tendsto_cesaro_expect_iter
      (fun s' => G.transition s' (Classical.arbitrary G.JointAct))
      (fun s => G.mixedStageEU s (x s) who) s₀
    exact ⟨v, hv.congr fun T =>
      (G.finiteAveragePayoff_markovBehaviorProfile hκ x s₀ who T).symm⟩
  choose v hv using hconv
  refine ⟨v, fun ε hε => ⟨G.markovBehaviorProfile x, ?_⟩⟩
  -- One horizon threshold works for all (finitely many) players.
  have hev : ∀ᶠ T : ℕ in atTop, ∀ who : ι,
      |G.finiteAveragePayoff s₀ T (G.markovBehaviorProfile x) who -
        v who| ≤ ε := by
    rw [eventually_all]
    intro who
    have hball : ∀ᶠ y : ℝ in nhds (v who), |y - v who| ≤ ε := by
      filter_upwards [Metric.closedBall_mem_nhds (v who) hε] with y hy
      simpa [Real.dist_eq] using hy
    exact (hv who).eventually hball
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  refine ⟨T₀, fun T hT => ⟨?_, hT₀ T hT⟩⟩
  exact G.isεHorizonNash_markovBehaviorProfile hκ hx s₀ T hε.le

end StochasticGame

end GameTheory
