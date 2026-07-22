/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.PMFProduct
import GameTheory.Languages.MultiRound.StochasticGame

/-!
# Behavior Strategies and Finite-Horizon Payoffs in Stochastic Games

Play of a stochastic game (`StochasticGame`) under history-dependent behavior
strategies: finite histories, the distribution over histories induced by a
behavior profile and the transition kernel, and expected average payoffs over
a finite horizon.

The model is the standard one of the uniform-equilibrium literature (Shapley
1953; Mertens–Neyman 1981; Vieille 2000): play starts at an initial state;
at every stage each player observes the entire history — all past states and
joint actions, plus the current state — and randomizes independently over
their own actions; the next state is drawn from the transition kernel.  The
`discount` field of `StochasticGame` plays no role here: finite-horizon
average payoffs are the payoff aggregations that uniform solution concepts
quantify over (see `GameTheory.Concepts.Stochastic.Uniform`).

## Main definitions

* `StochasticGame.Hist` — histories: past stage records plus current state
* `StochasticGame.BehaviorStrategy` / `StochasticGame.BehaviorProfile` —
  history-dependent randomized strategies
* `StochasticGame.histDist` — distribution over histories after `t` stages
* `StochasticGame.totalPayoff` / `StochasticGame.finiteAveragePayoff` —
  accumulated payoff along a history and expected average payoff over a
  finite horizon
* `StochasticGame.stageEUAt` — expected next-stage payoff after a history

## Main results

* `StochasticGame.expect_totalPayoff_succ` — one-step recursion for the
  expected total payoff
* `StochasticGame.mem_support_histDist_succ` — how `histDist` supports unfold
* `StochasticGame.abs_finiteAveragePayoff_le` — stage payoff bounds bound all
  finite-horizon average payoffs
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace StochasticGame

open Math.Probability Math.PMFProduct

variable {ι : Type}

/-- A joint (pure) action profile: one action per player. -/
abbrev JointAct (G : StochasticGame ι) : Type := ∀ i, G.Act i

/-- Record of the first `t` completed stages: for each past stage, the state
that was visited and the joint action that was played there. -/
abbrev StageRecord (G : StochasticGame ι) (t : ℕ) : Type :=
  Fin t → G.State × G.JointAct

/-- A history at decision epoch `t`: the record of the `t` completed stages
together with the current state. -/
abbrev Hist (G : StochasticGame ι) (t : ℕ) : Type := G.StageRecord t × G.State

/-- A behavior strategy for player `i`: an independent mixed action after
every finite history. -/
abbrev BehaviorStrategy (G : StochasticGame ι) (i : ι) : Type :=
  (t : ℕ) → G.Hist t → PMF (G.Act i)

/-- A behavior strategy profile. -/
abbrev BehaviorProfile (G : StochasticGame ι) : Type :=
  ∀ i, G.BehaviorStrategy i

/-- The stationary behavior profile that plays the fixed mixed action `x i`
after every history. -/
def stationaryBehaviorProfile (G : StochasticGame ι)
    (x : ∀ i, PMF (G.Act i)) : G.BehaviorProfile :=
  fun i _ _ => x i

/-- The empty history at initial state `s₀`. -/
def emptyHist (G : StochasticGame ι) (s₀ : G.State) : G.Hist 0 :=
  (Fin.elim0, s₀)

/-- The joint mixed action chosen after history `h` under profile `σ`:
players randomize independently. -/
def stageActionDist (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) : PMF G.JointAct :=
  pmfPi fun i => σ i t h

@[simp] theorem stageActionDist_stationaryBehaviorProfile
    (G : StochasticGame ι) [Fintype ι] (x : ∀ i, PMF (G.Act i))
    {t : ℕ} (h : G.Hist t) :
    G.stageActionDist (G.stationaryBehaviorProfile x) h = pmfPi x :=
  rfl

/-- Deviating from stationary play chooses the deviator's current mixed
action and keeps the opponents' stationary mixed actions. -/
theorem stageActionDist_update_stationaryBehaviorProfile
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (x : ∀ i, PMF (G.Act i)) (who : ι) (dev : G.BehaviorStrategy who)
    {t : ℕ} (h : G.Hist t) :
    G.stageActionDist
        (Function.update (G.stationaryBehaviorProfile x) who dev) h =
      pmfPi (Function.update x who (dev t h)) := by
  unfold stageActionDist
  congr 1
  funext j
  by_cases hj : j = who
  · subst hj
    simp
  · simp [Function.update_of_ne hj, stationaryBehaviorProfile]

/-- The distribution over histories after `t` completed stages, starting at
state `s₀`, when play follows the behavior profile `σ`. -/
def histDist (G : StochasticGame ι) [Fintype ι] (σ : G.BehaviorProfile)
    (s₀ : G.State) : (t : ℕ) → PMF (G.Hist t)
  | 0 => PMF.pure (G.emptyHist s₀)
  | t + 1 =>
      (histDist G σ s₀ t).bind fun h =>
        (G.stageActionDist σ h).bind fun a =>
          (G.transition h.2 a).bind fun s' =>
            PMF.pure (Fin.snoc h.1 (h.2, a), s')

@[simp] theorem histDist_zero (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) :
    G.histDist σ s₀ 0 = PMF.pure (G.emptyHist s₀) :=
  rfl

theorem histDist_succ (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) :
    G.histDist σ s₀ (t + 1) =
      (G.histDist σ s₀ t).bind fun h =>
        (G.stageActionDist σ h).bind fun a =>
          (G.transition h.2 a).bind fun s' =>
            PMF.pure (Fin.snoc h.1 (h.2, a), s') :=
  rfl

/-- Membership in the support of `histDist` at a successor time unfolds to a
one-step extension of a supported history. -/
theorem mem_support_histDist_succ (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) (h' : G.Hist (t + 1)) :
    h' ∈ (G.histDist σ s₀ (t + 1)).support ↔
      ∃ h ∈ (G.histDist σ s₀ t).support,
        ∃ a ∈ (G.stageActionDist σ h).support,
          ∃ s' ∈ (G.transition h.2 a).support,
            h' = (Fin.snoc h.1 (h.2, a), s') := by
  simp [histDist_succ]

/-- Total stage payoff accumulated along a history. -/
def totalPayoff (G : StochasticGame ι) (who : ι) {t : ℕ} (h : G.Hist t) : ℝ :=
  ∑ k, G.stagePayoff (h.1 k).1 (h.1 k).2 who

@[simp] theorem totalPayoff_zero (G : StochasticGame ι) (who : ι)
    (h : G.Hist 0) :
    G.totalPayoff who h = 0 := by
  simp [totalPayoff]

/-- Extending a history by one stage adds that stage's payoff. -/
theorem totalPayoff_snoc (G : StochasticGame ι) (who : ι) {t : ℕ}
    (h : G.Hist t) (a : G.JointAct) (s' : G.State) :
    G.totalPayoff who ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1)) =
      G.totalPayoff who h + G.stagePayoff h.2 a who := by
  simp [totalPayoff, Fin.sum_univ_castSucc]

/-- Expected payoff of the next stage after history `h`, when the joint
action is drawn from `σ`'s independent randomization at `h`. -/
def stageEUAt (G : StochasticGame ι) [Fintype ι] (σ : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (who : ι) : ℝ :=
  expect (G.stageActionDist σ h) fun a => G.stagePayoff h.2 a who

/-- Expected average payoff of player `who` over the first `T` stages of
play from initial state `s₀` under the behavior profile `σ`. -/
def finiteAveragePayoff (G : StochasticGame ι) [Fintype ι] (s₀ : G.State)
    (T : ℕ) (σ : G.BehaviorProfile) (who : ι) : ℝ :=
  (T : ℝ)⁻¹ * expect (G.histDist σ s₀ T) (fun h => G.totalPayoff who h)

@[simp] theorem finiteAveragePayoff_zero (G : StochasticGame ι) [Fintype ι]
    (s₀ : G.State) (σ : G.BehaviorProfile) (who : ι) :
    G.finiteAveragePayoff s₀ 0 σ who = 0 := by
  simp [finiteAveragePayoff]

/-- One-step recursion for expected total payoff: the expected total payoff
over `T + 1` stages is the expected total payoff over `T` stages plus the
expected payoff of stage `T`. -/
theorem expect_totalPayoff_succ (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) (who : ι) :
    expect (G.histDist σ s₀ (T + 1)) (fun h => G.totalPayoff who h) =
      expect (G.histDist σ s₀ T) (fun h => G.totalPayoff who h) +
        expect (G.histDist σ s₀ T) (fun h => G.stageEUAt σ h who) := by
  have hstep : ∀ h : G.Hist T,
      expect ((G.stageActionDist σ h).bind fun a =>
          (G.transition h.2 a).bind fun s' =>
            PMF.pure ((Fin.snoc h.1 (h.2, a), s') : G.Hist (T + 1)))
        (fun h' => G.totalPayoff who h') =
      G.totalPayoff who h + G.stageEUAt σ h who := by
    intro h
    rw [expect_bind]
    have hinner : ∀ a : G.JointAct,
        expect ((G.transition h.2 a).bind fun s' =>
            PMF.pure ((Fin.snoc h.1 (h.2, a), s') : G.Hist (T + 1)))
          (fun h' => G.totalPayoff who h') =
        G.totalPayoff who h + G.stagePayoff h.2 a who := by
      intro a
      rw [expect_bind]
      simp only [expect_pure, totalPayoff_snoc]
      exact expect_const _ _
    simp only [hinner]
    rw [expect_add (G.stageActionDist σ h) (fun _ => G.totalPayoff who h)
      (fun a => G.stagePayoff h.2 a who), expect_const]
    rfl
  rw [histDist_succ, expect_bind]
  simp only [hstep]
  exact expect_add _ _ _

/-- A uniform stage payoff bound bounds the total payoff along any history of
length `t` by `t` times the bound. -/
theorem abs_totalPayoff_le (G : StochasticGame ι) {who : ι} {C : ℝ}
    (hC : ∀ s a, |G.stagePayoff s a who| ≤ C) {t : ℕ} (h : G.Hist t) :
    |G.totalPayoff who h| ≤ t * C := by
  calc |G.totalPayoff who h|
      ≤ ∑ k : Fin t, |G.stagePayoff (h.1 k).1 (h.1 k).2 who| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin t, C := Finset.sum_le_sum fun k _ => hC _ _
    _ = t * C := by simp [Finset.sum_const, nsmul_eq_mul]

/-- A uniform stage payoff bound bounds every finite-horizon average payoff. -/
theorem abs_finiteAveragePayoff_le (G : StochasticGame ι) [Fintype ι]
    {who : ι} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (s₀ : G.State) (T : ℕ) (σ : G.BehaviorProfile) :
    |G.finiteAveragePayoff s₀ T σ who| ≤ C := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    simpa using hC0
  · have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    have hbd : |expect (G.histDist σ s₀ T) (fun h => G.totalPayoff who h)| ≤
        T * C :=
      abs_expect_le_of_abs_le _ _ fun h => G.abs_totalPayoff_le hC h
    calc |G.finiteAveragePayoff s₀ T σ who|
        = (T : ℝ)⁻¹ *
            |expect (G.histDist σ s₀ T) (fun h => G.totalPayoff who h)| := by
          rw [finiteAveragePayoff, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (T : ℝ)⁻¹ * (T * C) := by
          exact mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = C := by
          field_simp

-- ============================================================================
-- The horizon game: each finite truncation as a KernelGame
-- ============================================================================

/-- The `T`-stage game from `s₀` as a one-shot `KernelGame`: strategies are
whole behavior strategies, outcomes are `T`-stage histories, and utility is
the average payoff along the history.  A stochastic game is not a single
`KernelGame` — uniform solution concepts quantify over every horizon with
one profile — but each finite truncation is one, and this bridge lets
per-horizon `KernelGame` notions apply verbatim (see
`isεHorizonNash_iff_horizonGame` in
`GameTheory.Concepts.Stochastic.Uniform`). -/
def horizonGame (G : StochasticGame ι) [Fintype ι] (s₀ : G.State) (T : ℕ) :
    KernelGame ι where
  Strategy := G.BehaviorStrategy
  Outcome := G.Hist T
  utility := fun h who => (T : ℝ)⁻¹ * G.totalPayoff who h
  outcomeKernel := fun σ => G.histDist σ s₀ T

@[simp] theorem horizonGame_Strategy (G : StochasticGame ι) [Fintype ι]
    (s₀ : G.State) (T : ℕ) :
    (G.horizonGame s₀ T).Strategy = G.BehaviorStrategy :=
  rfl

/-- Expected utility in the horizon game is the finite-horizon average
payoff. -/
@[simp] theorem eu_horizonGame (G : StochasticGame ι) [Fintype ι]
    (s₀ : G.State) (T : ℕ) (σ : G.BehaviorProfile) (who : ι) :
    (G.horizonGame s₀ T).eu σ who = G.finiteAveragePayoff s₀ T σ who := by
  change expect (G.histDist σ s₀ T)
      (fun h => (T : ℝ)⁻¹ * G.totalPayoff who h) =
    (T : ℝ)⁻¹ * expect (G.histDist σ s₀ T) (fun h => G.totalPayoff who h)
  exact expect_const_mul _ _ _

end StochasticGame

end GameTheory
