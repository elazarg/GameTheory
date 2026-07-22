/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.StageGame
import GameTheory.Concepts.Stochastic.Discounted

/-!
# Uniform and Discounted Equilibria at Absorbing States

Proved special case of the uniform equilibrium existence problem
(`StochasticGame.exists_uniformEquilibriumPayoff`): if the initial state is
absorbing — every joint action surely stays — then play from it is a
repeated game, and stationary repetition of a mixed Nash equilibrium of the
stage game has the stage-Nash payoff as its per-stage expected payoff at
every stage, against every unilateral deviation earning at most that.
Consequently the stationary profile is an exact Nash equilibrium of every
finite-horizon game *and* of every `β`-discounted game, `β ∈ [0, 1)`, with
the stage-Nash payoff as its value under both aggregations.  In particular
every stochastic game with a single state (equivalently, every repeated
finite normal-form game presented as a stochastic game) has a uniform
equilibrium payoff.

## Main results

* `StochasticGame.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState`
  / `StochasticGame.expectedStagePayoff_update_stationaryBehaviorProfile_le_of_isAbsorbingState`
  — the per-stage payoff facts
* `StochasticGame.exists_uniformEquilibriumPayoff_of_isAbsorbingState` —
  uniform equilibrium payoffs exist from absorbing states
* `StochasticGame.exists_discountedNash_of_isAbsorbingState` — one
  stationary profile is an exact equilibrium of every discounted game
* `StochasticGame.exists_uniformEquilibriumPayoff_of_subsingleton_state` —
  the single-state (repeated game) case
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace StochasticGame

open Math.Probability Math.PMFProduct

variable {ι : Type}

/-- A state is absorbing if every joint action surely returns to it. -/
def IsAbsorbingState (G : StochasticGame ι) (s : G.State) : Prop :=
  ∀ a : G.JointAct, G.transition s a = PMF.pure s

/-- Every state of a stochastic game with a subsingleton state space is
absorbing. -/
theorem isAbsorbingState_of_subsingleton (G : StochasticGame ι)
    [Subsingleton G.State] (s : G.State) : G.IsAbsorbingState s :=
  fun a =>
    Math.ProbabilityMassFunction.eq_pure_of_subsingleton (G.transition s a) s

/-- Play from an absorbing state never leaves it: every supported history
ends at the initial state. -/
theorem snd_eq_of_mem_support_histDist_of_isAbsorbingState
    (G : StochasticGame ι) [Fintype ι] {s₀ : G.State}
    (hAbs : G.IsAbsorbingState s₀) (σ : G.BehaviorProfile) :
    ∀ (t : ℕ) (h : G.Hist t),
      h ∈ (G.histDist σ s₀ t).support → h.2 = s₀ := by
  intro t
  induction t with
  | zero =>
    intro h hh
    have hh' : h = G.emptyHist s₀ := by simpa using hh
    rw [hh']
    rfl
  | succ t ih =>
    intro h' hh'
    rw [G.mem_support_histDist_succ σ s₀ t h'] at hh'
    obtain ⟨h, hh, a, -, s', hs', rfl⟩ := hh'
    have h2 : h.2 = s₀ := ih h hh
    rw [h2, hAbs a] at hs'
    simpa using hs'

/-- At an absorbing initial state, stationary play of the mixed action `m`
has constant per-stage expected payoff: the mixed stage payoff of `m` at
the absorbing state. -/
theorem expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
    (G : StochasticGame ι) [Fintype ι] {s₀ : G.State}
    (hAbs : G.IsAbsorbingState s₀) (m : ∀ i, PMF (G.Act i)) (t : ℕ)
    (who : ι) :
    G.expectedStagePayoff (G.stationaryBehaviorProfile m) s₀ t who =
      G.mixedStageEU s₀ m who := by
  unfold expectedStagePayoff
  have heq : ∀ h ∈ (G.histDist (G.stationaryBehaviorProfile m) s₀ t).support,
      G.stageEUAt (G.stationaryBehaviorProfile m) h who =
        G.mixedStageEU s₀ m who := by
    intro h hh
    have h2 := G.snd_eq_of_mem_support_histDist_of_isAbsorbingState hAbs
      (G.stationaryBehaviorProfile m) t h hh
    unfold stageEUAt mixedStageEU
    rw [stageActionDist_stationaryBehaviorProfile, h2]
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _ heq,
    expect_const]

/-- At an absorbing initial state, a unilateral deviation from stationary
play of a stage-Nash mixed action earns at most the stage-Nash payoff at
every stage. -/
theorem expectedStagePayoff_update_stationaryBehaviorProfile_le_of_isAbsorbingState
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] {s₀ : G.State}
    (hAbs : G.IsAbsorbingState s₀) {m : ∀ i, PMF (G.Act i)} {who : ι}
    (hm : ∀ d : PMF (G.Act who),
      G.mixedStageEU s₀ (Function.update m who d) who ≤
        G.mixedStageEU s₀ m who)
    (dev : G.BehaviorStrategy who) (t : ℕ) :
    G.expectedStagePayoff
        (Function.update (G.stationaryBehaviorProfile m) who dev) s₀ t
        who ≤
      G.mixedStageEU s₀ m who := by
  unfold expectedStagePayoff
  apply Math.ProbabilityMassFunction.expect_le_of_le_on_support
  intro h hh
  have h2 := G.snd_eq_of_mem_support_histDist_of_isAbsorbingState hAbs
    (Function.update (G.stationaryBehaviorProfile m) who dev) t h hh
  unfold stageEUAt
  rw [G.stageActionDist_update_stationaryBehaviorProfile, h2]
  exact hm (dev t h)

/-- **Uniform equilibrium payoffs exist from absorbing states.**

If the initial state is absorbing, the stationary behavior profile that
repeats a mixed Nash equilibrium of the stage game is an exact Nash
equilibrium of every finite-horizon game, and its average payoff at every
positive horizon is the stage-Nash payoff.  This settles the absorbing-state
special case of `exists_uniformEquilibriumPayoff`. -/
theorem exists_uniformEquilibriumPayoff_of_isAbsorbingState
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    {s₀ : G.State} (hAbs : G.IsAbsorbingState s₀) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  obtain ⟨x, hx⟩ := G.exists_isMixedStageNash
  have havg_on : ∀ (who : ι) (T : ℕ), 1 ≤ T →
      G.finiteAveragePayoff s₀ T (G.stationaryBehaviorProfile (x s₀)) who =
        G.mixedStageEU s₀ (x s₀) who := by
    intro who T hT
    have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff,
      Finset.sum_congr rfl fun t _ =>
        G.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
          hAbs (x s₀) t who,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hT', one_mul]
  have havg_off : ∀ (who : ι) (dev : G.BehaviorStrategy who) (T : ℕ),
      1 ≤ T →
      G.finiteAveragePayoff s₀ T
          (Function.update (G.stationaryBehaviorProfile (x s₀)) who dev)
          who ≤
        G.mixedStageEU s₀ (x s₀) who := by
    intro who dev T hT
    have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    calc (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.expectedStagePayoff
            (Function.update (G.stationaryBehaviorProfile (x s₀)) who dev)
            s₀ t who
        ≤ (T : ℝ)⁻¹ * ∑ _t ∈ Finset.range T,
            G.mixedStageEU s₀ (x s₀) who := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun t _ => ?_) (by positivity)
          exact
            G.expectedStagePayoff_update_stationaryBehaviorProfile_le_of_isAbsorbingState
              hAbs (fun d => hx s₀ who d) dev t
      _ = G.mixedStageEU s₀ (x s₀) who := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← mul_assoc, inv_mul_cancel₀ hT', one_mul]
  refine ⟨fun who => G.mixedStageEU s₀ (x s₀) who, fun ε hε =>
    ⟨G.stationaryBehaviorProfile (x s₀), 1, fun T hT => ⟨?_, ?_⟩⟩⟩
  · intro who dev
    have h1 := havg_off who dev T hT
    have h2 := havg_on who T hT
    linarith
  · intro who
    rw [havg_on who T hT]
    simpa using hε.le

/-- **Absorbing states: one stationary profile is an exact equilibrium of
every discounted game**, with the stage-Nash payoff as its discounted
payoff, for every discount factor `β ∈ [0, 1)`. -/
theorem exists_discountedNash_of_isAbsorbingState
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    {s₀ : G.State} (hAbs : G.IsAbsorbingState s₀) :
    ∃ (σ : G.BehaviorProfile) (v : Payoff ι),
      ∀ {β : ℝ}, 0 ≤ β → β < 1 →
        (∀ who, G.discountedPayoff β σ s₀ who = v who) ∧
        ∀ {ε : ℝ}, 0 ≤ ε → G.IsDiscountedεNash β s₀ ε σ := by
  obtain ⟨x, hx⟩ := G.exists_isMixedStageNash
  refine ⟨G.stationaryBehaviorProfile (x s₀),
    fun who => G.mixedStageEU s₀ (x s₀) who, fun {β} hβ0 hβ1 => ⟨?_, ?_⟩⟩
  · intro who
    exact G.discountedPayoff_of_forall_expectedStagePayoff_eq
      (fun t =>
        G.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
          hAbs (x s₀) t who)
      hβ0 hβ1
  · intro ε hε who dev
    obtain ⟨C, hC⟩ := Math.Probability.exists_abs_bound_of_finite
      (fun p : G.State × G.JointAct => G.stagePayoff p.1 p.2 who)
    have hle := G.discountedPayoff_le_of_forall_expectedStagePayoff_le
      (fun s a => hC (s, a))
      (fun t =>
        G.expectedStagePayoff_update_stationaryBehaviorProfile_le_of_isAbsorbingState
          hAbs (fun d => hx s₀ who d) dev t)
      hβ0 hβ1
    have heq := G.discountedPayoff_of_forall_expectedStagePayoff_eq
      (fun t =>
        G.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
          hAbs (x s₀) t who)
      hβ0 hβ1
    rw [heq]
    linarith

/-- **The single-state case of the uniform equilibrium existence problem**:
a stochastic game with a subsingleton state space is a repeated normal-form
game, and it has a uniform equilibrium payoff from every initial state. -/
theorem exists_uniformEquilibriumPayoff_of_subsingleton_state
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Subsingleton G.State] [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (s₀ : G.State) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  haveI : Finite G.State := Finite.of_subsingleton
  exact G.exists_uniformEquilibriumPayoff_of_isAbsorbingState
    (G.isAbsorbingState_of_subsingleton s₀)

end StochasticGame

end GameTheory
