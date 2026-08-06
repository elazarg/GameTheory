/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Uniform

/-!
# Target-free closure of uniform-equilibrium payoff existence

For a finite stochastic-game skeleton, this module turns reward-table
approximation into existential uniform-equilibrium-payoff closure.  The only
compactness step is on the finite-dimensional payoff vector: behavior profiles
are reused from nearby games and are never passed to a limit.

The transition kernel, state space, action spaces, and discount field stay
fixed throughout; only the stage-payoff table varies.
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type}

/-- Every finite stochastic-game payoff table has one common nonnegative
absolute bound over states, joint actions, and players. -/
theorem exists_stagePayoff_nonneg_abs_bound
    (G : StochasticGame ι) [Finite ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s a who, |G.stagePayoff s a who| ≤ C := by
  classical
  obtain ⟨B, hB⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun x : G.State × G.JointAct × ι =>
      G.stagePayoff x.1 x.2.1 x.2.2)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro s a who
  exact (hB (s, a, who)).trans (le_max_left _ _)

/-- A uniform-equilibrium target for a game with stage payoffs bounded by `C`
lies in the coordinate cube `[-(C + 1), C + 1]`.  The one-unit slack is the
on-path approximation obtained by applying the definition at `ε = 1`. -/
theorem IsUniformEquilibriumPayoff.mem_payoffCube_of_abs_stagePayoff_le
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s a who, |G.stagePayoff s a who| ≤ C)
    {s₀ : G.State} {w : Payoff ι}
    (hUE : G.IsUniformEquilibriumPayoff s₀ w) :
    w ∈ Set.univ.pi (fun _ : ι => Set.Icc (-(C + 1)) (C + 1)) := by
  obtain ⟨σ, T₀, hσ⟩ := hUE 1 (by norm_num)
  obtain ⟨_, hon⟩ := hσ T₀ le_rfl
  rw [Set.mem_univ_pi]
  intro who
  rw [Set.mem_Icc]
  have havg : |G.finiteAveragePayoff s₀ T₀ σ who| ≤ C :=
    G.abs_finiteAveragePayoff_le hC0 (fun s a => hC s a who) s₀ T₀ σ
  have htarget : |w who| ≤ C + 1 := by
    calc
      |w who| = |(w who - G.finiteAveragePayoff s₀ T₀ σ who) +
          G.finiteAveragePayoff s₀ T₀ σ who| := by
        rw [sub_add_cancel]
      _ ≤ |w who - G.finiteAveragePayoff s₀ T₀ σ who| +
          |G.finiteAveragePayoff s₀ T₀ σ who| := abs_add_le _ _
      _ = |G.finiteAveragePayoff s₀ T₀ σ who - w who| +
          |G.finiteAveragePayoff s₀ T₀ σ who| := by
        rw [abs_sub_comm]
      _ ≤ 1 + C := add_le_add (hon who) havg
      _ = C + 1 := by ring
  exact abs_le.mp htarget

/-- Uniform-equilibrium payoff existence passes to a uniform reward-table
limit on a fixed finite skeleton, without a preselected convergent target
sequence. -/
theorem exists_uniformEquilibriumPayoff_of_uniform_stagePayoff_limit
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State)
    (reward : ℕ → G.State → G.JointAct → ι → ℝ)
    (hreward : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ s a who, |reward n s a who - G.stagePayoff s a who| ≤ η)
    (hUE : ∀ n, ∃ w : Payoff ι,
      (G.withStagePayoff (reward n)).IsUniformEquilibriumPayoff s₀ w) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  classical
  obtain ⟨C, hC0, hC⟩ := G.exists_stagePayoff_nonneg_abs_bound
  obtain ⟨N, hN⟩ := hreward 1 (by norm_num)
  choose w hw using fun n => hUE (N + n)
  have hRewardBound : ∀ n s a who, |reward (N + n) s a who| ≤ C + 1 := by
    intro n s a who
    calc
      |reward (N + n) s a who|
          = |(reward (N + n) s a who - G.stagePayoff s a who) +
              G.stagePayoff s a who| := by
        rw [sub_add_cancel]
      _ ≤ |reward (N + n) s a who - G.stagePayoff s a who| +
            |G.stagePayoff s a who| := abs_add_le _ _
      _ ≤ 1 + C := add_le_add (hN (N + n) (Nat.le_add_right N n) s a who)
          (hC s a who)
      _ = C + 1 := by ring
  let K : Set (Payoff ι) :=
    Set.univ.pi (fun _ : ι => Set.Icc (-(C + 2)) (C + 2))
  have hKcompact : IsCompact K :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hwK : ∀ n, w n ∈ K := by
    intro n
    have hbound :=
      IsUniformEquilibriumPayoff.mem_payoffCube_of_abs_stagePayoff_le
        (G := G.withStagePayoff (reward (N + n))) (C := C + 1)
        (by linarith [hC0])
        (by
          intro s a who
          simpa [withStagePayoff] using hRewardBound n s a who)
        (hw n)
    rw [Set.mem_univ_pi] at hbound ⊢
    intro who
    have hwho := hbound who
    rw [Set.mem_Icc] at hwho ⊢
    constructor <;> linarith
  obtain ⟨v, _, φ, hφ, hlim⟩ := hKcompact.tendsto_subseq hwK
  refine ⟨v, ?_⟩
  apply isUniformEquilibriumPayoff_of_uniform_stagePayoff_limit G s₀
    (fun n => reward (N + φ n)) (w ∘ φ) v
  · intro η hη
    obtain ⟨M, hM⟩ := hreward η hη
    refine ⟨M, fun n hn => ?_⟩
    exact hM (N + φ n)
      ((hn.trans (hφ.id_le n)).trans (Nat.le_add_left _ _))
  · intro η hη
    have hEventually : ∀ᶠ n in Filter.atTop,
        ∀ who, |(w ∘ φ) n who - v who| ≤ η := by
      rw [Filter.eventually_all]
      intro who
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp
        ((tendsto_pi_nhds.mp hlim) who) η hη
      exact Filter.eventually_atTop.mpr ⟨M, fun n hn => by
        simpa [Real.dist_eq] using (hM n hn).le⟩
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hEventually
    exact ⟨M, fun n hn who => hM n hn who⟩
  · intro n
    exact hw (φ n)

/-- If uniformly close reward tables on a fixed finite skeleton each admit
some uniform-equilibrium payoff, then the original game admits some
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_arbitrarily_close_stagePayoffs
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State)
    (happrox : ∀ η : ℝ, 0 < η →
      ∃ reward : G.State → G.JointAct → ι → ℝ,
        (∀ s a who, |reward s a who - G.stagePayoff s a who| ≤ η) ∧
        ∃ w : Payoff ι,
          (G.withStagePayoff reward).IsUniformEquilibriumPayoff s₀ w) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  classical
  choose reward hreward hUE using fun n : ℕ =>
    happrox ((1 : ℝ) / (n + 1)) (by positivity)
  apply exists_uniformEquilibriumPayoff_of_uniform_stagePayoff_limit G s₀ reward
  · intro η hη
    have hlim : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
          Filter.atTop (nhds 0))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      ((tendsto_order.mp hlim).2 η hη)
    refine ⟨N, fun n hn s a who => (hreward n s a who).trans (hN n hn).le⟩
  · exact hUE

end StochasticGame

end GameTheory
