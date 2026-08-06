/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformPayoffExistenceClosure

/-!
# Uniform equilibrium as bounded excess work

Uniform equilibrium can be expressed as a bounded-work condition.  Fix a
candidate target `v` and a positive linear penalty `η`.  A profile has bounded
work when one common constant `B` bounds, at every horizon,

* every deviator's cumulative payoff above `v + η`; and
* prescribed play's cumulative deficit below `v - η`.

The work is written as `T` times a finite-average excess.  This avoids adding a
second total-payoff API while keeping the intended interpretation exact.

The main theorem proves that a payoff vector is a uniform-equilibrium payoff if
and only if it has bounded-work certificates at every positive penalty.  The
forward direction uses uniformity for late horizons and the finite stage-payoff
bound for the finitely many early horizons.  The reverse direction divides the
fixed work budget by a sufficiently long horizon.

This is the semantic available-storage theorem.  It guarantees a root-level
bounded account but does not assert that the account has finite memory,
continuity, semialgebraicity, or a public implementation.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- A bounded-work certificate for target `v`.

For every positive penalty `η`, one profile and one nonnegative work budget
control all players, all horizons, and all unilateral behavioral deviations. -/
def HasBoundedWorkCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ (σ : G.BehaviorProfile) (B : ℝ), 0 ≤ B ∧
      ∀ (T : ℕ) (who : ι),
        (∀ dev : G.BehaviorStrategy who,
          (T : ℝ) *
              (G.finiteAveragePayoff s₀ T (Function.update σ who dev) who -
                v who - η) ≤ B) ∧
        (T : ℝ) *
            (v who - G.finiteAveragePayoff s₀ T σ who - η) ≤ B

/-- A positive work obstruction for target `v`.

One linear penalty defeats every profile and every proposed finite budget:
at some horizon either a unilateral behavior deviation exceeds the budget or
prescribed play accumulates more than that budget of target deficit. -/
def HasUnboundedWorkObstruction
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∃ η : ℝ, 0 < η ∧
    ∀ (σ : G.BehaviorProfile) (B : ℝ), 0 ≤ B →
      ∃ (T : ℕ) (who : ι),
        (∃ dev : G.BehaviorStrategy who,
          B < (T : ℝ) *
              (G.finiteAveragePayoff s₀ T (Function.update σ who dev) who -
                v who - η)) ∨
        B < (T : ℝ) *
            (v who - G.finiteAveragePayoff s₀ T σ who - η)

/-- A uniform-equilibrium payoff has bounded-work certificates at every
positive linear penalty. -/
theorem IsUniformEquilibriumPayoff.hasBoundedWorkCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {s₀ : G.State} {v : Payoff ι}
    (hUE : G.IsUniformEquilibriumPayoff s₀ v) :
    G.HasBoundedWorkCertificate s₀ v := by
  obtain ⟨C, hC0, hC⟩ := G.exists_stagePayoff_nonneg_abs_bound
  have hvCube :=
    IsUniformEquilibriumPayoff.mem_payoffCube_of_abs_stagePayoff_le
      G hC0 hC hUE
  rw [Set.mem_univ_pi] at hvCube
  intro η hη
  have hhalf : 0 < η / 2 := by linarith
  obtain ⟨σ, T₀, hσ⟩ := hUE (η / 2) hhalf
  let B : ℝ := (T₀ : ℝ) * (2 * C + 1)
  have hfactor0 : 0 ≤ 2 * C + 1 := by linarith
  have hB0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hfactor0
  refine ⟨σ, B, hB0, ?_⟩
  intro T who
  by_cases hlate : T₀ ≤ T
  · obtain ⟨hNash, hon⟩ := hσ T hlate
    constructor
    · intro dev
      have hdev := hNash who dev
      have honUpper := (abs_le.mp (hon who)).2
      have hdiff :
          G.finiteAveragePayoff s₀ T (Function.update σ who dev) who -
              v who - η ≤ 0 := by
        linarith
      exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hdiff).trans hB0
    · have honLower := (abs_le.mp (hon who)).1
      have hdiff : v who - G.finiteAveragePayoff s₀ T σ who - η ≤ 0 := by
        linarith
      exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hdiff).trans hB0
  · have hTlt : T < T₀ := Nat.lt_of_not_ge hlate
    have hTle : T ≤ T₀ := Nat.le_of_lt hTlt
    have hTleR : (T : ℝ) ≤ T₀ := by exact_mod_cast hTle
    have hv := hvCube who
    rw [Set.mem_Icc] at hv
    constructor
    · intro dev
      have havg := G.abs_finiteAveragePayoff_le hC0
        (fun s a => hC s a who) s₀ T (Function.update σ who dev)
      have havgUpper := (abs_le.mp havg).2
      have hdiff :
          G.finiteAveragePayoff s₀ T (Function.update σ who dev) who -
              v who - η ≤ 2 * C + 1 := by
        linarith
      calc
        (T : ℝ) *
              (G.finiteAveragePayoff s₀ T (Function.update σ who dev) who -
                v who - η)
            ≤ (T : ℝ) * (2 * C + 1) :=
          mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg _)
        _ ≤ (T₀ : ℝ) * (2 * C + 1) :=
          mul_le_mul_of_nonneg_right hTleR hfactor0
        _ = B := rfl
    · have havg := G.abs_finiteAveragePayoff_le hC0
        (fun s a => hC s a who) s₀ T σ
      have havgLower := (abs_le.mp havg).1
      have hdiff :
          v who - G.finiteAveragePayoff s₀ T σ who - η ≤
            2 * C + 1 := by
        linarith
      calc
        (T : ℝ) * (v who - G.finiteAveragePayoff s₀ T σ who - η)
            ≤ (T : ℝ) * (2 * C + 1) :=
          mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg _)
        _ ≤ (T₀ : ℝ) * (2 * C + 1) :=
          mul_le_mul_of_nonneg_right hTleR hfactor0
        _ = B := rfl

/-- Bounded-work certificates imply that `v` is a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_hasBoundedWorkCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι)
    (hwork : G.HasBoundedWorkCertificate s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  obtain ⟨σ, B, hB0, hcert⟩ := hwork (ε / 4) hquarter
  obtain ⟨T₀, hT₀gt⟩ := exists_nat_gt (4 * B / ε)
  have hratio0 : 0 ≤ 4 * B / ε := div_nonneg (by positivity) hε.le
  have hT₀pos : 0 < T₀ := by
    by_contra hnot
    have hzero : T₀ = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, Nat.cast_zero] at hT₀gt
    linarith
  have hfour : 4 * B < (T₀ : ℝ) * ε := by
    exact (div_lt_iff₀ hε).mp hT₀gt
  have hBsmall₀ : B < (T₀ : ℝ) * (ε / 4) := by
    nlinarith
  refine ⟨σ, T₀, fun T hT => ?_⟩
  have hTpos : 0 < T := lt_of_lt_of_le hT₀pos hT
  have hTRpos : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hTleR : (T₀ : ℝ) ≤ T := by exact_mod_cast hT
  have hBsmall : B < (T : ℝ) * (ε / 4) :=
    hBsmall₀.trans_le (mul_le_mul_of_nonneg_right hTleR hquarter.le)
  constructor
  · intro who dev
    obtain ⟨hdevWork, hbaseLowerWork⟩ := hcert T who
    have hdev := hdevWork dev
    have hbaseLower :
        v who - G.finiteAveragePayoff s₀ T σ who - ε / 4 < ε / 4 := by
      nlinarith
    have hdevUpper :
        G.finiteAveragePayoff s₀ T (Function.update σ who dev) who -
            v who - ε / 4 < ε / 4 := by
      nlinarith
    linarith
  · intro who
    obtain ⟨hdevWork, hbaseLowerWork⟩ := hcert T who
    have hbaseUpperWork := hdevWork (σ who)
    have hbaseUpperWork' :
        (T : ℝ) *
            (G.finiteAveragePayoff s₀ T σ who - v who - ε / 4) ≤ B := by
      simpa using hbaseUpperWork
    have hlower :
        v who - G.finiteAveragePayoff s₀ T σ who - ε / 4 < ε / 4 := by
      nlinarith
    have hupper :
        G.finiteAveragePayoff s₀ T σ who - v who - ε / 4 < ε / 4 := by
      nlinarith
    rw [abs_le]
    constructor <;> linarith

/-- Bounded-work characterization of a fixed uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_iff_hasBoundedWorkCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) :
    G.IsUniformEquilibriumPayoff s₀ v ↔
      G.HasBoundedWorkCertificate s₀ v := by
  constructor
  · exact IsUniformEquilibriumPayoff.hasBoundedWorkCertificate G
  · exact G.isUniformEquilibriumPayoff_of_hasBoundedWorkCertificate s₀ v

/-- A target fails to be a uniform-equilibrium payoff exactly when it has a
positive unbounded-work obstruction. -/
theorem not_isUniformEquilibriumPayoff_iff_hasUnboundedWorkObstruction
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) :
    (¬ G.IsUniformEquilibriumPayoff s₀ v) ↔
      G.HasUnboundedWorkObstruction s₀ v := by
  classical
  rw [G.isUniformEquilibriumPayoff_iff_hasBoundedWorkCertificate s₀ v]
  unfold HasBoundedWorkCertificate HasUnboundedWorkObstruction
  simp only [not_forall, not_exists, not_and_or, not_le]
  constructor
  · rintro ⟨η, hη, h⟩
    refine ⟨η, hη, ?_⟩
    intro σ B hB
    rcases h σ B with hneg | hcert
    · linarith
    · exact hcert
  · rintro ⟨η, hη, h⟩
    refine ⟨η, hη, ?_⟩
    intro σ B
    by_cases hB : 0 ≤ B
    · exact Or.inr (h σ B hB)
    · exact Or.inl (lt_of_not_ge hB)

end StochasticGame
end GameTheory

