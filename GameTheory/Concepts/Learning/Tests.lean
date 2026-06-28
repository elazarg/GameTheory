/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.MultiplicativeWeights
import GameTheory.Concepts.Learning.SelfPlay
import GameTheory.Concepts.Learning.MWSelfPlay

/-!
# Tests for the learning-dynamics (Tier A) development

Compilation tests exercising the no-regret ⇒ coarse correlated equilibrium pipeline:
the ε-correlated notions, the time-average reduction, multiplicative weights, and the
self-play assembly. Lives in the `GameTheoryTest` target, not the public surface.
-/

namespace GameTheory.Learning.Tests

open Math.OnlineLearning

/-- The multiplicative-weights regret bound instantiates concretely on a two-action set:
    the hypotheses are non-vacuous (here the all-zero gain sequence with learning rate `1`). -/
example (T : ℕ) :
    onlineExternalRegret (A := Bool) 1 (fun _ _ => 0) T
      ≤ Real.log (Fintype.card Bool) / 1 + (Real.exp 1 - 1 - 1) / 1 * T :=
  mw_externalRegret_le (by norm_num) (fun _ _ => Set.mem_Icc.mpr ⟨le_refl _, zero_le_one⟩) T

/-- Multiplicative weights is a genuine no-regret rule: at the optimal tuning the bound is
    finite for every horizon (sanity check that the bound is a real number, not `⊤`). -/
example (T : ℕ) (η : ℝ) (hη : 0 < η) :
    onlineExternalRegret (A := Bool) η (fun _ _ => 0) T
      ≤ Real.log (Fintype.card Bool) / η + (Real.exp η - 1 - η) / η * T :=
  mw_externalRegret_le hη (fun _ _ => Set.mem_Icc.mpr ⟨le_refl _, zero_le_one⟩) T

-- The reduction, the algorithm, the assembly, and the PoA-of-learning bound all type-check
-- with the intended signatures.
section API
open GameTheory.KernelGame

example : True := by
  have _ := @timeAverage_isεCCE_of_regret_le
  have _ := @selfPlay_timeAverage_isεCCE
  have _ := @externalRegret_pmfPi
  have _ := @IsSmooth.epsilonCoarseCorrelated_bound
  have _ := @isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero
  trivial

end API

/-! ### A concrete 2×2 game exercising the full MW-self-play → ε-CCE path -/

open KernelGame

/-- A 2×2 coordination game with payoffs in `[0,1]`: both players score `1` iff they match. -/
noncomputable def coordinationGame : KernelGame (Fin 2) :=
  KernelGame.ofPureEU (fun _ => Bool) (fun σ _ => if σ 0 = σ 1 then 1 else 0)

/-- The full Tier-A pipeline instantiates on a concrete game: multiplicative-weights self-play
    over the coordination game yields an explicit ε-coarse correlated equilibrium for every
    horizon (here learning rate `η = 1`, band `[0,1]`). -/
example {T : ℕ} [NeZero T] :
    ∃ μ, coordinationGame.IsεCoarseCorrelatedEq
      (1 * (Real.log 2 / 1 + (Real.exp 1 - 1 - 1) / 1 * (T : ℝ)) / (T : ℝ)) μ := by
  haveI : ∀ i, Fintype (coordinationGame.Strategy i) := fun _ => inferInstanceAs (Fintype Bool)
  haveI : ∀ i, Nonempty (coordinationGame.Strategy i) := fun _ => inferInstanceAs (Nonempty Bool)
  haveI : Finite coordinationGame.Outcome := inferInstanceAs (Finite (∀ _ : Fin 2, Bool))
  refine coordinationGame.exists_mwSelfPlay_isεCCE 1 (fun _ => 0) 1 (by norm_num) (by norm_num)
    ?_ ?_ T
  · intro i ω
    change (if ω 0 = ω 1 then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) (0 + 1)
    by_cases h : ω 0 = ω 1 <;> simp [h]
  · intro i
    have hc : Fintype.card (coordinationGame.Strategy i) = 2 := by
      simp only [coordinationGame, KernelGame.ofPureEU_Strategy]
      convert Fintype.card_bool
    rw [hc]
    norm_num

end GameTheory.Learning.Tests
