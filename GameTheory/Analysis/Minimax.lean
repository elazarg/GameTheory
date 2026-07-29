/-
# The minimax theorem

A two-player zero-sum finite game has a value: a number the first player can
guarantee and the second can hold them to. This is von Neumann's theorem, and
here it is a corollary rather than a separate argument — equilibria exist, a
zero-sum equilibrium is a saddle point, and a saddle point *is* a pair of
guarantees meeting at one number.

Everything except existence lives below the analytic boundary, including the
fact that all saddle points are worth the same. Only the assertion that one
exists needs a fixed point, and that is the single line this module contributes.
-/

import GameTheory.Analysis.Nash
import GameTheory.Core.ZeroSum

noncomputable section

namespace GameTheory

open Probability

universe us uo

variable {F : GameForm (Fin 2)} [∀ i, Fintype (F.sig.Strategy i)]
variable [∀ i, Nonempty (F.sig.Strategy i)] (utility : F.sig.Outcome → Fin 2 → ℝ)

/-- **A zero-sum finite game has a saddle point.** -/
theorem exists_isSaddlePoint (hzero : IsZeroSum utility) :
    ∃ σ : Profile F.sig.mixed, IsSaddlePoint utility σ :=
  let ⟨σ, hnash⟩ := exists_isNash_mixed utility
  ⟨σ, hnash.isSaddlePoint hzero⟩

/-- **The minimax theorem.** There is a number and a profile realizing it from
both sides: the first player cannot do better than the number against the second
player's half, and the second cannot hold the first below it. Any other saddle
point gives the same number, which is why it deserves the name *value*. -/
theorem exists_value (hzero : IsZeroSum utility) :
    ∃ (value : ℝ) (σ : Profile F.sig.mixed),
      (∀ μ : FinDist (F.sig.Strategy 0),
          expectedUtility utility 0 (F.mixed.play (Profile.update σ 0 μ)) ≤ value) ∧
        (∀ ν : FinDist (F.sig.Strategy 1),
            value ≤ expectedUtility utility 0 (F.mixed.play (Profile.update σ 1 ν))) ∧
          ∀ other : Profile F.sig.mixed, IsSaddlePoint utility other →
            expectedUtility utility 0 (F.mixed.play other) = value := by
  obtain ⟨σ, hsaddle⟩ := exists_isSaddlePoint utility hzero
  exact ⟨_, σ, hsaddle.1, hsaddle.2, fun other hother => hother.value_eq hsaddle⟩

end GameTheory
