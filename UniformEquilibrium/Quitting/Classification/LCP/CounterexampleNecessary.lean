/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.Gate
import UniformEquilibrium.Quitting.Classification.LCP.LaterLayerAbnormal
import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProducer
import UniformEquilibrium.Quitting.Classification.LCP.OrdinaryNonQClosure

/-!
# Exact LCP restrictions currently proved for a quitting counterexample

This file records the precise strategic boundary of the algebraic LCP gate.
It deliberately does not import the general quitting-game conjecture and does
not assume any unformalized theorem from the literature.

The corrected all-abnormal construction is now complete: the first-layer
branch is exact, while the later-layer branch uses a last surviving layer and
a two-scale owner/blocker stationary row.  Consequently nonexistence reduces
the faithful five-way matrix gate to three live alternatives:

1. the corrected normal core has a homogeneous simplex solution;
2. the nonhomogeneous corrected normal matrix is not standard Q; or
3. the corrected normal matrix is on the nonhomogeneous standard-Q side.

The corrected homogeneous and ordinary non-Q producers are also complete.
Consequently nonexistence of an ordinary uniform-equilibrium payoff forces the
corrected normal matrix onto the nonhomogeneous textbook standard-Q side.
Projective Q is the simplex convention used by the quitting-game LCP
classification; the completed theorem proves both conventions, with standard
Q as the sharper conclusion.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Unconditional counterexample-facing LCP gate.**  The complete corrected
all-abnormal producer removes the empty-core branch.  No unformalized non-Q or
homogeneous strategic theorem is smuggled into the conclusion. -/
theorem lcp_necessary_alternative_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    HomogeneousMatrixBranch reward ∨
      OrdinaryNonQMatrixBranch reward ∨
      StandardQMatrixSide reward := by
  rcases faithful_q_nonQ_lcp_matrix_gate reward with
    habnormal | hhomogeneous | hnonQ | hqbar | hresidual
  · exact False.elim
      (hnot (exists_uniformEquilibriumPayoff_of_allPlayersAbnormal
        reward habnormal))
  · exact Or.inl hhomogeneous
  · exact Or.inr (Or.inl hnonQ)
  · exact Or.inr (Or.inr hqbar.toStandardQMatrixSide)
  · exact Or.inr (Or.inr hresidual.toStandardQMatrixSide)

/-- A counterexample has a nonempty corrected normal core and its corrected
normal matrix is projective Q.  The homogeneous branch is one of the two
algebraic ways to be projective Q; the ordinary non-Q branch is now excluded
strategically. -/
theorem projectiveQ_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    HasNormalPlayers (normalizedSoloMatrix reward) ∧
      IsProjectiveQMatrix (normalizedNormalPlayerMatrix reward) := by
  rcases lcp_necessary_alternative_of_not_exists_uniformEquilibriumPayoff
      reward hnot with hhomogeneous | hnonQBranch | hstandard
  · exact ⟨hhomogeneous.normal_nonempty,
      (isProjectiveQMatrix_iff_standard_or_homogeneous
        (normalizedNormalPlayerMatrix reward)).2
        (Or.inr hhomogeneous.homogeneous)⟩
  · exact False.elim (hnot
      (exists_uniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch
        reward hnonQBranch))
  · exact ⟨hstandard.normal_nonempty,
      (isProjectiveQMatrix_iff_standard_or_homogeneous
        (normalizedNormalPlayerMatrix reward)).2
        (Or.inl hstandard.normal_standardQ)⟩

/-- **Sharp Q-matrix restriction for ordinary quitting counterexamples.**
Nonexistence of an ordinary uniform-equilibrium payoff forces a nonempty
corrected normal core, excludes the homogeneous simplex branch, and makes its
principal matrix a textbook standard-Q matrix. -/
theorem standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    StandardQMatrixSide reward := by
  rcases lcp_necessary_alternative_of_not_exists_uniformEquilibriumPayoff
      reward hnot with hhomogeneousBranch | hnonQBranch | hstandard
  · exact False.elim (hnot
      (exists_uniformEquilibriumPayoff_of_homogeneousMatrixBranch
        reward hhomogeneousBranch))
  · exact False.elim (hnot
      (exists_uniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch
        reward hnonQBranch))
  · exact hstandard

end QuittingLCPClassification
end GameTheory
