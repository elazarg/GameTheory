/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCore

/-!
# Algebraic Q/non-Q LCP regime gate

This module contains the unconditional classification actually proved by the
LCP layer.  It is deliberately a **matrix-regime theorem**, not a strategic
existence theorem.

After playerwise solo normalization and passage to the corrected
recursive normal-player principal matrix, exactly one of the following
algebraic regimes is reached:

1. the corrected normal core is empty;
2. that core is nonempty and has a homogeneous simplex-LCP solution;
3. after removing the homogeneous branch, its matrix is not standard Q;
4. its matrix is standard Q and the full normalized matrix is projective
   Q-bar; or
5. its matrix is standard Q and the full normalized matrix is not projective
   Q-bar.

The fifth regime is the precise residual hard class supplied by this file.
The fourth regime records only the matrix hypothesis used by the continuous
absorption-path literature.  It does not assert that a continuous path has
been formalized or compiled to ordinary strategies.  Likewise, the first
three regimes are not assigned stationary equilibria here: those are source
producer theorems that still require concrete formalization over the corrected
normal recursion.

Never and first-stage absorption are intentionally absent from the exhaustive
theorem below.  Never already has a repository-native strategic theorem, while
"there exists a first-stage-absorbing approximate equilibrium" is itself a
semantic conclusion and would make a purported producer gate self-referential.
Those strategic cases can be ordered around this matrix partition only after
an explicit witness-producing criterion and the relevant source theorems are
available.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The corrected normal core is nonempty and admits the zero-cemetery,
homogeneous simplex-LCP branch.  No stationary strategy conclusion is bundled
into this algebraic predicate. -/
structure HomogeneousMatrixBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  homogeneous : HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)

/-- After excluding the homogeneous branch, the corrected normal-player
matrix is not a textbook standard-Q matrix. -/
structure OrdinaryNonQMatrixBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  no_homogeneous : ¬HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)
  normal_not_standardQ : ¬IsStandardQMatrix
    (normalizedNormalPlayerMatrix reward)

/-- The corrected normal-player matrix is standard Q, the homogeneous branch
is absent, and the full normalized singleton matrix is projective Q-bar.
This is exactly the algebraic premise of the continuous-path route, not its
strategic conclusion. -/
structure ProjectiveQBarMatrixBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  no_homogeneous : ¬HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)
  normal_standardQ : IsStandardQMatrix
    (normalizedNormalPlayerMatrix reward)
  full_projectiveQBar : IsProjectiveQBarMatrix
    (normalizedSoloMatrix reward)

/-- **Precise residual hard class.**  The corrected normal core is nonempty,
the homogeneous branch is absent, its matrix is standard Q, and the full
normalized singleton matrix fails projective Q-bar. -/
structure ResidualHardClass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  no_homogeneous : ¬HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)
  normal_standardQ : IsStandardQMatrix
    (normalizedNormalPlayerMatrix reward)
  not_full_projectiveQBar : ¬IsProjectiveQBarMatrix
    (normalizedSoloMatrix reward)

/-- The standard-Q side of the corrected normal-player split, before deciding
whether the full normalized matrix is projective Q-bar. -/
structure StandardQMatrixSide
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  no_homogeneous : ¬HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)
  normal_standardQ : IsStandardQMatrix
    (normalizedNormalPlayerMatrix reward)

/-- Forget the full-matrix Q-bar fact and retain the corrected normal-core
standard-Q side. -/
theorem ProjectiveQBarMatrixBranch.toStandardQMatrixSide
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : ProjectiveQBarMatrixBranch reward) : StandardQMatrixSide reward where
  normal_nonempty := h.normal_nonempty
  no_homogeneous := h.no_homogeneous
  normal_standardQ := h.normal_standardQ

/-- Forget the full-matrix Q-bar failure and retain the corrected normal-core
standard-Q side. -/
theorem ResidualHardClass.toStandardQMatrixSide
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : ResidualHardClass reward) : StandardQMatrixSide reward where
  normal_nonempty := h.normal_nonempty
  no_homogeneous := h.no_homogeneous
  normal_standardQ := h.normal_standardQ

/-- On the nonhomogeneous branch, failure of standard Q is equivalently
failure of the source's projective/simplex Q convention. -/
theorem OrdinaryNonQMatrixBranch.not_projectiveQ
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : OrdinaryNonQMatrixBranch reward) :
    ¬IsProjectiveQMatrix (normalizedNormalPlayerMatrix reward) := by
  rw [isProjectiveQMatrix_iff_standard_of_noHomogeneous
    (normalizedNormalPlayerMatrix reward) h.no_homogeneous]
  exact h.normal_not_standardQ

/-- **Faithful algebraic LCP gate.**  Every finite quitting reward table lies
in one explicitly scoped matrix regime.  The theorem contains no borrowed
strategic implication and no branch whose definition already assumes the
existence of an equilibrium. -/
theorem faithful_q_nonQ_lcp_matrix_gate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    AllPlayersAbnormal (normalizedSoloMatrix reward) ∨
      HomogeneousMatrixBranch reward ∨
      OrdinaryNonQMatrixBranch reward ∨
      ProjectiveQBarMatrixBranch reward ∨
      ResidualHardClass reward := by
  classical
  by_cases hnormal : HasNormalPlayers (normalizedSoloMatrix reward)
  · by_cases hhomogeneous : HasHomogeneousSimplexSolution
        (normalizedNormalPlayerMatrix reward)
    · exact Or.inr (Or.inl
        { normal_nonempty := hnormal
          homogeneous := hhomogeneous })
    · by_cases hstandard : IsStandardQMatrix
          (normalizedNormalPlayerMatrix reward)
      · by_cases hqbar : IsProjectiveQBarMatrix
            (normalizedSoloMatrix reward)
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            { normal_nonempty := hnormal
              no_homogeneous := hhomogeneous
              normal_standardQ := hstandard
              full_projectiveQBar := hqbar })))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            { normal_nonempty := hnormal
              no_homogeneous := hhomogeneous
              normal_standardQ := hstandard
              not_full_projectiveQBar := hqbar })))
      · exact Or.inr (Or.inr (Or.inl
          { normal_nonempty := hnormal
            no_homogeneous := hhomogeneous
            normal_not_standardQ := hstandard }))
  · exact Or.inl
      ((allPlayersAbnormal_iff_not_hasNormalPlayers
        (normalizedSoloMatrix reward)).2 hnormal)

/-- The Q-bar and residual regimes form the exact split of the corrected
standard-Q side by the full normalized matrix. -/
theorem standardQMatrixSide_qbar_or_residual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hQ : StandardQMatrixSide reward) :
    ProjectiveQBarMatrixBranch reward ∨ ResidualHardClass reward := by
  classical
  by_cases hqbar : IsProjectiveQBarMatrix (normalizedSoloMatrix reward)
  · exact Or.inl
      { normal_nonempty := hQ.normal_nonempty
        no_homogeneous := hQ.no_homogeneous
        normal_standardQ := hQ.normal_standardQ
        full_projectiveQBar := hqbar }
  · exact Or.inr
      { normal_nonempty := hQ.normal_nonempty
        no_homogeneous := hQ.no_homogeneous
        normal_standardQ := hQ.normal_standardQ
        not_full_projectiveQBar := hqbar }

end QuittingLCPClassification
end GameTheory
