/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import GameTheory.Concepts.Repeated.Monitoring

/-!
# Signal-Informativeness Rank Conditions

Basis-free versions of the individual and pairwise full-rank conditions used
in imperfect-public-monitoring folk theorems. Rows are changes in the public
signal law caused by nontrivial unilateral deviations from a prescribed stage
profile. Removing the prescribed action makes the standard affine rank
conditions ordinary linear-independence conditions on deviation differences.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace KernelGame

namespace PublicMonitoring

variable {ι : Type} {G : KernelGame ι}

/-- A unilateral stage action distinct from the prescribed action. -/
abbrev NontrivialDeviation (a : Profile G) (who : ι) :=
  {dev : G.Strategy who // dev ≠ a who}

/-- Change in the real-valued public signal probability vector caused by one
unilateral deviation. -/
def deviationSignalVector
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (who : ι) (dev : G.Strategy who) : M.Signal → ℝ :=
  fun y =>
    (M.signalKernel (Function.update a who dev) y).toReal -
      (M.signalKernel a y).toReal

/-- Matrix of unilateral deviation-signal differences. Rows are indexed by
nontrivial deviations and columns by public signals. -/
def deviationSignalMatrix
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (who : ι) :
    Matrix (NontrivialDeviation a who) M.Signal ℝ :=
  fun dev => M.deviationSignalVector a who dev.1

/-- The deviation-difference rows for one player are linearly independent. -/
def IndividualFullRank
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (who : ι) : Prop :=
  LinearIndependent ℝ (M.deviationSignalMatrix a who)

/-- The two players' deviation subspaces intersect only at zero. This is the
linear-algebraic identifiability condition separating their unilateral signal
effects. -/
def PairwiseIdentifiable
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (i j : ι) : Prop :=
  Disjoint
    (Submodule.span ℝ (Set.range (M.deviationSignalMatrix a i)))
    (Submodule.span ℝ (Set.range (M.deviationSignalMatrix a j)))

/-- Combined family of two players' unilateral deviation-signal vectors. -/
def pairwiseDeviationSignalFamily
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (i j : ι) :
    NontrivialDeviation a i ⊕ NontrivialDeviation a j → M.Signal → ℝ :=
  Sum.elim (M.deviationSignalMatrix a i) (M.deviationSignalMatrix a j)

/-- Pairwise full rank: the combined deviation-difference rows for two players
are linearly independent. The intended use is for distinct players. -/
def PairwiseFullRank
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (i j : ι) : Prop :=
  LinearIndependent ℝ (M.pairwiseDeviationSignalFamily a i j)

/-- Every deviation-signal vector has coordinate sum zero because both signal
laws are probability distributions. -/
theorem sum_deviationSignalVector_eq_zero
    (M : G.PublicMonitoring) [DecidableEq ι] [Fintype M.Signal]
    (a : Profile G) (who : ι) (dev : G.Strategy who) :
    ∑ y, M.deviationSignalVector a who dev y = 0 := by
  simp only [deviationSignalVector, Finset.sum_sub_distrib,
    Math.Probability.pmf_toReal_sum_one, sub_self]

/-- Pairwise full rank is exactly individual full rank for both players plus
pairwise identifiability of their deviation subspaces. -/
theorem pairwiseFullRank_iff
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (i j : ι) :
    M.PairwiseFullRank a i j ↔
      M.IndividualFullRank a i ∧
        M.IndividualFullRank a j ∧
          M.PairwiseIdentifiable a i j := by
  simpa only [PairwiseFullRank, IndividualFullRank,
    PairwiseIdentifiable, pairwiseDeviationSignalFamily,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
      (linearIndependent_sum (R := ℝ)
        (v := M.pairwiseDeviationSignalFamily a i j))

/-- Pairwise identifiability is symmetric in the two players. -/
theorem PairwiseIdentifiable.symm
    {M : G.PublicMonitoring} [DecidableEq ι]
    {a : Profile G} {i j : ι}
    (h : M.PairwiseIdentifiable a i j) :
    M.PairwiseIdentifiable a j i :=
  Disjoint.symm h

/-- Pairwise full rank is symmetric in the two players. -/
theorem PairwiseFullRank.symm
    {M : G.PublicMonitoring} [DecidableEq ι]
    {a : Profile G} {i j : ι}
    (h : M.PairwiseFullRank a i j) :
    M.PairwiseFullRank a j i := by
  rw [M.pairwiseFullRank_iff] at h ⊢
  exact ⟨h.2.1, h.1, h.2.2.symm⟩

/-- Individual full rank forces every nontrivial deviation to change the
public signal law. -/
theorem IndividualFullRank.signalKernel_update_ne
    {M : G.PublicMonitoring} [DecidableEq ι]
    {a : Profile G} {who : ι}
    (h : M.IndividualFullRank a who)
    (dev : NontrivialDeviation a who) :
    M.signalKernel (Function.update a who dev.1) ≠ M.signalKernel a := by
  intro heq
  apply LinearIndependent.ne_zero dev h
  funext y
  simp only [deviationSignalMatrix, deviationSignalVector]
  rw [heq]
  simp

/-- Under individual full rank, distinct nontrivial deviations induce distinct
public signal laws. -/
theorem IndividualFullRank.signalKernel_update_injective
    {M : G.PublicMonitoring} [DecidableEq ι]
    {a : Profile G} {who : ι}
    (h : M.IndividualFullRank a who) :
    Function.Injective fun dev : NontrivialDeviation a who =>
      M.signalKernel (Function.update a who dev.1) := by
  intro dev dev' heq
  apply h.injective
  funext y
  simp only [deviationSignalMatrix, deviationSignalVector]
  change M.signalKernel (Function.update a who dev.1) =
    M.signalKernel (Function.update a who dev'.1) at heq
  rw [heq]

end PublicMonitoring

end KernelGame

end GameTheory
