/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
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

/-! ## Invariance under signal relabeling -/

private theorem linearIndependent_relabel_iff
    {Y S κ : Type} [Ring κ]
    {I : Type} {v : I → Y → κ} (e : Y ≃ S) :
    LinearIndependent κ (fun i =>
      LinearEquiv.piCongrLeft κ (fun _ : S => κ) e (v i)) ↔
      LinearIndependent κ v := by
  let E : (Y → κ) ≃ₗ[κ] (S → κ) :=
    LinearEquiv.piCongrLeft κ (fun _ : S => κ) e
  constructor
  · intro h
    change LinearIndependent κ (E.toLinearMap ∘ v) at h
    exact LinearIndependent.of_comp E.toLinearMap h
  · intro h
    change LinearIndependent κ (E.toLinearMap ∘ v)
    exact h.map' E.toLinearMap E.ker

/-- Relabeling public signals by an equivalence applies the corresponding
coordinate linear equivalence to every deviation row. -/
theorem deviationSignalMatrix_mapSignal_equiv
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (who : ι) {S : Type} (e : M.Signal ≃ S) :
    (M.mapSignal e).deviationSignalMatrix a who =
      fun dev => LinearEquiv.piCongrLeft ℝ (fun _ : S => ℝ) e
        (M.deviationSignalMatrix a who dev) := by
  funext dev y
  change S at y
  simp only [deviationSignalMatrix]
  rw [show LinearEquiv.piCongrLeft ℝ (fun _ : S => ℝ) e
      (M.deviationSignalVector a who dev.1) y =
        M.deviationSignalVector a who dev.1 (e.symm y) by
    simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']]
  simp only [deviationSignalVector]
  change
    ((M.signalKernel (Function.update a who dev.1)).map e y).toReal -
        ((M.signalKernel a).map e y).toReal = _
  rw [Math.ProbabilityMassFunction.map_equiv_apply,
    Math.ProbabilityMassFunction.map_equiv_apply]

/-- Individual full rank is invariant under bijective public-signal
relabeling. -/
theorem individualFullRank_mapSignal_equiv_iff
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (who : ι) {S : Type} (e : M.Signal ≃ S) :
    (M.mapSignal e).IndividualFullRank a who ↔
      M.IndividualFullRank a who := by
  rw [IndividualFullRank, M.deviationSignalMatrix_mapSignal_equiv]
  exact linearIndependent_relabel_iff e

/-- Relabeling public signals applies the same coordinate equivalence to the
combined pairwise deviation family. -/
theorem pairwiseDeviationSignalFamily_mapSignal_equiv
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (i j : ι) {S : Type} (e : M.Signal ≃ S) :
    (M.mapSignal e).pairwiseDeviationSignalFamily a i j =
      fun dev => LinearEquiv.piCongrLeft ℝ (fun _ : S => ℝ) e
        (M.pairwiseDeviationSignalFamily a i j dev) := by
  funext dev y
  cases dev with
  | inl dev =>
      exact congrFun
        (congrFun (M.deviationSignalMatrix_mapSignal_equiv a i e) dev) y
  | inr dev =>
      exact congrFun
        (congrFun (M.deviationSignalMatrix_mapSignal_equiv a j e) dev) y

/-- Pairwise full rank is invariant under bijective public-signal
relabeling. -/
theorem pairwiseFullRank_mapSignal_equiv_iff
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (i j : ι) {S : Type} (e : M.Signal ≃ S) :
    (M.mapSignal e).PairwiseFullRank a i j ↔
      M.PairwiseFullRank a i j := by
  rw [PairwiseFullRank, M.pairwiseDeviationSignalFamily_mapSignal_equiv]
  exact linearIndependent_relabel_iff e

/-- Under the individual-rank hypotheses, pairwise identifiability is also
invariant under bijective signal relabeling. -/
theorem pairwiseIdentifiable_mapSignal_equiv_iff_of_individualFullRank
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (i j : ι) {S : Type} (e : M.Signal ≃ S)
    (hi : M.IndividualFullRank a i)
    (hj : M.IndividualFullRank a j) :
    (M.mapSignal e).PairwiseIdentifiable a i j ↔
      M.PairwiseIdentifiable a i j := by
  have hi' := (M.individualFullRank_mapSignal_equiv_iff a i e).2 hi
  have hj' := (M.individualFullRank_mapSignal_equiv_iff a j e).2 hj
  constructor
  · intro hident
    have hp' : (M.mapSignal e).PairwiseFullRank a i j :=
      ((M.mapSignal e).pairwiseFullRank_iff a i j).2
        ⟨hi', hj', hident⟩
    have hp := (M.pairwiseFullRank_mapSignal_equiv_iff a i j e).1 hp'
    exact (M.pairwiseFullRank_iff a i j).1 hp |>.2.2
  · intro hident
    have hp : M.PairwiseFullRank a i j :=
      (M.pairwiseFullRank_iff a i j).2 ⟨hi, hj, hident⟩
    have hp' := (M.pairwiseFullRank_mapSignal_equiv_iff a i j e).2 hp
    exact ((M.mapSignal e).pairwiseFullRank_iff a i j).1 hp' |>.2.2

end PublicMonitoring

end KernelGame

end GameTheory
