/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
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
    Matrix (NontrivialDeviation a i ⊕ NontrivialDeviation a j) M.Signal ℝ :=
  Sum.elim (M.deviationSignalMatrix a i) (M.deviationSignalMatrix a j)

/-- Pairwise full rank: the combined deviation-difference rows for two players
are linearly independent. The intended use is for distinct players. -/
def PairwiseFullRank
    (M : G.PublicMonitoring) [DecidableEq ι]
    (a : Profile G) (i j : ι) : Prop :=
  LinearIndependent ℝ (M.pairwiseDeviationSignalFamily a i j)

/-! ## Finite-dimensional rank presentation -/

/-- Numerical row rank of one player's deviation-signal matrix. -/
noncomputable def individualDeviationRank
    (M : G.PublicMonitoring) [DecidableEq ι] [Fintype M.Signal]
    (a : Profile G) (who : ι) : ℕ :=
  (M.deviationSignalMatrix a who).rank

/-- Numerical row rank of the combined deviation-signal matrix for two
players. -/
noncomputable def pairwiseDeviationRank
    (M : G.PublicMonitoring) [DecidableEq ι] [Fintype M.Signal]
    (a : Profile G) (i j : ι) : ℕ :=
  (M.pairwiseDeviationSignalFamily a i j).rank

/-- For finitely many deviations, individual full rank says exactly that the
matrix rank equals the number of nontrivial deviations. -/
theorem individualFullRank_iff_individualDeviationRank_eq_card
    (M : G.PublicMonitoring) [DecidableEq ι] [Fintype M.Signal]
    (a : Profile G) (who : ι) [Fintype (NontrivialDeviation a who)] :
    M.IndividualFullRank a who ↔
      M.individualDeviationRank a who =
        Fintype.card (NontrivialDeviation a who) := by
  let A : Matrix (NontrivialDeviation a who) M.Signal ℝ :=
    M.deviationSignalMatrix a who
  change LinearIndependent ℝ A ↔ A.rank = _
  constructor
  · exact LinearIndependent.rank_matrix
  · intro h
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (NontrivialDeviation a who) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.row))
    rw [← Matrix.rank_eq_finrank_span_row]
    exact h.symm

/-- For finitely many deviations, pairwise full rank says exactly that the
combined matrix rank equals the total number of nontrivial deviations. -/
theorem pairwiseFullRank_iff_pairwiseDeviationRank_eq_card
    (M : G.PublicMonitoring) [DecidableEq ι] [Fintype M.Signal]
    (a : Profile G) (i j : ι)
    [Fintype (NontrivialDeviation a i)]
    [Fintype (NontrivialDeviation a j)] :
    M.PairwiseFullRank a i j ↔
      M.pairwiseDeviationRank a i j =
        Fintype.card (NontrivialDeviation a i) +
          Fintype.card (NontrivialDeviation a j) := by
  let A : Matrix (NontrivialDeviation a i ⊕ NontrivialDeviation a j)
      M.Signal ℝ := M.pairwiseDeviationSignalFamily a i j
  change LinearIndependent ℝ A ↔ A.rank = _
  constructor
  · intro h
    dsimp [A] at h ⊢
    simpa only [pairwiseDeviationSignalFamily, Fintype.card_sum] using
      h.rank_matrix
  · intro h
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (NontrivialDeviation a i ⊕ NontrivialDeviation a j) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.row))
    rw [← Matrix.rank_eq_finrank_span_row, Fintype.card_sum]
    simpa only [Fintype.card_sum] using h.symm

/-- Sum of the coordinates of a finite real vector, as a linear map. -/
def signalSumLinearMap (S : Type) [Fintype S] : (S → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun v => ∑ s, v s
    map_add' := fun v w => by
      change (∑ s, (v s + w s)) = (∑ s, v s) + ∑ s, w s
      exact Finset.sum_add_distrib
    map_smul' := fun c v => by
      change (∑ s, c * v s) = c * ∑ s, v s
      simpa using
        (Finset.mul_sum Finset.univ (fun s => v s) c).symm }

/-- The subspace of real signal vectors whose coordinates sum to zero. -/
def zeroSumSignalSubspace (S : Type) [Fintype S] : Submodule ℝ (S → ℝ) :=
  LinearMap.ker (signalSumLinearMap S)

@[simp]
theorem mem_zeroSumSignalSubspace_iff
    {S : Type} [Fintype S] (v : S → ℝ) :
    v ∈ zeroSumSignalSubspace S ↔ ∑ s, v s = 0 :=
  by simp [zeroSumSignalSubspace, signalSumLinearMap]

/-- The zero-sum signal subspace has the expected codimension one. -/
theorem finrank_zeroSumSignalSubspace
    (S : Type) [Fintype S] [Nonempty S] :
    Module.finrank ℝ (zeroSumSignalSubspace S) = Fintype.card S - 1 := by
  classical
  let L : (S → ℝ) →ₗ[ℝ] ℝ := signalSumLinearMap S
  have hrange : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_iff'.2
    intro x
    let s : S := Classical.choice inferInstance
    refine ⟨Pi.single s x, ?_⟩
    simp [L, signalSumLinearMap]
  have hdim := L.finrank_range_add_finrank_ker
  rw [hrange, finrank_top,
    Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hdim
  change Module.finrank ℝ (LinearMap.ker L) = Fintype.card S - 1
  omega

/-- Every deviation row belongs to the zero-sum signal subspace. -/
theorem deviationSignalMatrix_mem_zeroSumSignalSubspace
    (M : G.PublicMonitoring) [DecidableEq ι] [Fintype M.Signal]
    (a : Profile G) (who : ι) (dev : NontrivialDeviation a who) :
    M.deviationSignalMatrix a who dev ∈
      zeroSumSignalSubspace M.Signal := by
  rw [mem_zeroSumSignalSubspace_iff]
  simp only [deviationSignalMatrix, deviationSignalVector,
    Finset.sum_sub_distrib, Math.Probability.pmf_toReal_sum_one, sub_self]

/-- Individual deviation rank is at most the dimension of the normalized
signal simplex's direction space. -/
theorem individualDeviationRank_le_card_signal_sub_one
    (M : G.PublicMonitoring) [DecidableEq ι]
    [Fintype M.Signal] [Nonempty M.Signal]
    (a : Profile G) (who : ι)
    [Finite (NontrivialDeviation a who)] :
    M.individualDeviationRank a who ≤ Fintype.card M.Signal - 1 := by
  rw [individualDeviationRank, Matrix.rank_eq_finrank_span_row,
    ← finrank_zeroSumSignalSubspace M.Signal]
  apply Submodule.finrank_mono
  apply Submodule.span_le.2
  rintro _ ⟨dev, rfl⟩
  exact M.deviationSignalMatrix_mem_zeroSumSignalSubspace a who dev

/-- Individual full rank therefore requires at least one independent signal
direction per nontrivial deviation. -/
theorem IndividualFullRank.card_deviations_le_card_signal_sub_one
    {M : G.PublicMonitoring} [DecidableEq ι]
    [Fintype M.Signal] [Nonempty M.Signal]
    {a : Profile G} {who : ι} [Fintype (NontrivialDeviation a who)]
    (h : M.IndividualFullRank a who) :
    Fintype.card (NontrivialDeviation a who) ≤
      Fintype.card M.Signal - 1 := by
  rw [M.individualFullRank_iff_individualDeviationRank_eq_card] at h
  rw [← h]
  exact M.individualDeviationRank_le_card_signal_sub_one a who

/-- Pairwise deviation rank obeys the same sharp signal-dimension bound. -/
theorem pairwiseDeviationRank_le_card_signal_sub_one
    (M : G.PublicMonitoring) [DecidableEq ι]
    [Fintype M.Signal] [Nonempty M.Signal]
    (a : Profile G) (i j : ι)
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)] :
    M.pairwiseDeviationRank a i j ≤ Fintype.card M.Signal - 1 := by
  rw [pairwiseDeviationRank, Matrix.rank_eq_finrank_span_row,
    ← finrank_zeroSumSignalSubspace M.Signal]
  apply Submodule.finrank_mono
  apply Submodule.span_le.2
  rintro _ ⟨dev, rfl⟩
  cases dev with
  | inl dev =>
      exact M.deviationSignalMatrix_mem_zeroSumSignalSubspace a i dev
  | inr dev =>
      exact M.deviationSignalMatrix_mem_zeroSumSignalSubspace a j dev

/-- Pairwise full rank requires enough public-signal directions to distinguish
all nontrivial deviations by the two players. -/
theorem PairwiseFullRank.card_deviations_le_card_signal_sub_one
    {M : G.PublicMonitoring} [DecidableEq ι]
    [Fintype M.Signal] [Nonempty M.Signal]
    {a : Profile G} {i j : ι}
    [Fintype (NontrivialDeviation a i)]
    [Fintype (NontrivialDeviation a j)]
    (h : M.PairwiseFullRank a i j) :
    Fintype.card (NontrivialDeviation a i) +
        Fintype.card (NontrivialDeviation a j) ≤
      Fintype.card M.Signal - 1 := by
  rw [M.pairwiseFullRank_iff_pairwiseDeviationRank_eq_card] at h
  rw [← h]
  exact M.pairwiseDeviationRank_le_card_signal_sub_one a i j

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
