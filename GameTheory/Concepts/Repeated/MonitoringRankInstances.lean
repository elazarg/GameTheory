/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.LinearAlgebra.StdBasis
import GameTheory.Concepts.Repeated.MonitoringInstances
import GameTheory.Concepts.Repeated.MonitoringRank

/-!
# Rank Conditions for Canonical Monitoring Structures

Perfect profile monitoring satisfies individual full rank, and satisfies
pairwise full rank for distinct players. These results provide benchmark
sanity checks for the abstract public-monitoring rank conditions.
-/

noncomputable section

namespace GameTheory

namespace KernelGame

namespace PublicMonitoring

variable {ι : Type} {G : KernelGame ι}

/-- Differences between distinct coordinate vectors and a separate base
coordinate form a linearly independent family. -/
private theorem linearIndependent_single_sub_single
    {I X : Type} [DecidableEq X]
    (base : X) (f : I → X) (hf : Function.Injective f)
    (hbase : ∀ i, f i ≠ base) :
    LinearIndependent ℝ
      (fun i => Pi.single (f i) 1 - Pi.single base 1 : I → X → ℝ) := by
  rw [linearIndependent_iff']
  intro s c hsum i hi
  have hcoord := congrFun hsum (f i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hcoord
  rw [Finset.sum_eq_single i] at hcoord
  · simpa [Pi.single_apply, hbase i] using hcoord
  · intro j hj hji
    have hfji : f j ≠ f i := fun h => hji (hf h)
    simp [hfji, (hbase i).symm]
  · simp [hi]

/-- Under perfect profile monitoring, a deviation row is the difference of
the coordinate vectors at the deviating and prescribed profiles. -/
private theorem deviationSignalMatrix_profileMonitoring
    (G : KernelGame ι) [DecidableEq ι] [DecidableEq (Profile G)]
    (a : Profile G) (who : ι) :
    G.profileMonitoring.deviationSignalMatrix a who =
      fun dev =>
        Pi.single (Function.update a who dev.1) 1 - Pi.single a 1 := by
  classical
  funext dev y
  simp [deviationSignalMatrix, deviationSignalVector, PMF.pure_apply,
    Pi.single_apply]
  split_ifs <;> simp

/-- Perfect profile monitoring has individual full rank at every prescribed
profile and for every player. -/
theorem individualFullRank_profileMonitoring
    (G : KernelGame ι) [DecidableEq ι]
    (a : Profile G) (who : ι) :
    G.profileMonitoring.IndividualFullRank a who := by
  classical
  let f : NontrivialDeviation a who → Profile G :=
    fun dev => Function.update a who dev.1
  have hf : Function.Injective f := by
    intro dev dev' h
    apply Subtype.ext
    have hwho := congrFun h who
    simpa [f] using hwho
  have hbase : ∀ dev, f dev ≠ a := by
    intro dev h
    apply dev.property
    have hwho := congrFun h who
    simpa [f] using hwho
  rw [IndividualFullRank, deviationSignalMatrix_profileMonitoring]
  exact linearIndependent_single_sub_single a f hf hbase

/-- Updating distinct players to nontrivial deviations gives distinct
profiles, including across the two deviation families. -/
private theorem pairwise_update_injective
    [DecidableEq ι] (a : Profile G) {i j : ι} (hij : i ≠ j) :
    Function.Injective
      (Sum.elim
        (fun dev : NontrivialDeviation a i =>
          Function.update a i dev.1)
        (fun dev : NontrivialDeviation a j =>
          Function.update a j dev.1)) := by
  intro dev dev' h
  cases dev with
  | inl di =>
      cases dev' with
      | inl di' =>
          apply congrArg Sum.inl
          apply Subtype.ext
          have hi := congrFun h i
          simpa using hi
      | inr dj =>
          exfalso
          apply di.property
          have hi := congrFun h i
          change Function.update a i di.1 i =
            Function.update a j dj.1 i at hi
          rw [Function.update_of_ne hij] at hi
          simpa using hi
  | inr dj =>
      cases dev' with
      | inl di =>
          exfalso
          apply di.property
          have hi := congrFun h i
          change Function.update a j dj.1 i =
            Function.update a i di.1 i at hi
          rw [Function.update_of_ne hij] at hi
          simpa using hi.symm
      | inr dj' =>
          apply congrArg Sum.inr
          apply Subtype.ext
          have hj := congrFun h j
          simpa using hj

/-- Every profile obtained by a nontrivial deviation in the combined family
differs from the prescribed profile. -/
private theorem pairwise_update_ne_base
    [DecidableEq ι] (a : Profile G) (i j : ι) :
    ∀ dev : NontrivialDeviation a i ⊕ NontrivialDeviation a j,
      Sum.elim
        (fun di : NontrivialDeviation a i => Function.update a i di.1)
        (fun dj : NontrivialDeviation a j => Function.update a j dj.1) dev ≠ a
  | .inl di => by
      intro h
      apply di.property
      have hi := congrFun h i
      simpa using hi
  | .inr dj => by
      intro h
      apply dj.property
      have hj := congrFun h j
      simpa using hj

/-- Perfect profile monitoring has pairwise full rank for every pair of
distinct players. -/
theorem pairwiseFullRank_profileMonitoring
    (G : KernelGame ι) [DecidableEq ι]
    (a : Profile G) {i j : ι} (hij : i ≠ j) :
    G.profileMonitoring.PairwiseFullRank a i j := by
  classical
  let f : NontrivialDeviation a i ⊕ NontrivialDeviation a j → Profile G :=
    Sum.elim
      (fun dev => Function.update a i dev.1)
      (fun dev => Function.update a j dev.1)
  have hf : Function.Injective f := pairwise_update_injective a hij
  have hbase : ∀ dev, f dev ≠ a := pairwise_update_ne_base a i j
  rw [PairwiseFullRank, pairwiseDeviationSignalFamily]
  rw [show Sum.elim
      (G.profileMonitoring.deviationSignalMatrix a i)
      (G.profileMonitoring.deviationSignalMatrix a j) =
        fun dev => Pi.single (f dev) 1 - Pi.single a 1 by
    funext dev
    cases dev with
    | inl dev =>
        exact congrFun (deviationSignalMatrix_profileMonitoring G a i) dev
    | inr dev =>
        exact congrFun (deviationSignalMatrix_profileMonitoring G a j) dev]
  exact linearIndependent_single_sub_single a f hf hbase

/-- The unilateral deviation subspaces of distinct players are disjoint under
perfect profile monitoring. -/
theorem pairwiseIdentifiable_profileMonitoring
    (G : KernelGame ι) [DecidableEq ι]
    (a : Profile G) {i j : ι} (hij : i ≠ j) :
    G.profileMonitoring.PairwiseIdentifiable a i j :=
  (G.profileMonitoring.pairwiseFullRank_iff a i j).1
    (pairwiseFullRank_profileMonitoring G a hij) |>.2.2

/-! ## Pure-deviation rank for behavioral mixed extensions -/

/-- Signal-difference matrix generated by nontrivial pure unilateral
deviations from an embedded pure profile in a behavioral mixed extension. -/
def pureDeviationSignalMatrix
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (who : ι) :
    Matrix (NontrivialDeviation a who) M.Signal ℝ :=
  fun dev =>
    M.deviationSignalVector (G.pureMixedProfile a) who (PMF.pure dev.1)

/-- Individual full rank restricted to pure unilateral deviations. This is
the finite-action FLM condition for a behavioral mixed extension; indexing by
all mixed strategies would introduce affine redundancies. -/
def PureIndividualFullRank
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (who : ι) : Prop :=
  LinearIndependent ℝ (M.pureDeviationSignalMatrix a who)

/-- Combined pure-deviation signal family for two players. -/
def purePairwiseDeviationSignalFamily
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (i j : ι) :
    Matrix (NontrivialDeviation a i ⊕ NontrivialDeviation a j) M.Signal ℝ :=
  Sum.elim (M.pureDeviationSignalMatrix a i)
    (M.pureDeviationSignalMatrix a j)

/-- Pairwise full rank restricted to nontrivial pure deviations. -/
def PurePairwiseFullRank
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (i j : ι) : Prop :=
  LinearIndependent ℝ (M.purePairwiseDeviationSignalFamily a i j)

/-- The pure-deviation matrix under realized-action monitoring is exactly the
perfect-profile-monitoring deviation matrix of the underlying pure game. -/
theorem pureDeviationSignalMatrix_realizedActionMonitoring
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    (a : Profile G) (who : ι) :
    G.realizedActionMonitoring.pureDeviationSignalMatrix a who =
      G.profileMonitoring.deviationSignalMatrix a who := by
  funext dev y
  simp only [pureDeviationSignalMatrix, deviationSignalMatrix,
    deviationSignalVector]
  rw [← G.pureMixedProfile_update]
  have hdev :
      Math.PMFProduct.pmfPi
          (G.pureMixedProfile (Function.update a who dev.1)) =
        PMF.pure (Function.update a who dev.1) := by
    change Math.PMFProduct.pmfPi
      (fun i => (PMF.pure ((Function.update a who dev.1) i) :
        PMF (G.Strategy i))) = _
    exact Math.PMFProduct.pmfPi_pure _
  have hbase : Math.PMFProduct.pmfPi (G.pureMixedProfile a) =
      PMF.pure a := by
    change Math.PMFProduct.pmfPi
      (fun i => (PMF.pure (a i) : PMF (G.Strategy i))) = _
    exact Math.PMFProduct.pmfPi_pure _
  rw [hdev, hbase]

/-- Realized-action monitoring has full rank with respect to every player's
nontrivial pure deviations. -/
theorem pureIndividualFullRank_realizedActionMonitoring
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    (a : Profile G) (who : ι) :
    G.realizedActionMonitoring.PureIndividualFullRank a who := by
  rw [PureIndividualFullRank,
    pureDeviationSignalMatrix_realizedActionMonitoring G]
  exact individualFullRank_profileMonitoring G a who

/-- The combined pure-deviation family under realized-action monitoring is
the corresponding perfect-profile-monitoring family. -/
theorem purePairwiseDeviationSignalFamily_realizedActionMonitoring
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    (a : Profile G) (i j : ι) :
    G.realizedActionMonitoring.purePairwiseDeviationSignalFamily a i j =
      G.profileMonitoring.pairwiseDeviationSignalFamily a i j := by
  rw [purePairwiseDeviationSignalFamily, pairwiseDeviationSignalFamily,
    pureDeviationSignalMatrix_realizedActionMonitoring G,
    pureDeviationSignalMatrix_realizedActionMonitoring G]

/-- Realized-action monitoring has pairwise full rank with respect to pure
deviations by distinct players. -/
theorem purePairwiseFullRank_realizedActionMonitoring
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    (a : Profile G) {i j : ι} (hij : i ≠ j) :
    G.realizedActionMonitoring.PurePairwiseFullRank a i j := by
  rw [PurePairwiseFullRank,
    purePairwiseDeviationSignalFamily_realizedActionMonitoring G]
  exact pairwiseFullRank_profileMonitoring G a hij

/-- An arbitrary mixed deviation's signal vector is the probability-weighted
sum of the pure-deviation signal vectors. -/
theorem deviationSignalVector_mixedExtension_eq_sum_pure
    (M : G.PublicMonitoring) [Fintype ι] [DecidableEq ι]
    (a : Profile G) (who : ι) [Fintype (G.Strategy who)]
    (τ : PMF (G.Strategy who)) :
    M.mixedExtension.deviationSignalVector
        (G.pureMixedProfile a) who τ =
      ∑ dev, (τ dev).toReal • M.deviationSignalVector a who dev := by
  funext y
  change
    (M.mixedExtension.signalKernel
          (Function.update (G.pureMixedProfile a) who τ) y).toReal -
        (M.mixedExtension.signalKernel (G.pureMixedProfile a) y).toReal =
      (∑ dev, (τ dev).toReal • M.deviationSignalVector a who dev) y
  rw [M.mixedExtension_signalKernel_update_pureMixedProfile,
    M.mixedExtension_signalKernel_pure]
  simp only [deviationSignalVector, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    Math.Probability.pmf_toReal_sum_one, one_mul]

end PublicMonitoring

end KernelGame

end GameTheory
