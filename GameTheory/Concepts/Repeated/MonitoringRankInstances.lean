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

/-- The spans of two players' pure-deviation signal effects intersect only
at zero. -/
def PurePairwiseIdentifiable
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (i j : ι) : Prop :=
  Disjoint
    (Submodule.span ℝ (Set.range (M.pureDeviationSignalMatrix a i)))
    (Submodule.span ℝ (Set.range (M.pureDeviationSignalMatrix a j)))

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

/-- Pure pairwise full rank is exactly pure individual full rank for both
players plus identifiability of their pure-deviation subspaces. -/
theorem purePairwiseFullRank_iff
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (i j : ι) :
    M.PurePairwiseFullRank a i j ↔
      M.PureIndividualFullRank a i ∧
        M.PureIndividualFullRank a j ∧
          M.PurePairwiseIdentifiable a i j := by
  simpa only [PurePairwiseFullRank, PureIndividualFullRank,
    PurePairwiseIdentifiable, purePairwiseDeviationSignalFamily,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
      (linearIndependent_sum (R := ℝ)
        (v := M.purePairwiseDeviationSignalFamily a i j))

/-- Pure pairwise identifiability is symmetric in the two players. -/
theorem PurePairwiseIdentifiable.symm
    [Fintype ι] [DecidableEq ι]
    {M : G.mixedExtension.PublicMonitoring}
    {a : Profile G} {i j : ι}
    (h : M.PurePairwiseIdentifiable a i j) :
    M.PurePairwiseIdentifiable a j i :=
  Disjoint.symm h

/-- Pure pairwise full rank is symmetric in the two players. -/
theorem PurePairwiseFullRank.symm
    [Fintype ι] [DecidableEq ι]
    {M : G.mixedExtension.PublicMonitoring}
    {a : Profile G} {i j : ι}
    (h : M.PurePairwiseFullRank a i j) :
    M.PurePairwiseFullRank a j i := by
  rw [M.purePairwiseFullRank_iff] at h ⊢
  exact ⟨h.2.1, h.1, h.2.2.symm⟩

/-! ### Numerical pure-deviation ranks -/

/-- Numerical row rank of one player's pure-deviation signal matrix. The
chosen finite enumeration of signals is kept internal. -/
noncomputable def pureIndividualDeviationRank
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Finite M.Signal]
    (a : Profile G) (who : ι) : ℕ := by
  letI := Fintype.ofFinite M.Signal
  exact (M.pureDeviationSignalMatrix a who).rank

/-- Numerical row rank of the combined pure-deviation signal matrix for two
players. The chosen finite enumeration of signals is kept internal. -/
noncomputable def purePairwiseDeviationRank
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Finite M.Signal]
    (a : Profile G) (i j : ι) : ℕ := by
  letI := Fintype.ofFinite M.Signal
  exact (M.purePairwiseDeviationSignalFamily a i j).rank

/-- With finitely many pure deviations, pure individual full rank is exactly
full numerical row rank. -/
theorem pureIndividualFullRank_iff_pureIndividualDeviationRank_eq_card
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Finite M.Signal]
    (a : Profile G) (who : ι)
    [Finite (NontrivialDeviation a who)] :
    M.PureIndividualFullRank a who ↔
      M.pureIndividualDeviationRank a who =
        Nat.card (NontrivialDeviation a who) := by
  letI := Fintype.ofFinite M.Signal
  letI := Fintype.ofFinite (NontrivialDeviation a who)
  let A : Matrix (NontrivialDeviation a who) M.Signal ℝ :=
    M.pureDeviationSignalMatrix a who
  change LinearIndependent ℝ A ↔ A.rank = _
  constructor
  · intro h
    have hrank : A.rank = Fintype.card (NontrivialDeviation a who) :=
      h.rank_matrix
    simpa only [Nat.card_eq_fintype_card] using hrank
  · intro h
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (NontrivialDeviation a who) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.row))
    rw [← Matrix.rank_eq_finrank_span_row]
    simpa only [Nat.card_eq_fintype_card] using h.symm

/-- With finitely many pure deviations, pure pairwise full rank is exactly
full numerical row rank of the combined family. -/
theorem purePairwiseFullRank_iff_purePairwiseDeviationRank_eq_card
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Finite M.Signal]
    (a : Profile G) (i j : ι)
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)] :
    M.PurePairwiseFullRank a i j ↔
      M.purePairwiseDeviationRank a i j =
        Nat.card (NontrivialDeviation a i) +
          Nat.card (NontrivialDeviation a j) := by
  letI := Fintype.ofFinite M.Signal
  letI := Fintype.ofFinite (NontrivialDeviation a i)
  letI := Fintype.ofFinite (NontrivialDeviation a j)
  let A : Matrix (NontrivialDeviation a i ⊕ NontrivialDeviation a j)
      M.Signal ℝ := M.purePairwiseDeviationSignalFamily a i j
  change LinearIndependent ℝ A ↔ A.rank = _
  constructor
  · intro h
    dsimp [A] at h ⊢
    simpa only [purePairwiseDeviationSignalFamily,
      Nat.card_eq_fintype_card, Fintype.card_sum] using h.rank_matrix
  · intro h
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card
        (NontrivialDeviation a i ⊕ NontrivialDeviation a j) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.row))
    rw [← Matrix.rank_eq_finrank_span_row, Fintype.card_sum]
    simpa only [Nat.card_eq_fintype_card] using h.symm

/-- Pure individual deviation rank is bounded by the dimension of the
zero-sum signal subspace. -/
theorem pureIndividualDeviationRank_le_card_signal_sub_one
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    [Finite M.Signal] [Nonempty M.Signal]
    (a : Profile G) (who : ι)
    [Finite (NontrivialDeviation a who)] :
    M.pureIndividualDeviationRank a who ≤ Nat.card M.Signal - 1 := by
  letI := Fintype.ofFinite M.Signal
  rw [pureIndividualDeviationRank, Matrix.rank_eq_finrank_span_row,
    Nat.card_eq_fintype_card,
    ← Math.LinearAlgebra.finrank_zeroSumSubspace ℝ M.Signal]
  apply Submodule.finrank_mono
  apply Submodule.span_le.2
  rintro _ ⟨dev, rfl⟩
  change M.deviationSignalVector (G.pureMixedProfile a) who
    (PMF.pure dev.1) ∈ Math.LinearAlgebra.zeroSumSubspace ℝ M.Signal
  rw [Math.LinearAlgebra.mem_zeroSumSubspace_iff]
  exact M.sum_deviationSignalVector_eq_zero
    (G.pureMixedProfile a) who (PMF.pure dev.1)

/-- Pure individual full rank requires at least one independent signal
direction per nontrivial pure deviation. -/
theorem PureIndividualFullRank.card_deviations_le_card_signal_sub_one
    [Fintype ι] [DecidableEq ι]
    {M : G.mixedExtension.PublicMonitoring}
    [Finite M.Signal] [Nonempty M.Signal]
    {a : Profile G} {who : ι}
    [Finite (NontrivialDeviation a who)]
    (h : M.PureIndividualFullRank a who) :
    Nat.card (NontrivialDeviation a who) ≤ Nat.card M.Signal - 1 := by
  rw [← (M.pureIndividualFullRank_iff_pureIndividualDeviationRank_eq_card
    a who).1 h]
  exact M.pureIndividualDeviationRank_le_card_signal_sub_one a who

/-- Pure pairwise deviation rank is bounded by the dimension of the zero-sum
signal subspace. -/
theorem purePairwiseDeviationRank_le_card_signal_sub_one
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    [Finite M.Signal] [Nonempty M.Signal]
    (a : Profile G) (i j : ι)
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)] :
    M.purePairwiseDeviationRank a i j ≤ Nat.card M.Signal - 1 := by
  letI := Fintype.ofFinite M.Signal
  rw [purePairwiseDeviationRank, Matrix.rank_eq_finrank_span_row,
    Nat.card_eq_fintype_card,
    ← Math.LinearAlgebra.finrank_zeroSumSubspace ℝ M.Signal]
  apply Submodule.finrank_mono
  apply Submodule.span_le.2
  rintro _ ⟨dev, rfl⟩
  cases dev with
  | inl dev =>
      change M.deviationSignalVector (G.pureMixedProfile a) i
        (PMF.pure dev.1) ∈ Math.LinearAlgebra.zeroSumSubspace ℝ M.Signal
      rw [Math.LinearAlgebra.mem_zeroSumSubspace_iff]
      exact M.sum_deviationSignalVector_eq_zero
        (G.pureMixedProfile a) i (PMF.pure dev.1)
  | inr dev =>
      change M.deviationSignalVector (G.pureMixedProfile a) j
        (PMF.pure dev.1) ∈ Math.LinearAlgebra.zeroSumSubspace ℝ M.Signal
      rw [Math.LinearAlgebra.mem_zeroSumSubspace_iff]
      exact M.sum_deviationSignalVector_eq_zero
        (G.pureMixedProfile a) j (PMF.pure dev.1)

/-- Pure pairwise full rank requires enough signal directions for both
players' nontrivial pure deviations. -/
theorem PurePairwiseFullRank.card_deviations_le_card_signal_sub_one
    [Fintype ι] [DecidableEq ι]
    {M : G.mixedExtension.PublicMonitoring}
    [Finite M.Signal] [Nonempty M.Signal]
    {a : Profile G} {i j : ι}
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)]
    (h : M.PurePairwiseFullRank a i j) :
    Nat.card (NontrivialDeviation a i) +
        Nat.card (NontrivialDeviation a j) ≤ Nat.card M.Signal - 1 := by
  rw [← (M.purePairwiseFullRank_iff_purePairwiseDeviationRank_eq_card
    a i j).1 h]
  exact M.purePairwiseDeviationRank_le_card_signal_sub_one a i j

/-! ### Invariance under signal relabeling -/

/-- Relabeling public signals applies the corresponding coordinate linear
equivalence to every pure-deviation row. -/
theorem pureDeviationSignalMatrix_mapSignal_equiv
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (who : ι) {S : Type} (e : M.Signal ≃ S) :
    (M.mapSignal e).pureDeviationSignalMatrix a who =
      fun dev => LinearEquiv.piCongrLeft ℝ (fun _ : S => ℝ) e
        (M.pureDeviationSignalMatrix a who dev) := by
  funext dev y
  change S at y
  simp only [pureDeviationSignalMatrix]
  rw [show LinearEquiv.piCongrLeft ℝ (fun _ : S => ℝ) e
      (M.deviationSignalVector (G.pureMixedProfile a) who
        (PMF.pure dev.1)) y =
        M.deviationSignalVector (G.pureMixedProfile a) who
          (PMF.pure dev.1) (e.symm y) by
    simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']]
  simp only [deviationSignalVector]
  change
    ((M.signalKernel
          (Function.update (G.pureMixedProfile a) who
            (PMF.pure dev.1))).map e y).toReal -
        ((M.signalKernel (G.pureMixedProfile a)).map e y).toReal = _
  rw [Math.ProbabilityMassFunction.map_equiv_apply,
    Math.ProbabilityMassFunction.map_equiv_apply]

/-- Pure individual full rank is invariant under bijective public-signal
relabeling. -/
theorem pureIndividualFullRank_mapSignal_equiv_iff
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (who : ι) {S : Type} (e : M.Signal ≃ S) :
    (M.mapSignal e).PureIndividualFullRank a who ↔
      M.PureIndividualFullRank a who := by
  rw [PureIndividualFullRank,
    M.pureDeviationSignalMatrix_mapSignal_equiv a who e]
  exact Math.LinearAlgebra.linearIndependent_piCongrLeft_iff e

/-- Relabeling public signals applies the same coordinate equivalence to the
combined pure-deviation family. -/
theorem purePairwiseDeviationSignalFamily_mapSignal_equiv
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (i j : ι) {S : Type} (e : M.Signal ≃ S) :
    (M.mapSignal e).purePairwiseDeviationSignalFamily a i j =
      fun dev => LinearEquiv.piCongrLeft ℝ (fun _ : S => ℝ) e
        (M.purePairwiseDeviationSignalFamily a i j dev) := by
  funext dev y
  cases dev with
  | inl dev =>
      exact congrFun
        (congrFun
          (M.pureDeviationSignalMatrix_mapSignal_equiv a i e) dev) y
  | inr dev =>
      exact congrFun
        (congrFun
          (M.pureDeviationSignalMatrix_mapSignal_equiv a j e) dev) y

/-- Pure pairwise full rank is invariant under bijective public-signal
relabeling. -/
theorem purePairwiseFullRank_mapSignal_equiv_iff
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (i j : ι) {S : Type} (e : M.Signal ≃ S) :
    (M.mapSignal e).PurePairwiseFullRank a i j ↔
      M.PurePairwiseFullRank a i j := by
  rw [PurePairwiseFullRank,
    M.purePairwiseDeviationSignalFamily_mapSignal_equiv a i j e]
  exact Math.LinearAlgebra.linearIndependent_piCongrLeft_iff e

/-- Bijective public-signal relabeling preserves numerical pure individual
deviation rank. -/
theorem pureIndividualDeviationRank_mapSignal_equiv
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Finite M.Signal]
    (a : Profile G) (who : ι) {S : Type} [Finite S]
    [Finite (NontrivialDeviation a who)]
    (e : M.Signal ≃ S) :
    (M.mapSignal e).pureIndividualDeviationRank a who =
      M.pureIndividualDeviationRank a who := by
  letI := Fintype.ofFinite M.Signal
  letI := Fintype.ofFinite S
  let E : (M.Signal → ℝ) ≃ₗ[ℝ] (S → ℝ) :=
    LinearEquiv.piCongrLeft ℝ (fun _ : S => ℝ) e
  rw [pureIndividualDeviationRank, pureIndividualDeviationRank,
    M.pureDeviationSignalMatrix_mapSignal_equiv a who e,
    Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  change Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range (E.toLinearMap ∘ M.pureDeviationSignalMatrix a who))) =
    Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range (M.pureDeviationSignalMatrix a who)))
  rw [Set.range_comp, ← LinearMap.map_span]
  exact E.finrank_map_eq _

/-- Bijective public-signal relabeling preserves numerical pure pairwise
deviation rank. -/
theorem purePairwiseDeviationRank_mapSignal_equiv
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Finite M.Signal]
    (a : Profile G) (i j : ι) {S : Type} [Finite S]
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)]
    (e : M.Signal ≃ S) :
    (M.mapSignal e).purePairwiseDeviationRank a i j =
      M.purePairwiseDeviationRank a i j := by
  letI := Fintype.ofFinite M.Signal
  letI := Fintype.ofFinite S
  let E : (M.Signal → ℝ) ≃ₗ[ℝ] (S → ℝ) :=
    LinearEquiv.piCongrLeft ℝ (fun _ : S => ℝ) e
  rw [purePairwiseDeviationRank, purePairwiseDeviationRank,
    M.purePairwiseDeviationSignalFamily_mapSignal_equiv a i j e,
    Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  change Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range
          (E.toLinearMap ∘ M.purePairwiseDeviationSignalFamily a i j))) =
    Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range (M.purePairwiseDeviationSignalFamily a i j)))
  rw [Set.range_comp, ← LinearMap.map_span]
  exact E.finrank_map_eq _

/-- Under pure individual full rank, pure pairwise identifiability is
invariant under bijective signal relabeling. -/
theorem purePairwiseIdentifiable_mapSignal_equiv_iff_of_individualFullRank
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring)
    (a : Profile G) (i j : ι) {S : Type} (e : M.Signal ≃ S)
    (hi : M.PureIndividualFullRank a i)
    (hj : M.PureIndividualFullRank a j) :
    (M.mapSignal e).PurePairwiseIdentifiable a i j ↔
      M.PurePairwiseIdentifiable a i j := by
  have hi' := (M.pureIndividualFullRank_mapSignal_equiv_iff a i e).2 hi
  have hj' := (M.pureIndividualFullRank_mapSignal_equiv_iff a j e).2 hj
  constructor
  · intro hident
    have hp' : (M.mapSignal e).PurePairwiseFullRank a i j :=
      ((M.mapSignal e).purePairwiseFullRank_iff a i j).2
        ⟨hi', hj', hident⟩
    have hp := (M.purePairwiseFullRank_mapSignal_equiv_iff a i j e).1 hp'
    exact (M.purePairwiseFullRank_iff a i j).1 hp |>.2.2
  · intro hident
    have hp : M.PurePairwiseFullRank a i j :=
      (M.purePairwiseFullRank_iff a i j).2 ⟨hi, hj, hident⟩
    have hp' := (M.purePairwiseFullRank_mapSignal_equiv_iff a i j e).2 hp
    exact ((M.mapSignal e).purePairwiseFullRank_iff a i j).1 hp' |>.2.2

/-! ### Monotonicity under stochastic garbling -/

/-- Garbling applies the stochastic pushforward linear map to each
pure-deviation signal row. -/
theorem pureDeviationSignalMatrix_garble
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    {S : Type} (K : Math.Probability.Kernel M.Signal S)
    (a : Profile G) (who : ι) :
    (M.garble K).pureDeviationSignalMatrix a who =
      fun dev => K.pushforwardLinearMap
        (M.pureDeviationSignalMatrix a who dev) := by
  funext dev
  simp only [pureDeviationSignalMatrix]
  exact M.deviationSignalVector_garble K
    (G.pureMixedProfile a) who (PMF.pure dev.1)

/-- Garbling applies the same stochastic pushforward to the combined
pure-deviation family. -/
theorem purePairwiseDeviationSignalFamily_garble
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    {S : Type} (K : Math.Probability.Kernel M.Signal S)
    (a : Profile G) (i j : ι) :
    (M.garble K).purePairwiseDeviationSignalFamily a i j =
      fun dev => K.pushforwardLinearMap
        (M.purePairwiseDeviationSignalFamily a i j dev) := by
  funext dev
  cases dev with
  | inl dev =>
      exact congrFun (M.pureDeviationSignalMatrix_garble K a i) dev
  | inr dev =>
      exact congrFun (M.pureDeviationSignalMatrix_garble K a j) dev

/-- Stochastic garbling cannot create pure individual full rank. Only
finiteness of the original signal carrier is required. -/
theorem PureIndividualFullRank.of_garble
    [Fintype ι] [DecidableEq ι]
    {M : G.mixedExtension.PublicMonitoring} [Finite M.Signal]
    {S : Type} (K : Math.Probability.Kernel M.Signal S)
    {a : Profile G} {who : ι}
    (h : (M.garble K).PureIndividualFullRank a who) :
    M.PureIndividualFullRank a who := by
  letI := Fintype.ofFinite M.Signal
  rw [PureIndividualFullRank, M.pureDeviationSignalMatrix_garble K] at h
  exact LinearIndependent.of_comp K.pushforwardLinearMap h

/-- Stochastic garbling cannot create pure pairwise full rank. Only
finiteness of the original signal carrier is required. -/
theorem PurePairwiseFullRank.of_garble
    [Fintype ι] [DecidableEq ι]
    {M : G.mixedExtension.PublicMonitoring} [Finite M.Signal]
    {S : Type} (K : Math.Probability.Kernel M.Signal S)
    {a : Profile G} {i j : ι}
    (h : (M.garble K).PurePairwiseFullRank a i j) :
    M.PurePairwiseFullRank a i j := by
  letI := Fintype.ofFinite M.Signal
  rw [PurePairwiseFullRank,
    M.purePairwiseDeviationSignalFamily_garble K] at h
  exact LinearIndependent.of_comp K.pushforwardLinearMap h

/-- If the garbled experiment retains pure individual rank for both players,
its pure pairwise identifiability implies identifiability before garbling. -/
theorem PurePairwiseIdentifiable.of_garble
    [Fintype ι] [DecidableEq ι]
    {M : G.mixedExtension.PublicMonitoring} [Finite M.Signal]
    {S : Type} (K : Math.Probability.Kernel M.Signal S)
    {a : Profile G} {i j : ι}
    (hi : (M.garble K).PureIndividualFullRank a i)
    (hj : (M.garble K).PureIndividualFullRank a j)
    (hident : (M.garble K).PurePairwiseIdentifiable a i j) :
    M.PurePairwiseIdentifiable a i j := by
  have hp' : (M.garble K).PurePairwiseFullRank a i j :=
    ((M.garble K).purePairwiseFullRank_iff a i j).2
      ⟨hi, hj, hident⟩
  exact (M.purePairwiseFullRank_iff a i j).1 hp'.of_garble |>.2.2

/-- Stochastic garbling cannot increase numerical pure individual deviation
rank when both signal carriers and the pure-deviation family are finite. -/
theorem pureIndividualDeviationRank_garble_le
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Finite M.Signal]
    {S : Type} [Finite S] (K : Math.Probability.Kernel M.Signal S)
    (a : Profile G) (who : ι)
    [Finite (NontrivialDeviation a who)] :
    (M.garble K).pureIndividualDeviationRank a who ≤
      M.pureIndividualDeviationRank a who := by
  letI := Fintype.ofFinite M.Signal
  letI := Fintype.ofFinite S
  rw [pureIndividualDeviationRank, pureIndividualDeviationRank,
    Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row,
    M.pureDeviationSignalMatrix_garble K]
  change Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range
          (K.pushforwardLinearMap ∘ M.pureDeviationSignalMatrix a who))) ≤
    Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range (M.pureDeviationSignalMatrix a who)))
  rw [Set.range_comp, ← LinearMap.map_span]
  exact Submodule.finrank_map_le K.pushforwardLinearMap
    (Submodule.span ℝ (Set.range (M.pureDeviationSignalMatrix a who)))

/-- Stochastic garbling cannot increase numerical pure pairwise deviation
rank when both signal carriers and the pure-deviation families are finite. -/
theorem purePairwiseDeviationRank_garble_le
    [Fintype ι] [DecidableEq ι]
    (M : G.mixedExtension.PublicMonitoring) [Finite M.Signal]
    {S : Type} [Finite S] (K : Math.Probability.Kernel M.Signal S)
    (a : Profile G) (i j : ι)
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)] :
    (M.garble K).purePairwiseDeviationRank a i j ≤
      M.purePairwiseDeviationRank a i j := by
  letI := Fintype.ofFinite M.Signal
  letI := Fintype.ofFinite S
  rw [purePairwiseDeviationRank, purePairwiseDeviationRank,
    Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row,
    M.purePairwiseDeviationSignalFamily_garble K]
  change Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range
          (K.pushforwardLinearMap ∘
            M.purePairwiseDeviationSignalFamily a i j))) ≤
    Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range (M.purePairwiseDeviationSignalFamily a i j)))
  rw [Set.range_comp, ← LinearMap.map_span]
  exact Submodule.finrank_map_le K.pushforwardLinearMap
    (Submodule.span ℝ
      (Set.range (M.purePairwiseDeviationSignalFamily a i j)))

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

/-- Realized-action monitoring separates the pure-deviation subspaces of
distinct players. -/
theorem purePairwiseIdentifiable_realizedActionMonitoring
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    (a : Profile G) {i j : ι} (hij : i ≠ j) :
    G.realizedActionMonitoring.PurePairwiseIdentifiable a i j :=
  (G.realizedActionMonitoring.purePairwiseFullRank_iff a i j).1
    (purePairwiseFullRank_realizedActionMonitoring G a hij) |>.2.2

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
