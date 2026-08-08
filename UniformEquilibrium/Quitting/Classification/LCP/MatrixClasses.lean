/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.Normalization

/-!
# Standard, projective, and completely projective Q-matrices

The relevant quitting-game papers define `Q-matrix` using a normalized
simplex/projective LCP, while also comparing it with the textbook
nonhomogeneous LCP whose coefficient of `q` is fixed to one.  The conventions
are not equivalent in general.

This file defines both and proves the exact split recorded in AGKRS Remark
5.5(3):

`projective Q M ↔ standard Q M ∨ homogeneous simplex solution M`.

It also proves that Solan--Solan's "nontrivial solution of LCP(M, 0)" branch is
exactly the homogeneous simplex branch.  Thus the two Q conventions coincide
precisely after the simple stationary branch has been removed.
`IsProjectiveQBarMatrix` applies the projective notion to every nonempty
principal submatrix, exactly as in AGKRS Definition 5.2.  No strategic
conclusion is attached to any matrix predicate here.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Finset
open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A solution of the textbook nonhomogeneous LCP `w = q + Mz`. -/
structure StandardLCPSolution (M : ι → ι → ℝ) (q : ι → ℝ) where
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  residual_nonneg : ∀ i,
    0 ≤ q i + ∑ j, weight j * M i j
  complementary : ∀ i,
    weight i * (q i + ∑ j, weight j * M i j) = 0

/-- The standard LCP is solvable for this right-hand side. -/
def HasStandardLCPSolution (M : ι → ι → ℝ) (q : ι → ℝ) : Prop :=
  Nonempty (StandardLCPSolution M q)

/-- Textbook `Q`: the standard LCP is solvable for every vector `q`. -/
def IsStandardQMatrix (M : ι → ι → ℝ) : Prop :=
  ∀ q : ι → ℝ, HasStandardLCPSolution M q

/-- A solution of the normalized simplex/projective LCP
`w = z₀ q + Mz`, with `z₀ + ∑ zᵢ = 1`. -/
structure ProjectiveLCPSolution (M : ι → ι → ℝ) (q : ι → ℝ) where
  cemetery : ℝ
  singleton : ι → ℝ
  cemetery_nonneg : 0 ≤ cemetery
  singleton_nonneg : ∀ i, 0 ≤ singleton i
  total : cemetery + ∑ i, singleton i = 1
  residual_nonneg : ∀ i,
    0 ≤ cemetery * q i + ∑ j, singleton j * M i j
  complementary : ∀ i,
    singleton i * (cemetery * q i + ∑ j, singleton j * M i j) = 0

/-- The existing anchored projective packet is a solution of the explicit
projective LCP for its affine anchor direction and the normalized singleton
matrix.  This is the adapter from the repository algebra to the literature
normalization. -/
def anchoredPacketToProjectiveLCPSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingAnchoredProjectiveSingletonPacket reward) :
    ProjectiveLCPSolution (normalizedSoloMatrix reward)
      (fun who =>
        quittingAnchoredProjectiveLCPDirection reward packet.anchor who) := by
  classical
  refine
    { cemetery := packet.cemetery
      singleton := packet.singleton
      cemetery_nonneg := packet.cemetery_nonneg
      singleton_nonneg := packet.singleton_nonneg
      total := packet.total
      residual_nonneg := ?_
      complementary := ?_ }
  · intro who
    change 0 ≤ packet.cemetery *
        quittingAnchoredProjectiveLCPDirection reward packet.anchor who +
      ∑ owner, packet.singleton owner *
        quittingProjectiveLCPMatrix reward who owner
    rw [← quittingAnchoredProjectiveSingletonPacket_balance reward packet who]
    exact quittingAnchoredProjectiveSingletonPacket_slack_nonneg reward packet who
  · intro who
    change packet.singleton who *
      (packet.cemetery *
          quittingAnchoredProjectiveLCPDirection reward packet.anchor who +
        ∑ owner, packet.singleton owner *
          quittingProjectiveLCPMatrix reward who owner) = 0
    rw [← quittingAnchoredProjectiveSingletonPacket_balance reward packet who]
    exact quittingAnchoredProjectiveSingletonPacket_complementary reward packet who

/-- The zero-anchor projective packet specializes to a solution whose `q` is
the translated never payoff. -/
def singletonPacketToNormalizedProjectiveLCPSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingProjectiveSingletonPacket reward) :
    ProjectiveLCPSolution (normalizedSoloMatrix reward)
      (normalizedQuittingPayoffTable reward).never := by
  have hq : (normalizedQuittingPayoffTable reward).never =
      fun who => quittingAnchoredProjectiveLCPDirection reward 0 who := by
    funext who
    exact normalized_never_eq_zeroAnchorDirection reward who
  rw [hq]
  exact anchoredPacketToProjectiveLCPSolution reward packet.toAnchored

/-- The normalized projective LCP is solvable for this `q`. -/
def HasProjectiveLCPSolution (M : ι → ι → ℝ) (q : ι → ℝ) : Prop :=
  Nonempty (ProjectiveLCPSolution M q)

/-- The quitting-game papers' simplex/projective `Q` convention. -/
def IsProjectiveQMatrix (M : ι → ι → ℝ) : Prop :=
  ∀ q : ι → ℝ, HasProjectiveLCPSolution M q

/-- The homogeneous branch retained by a zero-cemetery projective solution.
This is exactly the repository's existing normalized singleton LCP. -/
abbrev HasHomogeneousSimplexSolution (M : ι → ι → ℝ) : Prop :=
  SingletonLCPFeasible M

/-- Solan--Solan's nontrivial zero-right-hand-side projective LCP branch:
not all normalized mass is assigned to the artificial `q` coordinate. -/
def HasNontrivialZeroProjectiveLCPSolution
    (M : ι → ι → ℝ) : Prop :=
  ∃ solution : ProjectiveLCPSolution M (0 : ι → ℝ),
    solution.cemetery < 1

private theorem sum_weight_nonneg
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ ∑ i, weight i :=
  Finset.sum_nonneg fun i _ => hweight i

/-- Normalize a standard LCP solution into a projective one with positive
cemetery coefficient. -/
def StandardLCPSolution.toProjective
    {M : ι → ι → ℝ} {q : ι → ℝ}
    (solution : StandardLCPSolution M q) : ProjectiveLCPSolution M q := by
  classical
  let mass : ℝ := 1 + ∑ i, solution.weight i
  have hsum : 0 ≤ ∑ i, solution.weight i :=
    sum_weight_nonneg solution.weight solution.weight_nonneg
  have hmass : 0 < mass := by
    dsimp [mass]
    linarith
  have hmass0 : mass ≠ 0 := ne_of_gt hmass
  refine
    { cemetery := mass⁻¹
      singleton := fun i => solution.weight i * mass⁻¹
      cemetery_nonneg := inv_nonneg.mpr hmass.le
      singleton_nonneg := fun i =>
        mul_nonneg (solution.weight_nonneg i) (inv_nonneg.mpr hmass.le)
      total := ?_
      residual_nonneg := ?_
      complementary := ?_ }
  · rw [← Finset.sum_mul]
    calc
      mass⁻¹ + (∑ i, solution.weight i) * mass⁻¹ =
          (1 + ∑ i, solution.weight i) * mass⁻¹ := by ring
      _ = mass * mass⁻¹ := by rfl
      _ = 1 := mul_inv_cancel₀ hmass0
  · intro i
    have heq :
        mass⁻¹ * q i +
            ∑ j, (solution.weight j * mass⁻¹) * M i j =
          mass⁻¹ * (q i + ∑ j, solution.weight j * M i j) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg (fun x => mass⁻¹ * q i + x)
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq]
    exact mul_nonneg (inv_nonneg.mpr hmass.le)
      (solution.residual_nonneg i)
  · intro i
    have heq :
        mass⁻¹ * q i +
            ∑ j, (solution.weight j * mass⁻¹) * M i j =
          mass⁻¹ * (q i + ∑ j, solution.weight j * M i j) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg (fun x => mass⁻¹ * q i + x)
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq]
    calc
      (solution.weight i * mass⁻¹) *
          (mass⁻¹ * (q i + ∑ j, solution.weight j * M i j)) =
          mass⁻¹ ^ 2 *
            (solution.weight i *
              (q i + ∑ j, solution.weight j * M i j)) := by ring
      _ = 0 := by rw [solution.complementary i, mul_zero]

/-- A homogeneous simplex solution solves every projective LCP by setting the
cemetery coefficient to zero. -/
def projectiveLCPSolutionOfHomogeneous
    {M : ι → ι → ℝ} (homogeneous : HasHomogeneousSimplexSolution M)
    (q : ι → ℝ) : ProjectiveLCPSolution M q := by
  classical
  obtain ⟨weight, hresidual, hcomplementary⟩ := homogeneous
  refine
    { cemetery := 0
      singleton := weight.val
      cemetery_nonneg := le_rfl
      singleton_nonneg := weight.property.1
      total := by simpa using weight.property.2
      residual_nonneg := ?_
      complementary := ?_ }
  · intro i
    simpa [singletonLCPResidual, wsum, dotProduct] using hresidual i
  · intro i
    simpa [singletonLCPResidual, wsum, dotProduct] using hcomplementary i

/-- **Exact zero-right-hand-side split.**  A projective solution of `LCP(M,0)`
with `z₀ < 1` exists exactly when the homogeneous simplex LCP is feasible. -/
theorem hasNontrivialZeroProjectiveLCPSolution_iff_homogeneous
    (M : ι → ι → ℝ) :
    HasNontrivialZeroProjectiveLCPSolution M ↔
      HasHomogeneousSimplexSolution M := by
  constructor
  · rintro ⟨solution, hnontrivial⟩
    classical
    let mass : ℝ := ∑ i, solution.singleton i
    have hmass : 0 < mass := by
      dsimp [mass]
      linarith [solution.total]
    have hmass0 : mass ≠ 0 := ne_of_gt hmass
    let weight : stdSimplex ℝ ι :=
      ⟨fun i => solution.singleton i * mass⁻¹,
        fun i => mul_nonneg (solution.singleton_nonneg i)
          (inv_nonneg.mpr hmass.le), by
        rw [← Finset.sum_mul]
        exact mul_inv_cancel₀ hmass0⟩
    refine ⟨weight, ?_, ?_⟩
    · intro i
      have horiginal : 0 ≤ ∑ j, solution.singleton j * M i j := by
        simpa using solution.residual_nonneg i
      have heq :
          singletonLCPResidual M weight i =
            mass⁻¹ * (∑ j, solution.singleton j * M i j) := by
        change (∑ j, (solution.singleton j * mass⁻¹) * M i j) = _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq]
      exact mul_nonneg (inv_nonneg.mpr hmass.le) horiginal
    · intro i
      have horiginal :
          solution.singleton i *
            (∑ j, solution.singleton j * M i j) = 0 := by
        simpa using solution.complementary i
      have heq :
          singletonLCPResidual M weight i =
            mass⁻¹ * (∑ j, solution.singleton j * M i j) := by
        change (∑ j, (solution.singleton j * mass⁻¹) * M i j) = _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq]
      change (solution.singleton i * mass⁻¹) *
        (mass⁻¹ * ∑ j, solution.singleton j * M i j) = 0
      calc
        (solution.singleton i * mass⁻¹) *
            (mass⁻¹ * ∑ j, solution.singleton j * M i j) =
            mass⁻¹ ^ 2 *
              (solution.singleton i *
                ∑ j, solution.singleton j * M i j) := by ring
        _ = 0 := by rw [horiginal, mul_zero]
  · intro homogeneous
    refine ⟨projectiveLCPSolutionOfHomogeneous homogeneous
      (0 : ι → ℝ), ?_⟩
    change (0 : ℝ) < 1
    norm_num

/-- Every projective solution either has positive cemetery coefficient and
rescales to a standard solution, or has zero cemetery coefficient and is the
homogeneous simplex branch. -/
theorem ProjectiveLCPSolution.standard_or_homogeneous
    {M : ι → ι → ℝ} {q : ι → ℝ}
    (solution : ProjectiveLCPSolution M q) :
    HasStandardLCPSolution M q ∨ HasHomogeneousSimplexSolution M := by
  classical
  by_cases hzero : solution.cemetery = 0
  · right
    let weight : stdSimplex ℝ ι :=
      ⟨solution.singleton, solution.singleton_nonneg, by
        linarith [solution.total]⟩
    refine ⟨weight, ?_, ?_⟩
    · intro i
      have h := solution.residual_nonneg i
      simpa [hzero, weight, singletonLCPResidual, wsum, dotProduct] using h
    · intro i
      have h := solution.complementary i
      simpa [hzero, weight, singletonLCPResidual, wsum, dotProduct] using h
  · left
    have hpos : 0 < solution.cemetery :=
      lt_of_le_of_ne solution.cemetery_nonneg (Ne.symm hzero)
    have hinv : 0 ≤ solution.cemetery⁻¹ := inv_nonneg.mpr hpos.le
    refine ⟨
      { weight := fun i => solution.singleton i * solution.cemetery⁻¹
        weight_nonneg := fun i =>
          mul_nonneg (solution.singleton_nonneg i) hinv
        residual_nonneg := ?_
        complementary := ?_ }⟩
    · intro i
      have heq :
          q i + ∑ j,
              (solution.singleton j * solution.cemetery⁻¹) * M i j =
            solution.cemetery⁻¹ *
              (solution.cemetery * q i +
                ∑ j, solution.singleton j * M i j) := by
        rw [mul_add, Finset.mul_sum]
        have hfirst :
            solution.cemetery⁻¹ * (solution.cemetery * q i) = q i := by
          rw [← mul_assoc, inv_mul_cancel₀ hzero, one_mul]
        rw [hfirst]
        apply congrArg (fun x => q i + x)
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq]
      exact mul_nonneg hinv (solution.residual_nonneg i)
    · intro i
      have heq :
          q i + ∑ j,
              (solution.singleton j * solution.cemetery⁻¹) * M i j =
            solution.cemetery⁻¹ *
              (solution.cemetery * q i +
                ∑ j, solution.singleton j * M i j) := by
        rw [mul_add, Finset.mul_sum]
        have hfirst :
            solution.cemetery⁻¹ * (solution.cemetery * q i) = q i := by
          rw [← mul_assoc, inv_mul_cancel₀ hzero, one_mul]
        rw [hfirst]
        apply congrArg (fun x => q i + x)
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq]
      calc
        (solution.singleton i * solution.cemetery⁻¹) *
            (solution.cemetery⁻¹ *
              (solution.cemetery * q i +
                ∑ j, solution.singleton j * M i j)) =
            solution.cemetery⁻¹ ^ 2 *
              (solution.singleton i *
                (solution.cemetery * q i +
                  ∑ j, solution.singleton j * M i j)) := by ring
        _ = 0 := by rw [solution.complementary i, mul_zero]

/-- **Exact convention split.**  The simplex/projective `Q` convention equals
the union of textbook `Q` and the homogeneous singleton-LCP branch. -/
theorem isProjectiveQMatrix_iff_standard_or_homogeneous
    (M : ι → ι → ℝ) :
    IsProjectiveQMatrix M ↔
      IsStandardQMatrix M ∨ HasHomogeneousSimplexSolution M := by
  constructor
  · intro hprojective
    by_cases hhomogeneous : HasHomogeneousSimplexSolution M
    · exact Or.inr hhomogeneous
    · left
      intro q
      obtain ⟨solution⟩ := hprojective q
      rcases solution.standard_or_homogeneous with hstandard | hhom
      · exact hstandard
      · exact absurd hhom hhomogeneous
  · rintro (hstandard | hhomogeneous) q
    · obtain ⟨solution⟩ := hstandard q
      exact ⟨solution.toProjective⟩
    · exact ⟨projectiveLCPSolutionOfHomogeneous hhomogeneous q⟩

/-- Once the homogeneous/simple stationary branch is excluded, the two
`Q` conventions coincide. -/
theorem isProjectiveQMatrix_iff_standard_of_noHomogeneous
    (M : ι → ι → ℝ) (hhomogeneous : ¬HasHomogeneousSimplexSolution M) :
    IsProjectiveQMatrix M ↔ IsStandardQMatrix M := by
  rw [isProjectiveQMatrix_iff_standard_or_homogeneous]
  tauto

/-- Principal submatrix supported on a nonempty player set. -/
def principalMatrix (M : ι → ι → ℝ) (players : Finset ι) :
    players → players → ℝ :=
  fun i j => M i.1 j.1

/-- AGKRS Definition 5.2: projective `Q` on every nonempty principal
submatrix. -/
def IsProjectiveQBarMatrix (M : ι → ι → ℝ) : Prop :=
  ∀ players : Finset ι, players.Nonempty →
    IsProjectiveQMatrix (principalMatrix M players)

/-- The standard completely-Q property, kept distinct from AGKRS's weaker
projective `Q̄`. -/
def IsStandardCompletelyQMatrix (M : ι → ι → ℝ) : Prop :=
  ∀ players : Finset ι, players.Nonempty →
    IsStandardQMatrix (principalMatrix M players)

/-- Standard completely-Q implies projective Q-bar, but the converse can fail
through a homogeneous solution on a principal submatrix. -/
theorem isProjectiveQBarMatrix_of_standardCompletelyQ
    {M : ι → ι → ℝ} (hstandard : IsStandardCompletelyQMatrix M) :
    IsProjectiveQBarMatrix M := by
  intro players hplayers
  exact (isProjectiveQMatrix_iff_standard_or_homogeneous
    (principalMatrix M players)).2 (Or.inl (hstandard players hplayers))

end QuittingLCPClassification
end GameTheory
