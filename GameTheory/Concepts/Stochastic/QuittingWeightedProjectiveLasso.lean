/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingProjectiveLassoWeighted

/-!
# Rotation-uniform weighted projective lassos

The invariant relative-return condition is not a pointwise estimate at each
phase.  It is the survival-weighted cyclewise estimate

`weightedResidual phase who ≤ error * weightedAbsorption`

for **every cyclic entry phase** and every player.  Requiring every rotation is
load-bearing: a large seam may be hidden behind a zero-survival prefix in one
orientation and be exposed when the same word is entered immediately before
that seam.

This file makes the weighted condition the canonical compiler interface.
`QuittingFiniteWeightedProjectiveLasso` carries the rotation-uniform weighted
seam, support-local approximate optimality, individual rationality, and one
absorbing phase.  It compiles through exact periodic correction to the
repository's finite support-rational cycle, divergent path, and uniform-payoff
consumer.

The older pointwise structure `QuittingFiniteChargedProjectiveLasso` is a
strictly stronger certificate.  `QuittingFiniteChargedProjectiveLasso.toWeighted`
embeds it into the weighted interface using
`quittingCyclicWeightedResidual_le_of_pointwise`.
-/

noncomputable section

namespace GameTheory

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The rotation-uniform weighted seam condition consumed by exact periodic
correction. -/
def IsQuittingRotationUniformWeightedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (error : ℝ) : Prop :=
  ∀ phase who,
    quittingCyclicWeightedResidual reward cycle value phase who ≤
      error * quittingCyclicWeightedAbsorption cycle

/-- Canonical finite projective-lasso certificate.  Its seam condition is
cyclewise and uniform over all cyclic rotations. -/
structure QuittingFiniteWeightedProjectiveLasso
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : ℕ) (error : ℝ) where
  cycle : Fin K → ι → PMF Bool
  value : Fin K → Payoff ι
  error_nonneg : 0 ≤ error
  weightedResidual_bound :
    IsQuittingRotationUniformWeightedResidual reward cycle value error
  support : ∀ phase,
    IsQuittingRootSupportApproxNash reward
      (value (finRotate K phase)) error (cycle phase)
  rational : ∀ target phase,
    quittingPunishmentValue reward target - error ≤ value phase target
  absorbingPhase : Fin K
  absorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase)

namespace QuittingFiniteWeightedProjectiveLasso

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℝ}

/-- Exact periodic continuation selected by the weighted lasso's root word. -/
def exactValue
    (lasso : QuittingFiniteWeightedProjectiveLasso reward K error) :
    Fin K → Payoff ι :=
  quittingCyclicTerminalValue reward lasso.cycle

/-- The rotation-uniform weighted seam correction costs at most the lasso
error at every phase and coordinate. -/
theorem abs_value_sub_exactValue_le
    (lasso : QuittingFiniteWeightedProjectiveLasso reward K error)
    (phase : Fin K) (who : ι) :
    |lasso.value phase who - exactValue lasso phase who| ≤ error := by
  exact abs_quittingCyclicValue_sub_terminalValue_le_of_weightedResidual
    reward lasso.cycle lasso.value lasso.weightedResidual_bound
      lasso.absorbingPhase lasso.absorbing phase who

/-- **Weighted projective-lasso correction.**  Replacing the displayed values
by actual periodic values yields an exact finite support-rational cycle at
twice the weighted-lasso error. -/
theorem toFiniteSupportRationalCycle
    (lasso : QuittingFiniteWeightedProjectiveLasso reward K error) :
    IsQuittingFiniteSupportRationalCycle reward lasso.cycle
      (exactValue lasso) (2 * error) (2 * error) := by
  refine ⟨?_, ?_, ?_⟩
  · intro phase
    exact quittingCyclicTerminalValue_eq_rootSuccessorPayoff
      reward lasso.cycle phase
  · intro phase
    have htransfer := isQuittingRootSupportApproxNash_of_tail_close
      reward (lasso.cycle phase)
        (lasso.value (finRotate K phase))
        (exactValue lasso (finRotate K phase))
        (δ := error) (η := error)
        (lasso.support phase) (fun who => ?_)
    · simpa [two_mul] using htransfer
    · simpa [exactValue, abs_sub_comm] using
        abs_value_sub_exactValue_le lasso (finRotate K phase) who
  · intro target phase
    have hir := lasso.rational target phase
    have hclose := abs_value_sub_exactValue_le lasso phase target
    rw [abs_le] at hclose
    have hupper := hclose.2
    dsimp only [exactValue] at hupper ⊢
    linarith

/-- A weighted projective lasso produces the divergent support-rational path
consumed by the support-witness compiler. -/
theorem exists_supportRationalDivergentPath
    (lasso : QuittingFiniteWeightedProjectiveLasso reward K error) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan (2 * error) ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      ∀ target time,
        quittingPunishmentValue reward target - 2 * error ≤
          quittingRootSequenceTerminalValue reward plan target time := by
  exact exists_supportRationalDivergentPath_of_finiteSupportRationalCycle
    reward lasso.cycle (exactValue lasso)
      (toFiniteSupportRationalCycle lasso)
      lasso.absorbingPhase lasso.absorbing

end QuittingFiniteWeightedProjectiveLasso

namespace QuittingFiniteChargedProjectiveLasso

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℝ}

/-- A pointwise charged lasso is, in particular, a rotation-uniform weighted
lasso. -/
def toWeighted
    (lasso : QuittingFiniteChargedProjectiveLasso reward K error) :
    QuittingFiniteWeightedProjectiveLasso reward K error where
  cycle := lasso.cycle
  value := lasso.value
  error_nonneg := lasso.error_nonneg
  weightedResidual_bound := by
    intro phase who
    exact quittingCyclicWeightedResidual_le_of_pointwise
      reward lasso.cycle lasso.value lasso.residual_bound phase who
  support := lasso.support
  rational := lasso.rational
  absorbingPhase := lasso.absorbingPhase
  absorbing := lasso.absorbing

end QuittingFiniteChargedProjectiveLasso

/-- **Canonical weighted uniform-payoff interface.**  Rotation-uniform
weighted projective lassos at every positive accuracy imply a
uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_weightedProjectiveLassos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        Nonempty (QuittingFiniteWeightedProjectiveLasso reward K error)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths
    reward
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨K, ⟨lasso⟩⟩ := hproducer (δ / 2) hhalf
  obtain ⟨plan, hsupport, hdiverges, hir⟩ :=
    QuittingFiniteWeightedProjectiveLasso.exists_supportRationalDivergentPath
      lasso
  have htwo : (2 : ℝ) * (δ / 2) = δ := by ring
  rw [htwo] at hsupport hir
  exact ⟨plan, hsupport, hdiverges, hir⟩

/-- The older pointwise producer interface factors through the canonical
weighted interface. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_pointwiseProjectiveLassos_via_weighted
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        Nonempty (QuittingFiniteChargedProjectiveLasso reward K error)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_weightedProjectiveLassos
    reward
  intro error herror
  obtain ⟨K, ⟨lasso⟩⟩ := hproducer error herror
  exact ⟨K, ⟨lasso.toWeighted⟩⟩

end GameTheory
