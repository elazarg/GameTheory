/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Projective.SignedProjectiveLasso

/-!
# Rotation-uniform absolute-weighted projective lassos

The absolute-weighted condition bounds

`weightedResidual phase who ≤ error * weightedAbsorption`

for every cyclic entry phase and player.  Requiring every rotation remains
load-bearing: a large seam may be hidden behind a zero-survival prefix in one
orientation and exposed from another entry phase.

This is a strong, convenient compatibility certificate.  The compiler base is
`QuittingFiniteSignedProjectiveLasso`: the triangle inequality converts every
absolute-weighted lasso to a signed lasso, and the weighted compiler theorems
below are wrappers through that conversion.  For a fixed candidate, the
absolute condition can be strictly stronger because it discards within-turn
cancellation.  At the all-accuracy existential level, both interfaces remain
equivalent to exact finite support-rational-cycle production.

The older pointwise structure `QuittingFiniteChargedProjectiveLasso` is
stronger again.  Its `toWeighted` adapter is retained unchanged.
-/

noncomputable section

namespace GameTheory

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The rotation-uniform survival-weighted absolute seam condition. -/
def IsQuittingRotationUniformWeightedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (error : ℝ) : Prop :=
  ∀ phase who,
    quittingCyclicWeightedResidual reward cycle value phase who ≤
      error * quittingCyclicWeightedAbsorption cycle

/-- Finite absolute-weighted projective-lasso certificate.  It is a stronger
compatibility surface for the signed compiler. -/
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

/-- Every absolute-weighted lasso is a signed lasso. -/
def toSigned
    (lasso : QuittingFiniteWeightedProjectiveLasso reward K error) :
    QuittingFiniteSignedProjectiveLasso reward K error where
  cycle := lasso.cycle
  value := lasso.value
  error_nonneg := lasso.error_nonneg
  signedResidual_bound := by
    intro phase who
    exact
      (abs_quittingCyclicSignedResidual_le_weightedResidual
        reward lasso.cycle lasso.value phase who).trans
        (lasso.weightedResidual_bound phase who)
  support := lasso.support
  rational := lasso.rational
  absorbingPhase := lasso.absorbingPhase
  absorbing := lasso.absorbing

/-- Exact periodic continuation selected by the weighted lasso's root word. -/
def exactValue
    (lasso : QuittingFiniteWeightedProjectiveLasso reward K error) :
    Fin K → Payoff ι :=
  quittingCyclicTerminalValue reward lasso.cycle

/-- The absolute-weighted correction theorem is the signed correction theorem
applied after `toSigned`. -/
theorem abs_value_sub_exactValue_le
    (lasso : QuittingFiniteWeightedProjectiveLasso reward K error)
    (phase : Fin K) (who : ι) :
    |lasso.value phase who - exactValue lasso phase who| ≤ error := by
  simpa only [exactValue, QuittingFiniteSignedProjectiveLasso.exactValue,
    toSigned] using
    QuittingFiniteSignedProjectiveLasso.abs_value_sub_exactValue_le
      lasso.toSigned phase who

/-- Replacing the displayed values by actual periodic values yields an exact
finite support-rational cycle at twice the weighted-lasso error. -/
theorem toFiniteSupportRationalCycle
    (lasso : QuittingFiniteWeightedProjectiveLasso reward K error) :
    IsQuittingFiniteSupportRationalCycle reward lasso.cycle
      (exactValue lasso) (2 * error) (2 * error) := by
  simpa only [exactValue, QuittingFiniteSignedProjectiveLasso.exactValue,
    toSigned] using
    QuittingFiniteSignedProjectiveLasso.toFiniteSupportRationalCycle
      lasso.toSigned

/-- A weighted projective lasso produces the divergent support-rational path
through its signed image. -/
theorem exists_supportRationalDivergentPath
    (lasso : QuittingFiniteWeightedProjectiveLasso reward K error) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan (2 * error) ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      ∀ target time,
        quittingPunishmentValue reward target - 2 * error ≤
          quittingRootSequenceTerminalValue reward plan target time := by
  simpa only [toSigned] using
    QuittingFiniteSignedProjectiveLasso.exists_supportRationalDivergentPath
      lasso.toSigned

end QuittingFiniteWeightedProjectiveLasso

namespace QuittingFiniteChargedProjectiveLasso

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℝ}

/-- A pointwise charged lasso is, in particular, an absolute-weighted lasso. -/
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

/-- Absolute-weighted lassos at every positive accuracy imply a uniform payoff
through the signed compiler. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_weightedProjectiveLassos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        Nonempty (QuittingFiniteWeightedProjectiveLasso reward K error)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_signedProjectiveLassos
    reward
  intro error herror
  obtain ⟨K, ⟨lasso⟩⟩ := hproducer error herror
  exact ⟨K, ⟨lasso.toSigned⟩⟩

/-- The pointwise producer interface factors through the absolute-weighted and
then signed compatibility adapters. -/
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
