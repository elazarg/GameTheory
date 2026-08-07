/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingWeightedProjectiveLasso

/-!
# Cancellation-aware signed projective lassos

Exact cyclic policy evaluation only sees the **signed monodromy** of the local
Bellman seams.  For every entry phase and player, the exact identity proved in
`QuittingProjectiveLassoWeighted` is

`weightedAbsorption * (value - exactValue) = signedResidual`.

Consequently, the rotation-uniform condition

`|signedResidual phase who| ≤ error * weightedAbsorption`

is sufficient for periodic correction.  It is strictly weaker than bounding
the survival-weighted sum of the absolute seams: oscillating local errors may
cancel over one turn.  Rotation-uniformity remains essential; cancellation is
allowed within each rotated turn, not across different entry phases.

This file exposes that weakest exact finite compiler interface.  The existing
`QuittingFiniteWeightedProjectiveLasso` remains available and embeds into the
signed interface by the triangle inequality.
-/

noncomputable section

namespace GameTheory

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The cancellation-aware relative-return condition: every rotated signed
Bellman monodromy is small relative to one-turn real absorption. -/
def IsQuittingRotationUniformSignedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (error : ℝ) : Prop :=
  ∀ phase who,
    |quittingCyclicSignedResidual reward cycle value phase who| ≤
      error * quittingCyclicWeightedAbsorption cycle

/-- Finite cancellation-aware projective-lasso certificate.  Its strategic
fields coincide with the absolute weighted certificate; only the seam
hypothesis is weakened from total variation to signed monodromy. -/
structure QuittingFiniteSignedProjectiveLasso
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : ℕ) (error : ℝ) where
  cycle : Fin K → ι → PMF Bool
  value : Fin K → Payoff ι
  error_nonneg : 0 ≤ error
  signedResidual_bound :
    IsQuittingRotationUniformSignedResidual reward cycle value error
  support : ∀ phase,
    IsQuittingRootSupportApproxNash reward
      (value (finRotate K phase)) error (cycle phase)
  rational : ∀ target phase,
    quittingPunishmentValue reward target - error ≤ value phase target
  absorbingPhase : Fin K
  absorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase)

namespace QuittingFiniteSignedProjectiveLasso

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℝ}

/-- Exact periodic continuation selected by the signed lasso's root word. -/
def exactValue
    (lasso : QuittingFiniteSignedProjectiveLasso reward K error) :
    Fin K → Payoff ι :=
  quittingCyclicTerminalValue reward lasso.cycle

/-- Signed monodromy correction costs at most the lasso error at every phase
and coordinate. -/
theorem abs_value_sub_exactValue_le
    (lasso : QuittingFiniteSignedProjectiveLasso reward K error)
    (phase : Fin K) (who : ι) :
    |lasso.value phase who - exactValue lasso phase who| ≤ error := by
  exact abs_quittingCyclicValue_sub_terminalValue_le_of_signedResidual
    reward lasso.cycle lasso.value lasso.signedResidual_bound
      (quittingCyclicWeightedAbsorption_pos_of_absorbingPhase
        lasso.cycle lasso.absorbingPhase lasso.absorbing)
      phase who

/-- **Signed projective-lasso correction.**  Replacing the displayed values by
actual periodic values yields an exact finite support-rational cycle at twice
the signed-lasso error. -/
theorem toFiniteSupportRationalCycle
    (lasso : QuittingFiniteSignedProjectiveLasso reward K error) :
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

/-- A signed projective lasso produces the divergent support-rational path
consumed by the support-witness compiler. -/
theorem exists_supportRationalDivergentPath
    (lasso : QuittingFiniteSignedProjectiveLasso reward K error) :
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

end QuittingFiniteSignedProjectiveLasso

namespace QuittingFiniteWeightedProjectiveLasso

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℝ}

/-- Every absolute weighted lasso is a signed lasso.  This is the compatibility
embedding from the previous compiler interface into the cancellation-aware
one. -/
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

end QuittingFiniteWeightedProjectiveLasso

/-- **Cancellation-aware uniform-payoff interface.**  Rotation-uniform signed
projective lassos at every positive accuracy imply a uniform-equilibrium
payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_signedProjectiveLassos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        Nonempty (QuittingFiniteSignedProjectiveLasso reward K error)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths
    reward
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨K, ⟨lasso⟩⟩ := hproducer (δ / 2) hhalf
  obtain ⟨plan, hsupport, hdiverges, hir⟩ :=
    QuittingFiniteSignedProjectiveLasso.exists_supportRationalDivergentPath
      lasso
  have htwo : (2 : ℝ) * (δ / 2) = δ := by ring
  rw [htwo] at hsupport hir
  exact ⟨plan, hsupport, hdiverges, hir⟩

end GameTheory
