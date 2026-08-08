/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Projective.LassoWeighted

/-!
# Cancellation-aware signed projective lassos

Exact cyclic policy evaluation only sees the **signed monodromy** of the local
Bellman seams.  For every entry phase and player,

`weightedAbsorption * (value - exactValue) = signedResidual`.

Under positive weighted absorption, the rotation-uniform signed condition is
therefore exactly equivalent to uniform closeness of the displayed values to
the true periodic values.  For a fixed candidate `(cycle, value)` it is a
strictly weaker acceptance test than bounding the survival-weighted sum of the
absolute seams, because local errors may cancel within a turn.  Rotation
uniformity remains essential: cancellation is allowed inside each rotated
turn, not across entry phases.

This does **not** weaken the all-accuracy existential producer problem.  Exact
finite support-rational cycles package back into signed lassos with zero seam,
while signed lassos correct to exact cycles after rescaling the tolerance.  The
all-accuracy producer hypotheses are therefore equivalent; the signed API is a
sharper intermediate certificate for an upstream analytic or geometric
construction.
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

omit [DecidableEq ι] in
/-- **Exact signed-correction characterization.**  Under positive aggregate
absorption, the rotation-uniform signed predicate is equivalent to uniform
coordinatewise closeness to the true periodic values. -/
theorem isQuittingRotationUniformSignedResidual_iff_value_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (error : ℝ)
    (habsorption : 0 < quittingCyclicWeightedAbsorption cycle) :
    IsQuittingRotationUniformSignedResidual reward cycle value error ↔
      ∀ phase who,
        |value phase who -
          quittingCyclicTerminalValue reward cycle phase who| ≤ error := by
  constructor
  · intro hsigned phase who
    exact
      (abs_quittingCyclicSignedResidual_le_iff_value_close
        reward cycle value habsorption phase who).mp
        (hsigned phase who)
  · intro hclose phase who
    exact
      (abs_quittingCyclicSignedResidual_le_iff_value_close
        reward cycle value habsorption phase who).mpr
        (hclose phase who)

/-- Finite cancellation-aware projective-lasso certificate.  Its strategic
fields match the older weighted certificate; its seam field uses the exact
signed correction coordinate. -/
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
  exact
    (isQuittingRotationUniformSignedResidual_iff_value_close
      reward lasso.cycle lasso.value error
      (quittingCyclicWeightedAbsorption_pos_of_absorbingPhase
        lasso.cycle lasso.absorbingPhase lasso.absorbing)).mp
      lasso.signedResidual_bound phase who

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

/-- An exact finite support-rational cycle is a signed lasso with zero Bellman
seam.  This is the reverse adapter showing that the signed certificate does not
weaken the existential all-accuracy producer problem. -/
def ofFiniteSupportRationalCycle
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (herror : 0 ≤ error)
    (hcycle : IsQuittingFiniteSupportRationalCycle
      reward cycle value error error)
    (absorbingPhase : Fin K)
    (habsorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase)) :
    QuittingFiniteSignedProjectiveLasso reward K error where
  cycle := cycle
  value := value
  error_nonneg := herror
  signedResidual_bound := by
    have hcontract :
        (∏ phase : Fin K,
          quittingStationaryContinueMass (cycle phase)) < 1 :=
      prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
        cycle absorbingPhase habsorbing
    have hselected :
        value = quittingCyclicTerminalValue reward cycle :=
      eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
        reward cycle value hcycle.1 hcontract
    apply
      (isQuittingRotationUniformSignedResidual_iff_value_close
        reward cycle value error
        (quittingCyclicWeightedAbsorption_pos_of_absorbingPhase
          cycle absorbingPhase habsorbing)).mpr
    intro phase who
    rw [hselected, sub_self, abs_zero]
    exact herror
  support := hcycle.2.1
  rational := hcycle.2.2
  absorbingPhase := absorbingPhase
  absorbing := habsorbing

end QuittingFiniteSignedProjectiveLasso

/-- **All-accuracy equivalence.**  Signed lassos exist at every positive
accuracy iff exact finite support-rational cycles do.  The forward direction
uses signed correction at half the requested error; the reverse direction is
the zero-seam adapter above. -/
theorem
    quittingSignedProjectiveLassos_all_errors_iff_finiteSupportRationalCycles
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        Nonempty (QuittingFiniteSignedProjectiveLasso reward K error)) ↔
    (∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        ∃ cycle : Fin K → ι → PMF Bool,
          ∃ value : Fin K → Payoff ι,
            ∃ absorbingPhase : Fin K,
              IsQuittingFiniteSupportRationalCycle
                  reward cycle value error error ∧
                0 < quittingRootAbsorptionMass
                  (cycle absorbingPhase)) := by
  constructor
  · intro hsigned error herror
    have hhalf : 0 < error / 2 := by linarith
    obtain ⟨K, ⟨lasso⟩⟩ := hsigned (error / 2) hhalf
    refine ⟨K, lasso.cycle, lasso.exactValue, lasso.absorbingPhase, ?_,
      lasso.absorbing⟩
    have hcycle := lasso.toFiniteSupportRationalCycle
    have htwo : (2 : ℝ) * (error / 2) = error := by ring
    simpa only [htwo] using hcycle
  · intro hcycles error herror
    obtain ⟨K, cycle, value, absorbingPhase, hcycle, habsorbing⟩ :=
      hcycles error herror
    exact ⟨K, ⟨
      QuittingFiniteSignedProjectiveLasso.ofFiniteSupportRationalCycle
        cycle value (le_of_lt herror) hcycle absorbingPhase habsorbing⟩⟩

/-- Signed projective lassos at every positive accuracy imply a
uniform-equilibrium payoff.  By the preceding theorem, this is the established
finite-cycle producer theorem expressed through the sharper fixed-candidate
certificate. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_signedProjectiveLassos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        Nonempty (QuittingFiniteSignedProjectiveLasso reward K error)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteSupportRationalCycles
    reward
  exact
    (quittingSignedProjectiveLassos_all_errors_iff_finiteSupportRationalCycles
      reward).mp hproducer

end GameTheory
