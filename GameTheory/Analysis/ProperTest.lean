module

/-
# Proper equilibrium with genuine mixing and infinite outcome laws

The full-support Matching Pennies equilibrium witnesses properness without a
pure equilibrium. Finite existence also accepts the established game with
infinite-support outcomes and unbounded integrable utility.
-/

public import GameTheory.Analysis.ProperExistence
public import GameTheory.Analysis.TremblingHandTest
public import GameTheory.Analysis.PMFExistenceTest

@[expose] public section

noncomputable section

namespace GameTheory.Analysis.ProperTest

open GameTheory GameTheory.Math.Probability GameTheory.Examples

private theorem pennies_integrable :
    matchingPennies.toForm.HasIntegrableUtility matchingPennies.utility := by
  intro who profile
  exact payoffIntegrable_of_finite _ _

theorem fairPennies_isProper :
    matchingPennies.toForm.IsProper matchingPennies.utility fairPennies := by
  exact fairPennies_isNash.isProper_of_fullSupport matchingPennies.toForm
    TremblingHandTest.fairPennies_fullSupport
    (fun who => pennies_integrable.mixed_of_finite who fairPennies)

/-- Properness is witnessed at an actually mixed equilibrium, in a game that
has no pure equilibrium. -/
theorem proper_without_pure_equilibrium :
    matchingPennies.toForm.IsProper matchingPennies.utility fairPennies ∧
      ∀ profile, ¬ IsNash matchingPennies.toForm
        (euPreference matchingPennies.utility) profile :=
  ⟨fairPennies_isProper, matchingPennies_noPureNash⟩

/-- Existence and the canonical Nash bridge keep the infinite-support play
law and unbounded utility of the original consumer. -/
theorem infiniteLaw_proper_and_nash :
    ∃ profile : Profile PMFExistenceTest.infiniteOutcomeForm.sig.mixed,
      PMFExistenceTest.infiniteOutcomeForm.IsProper PMFExistenceTest.infiniteLinearUtility profile ∧
      IsNash PMFExistenceTest.infiniteOutcomeForm.mixed
        (euPreference PMFExistenceTest.infiniteLinearUtility) profile := by
  obtain ⟨profile, proper⟩ := PMFExistenceTest.infiniteOutcomeForm.exists_isProper
    PMFExistenceTest.infiniteLinearUtility PMFExistenceTest.pure_integrable
  exact ⟨profile, proper,
    proper.isNash PMFExistenceTest.infiniteOutcomeForm PMFExistenceTest.pure_integrable⟩

/-- An infinite expected payoff cannot be silently treated as a finite real
score, even when there is only one action and no profitable Nash deviation. -/
theorem nonintegrable_utility_not_proper
    (profile : Profile Experimental.PMFStaticGate.singletonForm.sig.mixed) :
    ¬ Experimental.PMFStaticGate.singletonForm.IsProper
      Experimental.PMFStaticGate.explodingUtility profile := by
  rintro ⟨epsilon, approximating, proper, _, _⟩
  have integrable := (proper 0).2.2.1 0 ()
  apply Experimental.PMFStaticGate.explodingUtility_not_integrable
  simpa only [GameForm.mixed_play, Experimental.PMFStaticGate.singletonForm,
    PMF.bind_const] using integrable

end GameTheory.Analysis.ProperTest
