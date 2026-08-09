/-
# Nondegenerate trembling-hand fixture

The fair Matching Pennies equilibrium has full support even though the game has
no pure Nash equilibrium.  It therefore exercises genuine mixed refinement,
not a point-mass or singleton shortcut.
-/

import GameTheory.Analysis.TremblingHand
import GameTheory.Examples.Classic
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Analysis.TremblingHandTest

open GameTheory GameTheory.Finite GameTheory.Probability GameTheory.Examples

/-- Both actions receive strictly positive probability at the fair profile. -/
theorem fairPennies_fullSupport (who : Fin 2) :
    (fairPennies who).FullSupport := by
  intro action
  rw [← FinDist.prob_pos_iff, TableGame.toMixed_prob]
  norm_num [uniformPennies]

/-- The fair mixed Nash profile carries an explicit positive, vanishing
perturbation certificate through the general theorem. -/
theorem fairPennies_isTremblingHandPerfect :
    matchingPennies.toForm.IsTremblingHandPerfect
      (euPreference matchingPennies.utility) fairPennies :=
  fairPennies_isNash.isTremblingHandPerfect_of_fullSupport
    matchingPennies.toForm fairPennies_fullSupport

/-- Nondegeneracy is visible in the statement: the game has no pure Nash
profile but does have a trembling-hand-perfect mixed profile. -/
theorem matchingPennies_refinement_without_pure_equilibrium :
    (∀ profile : Profile matchingPennies.sig,
      ¬ IsNash matchingPennies.toForm
        (euPreference matchingPennies.utility) profile) ∧
      matchingPennies.toForm.IsTremblingHandPerfect
        (euPreference matchingPennies.utility) fairPennies :=
  ⟨matchingPennies_noPureNash, fairPennies_isTremblingHandPerfect⟩

end GameTheory.Analysis.TremblingHandTest
