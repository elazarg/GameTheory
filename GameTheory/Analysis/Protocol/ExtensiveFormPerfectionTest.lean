/-
# Perfection in the entry-deterrence arena

The entry-deterrence arena has an extensive-form trembling-hand perfect
profile, and every such profile is the strategy of a sequential equilibrium.
-/

import GameTheory.Analysis.Protocol.ExtensiveFormPerfection
import GameTheory.Analysis.Protocol.SequentialOneShotTest

noncomputable section

namespace GameTheory.Tests.ExtensiveFormPerfection

open GameTheory GameTheory.Protocol
open GameTheory.Tests.SubgamePerfect GameTheory.Tests.InformationLocalization
open GameTheory.Tests.SequentialOneShot
open InformationModel

/-- Selten's construction gives a perfect profile of the arena. -/
theorem perfect_exists :
    ∃ strategy, model.IsExtensiveFormPerfect (fun _ => incumbentPolicy)
      arena_wellFoundedHistories sePayoff strategy :=
  model.exists_isExtensiveFormPerfect _ _ _

/-- Perfection yields a sequential equilibrium of the arena. -/
theorem perfect_sequentialEquilibrium :
    ∃ assessment : model.BehavioralAssessment,
      assessment.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        arena_wellFoundedHistories sePayoff := by
  obtain ⟨strategy, perfect⟩ := perfect_exists
  obtain ⟨assessment, -, equilibrium⟩ := perfect.exists_sequentialEquilibrium model decisionRecall
  exact ⟨assessment, equilibrium⟩

end GameTheory.Tests.ExtensiveFormPerfection
