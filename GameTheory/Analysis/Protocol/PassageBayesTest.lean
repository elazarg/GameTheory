module

public import GameTheory.Analysis.Protocol.PassageBayes
public import GameTheory.Analysis.Protocol.SequentialExistenceTest

@[expose] public section
noncomputable section
namespace GameTheory.Tests.PassageBayes
open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability GameTheory.Tests.SequentialExistence

/-- Actual passage gives Bayes beliefs on an information fiber with unequal trace depths. -/
theorem unequal_depth_conditional_ancestor (strategy : ∀ who, information.BehavioralPolicy who)
    (positive : 0 < information.informationMass strategy () actingSite) :
    (¬ ∃ depth, InformationSite.CommonDepth information actingSite depth) ∧
      (information.bayesBelief strategy () actingSite (antichain () actingSite) positive).map some =
        fiberPosterior
          ((information.runBehavioralTerminalFrom game.wellFoundedHistories strategy
            execution.initHistory).map (actingSite.ancestor? information)) Option.isSome true :=
  ⟨no_commonDepth, actingSite.bayesBelief_eq_conditional_ancestor information
    (antichain () actingSite) game.wellFoundedHistories strategy positive⟩

end GameTheory.Tests.PassageBayes
