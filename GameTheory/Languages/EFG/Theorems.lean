import GameTheory.Theorems
import GameTheory.Languages.EFG.Syntax
import GameTheory.Languages.EFG.Compile
import GameTheory.Languages.EFG.Kuhn

namespace GameTheory
namespace Languages
namespace EFG

open GameTheory.Theorems

/-- Original-strength EFG Kuhn (behavioral -> mixed), re-exported in the new
language layout. -/
theorem kuhn_behavioral_to_mixed
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (σ : _root_.EFG.BehavioralProfile S) (t : _root_.EFG.GameTree S Outcome)
    (hpr : _root_.EFG.PerfectRecall t) :
    ∃ μ : PMF (_root_.EFG.FlatProfile S),
      μ.bind (fun s => t.evalDist (_root_.EFG.flatToBehavioral s)) = t.evalDist σ :=
  _root_.EFG.kuhn_behavioral_to_mixed (S := S) (Outcome := Outcome) σ t hpr

/-- Original-strength EFG Kuhn (mixed -> behavioral), re-exported in the new
language layout. -/
theorem kuhn_mixed_to_behavioral
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    (hpr : _root_.EFG.PerfectRecall t)
    (μP : _root_.EFG.MixedProfile S) :
    ∃ sigma : _root_.EFG.BehavioralProfile S,
      t.evalDist sigma =
      (_root_.EFG.mixedProfileJoint (S := S) μP).bind
        (fun pi => t.evalDist (_root_.EFG.pureToBehavioral (S := S) pi)) :=
  _root_.EFG.kuhn_mixed_to_behavioral (S := S) (Outcome := Outcome) t hpr μP

/-- EFG-level behavioral evaluator as an outcome distribution. -/
noncomputable def evalBehavioral (G : _root_.EFG.EFGGame)
    (σ : _root_.EFG.BehavioralProfile G.inf) : PMF G.Outcome :=
  G.tree.evalDist σ

/-- EFG-level pure evaluator, via pure -> behavioral lift. -/
noncomputable def evalPure (G : _root_.EFG.EFGGame)
    (π : _root_.EFG.PureProfile G.inf) : PMF G.Outcome :=
  G.tree.evalDist (_root_.EFG.pureToBehavioral π)

/-- EFG Kuhn as an immediate corollary of the semantics-level Kuhn assembly theorem. -/
theorem kuhn_outcome_both_directions
    (G : _root_.EFG.EFGGame)
    (I : InfoSemantics G.inf.Player
      (_root_.EFG.GameTree G.inf G.Outcome)
      (_root_.EFG.HistoryStep G.inf))
    (hPR : I.PerfectRecall _root_.EFG.HistoryStepStep G.tree)
    (mixedOfBehavioral : _root_.EFG.BehavioralProfile G.inf → PMF (_root_.EFG.PureProfile G.inf))
    (hB2M :
      KuhnBehavioralToMixedOutcome
        (_root_.EFG.BehavioralProfile G.inf)
        (_root_.EFG.PureProfile G.inf)
        G.Outcome
        mixedOfBehavioral
        (evalBehavioral G)
        (evalPure G))
    (hM2B :
      I.PerfectRecall _root_.EFG.HistoryStepStep G.tree →
        KuhnMixedToBehavioralViaOutcome
          (_root_.EFG.BehavioralProfile G.inf)
          (PMF (_root_.EFG.PureProfile G.inf))
          (_root_.EFG.PureProfile G.inf)
          G.Outcome
          (fun μ => μ)
          (evalBehavioral G)
          (evalPure G)) :
    KuhnBehavioralToMixedOutcome
      (_root_.EFG.BehavioralProfile G.inf)
      (_root_.EFG.PureProfile G.inf)
      G.Outcome
      mixedOfBehavioral
      (evalBehavioral G)
      (evalPure G)
    ∧
    KuhnMixedToBehavioralViaOutcome
      (_root_.EFG.BehavioralProfile G.inf)
      (PMF (_root_.EFG.PureProfile G.inf))
      (_root_.EFG.PureProfile G.inf)
      G.Outcome
      (fun μ => μ)
      (evalBehavioral G)
      (evalPure G) := by
  exact GameTheory.Theorems.kuhn_outcome_both_directions_of_state_machine
    (I := I)
    (step := _root_.EFG.HistoryStepStep)
    (init := G.tree)
    (mixedOfBehavioral := mixedOfBehavioral)
    (joint := fun μ => μ)
    (evalBehavioral := evalBehavioral G)
    (evalPure := evalPure G)
    hPR hB2M hM2B

/-- Same corollary specialized to the canonical EFG compilation interface:
`EFG.PerfectRecall` is transported to semantics-level perfect recall automatically. -/
theorem kuhn_outcome_both_directions_of_perfectRecall
    (G : _root_.EFG.EFGGame)
    (hPR : _root_.EFG.PerfectRecall G.tree)
    (mixedOfBehavioral : _root_.EFG.BehavioralProfile G.inf → PMF (_root_.EFG.PureProfile G.inf))
    (hB2M :
      KuhnBehavioralToMixedOutcome
        (_root_.EFG.BehavioralProfile G.inf)
        (_root_.EFG.PureProfile G.inf)
        G.Outcome
        mixedOfBehavioral
        (evalBehavioral G)
        (evalPure G))
    (hM2B :
      (GameTheory.Languages.EFG.infoSemantics G.inf G.Outcome).PerfectRecall
          _root_.EFG.HistoryStepStep G.tree →
        KuhnMixedToBehavioralViaOutcome
          (_root_.EFG.BehavioralProfile G.inf)
          (PMF (_root_.EFG.PureProfile G.inf))
          (_root_.EFG.PureProfile G.inf)
          G.Outcome
          (fun μ => μ)
          (evalBehavioral G)
          (evalPure G)) :
    KuhnBehavioralToMixedOutcome
      (_root_.EFG.BehavioralProfile G.inf)
      (_root_.EFG.PureProfile G.inf)
      G.Outcome
      mixedOfBehavioral
      (evalBehavioral G)
      (evalPure G)
    ∧
    KuhnMixedToBehavioralViaOutcome
      (_root_.EFG.BehavioralProfile G.inf)
      (PMF (_root_.EFG.PureProfile G.inf))
      (_root_.EFG.PureProfile G.inf)
      G.Outcome
      (fun μ => μ)
      (evalBehavioral G)
      (evalPure G) := by
  exact kuhn_outcome_both_directions
    (G := G)
    (I := GameTheory.Languages.EFG.infoSemantics G.inf G.Outcome)
    (hPR := GameTheory.Languages.EFG.infoSemantics_perfectRecall_of_efgPerfectRecall
      (S := G.inf) (Outcome := G.Outcome) (t := G.tree) hPR)
    (mixedOfBehavioral := mixedOfBehavioral)
    hB2M hM2B

end EFG
end Languages
end GameTheory
