import GameTheory.Theorems
import GameTheory.Languages.EFG.Syntax
import GameTheory.Languages.EFG.Compile
import GameTheory.Languages.EFG.SOS
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

/-- Canonical mixed realization of an EFG behavioral profile as a PMF over pure
profiles, obtained by independently sampling each infoset action and then
repacking the resulting flat contingent plan as a per-player pure profile. -/
noncomputable def mixedOfBehavioralPure (G : _root_.EFG.EFGGame)
    (σ : _root_.EFG.BehavioralProfile G.inf) : PMF (_root_.EFG.PureProfile G.inf) :=
  (_root_.EFG.productProfile σ).bind
    (fun s => PMF.pure ((_root_.EFG.flatProfileEquivPureProfile (S := G.inf)) s))

/-- Outcome-level behavioral -> mixed direction, packaged with the canonical PMF
over pure profiles rather than flat contingent plans. -/
theorem kuhn_behavioral_to_mixed_pure
    (G : _root_.EFG.EFGGame)
    (hpr : _root_.EFG.PerfectRecall G.tree) :
    KuhnBehavioralToMixedOutcome
      (_root_.EFG.BehavioralProfile G.inf)
      (_root_.EFG.PureProfile G.inf)
      G.Outcome
      (mixedOfBehavioralPure G)
      (evalBehavioral G)
      (evalPure G) := by
  intro σ
  have hflat :
      (_root_.EFG.productProfile σ).bind
        (fun s => G.tree.evalDist (_root_.EFG.pureToBehavioral
          ((_root_.EFG.flatProfileEquivPureProfile (S := G.inf)) s))) =
      (_root_.EFG.productProfile σ).bind
        (fun s => G.tree.evalDist (_root_.EFG.flatToBehavioral s)) := by
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      (_root_.EFG.productProfile σ)
      (fun s => G.tree.evalDist (_root_.EFG.pureToBehavioral
        ((_root_.EFG.flatProfileEquivPureProfile (S := G.inf)) s)))
      (fun s => G.tree.evalDist (_root_.EFG.flatToBehavioral s))
      ?_
    intro s _
    have hbeh :
        _root_.EFG.pureToBehavioral
          ((_root_.EFG.flatProfileEquivPureProfile (S := G.inf)) s) =
          _root_.EFG.flatToBehavioral s := by
      funext p I
      simp [_root_.EFG.flatProfileEquivPureProfile, _root_.EFG.pureToBehavioral,
        _root_.EFG.flatToBehavioral]
    simp [hbeh]
  calc
    (mixedOfBehavioralPure G σ).bind (evalPure G)
      =
      (_root_.EFG.productProfile σ).bind
        (fun s => G.tree.evalDist (_root_.EFG.pureToBehavioral
          ((_root_.EFG.flatProfileEquivPureProfile (S := G.inf)) s))) := by
            simp [mixedOfBehavioralPure, evalPure, PMF.bind_bind]
    _ =
      (_root_.EFG.productProfile σ).bind
        (fun s => G.tree.evalDist (_root_.EFG.flatToBehavioral s)) := hflat
    _ = evalBehavioral G σ := by
            simpa [evalBehavioral] using
              (_root_.EFG.behavioral_to_mixed
                (S := G.inf) (Outcome := G.Outcome) σ G.tree
                (_root_.EFG.PerfectRecall_implies_NoInfoSetRepeat G.tree hpr))

/-- Complete EFG Kuhn theorem at the outcome-distribution level. The
behavioral->mixed direction uses the canonical product measure over infosets,
repacked as a PMF on pure strategy profiles. -/
theorem kuhn_complete
    (G : _root_.EFG.EFGGame)
    (hpr : _root_.EFG.PerfectRecall G.tree) :
    KuhnCompleteViaOutcome
      (_root_.EFG.BehavioralProfile G.inf)
      (_root_.EFG.MixedProfile G.inf)
      (_root_.EFG.PureProfile G.inf)
      G.Outcome
      (mixedOfBehavioralPure G)
      (_root_.EFG.mixedProfileJoint (S := G.inf))
      (evalBehavioral G)
      (evalPure G) := by
  exact ⟨
    kuhn_behavioral_to_mixed_pure G hpr,
    fun μ =>
      by
        simpa [evalBehavioral, evalPure] using
          (_root_.EFG.kuhn_mixed_to_behavioral
            (S := G.inf) (Outcome := G.Outcome) G.tree hpr μ)
  ⟩

/-- Bundle both EFG Kuhn directions at the outcome-distribution level. -/
theorem kuhn_outcome_both_directions
    (G : _root_.EFG.EFGGame)
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
  exact ⟨hB2M, hM2B⟩

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
  have _ := hPR
  exact kuhn_outcome_both_directions
    (G := G)
    (mixedOfBehavioral := mixedOfBehavioral)
    hB2M hM2B

end EFG
end Languages
end GameTheory
