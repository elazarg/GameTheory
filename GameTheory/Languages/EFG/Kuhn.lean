/-
# Kuhn correspondence for extensive-form games

The substantive behavioral/mixed equivalence lives on the accepted
`InformationModel`. This module gives an EFG-facing surface without introducing
another evaluator, strategy representation, or equilibrium notion.

The two directions deliberately retain their sharp hypotheses. Predrawing a
behavioral plan needs no repeated nontrivial information state; reading a mixed
plan behaviorally needs recall, used through the weaker constraint-locality
fact it implies. The protocol layer proves unilateral realization while
holding every opponent coordinate fixed; this EFG surface uses those laws to
transfer Nash equilibria in both directions.
-/

import GameTheory.Languages.EFG.Strategic
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Languages.EFG

open GameTheory.Protocol Probability

universe uι us ua up uq uk uo

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua, up, uq, uk} ι)

/-- A behavioral EFG plan randomizes locally at each information state. -/
abbrev BehavioralPlan (who : ι) :=
  G.information.BehavioralPolicy who

/-- A mixed EFG plan draws one information-local contingent plan once. -/
abbrev MixedPlan (who : ι) :=
  G.information.MixedPolicy who

/-- The EFG behavioral signature is the accepted information-model signature. -/
abbrev behavioralSignature : GameSignature ι :=
  G.information.behavioralSignature

variable [Fintype ι]

/-- Present behavioral EFG plans through the canonical behavioral runner. -/
@[reducible]
def toBehavioralGameForm (horizon : ℕ) : GameForm ι :=
  G.information.toBehavioralGameForm horizon

/-- The behavioral EFG compiler has no language-specific evaluator. -/
@[simp]
theorem toBehavioralGameForm_play (horizon : ℕ)
    (behavioral : Profile G.behavioralSignature) :
    (G.toBehavioralGameForm horizon).play behavioral =
      G.information.runBehavioral behavioral horizon :=
  InformationModel.toBehavioralGameForm_play G.information horizon behavioral

section Unilateral

variable [DecidableEq ι]

/-- Behavioral Nash of the extracted EFG is exactly the native behavioral
deviation inequality. -/
theorem isNash_toBehavioralGameForm_iff
    (utility : G.History → ι → ℝ)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ) :
    IsNash (G.toBehavioralGameForm horizon) (euPreference utility) behavioral ↔
      ∀ who replacement,
        expectedUtility utility who
            (G.information.runBehavioral
              (Profile.update behavioral who replacement) horizon) ≤
          expectedUtility utility who
            (G.information.runBehavioral behavioral horizon) := by
  rw [isNash_iff]
  rfl

/-- A player's mixed strategy may be read behaviorally and redrawn as mixed
without changing the history law against the other players' fixed mixed
strategies. This EFG-facing theorem specializes the protocol-level unilateral
realization law. -/
theorem kuhn_mixed_roundTrip_update
    [∀ i, Fintype (G.information.InfoState i)]
    [∀ i, DecidableEq (G.information.InfoState i)]
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.strategicSignature.mixed) (who : ι)
    (replacement : G.MixedPlan who) (horizon : ℕ) :
    G.information.runMixed
        (Profile.update mixed who
          (InformationModel.MixedPolicy.toBehavioral
            (M := G.information) replacement).toMixed) horizon =
      G.information.runMixed
        (Profile.update mixed who replacement) horizon :=
  G.information.kuhn_mixed_roundTrip_update
    hrecall mixed who replacement horizon

end Unilateral

/-- **Behavioral-to-mixed Kuhn direction.** Predrawing every local choice gives
an explicit mixed contingent-plan profile with exactly the same history law. -/
theorem kuhn_behavioral_to_mixed
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ) :
    ∃ mixed : Profile G.strategicSignature.mixed,
      G.information.runMixed mixed horizon =
        G.information.runBehavioral behavioral horizon :=
  ⟨fun who => (behavioral who).toMixed,
    G.information.runMixed_toMixed hactsOnce behavioral horizon⟩

/-- **Mixed-to-behavioral Kuhn direction.** Under perfect recall, the canonical
behavioral reading of a mixed contingent plan has exactly the same history
law. -/
theorem kuhn_mixed_to_behavioral
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.strategicSignature.mixed) (horizon : ℕ) :
    ∃ behavioral : Profile G.behavioralSignature,
      G.information.runBehavioral behavioral horizon =
        G.information.runMixed mixed horizon :=
  ⟨fun who =>
      InformationModel.MixedPolicy.toBehavioral
        (M := G.information) (mixed who),
    (G.information.runMixed_toBehavioral
      (InformationModel.constrainsAlike_of_perfectRecall hrecall)
      horizon mixed).symm⟩

/-- Under perfect recall, behavioral and mixed EFG profiles realize exactly the
same history laws. Perfect recall supplies the no-revisit consequence used in
the behavioral-to-mixed direction. -/
theorem kuhn_historyLaws
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hrecall : G.information.PerfectRecall) (horizon : ℕ) :
    { law | ∃ behavioral : Profile G.behavioralSignature,
        G.information.runBehavioral behavioral horizon = law } =
      { law | ∃ mixed : Profile G.strategicSignature.mixed,
        G.information.runMixed mixed horizon = law } :=
  G.information.runBehavioral_image_eq_runMixed_image
    (G.information.actsOnceWhereItMatters_of_perfectRecall hrecall)
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon

section UnilateralTransfers

variable [DecidableEq ι]

/-- A behavioral policy and its behavioral-to-mixed-to-behavioral round trip
are realization-equivalent for one player while every other behavioral policy
is held fixed. -/
theorem kuhn_behavioral_roundTrip_update
    [∀ i, Fintype (G.information.InfoState i)]
    [∀ i, DecidableEq (G.information.InfoState i)]
    (hrecall : G.information.PerfectRecall)
    (behavioral : Profile G.behavioralSignature) (who : ι)
    (replacement : G.BehavioralPlan who) (horizon : ℕ) :
    G.information.runBehavioral
        (Profile.update behavioral who
          (InformationModel.MixedPolicy.toBehavioral
            (M := G.information) replacement.toMixed)) horizon =
      G.information.runBehavioral
        (Profile.update behavioral who replacement) horizon :=
  G.information.kuhn_behavioral_roundTrip_update
    hrecall behavioral who replacement horizon

/-- **Unilateral mixed-to-behavioral realization.** Replacing one player's
mixed strategy by an arbitrary behavioral strategy commutes with Kuhn's
reading while every nondeviator keeps its induced behavior. -/
theorem kuhn_mixed_update_toBehavioral
    [∀ i, Fintype (G.information.InfoState i)]
    [∀ i, DecidableEq (G.information.InfoState i)]
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.strategicSignature.mixed) (who : ι)
    (replacement : G.BehavioralPlan who) (horizon : ℕ) :
    G.information.runBehavioral
        (Profile.update (sig := G.information.behavioralSignature)
          (fun i => InformationModel.MixedPolicy.toBehavioral
            (M := G.information) (mixed i)) who replacement) horizon =
      G.information.runMixed
        (Profile.update (sig := G.information.strategicSignature.mixed)
          mixed who replacement.toMixed) horizon :=
  G.information.kuhn_mixed_update_toBehavioral
    hrecall mixed who replacement horizon

/-- **Unilateral behavioral-to-mixed realization.** Starting from a behavioral
profile, an arbitrary mixed deviation is realized by its behavioral reading
without changing any nondeviator's behavioral policy. -/
theorem kuhn_behavioral_update_toMixed
    [∀ i, Fintype (G.information.InfoState i)]
    [∀ i, DecidableEq (G.information.InfoState i)]
    (hrecall : G.information.PerfectRecall)
    (behavioral : Profile G.behavioralSignature) (who : ι)
    (replacement : G.MixedPlan who) (horizon : ℕ) :
    G.information.runMixed
        (Profile.update (sig := G.information.strategicSignature.mixed)
          (fun i => (behavioral i).toMixed) who replacement) horizon =
      G.information.runBehavioral
        (Profile.update (sig := G.information.behavioralSignature)
          behavioral who
            (InformationModel.MixedPolicy.toBehavioral
              (M := G.information) replacement)) horizon :=
  G.information.kuhn_behavioral_update_toMixed
    hrecall behavioral who replacement horizon

/-- A behavioral Nash equilibrium becomes a mixed Nash equilibrium by
predrawing every local choice. The proof uses the unilateral law, so arbitrary
mixed deviations—not only converted behavioral deviations—are covered. -/
theorem isNash_toMixed_of_isNash_behavioral
    [∀ i, Fintype (G.information.InfoState i)]
    [∀ i, DecidableEq (G.information.InfoState i)]
    (hrecall : G.information.PerfectRecall)
    (utility : G.History → ι → ℝ)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ)
    (hnash : IsNash (G.toBehavioralGameForm horizon)
      (euPreference utility) behavioral) :
    IsNash (G.toGameForm horizon).mixed (euPreference utility)
      (fun i => (behavioral i).toMixed) := by
  rw [G.isNash_mixed_toGameForm_iff]
  rw [G.isNash_toBehavioralGameForm_iff] at hnash
  intro who replacement
  have hdeviation := G.kuhn_behavioral_update_toMixed
    hrecall behavioral who replacement horizon
  have hbaseline := G.information.runMixed_toMixed
    (G.information.actsOnceWhereItMatters_of_perfectRecall hrecall)
    behavioral horizon
  rw [hdeviation, hbaseline]
  exact hnash who
    (InformationModel.MixedPolicy.toBehavioral
      (M := G.information) replacement)

/-- A mixed Nash equilibrium becomes a behavioral Nash equilibrium under the
canonical conditional behavioral reading. Arbitrary behavioral deviations are
covered by unilateral realization with the nondeviators fixed. -/
theorem isNash_toBehavioral_of_isNash_mixed
    [∀ i, Fintype (G.information.InfoState i)]
    [∀ i, DecidableEq (G.information.InfoState i)]
    (hrecall : G.information.PerfectRecall)
    (utility : G.History → ι → ℝ)
    (mixed : Profile G.strategicSignature.mixed) (horizon : ℕ)
    (hnash : IsNash (G.toGameForm horizon).mixed
      (euPreference utility) mixed) :
    IsNash (G.toBehavioralGameForm horizon) (euPreference utility)
      (fun i => InformationModel.MixedPolicy.toBehavioral
        (M := G.information) (mixed i)) := by
  rw [G.isNash_toBehavioralGameForm_iff]
  rw [G.isNash_mixed_toGameForm_iff] at hnash
  intro who replacement
  have hdeviation := G.kuhn_mixed_update_toBehavioral
    hrecall mixed who replacement horizon
  have hbaseline := G.information.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall)
    horizon mixed
  rw [hdeviation, ← hbaseline]
  exact hnash who replacement.toMixed

end UnilateralTransfers

/-- Pushing a behavioral history law through any outcome map preserves the
behavioral-to-mixed correspondence. This is the utility-distribution theorem
with utility generalized to arbitrary retained outcome data. -/
theorem kuhn_behavioral_to_mixed_outcomeLaw
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ)
    {Outcome : Type uo} (outcome : G.History → Outcome) :
    ∃ mixed : Profile G.strategicSignature.mixed,
      FinDist.map outcome (G.information.runMixed mixed horizon) =
        FinDist.map outcome (G.information.runBehavioral behavioral horizon) := by
  obtain ⟨mixed, hmixed⟩ :=
    G.kuhn_behavioral_to_mixed hactsOnce behavioral horizon
  exact ⟨mixed, congrArg (FinDist.map outcome) hmixed⟩

/-- Pushing a mixed history law through any outcome map preserves the
mixed-to-behavioral correspondence. -/
theorem kuhn_mixed_to_behavioral_outcomeLaw
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.strategicSignature.mixed) (horizon : ℕ)
    {Outcome : Type uo} (outcome : G.History → Outcome) :
    ∃ behavioral : Profile G.behavioralSignature,
      FinDist.map outcome (G.information.runBehavioral behavioral horizon) =
        FinDist.map outcome (G.information.runMixed mixed horizon) := by
  obtain ⟨behavioral, hbehavioral⟩ :=
    G.kuhn_mixed_to_behavioral hrecall mixed horizon
  exact ⟨behavioral, congrArg (FinDist.map outcome) hbehavioral⟩

/-- The behavioral-to-mixed witness preserves every player's expected utility. -/
theorem kuhn_behavioral_to_mixed_expectedUtility
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ)
    (utility : G.History → ι → ℝ) :
    ∃ mixed : Profile G.strategicSignature.mixed,
      ∀ who,
        expectedUtility utility who
            (G.information.runMixed mixed horizon) =
          expectedUtility utility who
            (G.information.runBehavioral behavioral horizon) := by
  obtain ⟨mixed, hmixed⟩ :=
    G.kuhn_behavioral_to_mixed hactsOnce behavioral horizon
  exact ⟨mixed, fun who => congrArg (expectedUtility utility who) hmixed⟩

/-- The mixed-to-behavioral witness preserves every player's expected utility. -/
theorem kuhn_mixed_to_behavioral_expectedUtility
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.strategicSignature.mixed) (horizon : ℕ)
    (utility : G.History → ι → ℝ) :
    ∃ behavioral : Profile G.behavioralSignature,
      ∀ who,
        expectedUtility utility who
            (G.information.runBehavioral behavioral horizon) =
          expectedUtility utility who
            (G.information.runMixed mixed horizon) := by
  obtain ⟨behavioral, hbehavioral⟩ :=
    G.kuhn_mixed_to_behavioral hrecall mixed horizon
  exact
    ⟨behavioral,
      fun who => congrArg (expectedUtility utility who) hbehavioral⟩

end Game

end GameTheory.Languages.EFG
