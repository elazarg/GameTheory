/-
# Behavioral terminal continuations

Well-founded behavioral play uses the canonical randomized terminal law.
Assessment contexts integrate whole-policy continuations from their beliefs to
their terminal outcomes; sequential rationality is optimality in these
contexts.
-/

import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Protocol.RandomizedBackward

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} [Fintype ι] {E : ExecutionProtocol ι}

namespace InformationModel

variable {M : InformationModel E}

/-- The terminal history law of a behavioral profile from a given history. -/
def runBehavioralTerminalFrom (M : InformationModel E)
    (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (history : E.History) :
    PMF E.History :=
  E.randomizedBackwardLaw certificate (M.randomizedChooser policies) history

/-- Terminal behavioral play of a deterministic profile is the terminal law of
its point-mass chooser. -/
theorem runBehavioralTerminalFrom_toBehavioral (M : InformationModel E)
    (certificate : E.WellFoundedHistories) (policies : (i : ι) → M.Policy i)
    (history : E.History) :
    M.runBehavioralTerminalFrom certificate (fun i => (policies i).toBehavioral) history =
      E.randomizedBackwardLaw certificate (M.historyChooser policies).toRandomized history := by
  rw [runBehavioralTerminalFrom, M.randomizedChooser_toBehavioral]

/-- A certified global horizon makes terminal play equal behavioral play cut
off at that horizon, from every starting history. -/
theorem runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (M : InformationModel E) (certificate : E.WellFoundedHistories) {bound : ℕ}
    (bounded : E.BoundedHorizon bound)
    (policies : (i : ι) → M.BehavioralPolicy i) (history : E.History) :
    M.runBehavioralTerminalFrom certificate policies history =
      M.runBehavioralFrom policies bound history := by
  exact E.randomizedBackwardLaw_eq_runRandomizedFor_of_bound bounded
    (M.randomizedChooser policies) history

/-- Every supported behavioral terminal outcome is terminal. -/
theorem runBehavioralTerminalFrom_support_terminal
    (M : InformationModel E) (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (history : E.History) :
    ∀ final ∈ (M.runBehavioralTerminalFrom certificate policies history).support,
      E.terminal final.state :=
  E.randomizedBackwardLaw_support_terminal history

/-- Terminal-only payoff bounds integrate every behavioral terminal law. -/
theorem payoffIntegrable_runBehavioralTerminalFrom_of_bounded_terminal
    (M : InformationModel E) (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) (C : ℝ)
    (hbound : ∀ final, E.terminal final.state → |payoff final| ≤ C)
    (history : E.History) :
    PayoffIntegrable (M.runBehavioralTerminalFrom certificate policies history)
      payoff :=
  E.payoffIntegrable_randomizedBackwardLaw_of_bounded_terminal hbound history

/-- The continuation context of an assessment: an alternative is a whole
behavioral policy for the player, all other policies remain fixed, and play
runs from the history sampled by the belief to its terminal outcome. -/
def BehavioralAssessment.continuationContext
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) :
    Context (M.BehavioralPolicy i) E.History :=
  assessment.continuationContextWith (M.runBehavioralTerminalFrom certificate) site payoff

@[simp]
theorem BehavioralAssessment.continuationContext_value
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ)
    (alternative : M.BehavioralPolicy i) :
    (assessment.continuationContext certificate site payoff).value alternative =
      expect ((assessment.belief i site).bind fun history =>
        M.runBehavioralTerminalFrom certificate
          (Profile.update (sig := M.behavioralSignature)
            assessment.strategy i alternative) history.1) payoff :=
  rfl

/-- A horizon certificate identifies the continuation context with its
truncation at that horizon, including the guarded value domains. -/
theorem BehavioralAssessment.continuationContext_eq_truncated_of_bounded
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories) {bound : ℕ}
    (bounded : E.BoundedHorizon bound) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) :
    assessment.continuationContext certificate site payoff =
      assessment.truncatedContinuationContext site payoff bound := by
  apply congrArg₂ (fun outcome continuation => Context.mk outcome continuation)
  · funext alternative
    apply bind_congr_on_support
    intro history _
    exact M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      certificate bounded
      (Profile.update (sig := M.behavioralSignature)
        assessment.strategy i alternative) history.1
  · rfl

/-- Every outcome of a belief-averaged continuation is terminal. -/
theorem BehavioralAssessment.continuationContext_support_terminal
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ)
    (alternative : M.BehavioralPolicy i) :
    ∀ final ∈
      ((assessment.continuationContext certificate site payoff).outcome
        alternative).support,
      E.terminal final.state := by
  intro final hfinal
  have hfinal' : final ∈ ((assessment.belief i site).bind fun history =>
      M.runBehavioralTerminalFrom certificate
        (Profile.update (sig := M.behavioralSignature)
          assessment.strategy i alternative) history.1).support := hfinal
  rw [PMF.support_bind] at hfinal'
  obtain ⟨history, _, hchild⟩ := Set.mem_iUnion₂.mp hfinal'
  exact M.runBehavioralTerminalFrom_support_terminal certificate _ history.1
    final hchild

/-- A terminal-only payoff bound certifies every whole-policy comparison. -/
theorem BehavioralAssessment.continuationContext_integrable_of_bounded_terminal
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) (C : ℝ)
    (hbound : ∀ final, E.terminal final.state → |payoff final| ≤ C)
    (alternative : M.BehavioralPolicy i) :
    (assessment.continuationContext certificate site payoff).IntegrableAt
      alternative := by
  apply payoffIntegrable_of_bounded_on_support
  intro final hfinal
  exact hbound final
    (assessment.continuationContext_support_terminal certificate
      site payoff alternative final hfinal)

/-- Sequential rationality: at every information site, the assessment's
policy is optimal among whole replacement policies, scored by terminal play
from the belief. -/
def BehavioralAssessment.IsSequentiallyRational
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories)
    (payoff : ι → E.History → ℝ) : Prop :=
  assessment.IsSequentiallyRationalFor fun i site =>
    assessment.continuationContext certificate site (payoff i)

/-- Sequential rationality is rationality against the terminal runner. -/
theorem BehavioralAssessment.isSequentiallyRational_iff_with
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) :
    assessment.IsSequentiallyRational certificate payoff ↔
      assessment.IsSequentiallyRationalWith (M.runBehavioralTerminalFrom certificate) payoff :=
  Iff.rfl

/-- With identically zero payoff every assessment is sequentially rational. -/
theorem BehavioralAssessment.isSequentiallyRational_zero
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories) :
    assessment.IsSequentiallyRational certificate (fun _ _ => 0) :=
  assessment.isSequentiallyRationalWith_zero _

/-- Under a certified global bound, sequential rationality is rationality
against play truncated at that bound. Integrability obligations are preserved
by equality of continuation contexts. -/
theorem BehavioralAssessment.isSequentiallyRational_iff_truncated_of_bounded
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories) {bound : ℕ}
    (bounded : E.BoundedHorizon bound) (payoff : ι → E.History → ℝ) :
    assessment.IsSequentiallyRational certificate payoff ↔
      assessment.IsSequentiallyRationalFor fun i site =>
        assessment.truncatedContinuationContext site (payoff i) bound := by
  simp only [IsSequentiallyRational, IsSequentiallyRationalFor]
  constructor <;> intro h i site
  · simpa only [assessment.continuationContext_eq_truncated_of_bounded
      certificate bounded site (payoff i)] using h i site
  · simpa only [assessment.continuationContext_eq_truncated_of_bounded
      certificate bounded site (payoff i)] using h i site

end InformationModel

end GameTheory.Protocol
