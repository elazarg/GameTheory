/-
# Behavioral terminal continuations

Well-founded behavioral play uses the canonical randomized terminal law.
Assessment contexts integrate whole-policy continuations from their beliefs.
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
    (certificate : E.WellFoundedPlay)
    (policies : (i : ι) → M.BehavioralPolicy i) (history : E.History) :
    PMF E.History :=
  E.randomizedBackwardLaw certificate (M.randomizedChooser policies) history

/-- A certified global horizon makes terminal-law play equal the existing
fuelled behavioral runner, from every starting history. -/
theorem runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (M : InformationModel E) (certificate : E.WellFoundedPlay) {bound : ℕ}
    (bounded : E.BoundedHorizon bound)
    (policies : (i : ι) → M.BehavioralPolicy i) (history : E.History) :
    M.runBehavioralTerminalFrom certificate policies history =
      M.runBehavioralFrom policies bound history := by
  exact E.randomizedBackwardLaw_eq_runRandomizedFor_of_bound bounded
    (M.randomizedChooser policies) history

/-- Every supported behavioral terminal outcome is terminal. -/
theorem runBehavioralTerminalFrom_support_terminal
    (M : InformationModel E) (certificate : E.WellFoundedPlay)
    (policies : (i : ι) → M.BehavioralPolicy i) (history : E.History) :
    ∀ final ∈ (M.runBehavioralTerminalFrom certificate policies history).support,
      E.terminal final.state :=
  E.randomizedBackwardLaw_support_terminal history

/-- Terminal-only payoff bounds integrate every behavioral terminal law. -/
theorem payoffIntegrable_runBehavioralTerminalFrom_of_bounded_terminal
    (M : InformationModel E) (certificate : E.WellFoundedPlay)
    (policies : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) (C : ℝ)
    (hbound : ∀ final, E.terminal final.state → |payoff final| ≤ C)
    (history : E.History) :
    PayoffIntegrable (M.runBehavioralTerminalFrom certificate policies history)
      payoff :=
  E.payoffIntegrable_randomizedBackwardLaw_of_bounded_terminal hbound history

/-- A belief-averaged terminal continuation compares whole behavioral policies. -/
def BehavioralAssessment.terminalContinuationContext
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedPlay) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) :
    Context (M.BehavioralPolicy i) E.History :=
  Context.ofBelief (assessment.belief i site)
    (fun history alternative =>
      M.runBehavioralTerminalFrom certificate
        (Profile.update (sig := M.behavioralSignature)
          assessment.strategy i alternative) history.1) payoff

/-- A horizon certificate identifies terminal and fuelled continuation
contexts, including their guarded value domains. -/
theorem BehavioralAssessment.terminalContinuationContext_eq_continuationContext_of_bounded
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedPlay) {bound : ℕ}
    (bounded : E.BoundedHorizon bound) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) :
    assessment.terminalContinuationContext certificate site payoff =
      assessment.continuationContext site payoff bound := by
  apply congrArg₂ (fun outcome continuation => Context.mk outcome continuation)
  · funext alternative
    apply bind_congr_on_support
    intro history _
    exact M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      certificate bounded
      (Profile.update (sig := M.behavioralSignature)
        assessment.strategy i alternative) history.1
  · rfl

/-- Every outcome of a belief-averaged terminal continuation is terminal. -/
theorem BehavioralAssessment.terminalContinuationContext_support_terminal
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedPlay) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ)
    (alternative : M.BehavioralPolicy i) :
    ∀ final ∈
      ((assessment.terminalContinuationContext certificate site payoff).outcome
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
theorem BehavioralAssessment.terminalContinuationContext_integrable_of_bounded_terminal
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedPlay) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) (C : ℝ)
    (hbound : ∀ final, E.terminal final.state → |payoff final| ≤ C)
    (alternative : M.BehavioralPolicy i) :
    (assessment.terminalContinuationContext certificate site payoff).IntegrableAt
      alternative := by
  apply payoffIntegrable_of_bounded_on_support
  intro final hfinal
  exact hbound final
    (assessment.terminalContinuationContext_support_terminal certificate
      site payoff alternative final hfinal)

/-- Whole-policy sequential rationality for well-founded terminal play. -/
def BehavioralAssessment.IsSequentiallyRationalTerminal
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedPlay)
    (payoff : ι → E.History → ℝ) : Prop :=
  assessment.IsSequentiallyRational fun i site =>
    assessment.terminalContinuationContext certificate site (payoff i)

/-- Under a certified global bound, terminal sequential rationality is exactly
the existing whole-policy rationality predicate evaluated with sufficient
fuel. Integrability obligations are preserved by equality of continuation
contexts. -/
theorem BehavioralAssessment.isSequentiallyRationalTerminal_iff_within_of_bounded
    [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedPlay) {bound : ℕ}
    (bounded : E.BoundedHorizon bound) (payoff : ι → E.History → ℝ) :
    assessment.IsSequentiallyRationalTerminal certificate payoff ↔
      assessment.IsSequentiallyRationalWithin payoff bound := by
  simp only [IsSequentiallyRationalTerminal, IsSequentiallyRationalWithin,
    IsSequentiallyRational, IsSequentiallyRationalAt]
  constructor <;> intro h i site
  · simpa only [assessment.terminalContinuationContext_eq_continuationContext_of_bounded
      certificate bounded site (payoff i)] using h i site
  · simpa only [assessment.terminalContinuationContext_eq_continuationContext_of_bounded
      certificate bounded site (payoff i)] using h i site

end InformationModel

end GameTheory.Protocol
