/-
# EXP-079: intrinsic selected-solution strategic form

This spike tests whether unique closed-loop solutions can feed the canonical
static game form and Nash predicate without choosing a temporal execution.
The hostile sender deviation must re-solve the receiver's downstream action.
-/

import GameTheory.Examples.Intrinsic
import GameTheory.Languages.Intrinsic.Solution
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Experimental.IntrinsicStrategic

open GameTheory.Languages.Intrinsic
open GameTheory.Examples.Intrinsic
open GameTheory.Probability

namespace Candidate

universe uAgent uNature uDecision

/-- Intrinsic agents own their complete information-local decision rules; the
outcome retains the selected closed-loop configuration. -/
abbrev strategicSignature
    (M : Model.{uAgent, uNature, uDecision}) : GameSignature M.Agent where
  Strategy := M.PureStrategy
  Outcome := M.Configuration

/-- Compile one fixed nature state by selecting the certified unique
closed-loop solution. -/
@[reducible]
def toGameForm (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (nature : M.Nature) : GameForm M.Agent where
  sig := strategicSignature M
  play profile := FinDist.pure
    ⟨nature, M.solution solvable profile nature⟩

@[simp]
theorem toGameForm_play (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (nature : M.Nature)
    (profile : M.PureProfile) :
    (toGameForm M solvable nature).play profile =
      FinDist.pure ⟨nature, M.solution solvable profile nature⟩ := rfl

/-- Canonical Nash is exactly comparison of the re-solved configuration after
one intrinsic agent replaces its complete decision rule. -/
theorem isNash_toGameForm_iff
    (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (nature : M.Nature)
    [DecidableEq M.Agent] (utility : M.Configuration → M.Agent → ℝ)
    (profile : M.PureProfile) :
    IsNash (toGameForm M solvable nature) (euPreference utility) profile ↔
      ∀ who replacement,
        utility
            ⟨nature, M.solution solvable
              (Profile.update (sig := strategicSignature M)
                profile who replacement) nature⟩ who ≤
          utility ⟨nature, M.solution solvable profile nature⟩ who := by
  rw [isNash_iff]
  simp only [euPreference_apply, expectedUtility_pure]

end Candidate

/-! ## Hostile sender–receiver slice -/

local instance signalingAgentDecidableEq : DecidableEq signaling.Agent := by
  show DecidableEq Bool
  infer_instance

local instance signalingDecisionDecidableEq
    (agent : signaling.Agent) : DecidableEq (signaling.Decision agent) := by
  show DecidableEq Bool
  infer_instance

/-- Causality makes the signaling fixture uniquely solvable: first solve the
sender rule from nature, then solve the receiver rule from the sender action. -/
theorem signaling_isSolvable : signaling.IsSolvable := by
  intro profile nature
  let senderReference : signaling.Configuration :=
    ⟨nature, fun _ => false⟩
  let sender := (profile false).act senderReference
  let receiverReference : signaling.Configuration :=
    ⟨nature, fun agent => if (show Bool from agent) then false else sender⟩
  let receiver := (profile true).act receiverReference
  let decisions : (agent : Bool) → signaling.Decision agent :=
    fun agent => if (show Bool from agent) then receiver else sender
  refine ⟨decisions, ?_, ?_⟩
  · intro agent
    cases agent with
    | false =>
        exact (profile false).respects senderReference
          ⟨nature, decisions⟩ rfl
    | true =>
        apply (profile true).respects receiverReference
          ⟨nature, decisions⟩
        rfl
  · intro other hfixed
    have hsender : other false = sender := by
      calc
        other false = (profile false).act ⟨nature, other⟩ := hfixed false
        _ = (profile false).act senderReference :=
          (profile false).respects _ _ rfl
        _ = sender := rfl
    funext agent
    cases agent with
    | false => exact hsender
    | true =>
        calc
          other true = (profile true).act ⟨nature, other⟩ := hfixed true
          _ = (profile true).act receiverReference :=
            (profile true).respects _ _ (by
              show other false = receiverReference.decision false
              simpa [receiverReference] using hsender)
          _ = receiver := rfl

def truthfulSender : signaling.PureStrategy false where
  act configuration := configuration.nature
  respects _ _ hinfo := hinfo

def falseSender : signaling.PureStrategy false where
  act _ := false
  respects _ _ _ := rfl

def copyingReceiver : signaling.PureStrategy true where
  act configuration := configuration.decision false
  respects _ _ hinfo := hinfo

def signalingProfile (sender : signaling.PureStrategy false) :
    signaling.PureProfile
  | false => sender
  | true => copyingReceiver

def truthfulProfile : signaling.PureProfile :=
  signalingProfile truthfulSender

def lyingProfile : signaling.PureProfile :=
  signalingProfile falseSender

theorem truthful_solution :
    signaling.solution signaling_isSolvable truthfulProfile true =
      fun _ => true := by
  symm
  apply signaling.solution_unique signaling_isSolvable truthfulProfile true
  intro agent
  cases agent <;> rfl

theorem lying_solution :
    signaling.solution signaling_isSolvable lyingProfile true =
      fun _ => false := by
  symm
  apply signaling.solution_unique signaling_isSolvable lyingProfile true
  intro agent
  cases agent <;> rfl

theorem update_lying_sender :
    Profile.update (sig := Candidate.strategicSignature signaling)
        lyingProfile false truthfulSender = truthfulProfile := by
  funext agent
  cases agent <;>
    simp [lyingProfile, truthfulProfile, signalingProfile]

/-- Both agents value the receiver matching nature. -/
def utility (configuration : signaling.Configuration) (_who : Bool) : ℝ :=
  if configuration.decision true = configuration.nature then 1 else 0

/-- Truthful signaling and copying is Nash at the true nature value. -/
theorem truthful_isNash :
    IsNash (Candidate.toGameForm signaling signaling_isSolvable true)
      (euPreference utility) truthfulProfile := by
  rw [Candidate.isNash_toGameForm_iff]
  intro who replacement
  rw [truthful_solution]
  simp only [utility]
  split <;> norm_num

/-- The all-false selected solution is not Nash. Replacing only the sender's
rule makes the receiver change too, raising the shared payoff from zero to
one. -/
theorem lying_not_isNash :
    ¬ IsNash (Candidate.toGameForm signaling signaling_isSolvable true)
      (euPreference utility) lyingProfile := by
  intro hnash
  have hdeviation :=
    (Candidate.isNash_toGameForm_iff signaling signaling_isSolvable true
      utility lyingProfile).1 hnash false truthfulSender
  rw [update_lying_sender, truthful_solution, lying_solution] at hdeviation
  simp [utility] at hdeviation
  norm_num at hdeviation

end GameTheory.Experimental.IntrinsicStrategic
