/-
# Sequential equilibrium without perfect recall

A player votes once and afterwards observes only that play has stopped, so it
forgets which way it voted: the model violates perfect recall. It has recall
wherever it can act, because it acts only before voting. Finite existence
therefore still supplies a consistent, sequentially rational assessment.
-/

import GameTheory.Analysis.Protocol.SequentialExistence
import GameTheory.Protocol.FiniteHorizon
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Analysis.Protocol.DecisionRecallExistenceTest

open GameTheory GameTheory.Protocol GameTheory.Tests.Randomized
open GameTheory.Protocol.ExecutionProtocol (Trace History)

/-- The one-vote states are the start and the two votes. -/
instance : Fintype Single :=
  Fintype.ofEquiv (Option Vote)
    { toFun := fun | none => .start | some vote => .voted vote
      invFun := fun | .start => none | .voted vote => some vote
      left_inv := fun | none => rfl | some _ => rfl
      right_inv := fun | .start => rfl | .voted _ => rfl }

/-- A legal joint action is a vote at the start. -/
theorem legal_start {state : Single} {joint : ∀ _ : Unit, Option Vote}
    (legal : once.Legal state joint) :
    state = .start ∧ ∃ vote, joint () = some vote ∧
      once.step state ⟨joint, legal⟩ = PMF.pure (.voted vote) := by
  have hstart := eq_start_of_not_stopped legal.1
  subst hstart
  obtain ⟨vote, hvote⟩ := LegalOption.exists_eq_some_of_active (joint ())
    (ExecutionProtocol.legalOption_of_legal legal ()) (show once.active Single.start () from rfl)
  refine ⟨rfl, vote, hvote, ?_⟩
  show (match joint () with
    | some v => PMF.pure (Single.voted v)
    | none => PMF.pure (Single.voted Vote.up)) = _
  rw [hvote]

theorem once_isTreeShaped : once.IsTreeShaped := by
  apply ExecutionProtocol.isTreeShaped_of_predecessor_unique
  · intro source joint legal hinit
    obtain ⟨-, vote, -, hstep⟩ := legal_start legal
    rw [hstep, PMF.mem_support_pure_iff] at hinit
    cases hinit
  · intro target firstSource secondSource firstJoint secondJoint firstLegal secondLegal
      hfirst hsecond
    obtain ⟨rfl, firstVote, hfirstVote, hfirstStep⟩ := legal_start firstLegal
    obtain ⟨rfl, secondVote, hsecondVote, hsecondStep⟩ := legal_start secondLegal
    rw [hfirstStep, PMF.mem_support_pure_iff] at hfirst
    rw [hsecondStep, PMF.mem_support_pure_iff] at hsecond
    have hvote : firstVote = secondVote := by
      have := hfirst.symm.trans hsecond
      cases this
      rfl
    refine ⟨rfl, funext fun _ => ?_⟩
    rw [hfirstVote, hsecondVote, hvote]

instance : Fintype once.History := once.historyFintype once_isTreeShaped

/-- **Decision recall holds.** The only decision information state is the one
before voting, reached only by the empty own record. -/
theorem single_decisionRecall : singleModel.DecisionRecall := by
  rintro ⟨⟩ site first second
  obtain ⟨witness, hnonterminal, -⟩ := site.2
  have hsite : site.1 = false := by
    rw [← witness.2]
    exact (singleInfoOf_eq_stopped witness.1.trace).trans (by simpa using hnonterminal)
  have hplay (history : singleModel.InformationHistory () site.1) :
      singleModel.ownPlay () history.1.trace = [] := by
    have hstopped : history.1.state.stopped = false :=
      (singleInfoOf_eq_stopped history.1.trace).symm.trans (history.2.trans hsite)
    have hacted := actedAt_single history.1.trace
    rw [hstopped, InfoSignals.actedAt_eq_map_ownPlay] at hacted
    simpa using hacted
  rw [hplay first, hplay second]

/-- The model violates perfect recall. -/
theorem singleModel_not_perfectRecall : ¬ singleModel.PerfectRecall :=
  single_not_perfectRecall

/-- A total fallback policy. -/
def fallback : (i : Unit) → singleModel.Policy i := fun _ info =>
  match info with
  | false => ⟨some .up, by simp [menuAt]⟩
  | true => ⟨none, by simp [menuAt]⟩

/-- Reward for voting up. -/
def payoff (_ : Unit) (history : once.History) : ℝ :=
  match history.state with
  | .voted .up => 1
  | _ => 0

/-- **A sequential equilibrium exists without perfect recall.** -/
theorem exists_sequentialEquilibrium :
    ∃ (fuel : ℕ) (assessment : singleModel.BehavioralAssessment),
      assessment.IsSequentiallyRationalWithin payoff (fuel + 1) ∧
        assessment.IsSequentiallyConsistent single_decisionRecall.decisionInformationAntichain := by
  obtain ⟨bound, hpositive, hbound⟩ := once.exists_pos_boundedHorizon
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  exact ⟨fuel, singleModel.exists_sequentialEquilibriumWithin single_decisionRecall
    fallback payoff fuel hbound⟩

end GameTheory.Analysis.Protocol.DecisionRecallExistenceTest
