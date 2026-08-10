/-
# Signals and posterior laws

A posterior assignment is valid for a signal when the joint state-message mass
factors into message mass times posterior mass.  Pushing the message marginal
through such an assignment gives the canonical posterior law, and the signal's
state-marginal theorem proves that law Bayes plausible.
-/

import GameTheory.Mechanism.FeasiblePosteriors
import GameTheory.Mechanism.InformationDesign

noncomputable section

namespace GameTheory

open Probability

universe us um

namespace SignalStructure

variable {State : Type us} {Message : Type um}

/-- The law of posteriors announced by messages. -/
def inducedPosteriorLaw (S : SignalStructure State Message)
    (prior : FinDist State) (posterior : Message → FinDist State) :
    PosteriorLaw State :=
  (S.messageMarginal prior).map posterior

/-- Bayes factorization for a total posterior assignment.  At a zero-mass
message both sides are zero, so its arbitrary posterior is immaterial. -/
def IsPosteriorAssignment [DecidableEq State] [DecidableEq Message]
    (S : SignalStructure State Message) (prior : FinDist State)
    (posterior : Message → FinDist State) : Prop :=
  ∀ state message,
    (S.joint prior).prob (state, message) =
      (S.messageMarginal prior).prob message *
        (posterior message).prob state

/-- A Bayes-factorizing signal induces a Bayes-plausible posterior law. -/
theorem inducedPosteriorLaw_isBayesPlausible
    [Fintype State] [DecidableEq State]
    [Fintype Message] [DecidableEq Message]
    (S : SignalStructure State Message) (prior : FinDist State)
    (posterior : Message → FinDist State)
    (hposterior : S.IsPosteriorAssignment prior posterior) :
    (S.inducedPosteriorLaw prior posterior).IsBayesPlausible prior := by
  unfold PosteriorLaw.IsBayesPlausible PosteriorLaw.mean inducedPosteriorLaw
  apply FinDist.ext_of_prob
  intro state
  rw [FinDist.prob_bind, FinDist.expect_map, FinDist.expect_eq_sum]
  calc
    ∑ message,
        (S.messageMarginal prior).prob message *
          (posterior message).prob state =
        ∑ message, (S.joint prior).prob (state, message) := by
      apply Finset.sum_congr rfl
      intro message _
      exact (hposterior state message).symm
    _ = ((S.joint prior).map Prod.fst).prob state := by
      rw [FinDist.prob_map, FinDist.expect_eq_sum]
      simp only [Fintype.sum_prod_type]
      classical
      simp
    _ = prior.prob state :=
      congrArg (fun law : FinDist State => law.prob state)
        (S.map_fst_joint prior)

/-- Full information assigns the point posterior at the announced state. -/
theorem fullInformation_isPosteriorAssignment [DecidableEq State]
    (prior : FinDist State) :
    (fullInformation State).IsPosteriorAssignment prior FinDist.pure := by
  have hmarginal :
      (fullInformation State).messageMarginal prior = prior := by
    rw [messageMarginal_eq_bind]
    exact FinDist.bind_pure prior
  intro state message
  rw [prob_joint, hmarginal]
  simp only [fullInformation_kernel, FinDist.prob_pure_eq_ite]
  by_cases heq : state = message
  · subst message
    simp
  · simp [heq, Ne.symm heq]

/-- The posterior law induced by full information is full revelation. -/
theorem inducedPosteriorLaw_fullInformation (prior : FinDist State) :
    (fullInformation State).inducedPosteriorLaw prior FinDist.pure =
      PosteriorLaw.fullRevelation prior := by
  unfold inducedPosteriorLaw PosteriorLaw.fullRevelation
  congr 1
  rw [messageMarginal_eq_bind]
  exact FinDist.bind_pure prior

end SignalStructure

end GameTheory
