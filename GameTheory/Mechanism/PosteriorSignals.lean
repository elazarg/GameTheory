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

open GameTheory.Math.Probability

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
def IsPosteriorAssignment (S : SignalStructure State Message)
    (prior : FinDist State)
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

/-! ## Splitting a Bayes-plausible posterior law

The canonical coupling already contains the required signal experiment.  Given
the realized state, disintegrate the coupling along its state coordinate and
announce only the posterior coordinate.  Bayes plausibility identifies the
coupling's state marginal with the requested prior. -/

/-- The signal experiment obtained by disintegrating a posterior law's
canonical coupling along the realized state. -/
def fromPosteriorLaw (law : PosteriorLaw State) :
    SignalStructure State (FinDist State) where
  kernel state :=
    (law.coupling.condOnFibre Prod.fst state).map Prod.snd

/-- Under Bayes plausibility, the disintegrated signal reconstructs the
canonical state-posterior coupling exactly. -/
theorem joint_fromPosteriorLaw (prior : FinDist State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    (fromPosteriorLaw law).joint prior = law.coupling := by
  have hmarginal : law.coupling.map Prod.fst = prior :=
    law.map_fst_coupling.trans hlaw
  unfold SignalStructure.joint fromPosteriorLaw
  rw [← hmarginal]
  calc
    (law.coupling.map Prod.fst).bind (fun state =>
        ((law.coupling.condOnFibre Prod.fst state).map Prod.snd).map
          fun belief => (state, belief)) =
        (law.coupling.map Prod.fst).bind
          (law.coupling.condOnFibre Prod.fst) := by
      apply FinDist.bind_congr
      intro state hstate
      rw [FinDist.map_comp]
      calc
        (law.coupling.condOnFibre Prod.fst state).map
              ((fun belief => (state, belief)) ∘ Prod.snd) =
            (law.coupling.condOnFibre Prod.fst state).map id := by
          apply FinDist.map_congr_of_eq_on_support
          intro pair hpair
          rw [Function.comp_apply]
          have hfibre :
              ∃ witness ∈ Prod.fst ⁻¹' {state},
                witness ∈ law.coupling.support := by
            rw [FinDist.support_map] at hstate
            rcases hstate with ⟨witness, hwitness, hcoordinate⟩
            exact ⟨witness, by simpa using hcoordinate, hwitness⟩
          have hpairFiber : pair ∈ Prod.fst ⁻¹' {state} := by
            have hconditioned := hpair
            simp only [FinDist.condOnFibre, dif_pos hfibre] at hconditioned
            exact (FinDist.support_condOn law.coupling
              (Prod.fst ⁻¹' {state}) hfibre hconditioned).1
          have hcoordinate : pair.1 = state := by simpa using hpairFiber
          rcases pair with ⟨pairState, belief⟩
          simp only at hcoordinate ⊢
          subst pairState
          rfl
        _ = law.coupling.condOnFibre Prod.fst state := FinDist.map_id _
    _ = law.coupling :=
      (FinDist.eq_bind_condOnFibre law.coupling Prod.fst).symm

/-- The messages generated by the splitting signal have exactly the requested
posterior law. -/
theorem messageMarginal_fromPosteriorLaw (prior : FinDist State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    (fromPosteriorLaw law).messageMarginal prior = law := by
  unfold messageMarginal
  rw [joint_fromPosteriorLaw prior law hlaw, law.map_snd_coupling]

/-- Announcing each disintegrated posterior is a valid total posterior
assignment. -/
theorem fromPosteriorLaw_isPosteriorAssignment [DecidableEq State]
    (prior : FinDist State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    (fromPosteriorLaw law).IsPosteriorAssignment prior id := by
  classical
  intro state belief
  rw [joint_fromPosteriorLaw prior law hlaw,
    messageMarginal_fromPosteriorLaw prior law hlaw,
    law.prob_coupling]
  rfl

/-- The splitting construction induces the original Bayes-plausible law. -/
theorem inducedPosteriorLaw_fromPosteriorLaw (prior : FinDist State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    (fromPosteriorLaw law).inducedPosteriorLaw prior id = law := by
  unfold inducedPosteriorLaw
  rw [messageMarginal_fromPosteriorLaw prior law hlaw, FinDist.map_id]

/-- **Finite splitting characterization, substantive direction.** Every
Bayes-plausible finite posterior law is generated by a signal experiment whose
announced posteriors obey Bayes factorization. -/
theorem exists_signalStructure_of_isBayesPlausible [DecidableEq State]
    (prior : FinDist State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    ∃ (signal : SignalStructure State (FinDist State))
      (posterior : FinDist State → FinDist State),
      signal.IsPosteriorAssignment prior posterior ∧
        signal.inducedPosteriorLaw prior posterior = law := by
  exact ⟨fromPosteriorLaw law, id,
    fromPosteriorLaw_isPosteriorAssignment prior law hlaw,
    inducedPosteriorLaw_fromPosteriorLaw prior law hlaw⟩

end SignalStructure

end GameTheory
