/-
# Signals and posterior laws

A posterior assignment factorizes the joint state-message mass. Its induced
belief law is Bayes plausible, and every Bayes-plausible posterior law can be
implemented by a signal built from conditional PMFs on positive state fibers.
-/

import GameTheory.Mechanism.FeasiblePosteriors
import GameTheory.Mechanism.InformationDesign
import GameTheory.Math.Probability.Conditioning

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe us um

namespace SignalStructure

variable {State : Type us} {Message : Type um}

/-- Law of posterior beliefs announced by messages. -/
def inducedPosteriorLaw (S : SignalStructure State Message)
    (prior : PMF State) (posterior : Message → PMF State) :
    PosteriorLaw State :=
  (S.messageMarginal prior).map posterior

/-- Bayes factorization at every state-message atom. Null messages satisfy
the identity regardless of the assigned posterior. -/
def IsPosteriorAssignment (S : SignalStructure State Message)
    (prior : PMF State) (posterior : Message → PMF State) : Prop :=
  ∀ state message,
    S.joint prior (state, message) =
      S.messageMarginal prior message * posterior message state

/-- A factorizing signal induces a Bayes-plausible posterior law, without
finite state or message carriers. -/
theorem inducedPosteriorLaw_isBayesPlausible
    (S : SignalStructure State Message) (prior : PMF State)
    (posterior : Message → PMF State)
    (hposterior : S.IsPosteriorAssignment prior posterior) :
    (S.inducedPosteriorLaw prior posterior).IsBayesPlausible prior := by
  have hcoupling :
      S.joint prior =
        (bindPairLaw (S.messageMarginal prior) posterior).map Prod.swap := by
    ext pair
    rcases pair with ⟨state, message⟩
    rw [bindPairLaw_swap_apply]
    exact hposterior state message
  unfold PosteriorLaw.IsBayesPlausible PosteriorLaw.mean inducedPosteriorLaw
  rw [PMF.bind_map]
  calc
    (S.messageMarginal prior).bind (id ∘ posterior) =
        (bindPairLaw (S.messageMarginal prior) posterior).map Prod.snd := by
      simpa only [Function.id_comp] using
        (bindPairLaw_map_snd (S.messageMarginal prior) posterior).symm
    _ = ((bindPairLaw (S.messageMarginal prior) posterior).map Prod.swap).map
        Prod.fst := by
      rw [PMF.map_comp]
      rfl
    _ = (S.joint prior).map Prod.fst := by rw [hcoupling]
    _ = prior := S.map_fst_joint prior

/-- Full information assigns the point belief at the announced state. -/
theorem fullInformation_isPosteriorAssignment
    (prior : PMF State) :
    (fullInformation State).IsPosteriorAssignment prior PMF.pure := by
  have hmarginal :
      (fullInformation State).messageMarginal prior = prior := by
    rw [messageMarginal_eq_bind]
    exact PMF.bind_pure prior
  intro state message
  rw [joint_apply, hmarginal]
  simp only [fullInformation_kernel]
  by_cases heq : state = message
  · subst message
    simp [PMF.pure_apply]
  · simp [PMF.pure_apply, heq, Ne.symm heq]

/-- Full information induces full revelation. -/
theorem inducedPosteriorLaw_fullInformation (prior : PMF State) :
    (fullInformation State).inducedPosteriorLaw prior PMF.pure =
      PosteriorLaw.fullRevelation prior := by
  unfold inducedPosteriorLaw PosteriorLaw.fullRevelation
  congr 1
  rw [messageMarginal_eq_bind]
  exact PMF.bind_pure prior

/-! ## Splitting a Bayes-plausible posterior law -/

/-- Disintegrate the canonical coupling along the state coordinate. The
original posterior law is a harmless total fallback at null state fibers. -/
def fromPosteriorLaw (law : PosteriorLaw State) :
    SignalStructure State (PMF State) where
  kernel state := by
    classical
    exact if hs : state ∈ (law.coupling.map Prod.fst).support then
      (fiberPosterior law.coupling Prod.fst state hs).map Prod.snd
    else law

/-- The resulting joint law reconstructs the canonical coupling. -/
theorem joint_fromPosteriorLaw (prior : PMF State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    (fromPosteriorLaw law).joint prior = law.coupling := by
  classical
  let μ := law.coupling
  have hmarginal : μ.map Prod.fst = prior :=
    law.map_fst_coupling.trans hlaw
  have hfiber (state : State) (hs : state ∈ (μ.map Prod.fst).support) :
      ((fiberPosterior μ Prod.fst state hs).map Prod.snd).map
          (fun belief => (state, belief)) =
        fiberPosterior μ Prod.fst state hs := by
    rw [PMF.map_comp]
    let conditioned := fiberPosterior μ Prod.fst state hs
    have hpoint : ∀ pair ∈ conditioned.support,
        ((fun belief => (state, belief)) ∘ Prod.snd) pair = pair := by
      intro pair hpair
      have hmem : pair ∈ {pair | pair.1 = state} ∩ μ.support := by
        simpa only [conditioned, fiberPosterior_support] using hpair
      rcases pair with ⟨pairState, belief⟩
      have hstate : pairState = state := hmem.1
      simp only [Function.comp_apply] at hstate ⊢
      subst pairState
      rfl
    calc
      conditioned.map ((fun belief => (state, belief)) ∘ Prod.snd) =
          conditioned.map id := by
        rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
        apply bind_congr_on_support
        intro pair hpair
        exact congrArg PMF.pure (hpoint pair hpair)
      _ = conditioned := PMF.map_id _
  let total : State → PMF (State × PMF State) := fun state =>
    if hs : state ∈ (μ.map Prod.fst).support then
      fiberPosterior μ Prod.fst state hs
    else μ
  unfold SignalStructure.joint bindPairLaw fromPosteriorLaw
  rw [← hmarginal]
  calc
    (μ.map Prod.fst).bind (fun state =>
        ((if hs : state ∈ (μ.map Prod.fst).support then
          (fiberPosterior μ Prod.fst state hs).map Prod.snd
        else law).map fun belief => (state, belief))) =
      (μ.map Prod.fst).bind total := by
      apply bind_congr_on_support
      intro state hs
      simp only [total, dite_eq_left hs]
      exact hfiber state hs
    _ = (μ.map Prod.fst).bindOnSupport
        (fun state hs => fiberPosterior μ Prod.fst state hs) := by
      symm
      apply bindOnSupport_eq_bind_of_eq_on_support
      intro state hs
      simp only [total, dite_eq_left hs]
    _ = μ := fiberPosterior_reconstruct μ Prod.fst

/-- The messages generated by splitting have the requested posterior law. -/
theorem messageMarginal_fromPosteriorLaw (prior : PMF State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    (fromPosteriorLaw law).messageMarginal prior = law := by
  unfold messageMarginal
  rw [joint_fromPosteriorLaw prior law hlaw, law.map_snd_coupling]

/-- Announcing each disintegrated belief is a valid total assignment. -/
theorem fromPosteriorLaw_isPosteriorAssignment
    (prior : PMF State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    (fromPosteriorLaw law).IsPosteriorAssignment prior id := by
  intro state belief
  rw [joint_fromPosteriorLaw prior law hlaw,
    messageMarginal_fromPosteriorLaw prior law hlaw,
    law.coupling_apply]
  rfl

/-- Splitting induces the original Bayes-plausible law. -/
theorem inducedPosteriorLaw_fromPosteriorLaw (prior : PMF State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    (fromPosteriorLaw law).inducedPosteriorLaw prior id = law := by
  unfold inducedPosteriorLaw
  rw [messageMarginal_fromPosteriorLaw prior law hlaw, PMF.map_id]

/-- Every Bayes-plausible posterior law is implemented by a signal. -/
theorem exists_signalStructure_of_isBayesPlausible
    (prior : PMF State)
    (law : PosteriorLaw State) (hlaw : law.IsBayesPlausible prior) :
    ∃ (signal : SignalStructure State (PMF State))
      (posterior : PMF State → PMF State),
      signal.IsPosteriorAssignment prior posterior ∧
        signal.inducedPosteriorLaw prior posterior = law := by
  exact ⟨fromPosteriorLaw law, id,
    fromPosteriorLaw_isPosteriorAssignment prior law hlaw,
    inducedPosteriorLaw_fromPosteriorLaw prior law hlaw⟩

end SignalStructure

end GameTheory
