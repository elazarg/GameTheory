/-
# Feasible joint posterior laws

A joint posterior law records one finite-support belief per player.  Feasibility
requires a common coupling whose state and belief-profile marginals are right
and whose projection to each player is that player's canonical posterior
coupling.  Marginal Bayes plausibility is necessary, not asserted sufficient.
-/

import GameTheory.Mechanism.FeasiblePosteriors

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe up us

/-- A finite-support law over profiles of posterior beliefs. -/
abbrev JointPosteriorLaw (Player : Type up) (State : Type us) :=
  FinDist (Player → FinDist State)

namespace JointPosteriorLaw

variable {Player : Type up} {State : Type us}

/-- One player's marginal law over posterior beliefs. -/
def agentMarginal (law : JointPosteriorLaw Player State) (who : Player) :
    PosteriorLaw State :=
  law.map fun profile => profile who

/-- Every player's marginal posterior law has the common prior as its mean. -/
def IsBayesPlausible (prior : FinDist State)
    (law : JointPosteriorLaw Player State) : Prop :=
  ∀ who, (law.agentMarginal who).IsBayesPlausible prior

/-- A common-prior coupling realizes the joint belief profile and agrees with
each player's canonical posterior coupling. -/
def IsFeasible (prior : FinDist State)
    (law : JointPosteriorLaw Player State) : Prop :=
  ∃ coupling : FinDist (State × (Player → FinDist State)),
    coupling.map Prod.fst = prior ∧
      coupling.map Prod.snd = law ∧
      ∀ who,
        coupling.map (fun outcome => (outcome.1, outcome.2 who)) =
          (law.agentMarginal who).coupling

/-- Feasibility forces each player's marginal posterior law to be Bayes
plausible. -/
theorem IsFeasible.agentMarginal_isBayesPlausible
    {prior : FinDist State} {law : JointPosteriorLaw Player State}
    (hfeasible : law.IsFeasible prior) (who : Player) :
    (law.agentMarginal who).IsBayesPlausible prior := by
  obtain ⟨coupling, hstate, _, hconsistent⟩ := hfeasible
  unfold PosteriorLaw.IsBayesPlausible
  rw [← PosteriorLaw.map_fst_coupling (law.agentMarginal who),
    ← hconsistent who, FinDist.map_comp,
    show Prod.fst ∘
        (fun outcome : State × (Player → FinDist State) =>
          (outcome.1, outcome.2 who)) = Prod.fst from rfl]
  exact hstate

/-- Every marginal of a feasible joint law is Bayes plausible. -/
theorem IsFeasible.isBayesPlausible
    {prior : FinDist State} {law : JointPosteriorLaw Player State}
    (hfeasible : law.IsFeasible prior) :
    law.IsBayesPlausible prior :=
  fun who => hfeasible.agentMarginal_isBayesPlausible who

/-- The joint posterior law in which nobody learns the state. -/
def uninformative (prior : FinDist State) : JointPosteriorLaw Player State :=
  FinDist.pure fun _ => prior

/-- The joint posterior law in which every player learns the state. -/
def fullRevelation (prior : FinDist State) : JointPosteriorLaw Player State :=
  prior.map fun state _ => FinDist.pure state

/-- The uninformative joint posterior law is feasible. -/
theorem isFeasible_uninformative (prior : FinDist State) :
    (uninformative (Player := Player) prior).IsFeasible prior := by
  refine ⟨prior.map (fun state => (state, fun _ => prior)), ?_, ?_, fun who => ?_⟩
  · rw [FinDist.map_comp,
      show Prod.fst ∘ (fun state => (state, fun _ : Player => prior)) = id from rfl,
      FinDist.map_id]
  · rw [FinDist.map_comp,
      show Prod.snd ∘ (fun state => (state, fun _ : Player => prior)) =
        (fun _ => (fun _ : Player => prior)) from rfl,
      FinDist.map_const]
    rfl
  · have hmarginal :
        (uninformative (Player := Player) prior).agentMarginal who =
          FinDist.pure prior := by
        simp [agentMarginal, uninformative]
    rw [hmarginal, PosteriorLaw.coupling_pure, FinDist.map_comp]
    rfl

/-- Common full revelation is jointly feasible. -/
theorem isFeasible_fullRevelation (prior : FinDist State) :
    (fullRevelation (Player := Player) prior).IsFeasible prior := by
  refine ⟨prior.map (fun state => (state, fun _ => FinDist.pure state)),
    ?_, ?_, fun who => ?_⟩
  · rw [FinDist.map_comp,
      show Prod.fst ∘
          (fun state => (state, fun _ : Player => FinDist.pure state)) = id from rfl,
      FinDist.map_id]
  · rw [FinDist.map_comp]
    rfl
  · have hmarginal :
        (fullRevelation (Player := Player) prior).agentMarginal who =
          PosteriorLaw.fullRevelation prior := by
        unfold agentMarginal fullRevelation PosteriorLaw.fullRevelation
        rw [FinDist.map_comp]
        rfl
    rw [hmarginal, PosteriorLaw.coupling_fullRevelation, FinDist.map_comp]
    rfl

end JointPosteriorLaw

end GameTheory
