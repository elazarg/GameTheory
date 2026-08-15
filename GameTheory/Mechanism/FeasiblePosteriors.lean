/-
# Feasible finite posterior laws

A law over posterior beliefs is feasible exactly when its mean belief is the
prior.  Both levels use the canonical finite-support distribution, and the
canonical coupling draws a posterior and then a state from that posterior.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe us

/-- A finite-support law over finite-support posterior beliefs. -/
abbrev PosteriorLaw (State : Type us) := FinDist (FinDist State)

namespace PosteriorLaw

variable {State : Type us}

/-- The predictive distribution obtained by averaging posterior beliefs. -/
def mean (law : PosteriorLaw State) : FinDist State :=
  law.bind id

/-- Pointwise mass in the mean posterior. -/
theorem prob_mean (law : PosteriorLaw State) (state : State) :
    law.mean.prob state = law.expect fun belief => belief.prob state := by
  exact FinDist.prob_bind law id state

/-- Bayes plausibility: the mean posterior equals the prior. -/
def IsBayesPlausible (prior : FinDist State) (law : PosteriorLaw State) : Prop :=
  law.mean = prior

/-- Draw a posterior and then a state from it, recording both. -/
def coupling (law : PosteriorLaw State) : FinDist (State × FinDist State) :=
  law.bind fun belief => belief.map fun state => (state, belief)

/-- Canonical-coupling masses factor into the posterior-law mass and the
posterior state mass. -/
theorem prob_coupling [DecidableEq State] (law : PosteriorLaw State)
    (state : State) (belief : FinDist State) :
    law.coupling.prob (state, belief) =
      law.prob belief * belief.prob state := by
  classical
  rw [coupling, FinDist.prob_bind]
  rw [show
    (fun belief' =>
      (belief'.map fun state' => (state', belief')).prob (state, belief)) =
      fun belief' => if belief = belief' then belief.prob state else 0 by
    funext belief'
    by_cases hbelief : belief = belief'
    · subst belief'
      rw [if_pos rfl]
      exact FinDist.prob_map_of_injective
        (fun state' => (state', belief))
        (fun _ _ h => (Prod.mk.inj h).1) belief state
    · rw [if_neg hbelief, FinDist.prob_map]
      calc
        belief'.expect
              (fun state' => if (state, belief) = (state', belief') then 1 else 0) =
            belief'.expect (fun _ => 0) := by
          apply FinDist.expect_congr
          intro state' _
          rw [if_neg fun hpair => hbelief (congrArg Prod.snd hpair)]
        _ = 0 := FinDist.expect_const belief' 0]
  exact FinDist.expect_ite_eq law belief (belief.prob state)

/-- The posterior marginal of the canonical coupling is the original law. -/
theorem map_snd_coupling (law : PosteriorLaw State) :
    law.coupling.map Prod.snd = law := by
  unfold coupling
  rw [FinDist.map_bind]
  calc
    law.bind
          (fun belief =>
            (belief.map fun state => (state, belief)).map Prod.snd) =
        law.bind FinDist.pure := by
      apply FinDist.bind_congr
      intro belief _
      rw [FinDist.map_comp,
        show Prod.snd ∘ (fun state => (state, belief)) =
          (fun _ => belief) from rfl,
        FinDist.map_const]
    _ = law := FinDist.bind_pure law

/-- The state marginal of the canonical coupling is the mean posterior. -/
theorem map_fst_coupling (law : PosteriorLaw State) :
    law.coupling.map Prod.fst = law.mean := by
  unfold coupling mean
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro belief _
  rw [FinDist.map_comp,
    show Prod.fst ∘ (fun state => (state, belief)) = id from rfl,
    FinDist.map_id]
  rfl

/-- Feasibility through the canonical coupling is exactly Bayes
plausibility. -/
theorem isBayesPlausible_iff_map_fst_coupling
    (prior : FinDist State) (law : PosteriorLaw State) :
    law.IsBayesPlausible prior ↔ law.coupling.map Prod.fst = prior := by
  rw [law.map_fst_coupling]
  rfl

/-- The posterior law that reveals no information. -/
def uninformative (prior : FinDist State) : PosteriorLaw State :=
  FinDist.pure prior

/-- The posterior law that reveals the realized state. -/
def fullRevelation (prior : FinDist State) : PosteriorLaw State :=
  prior.map FinDist.pure

@[simp]
theorem coupling_pure (belief : FinDist State) :
    coupling (FinDist.pure belief : PosteriorLaw State) =
      belief.map fun state => (state, belief) := by
  unfold coupling
  rw [FinDist.pure_bind]

@[simp]
theorem coupling_fullRevelation (prior : FinDist State) :
    coupling (fullRevelation prior) =
      prior.map fun state => (state, FinDist.pure state) := by
  unfold coupling fullRevelation
  rw [FinDist.bind_map]
  simp only [FinDist.map_pure]
  exact (FinDist.map_eq_bind _ prior).symm

theorem isBayesPlausible_uninformative (prior : FinDist State) :
    (uninformative prior).IsBayesPlausible prior := by
  simp [IsBayesPlausible, mean, uninformative]

theorem isBayesPlausible_fullRevelation (prior : FinDist State) :
    (fullRevelation prior).IsBayesPlausible prior := by
  simp [IsBayesPlausible, mean, fullRevelation]

/-- Randomizing among posterior laws with the same mean preserves Bayes
plausibility. -/
theorem isBayesPlausible_bind {Index : Type*} (prior : FinDist State)
    (selector : FinDist Index) (law : Index → PosteriorLaw State)
    (h : ∀ index, (law index).IsBayesPlausible prior) :
    IsBayesPlausible prior (selector.bind law) := by
  unfold IsBayesPlausible mean
  rw [FinDist.bind_bind]
  calc
    selector.bind (fun index => (law index).bind id) =
        selector.bind (fun _ => prior) := by
      apply FinDist.bind_congr
      intro index _
      simpa [IsBayesPlausible, mean] using h index
    _ = prior := FinDist.bind_const selector prior

/-- Sequentially splitting every posterior into a law with the same mean
preserves Bayes plausibility. -/
theorem isBayesPlausible_bind_pointwise (prior : FinDist State)
    (law : PosteriorLaw State) (split : FinDist State → PosteriorLaw State)
    (hlaw : law.IsBayesPlausible prior)
    (hsplit : ∀ belief, (split belief).IsBayesPlausible belief) :
    IsBayesPlausible prior (law.bind split) := by
  unfold IsBayesPlausible mean
  rw [FinDist.bind_bind]
  calc
    law.bind (fun belief => (split belief).bind id) = law.bind id := by
      apply FinDist.bind_congr
      intro belief _
      simpa [IsBayesPlausible, mean] using hsplit belief
    _ = prior := by simpa [IsBayesPlausible, mean] using hlaw

end PosteriorLaw

end GameTheory
