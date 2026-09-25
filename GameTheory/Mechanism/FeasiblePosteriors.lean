/-
# Feasible posterior laws

A law over posterior beliefs is feasible exactly when its mean belief is the
prior. Both levels are ordinary PMFs, so infinite-support splittings are
included without a separate finite probability type.
-/

import GameTheory.Math.Probability.Joint

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe us

/-- A law over posterior beliefs. -/
abbrev PosteriorLaw (State : Type us) := PMF (PMF State)

namespace PosteriorLaw

variable {State : Type us}

/-- The predictive law obtained by averaging posterior beliefs. -/
def mean (law : PosteriorLaw State) : PMF State :=
  law.bind id

/-- Pointwise mass in the mean posterior. -/
theorem mean_apply (law : PosteriorLaw State) (state : State) :
    law.mean state = ∑' belief, law belief * belief state := by
  rw [mean, PMF.bind_apply]
  rfl

/-- Bayes plausibility: the mean posterior equals the prior. -/
def IsBayesPlausible (prior : PMF State) (law : PosteriorLaw State) : Prop :=
  law.mean = prior

/-- Draw a belief, then a state from it, recording both. -/
def coupling (law : PosteriorLaw State) : PMF (State × PMF State) :=
  (bindPairLaw law id).map Prod.swap

/-- Canonical coupling masses factor into belief-law and state masses. -/
theorem coupling_apply (law : PosteriorLaw State)
    (state : State) (belief : PMF State) :
    law.coupling (state, belief) = law belief * belief state := by
  exact bindPairLaw_swap_apply law id state belief

/-- The belief marginal of the canonical coupling is the original law. -/
theorem map_snd_coupling (law : PosteriorLaw State) :
    law.coupling.map Prod.snd = law := by
  rw [coupling, PMF.map_comp]
  rw [show Prod.snd ∘ Prod.swap = Prod.fst from rfl,
    bindPairLaw_map_fst]

/-- The state marginal of the canonical coupling is the mean posterior. -/
theorem map_fst_coupling (law : PosteriorLaw State) :
    law.coupling.map Prod.fst = law.mean := by
  rw [coupling, PMF.map_comp]
  rw [show Prod.fst ∘ Prod.swap = Prod.snd from rfl,
    bindPairLaw_map_snd]
  rfl

/-- Feasibility through the canonical coupling is Bayes plausibility. -/
theorem isBayesPlausible_iff_map_fst_coupling
    (prior : PMF State) (law : PosteriorLaw State) :
    law.IsBayesPlausible prior ↔ law.coupling.map Prod.fst = prior := by
  rw [law.map_fst_coupling]
  rfl

/-- The posterior law that reveals no information. -/
def uninformative (prior : PMF State) : PosteriorLaw State :=
  PMF.pure prior

/-- The posterior law that reveals the realized state. -/
def fullRevelation (prior : PMF State) : PosteriorLaw State :=
  prior.map PMF.pure

@[simp]
theorem coupling_pure (belief : PMF State) :
    coupling (PMF.pure belief : PosteriorLaw State) =
      belief.map fun state => (state, belief) := by
  unfold coupling bindPairLaw
  rw [PMF.pure_bind, PMF.map_comp]
  rfl

@[simp]
theorem coupling_fullRevelation (prior : PMF State) :
    coupling (fullRevelation prior) =
      prior.map fun state => (state, PMF.pure state) := by
  unfold coupling fullRevelation bindPairLaw
  rw [PMF.bind_map, PMF.map_bind]
  rw [← PMF.bind_pure_comp]
  apply congrArg (fun k => prior.bind k)
  funext state
  simp [PMF.pure_map]

theorem isBayesPlausible_uninformative (prior : PMF State) :
    (uninformative prior).IsBayesPlausible prior := by
  simp [IsBayesPlausible, mean, uninformative]

theorem isBayesPlausible_fullRevelation (prior : PMF State) :
    (fullRevelation prior).IsBayesPlausible prior := by
  simp [IsBayesPlausible, mean, fullRevelation, PMF.bind_map]

/-- A mixture of posterior laws with the same mean remains plausible. -/
theorem isBayesPlausible_bind {Index : Type*} (prior : PMF State)
    (selector : PMF Index) (law : Index → PosteriorLaw State)
    (h : ∀ index, (law index).IsBayesPlausible prior) :
    IsBayesPlausible prior (selector.bind law) := by
  unfold IsBayesPlausible mean
  rw [PMF.bind_bind]
  calc
    selector.bind (fun index => (law index).bind id) =
        selector.bind (fun _ => prior) := by
      congr 1
      funext index
      exact h index
    _ = prior := PMF.bind_const selector prior

/-- Splitting each belief into a same-mean law preserves plausibility. -/
theorem isBayesPlausible_bind_pointwise (prior : PMF State)
    (law : PosteriorLaw State) (split : PMF State → PosteriorLaw State)
    (hlaw : law.IsBayesPlausible prior)
    (hsplit : ∀ belief, (split belief).IsBayesPlausible belief) :
    IsBayesPlausible prior (law.bind split) := by
  unfold IsBayesPlausible mean
  rw [PMF.bind_bind]
  calc
    law.bind (fun belief => (split belief).bind id) = law.bind id := by
      congr 1
      funext belief
      exact hsplit belief
    _ = prior := hlaw

end PosteriorLaw

end GameTheory
