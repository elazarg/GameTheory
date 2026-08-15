/-
# EXP-094: high-probability equilibrium certification

This hostile probability consumer proves a tail bound through the public
finite-law algebra and applies it to canonical mixed improvement and
approximate Nash.  It must not inspect the underlying PMF representation or
introduce another probability, regret, or equilibrium definition.
-/

import GameTheory.Core.MixedImprovement
import GameTheory.Mechanism.FeasiblePosteriors
import GameTheory.Math.Probability.Bounds

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.ProbabilityTailAdequacy

open GameTheory.Math.Probability

universe uι us uo

/-! ## Probability to canonical approximate equilibrium -/

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Small expected aggregate positive deviation gain gives a high-probability
certificate: sampling a profile that fails canonical `IsεNash` has probability
at most `δ / ε`. -/
theorem prob_not_isεNash_le (G : UtilityGame.{uι, us, uo} ι)
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (law : FinDist (Profile G.form.sig.mixed)) {ε δ : ℝ} (hε : 0 < ε)
    (hexpect : law.expect G.mixedImprovement ≤ δ) :
    law.probOf {profile | ¬ IsεNash G.form.mixed G.utility ε profile} ≤ δ / ε := by
  calc
    law.probOf {profile | ¬ IsεNash G.form.mixed G.utility ε profile} ≤
        law.expect G.mixedImprovement / ε := by
      apply FinDist.probOf_le_expect_div law
          {profile | ¬ IsεNash G.form.mixed G.utility ε profile}
          G.mixedImprovement hε
      · intro profile _
        exact G.mixedImprovement_nonneg profile
      · intro profile _ hnotNash
        have hnotle : ¬ G.mixedImprovement profile ≤ ε := by
          intro himprovement
          exact hnotNash (G.isεNash_of_mixedImprovement_le himprovement)
        exact (not_le.mp hnotle).le
    _ ≤ δ / ε := (div_le_div_iff_of_pos_right hε).2 hexpect

/-! ## A concrete probability-to-equilibrium consumer -/

/-- A one-player decision problem is enough to make the probabilistic seam
hostile: the law below ranges over mixed profiles, not realized actions. -/
@[reducible]
def choiceSignature : GameSignature Unit where
  Strategy _ := Bool
  Outcome := Bool

@[reducible]
def choiceForm : GameForm Unit :=
  GameForm.deterministic choiceSignature fun profile => profile ()

def choiceUtility (outcome : Bool) (_who : Unit) : ℝ :=
  if outcome then 2 else 0

@[reducible]
def choiceGame : UtilityGame Unit where
  form := choiceForm
  utility := choiceUtility

def optimalPure : Profile choiceGame.form.sig := fun _ => true

def exploitablePure : Profile choiceGame.form.sig := fun _ => false

def optimalMixed : Profile choiceGame.form.sig.mixed :=
  choiceGame.form.purify optimalPure

def exploitableMixed : Profile choiceGame.form.sig.mixed :=
  choiceGame.form.purify exploitablePure

theorem optimalPure_isNash :
    IsNash choiceGame.form (euPreference choiceGame.utility) optimalPure := by
  rw [isNash_iff]
  intro who replacement
  rcases who with ⟨⟩
  rw [euPreference_apply]
  cases replacement <;>
    norm_num [choiceGame, choiceForm, choiceUtility, optimalPure,
      expectedUtility, Profile.update]

theorem optimalMixed_isNash :
    IsNash choiceGame.form.mixed (euPreference choiceGame.utility) optimalMixed :=
  optimalPure_isNash.purify

theorem optimalMixed_improvement :
    choiceGame.mixedImprovement optimalMixed = 0 :=
  (choiceGame.isNash_iff_mixedImprovement_eq_zero optimalMixed).1
    optimalMixed_isNash

theorem choice_mixedGain_purify (profile : Profile choiceGame.form.sig)
    (action : Bool) :
    choiceGame.mixedGain (choiceGame.form.purify profile) () action =
      choiceUtility action () - choiceUtility (profile ()) () := by
  unfold UtilityGame.mixedGain
  rw [purify_update, GameForm.mixed_play_purify,
    GameForm.mixed_play_purify]
  norm_num [choiceGame, choiceForm, choiceUtility, expectedUtility,
    Profile.update]

theorem exploitableMixed_improvement :
    choiceGame.mixedImprovement exploitableMixed = 2 := by
  rw [UtilityGame.mixedImprovement, Fintype.sum_unique, Fintype.sum_bool,
    exploitableMixed, choice_mixedGain_purify, choice_mixedGain_purify]
  norm_num [exploitablePure, choiceUtility]

theorem exploitableMixed_not_isOneNash :
    ¬ IsεNash choiceGame.form.mixed choiceGame.utility 1 exploitableMixed := by
  intro h
  have hdeviation :=
    (isεNash_iff choiceGame.form.mixed choiceGame.utility).1 h ()
      (FinDist.pure true)
  rw [exploitableMixed, purify_update, GameForm.mixed_play_purify,
    GameForm.mixed_play_purify] at hdeviation
  norm_num [choiceGame, choiceForm, choiceUtility, exploitablePure,
    expectedUtility, Profile.update] at hdeviation

/-- The sampling procedure emits an exploitable mixed profile one quarter of
the time and the exact equilibrium otherwise. -/
def sampledMixedProfile : FinDist (Profile choiceGame.form.sig.mixed) :=
  FinDist.mix (1 / 4) (by norm_num) (by norm_num)
    (FinDist.pure exploitableMixed) (FinDist.pure optimalMixed)

theorem sampled_expected_improvement :
    sampledMixedProfile.expect choiceGame.mixedImprovement = 1 / 2 := by
  rw [sampledMixedProfile, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.expect_pure, exploitableMixed_improvement,
    optimalMixed_improvement]
  norm_num

/-- The generic theorem now certifies an actual random mixed-profile output.
Its bad event uses canonical `IsεNash` directly. -/
theorem sampled_failure_probability_le_half :
    sampledMixedProfile.probOf
        {profile | ¬ IsεNash choiceGame.form.mixed choiceGame.utility 1 profile} ≤
      1 / 2 := by
  simpa using
    prob_not_isεNash_le choiceGame sampledMixedProfile
      (ε := 1) (δ := 1 / 2) (by norm_num)
      (le_of_eq sampled_expected_improvement)

/-- The bounded failure event is genuinely inhabited with positive mass. -/
theorem sampled_failure_probability_pos :
    0 < sampledMixedProfile.probOf
        {profile | ¬ IsεNash choiceGame.form.mixed choiceGame.utility 1 profile} := by
  apply FinDist.probOf_pos
  refine ⟨exploitableMixed, exploitableMixed_not_isOneNash, ?_⟩
  apply FinDist.mem_support_mix_left (1 / 4) (by norm_num) (by norm_num) (by norm_num)
  exact FinDist.mem_support_pure.mpr rfl

/-! ## Independent reuse: posterior concentration -/

/-- Bayes plausibility and the same event bound limit how often posteriors can
assign a rare state a large probability.  This consumer is independent of
games, deviations, and equilibrium. -/
theorem posterior_state_tail_le {State : Type*} (prior : FinDist State)
    (law : PosteriorLaw State) (hplausible : law.IsBayesPlausible prior)
    (state : State) {threshold : ℝ} (hthreshold : 0 < threshold) :
    law.probOf {belief | threshold ≤ belief.prob state} ≤
      prior.prob state / threshold := by
  calc
    law.probOf {belief | threshold ≤ belief.prob state} ≤
        law.expect (fun belief => belief.prob state) / threshold := by
      apply FinDist.markov_inequality law
          (fun belief => belief.prob state) hthreshold
      · intro belief _
        exact belief.prob_nonneg state
    _ = prior.prob state / threshold := by
      rw [← law.prob_mean, hplausible]

def fairPrior : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def revealingPosteriorLaw : PosteriorLaw Bool :=
  PosteriorLaw.fullRevelation fairPrior

/-- Under full revelation of a fair state, posteriors assigning at least
three-quarters to `true` occur with probability at most two-thirds. -/
theorem revealing_true_tail_le_two_thirds :
    revealingPosteriorLaw.probOf {belief | 3 / 4 ≤ belief.prob true} ≤ 2 / 3 := by
  have h := posterior_state_tail_le fairPrior revealingPosteriorLaw
    (PosteriorLaw.isBayesPlausible_fullRevelation fairPrior) true
    (threshold := 3 / 4) (by norm_num)
  norm_num [fairPrior, FinDist.prob_mix, FinDist.prob_pure_eq_ite] at h ⊢
  exact h

end GameTheory.Experimental.PostArchitecture.ProbabilityTailAdequacy
