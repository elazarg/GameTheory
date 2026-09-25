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
import GameTheory.Math.Probability.Uniform

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
    (law : PMF (Profile G.form.sig.mixed)) (score : Profile G.form.sig.mixed → ℝ)
    {ε δ : ℝ} (hε : 0 < ε)
    (hscore : PayoffIntegrable law score)
    (hpure : ∀ profile ∈ law.support, ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play (Profile.update profile who (PMF.pure action))))
    (hscore_eq : ∀ profile (hs : profile ∈ law.support),
      score profile = G.mixedImprovement profile (hpure profile hs))
    (hexpect : expect law score hscore ≤ δ) :
    (law.toOuterMeasure
      {profile | ¬ IsεNash G.form.mixed G.utility ε profile}).toReal ≤
      δ / ε := by
  calc
    (law.toOuterMeasure
      {profile | ¬ IsεNash G.form.mixed G.utility ε profile}).toReal ≤
        expect law score hscore / ε := by
      apply eventMass_toReal_le_expect_div law
          {profile | ¬ IsεNash G.form.mixed G.utility ε profile}
          score hε hscore
      · intro profile hs
        rw [hscore_eq profile hs]
        exact G.mixedImprovement_nonneg profile (hpure profile hs)
      · intro profile hs hnotNash
        rw [hscore_eq profile hs]
        have hnotle : ¬ G.mixedImprovement profile (hpure profile hs) ≤ ε := by
          intro himprovement
          exact hnotNash (G.isεNash_of_mixedImprovement_le
            (hpure profile hs) himprovement)
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

/-- The realized pure replacement law integrates this finite choice payoff. -/
theorem choiceGuard (profile : Profile choiceGame.form.sig.mixed)
    (who : Unit) (action : Bool) :
    UtilityIntegrable choiceGame.utility who
      (choiceGame.form.mixed.play
        (Profile.update profile who (PMF.pure action))) :=
  payoffIntegrable_of_finite _ _

/-- Every mixed profile has an integrable payoff in the finite choice form. -/
theorem choiceBaseGuard (profile : Profile choiceGame.form.sig.mixed)
    (who : Unit) :
    UtilityIntegrable choiceGame.utility who
      (choiceGame.form.mixed.play profile) :=
  payoffIntegrable_of_finite _ _

/-- The canonical mixed-improvement score for this finite choice fixture. -/
def choiceScore (profile : Profile choiceGame.form.sig.mixed) : ℝ :=
  choiceGame.mixedImprovement profile (choiceGuard profile)

theorem optimalPure_isNash :
    IsNash choiceGame.form (euPreference choiceGame.utility) optimalPure := by
  rw [isNash_iff]
  intro who replacement
  rcases who with ⟨⟩
  rw [euPreference_apply]
  refine ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _, ?_⟩
  cases replacement <;>
    norm_num [choiceGame, choiceForm, choiceUtility, optimalPure,
      expectedUtility_pure, Profile.update]

theorem optimalMixed_isNash :
    IsNash choiceGame.form.mixed (euPreference choiceGame.utility) optimalMixed :=
  optimalPure_isNash.purify_of_finite

theorem optimalMixed_improvement :
    choiceScore optimalMixed = 0 :=
  (choiceGame.isNash_iff_mixedImprovement_eq_zero optimalMixed
    (choiceGuard optimalMixed)).1
    optimalMixed_isNash

theorem choice_mixedGain_purify (profile : Profile choiceGame.form.sig)
    (action : Bool) :
    choiceGame.mixedGain (choiceGame.form.purify profile) () action
      (choiceBaseGuard (choiceGame.form.purify profile) ())
      (choiceGuard (choiceGame.form.purify profile) () action) =
      choiceUtility action () - choiceUtility (profile ()) () := by
  unfold UtilityGame.mixedGain
  have hdev : choiceGame.form.mixed.play
      (Profile.update (choiceGame.form.purify profile) () (PMF.pure action)) =
      PMF.pure action := by
    rw [purify_update, GameForm.mixed_play_purify]
    simp [choiceGame, choiceForm, Profile.update]
  have hbase : choiceGame.form.mixed.play (choiceGame.form.purify profile) =
      PMF.pure (profile ()) := by
    rw [GameForm.mixed_play_purify]
  have hdevEU := expectedUtility_congr_law choiceGame.utility () hdev
    (choiceGuard (choiceGame.form.purify profile) () action)
    (payoffIntegrable_pure action (fun outcome => choiceGame.utility outcome ()))
  have hbaseEU := expectedUtility_congr_law choiceGame.utility () hbase
    (choiceBaseGuard (choiceGame.form.purify profile) ())
    (payoffIntegrable_pure (profile ()) (fun outcome => choiceGame.utility outcome ()))
  rw [hdevEU, hbaseEU]
  simp [choiceUtility]

theorem exploitableMixed_improvement :
    choiceScore exploitableMixed = 2 := by
  unfold choiceScore
  simp only [UtilityGame.mixedImprovement, Fintype.sum_unique,
    Fintype.sum_bool]
  have htrue := choice_mixedGain_purify exploitablePure true
  have hfalse := choice_mixedGain_purify exploitablePure false
  simp only [exploitableMixed] at *
  rw [htrue, hfalse]
  norm_num [exploitablePure, choiceUtility]

theorem exploitableMixed_not_isOneNash :
    ¬ IsεNash choiceGame.form.mixed choiceGame.utility 1 exploitableMixed := by
  intro h
  have hdeviation :=
    (isεNash_iff choiceGame.form.mixed choiceGame.utility).1 h ()
      (PMF.pure true)
  rcases hdeviation with ⟨_, _, hdeviation⟩
  have hgain := choice_mixedGain_purify exploitablePure true
  have hle : choiceGame.mixedGain exploitableMixed () true
      (choiceBaseGuard exploitableMixed ())
      (choiceGuard exploitableMixed () true) ≤ 1 := by
    apply (sub_le_iff_le_add).2
    simpa only [UtilityGame.mixedGain, add_comm] using hdeviation
  simp only [exploitableMixed] at hle
  rw [hgain] at hle
  norm_num [choiceUtility, exploitablePure] at hle

/-- The sampling procedure emits an exploitable mixed profile one quarter of
the time and the exact equilibrium otherwise. -/
def sampledMixedProfile : PMF (Profile choiceGame.form.sig.mixed) :=
  (PMF.uniformOfFintype (Fin 4)).map fun index =>
    if index = 0 then exploitableMixed else optimalMixed

/-- The finite sampled-profile law integrates its improvement score. -/
theorem sampledGuard : PayoffIntegrable sampledMixedProfile choiceScore := by
  apply payoffIntegrable_of_finite_support
  rw [sampledMixedProfile, PMF.support_map]
  exact (Set.toFinite _).image _

theorem sampled_expected_improvement :
    expect sampledMixedProfile choiceScore sampledGuard = 1 / 2 := by
  let relabel : Fin 4 → Profile choiceGame.form.sig.mixed := fun index =>
    if index = 0 then exploitableMixed else optimalMixed
  have hsource : PayoffIntegrable (PMF.uniformOfFintype (Fin 4))
      (choiceScore ∘ relabel) := payoffIntegrable_of_finite _ _
  calc
    expect sampledMixedProfile choiceScore sampledGuard =
        expect (PMF.uniformOfFintype (Fin 4))
          (choiceScore ∘ relabel) hsource := by
      exact expect_map relabel (PMF.uniformOfFintype (Fin 4))
        choiceScore hsource sampledGuard
    _ = 1 / 2 := by
      rw [expect_uniformFin]
      norm_num [relabel, Function.comp_def, Fin.sum_univ_succ,
        exploitableMixed_improvement, optimalMixed_improvement]

/-- The generic theorem now certifies an actual random mixed-profile output.
Its bad event uses canonical `IsεNash` directly. -/
theorem sampled_failure_probability_le_half :
    (sampledMixedProfile.toOuterMeasure
        {profile | ¬ IsεNash choiceGame.form.mixed choiceGame.utility 1 profile}).toReal ≤
      1 / 2 := by
  simpa using
    prob_not_isεNash_le choiceGame sampledMixedProfile choiceScore
      (ε := 1) (δ := 1 / 2) (by norm_num) sampledGuard
      (fun profile _ => choiceGuard profile)
      (fun profile _ => rfl)
      (le_of_eq sampled_expected_improvement)

/-- The bounded failure event is genuinely inhabited with positive mass. -/
theorem sampled_failure_probability_pos :
    0 < (sampledMixedProfile.toOuterMeasure
        {profile | ¬ IsεNash choiceGame.form.mixed choiceGame.utility 1 profile}).toReal := by
  let event : Set (Profile choiceGame.form.sig.mixed) :=
    {profile | ¬ IsεNash choiceGame.form.mixed choiceGame.utility 1 profile}
  have hsupport : exploitableMixed ∈ sampledMixedProfile.support := by
    rw [sampledMixedProfile, PMF.support_map]
    exact ⟨0, by simp, by simp⟩
  have hmass : 0 < sampledMixedProfile exploitableMixed :=
    pos_iff_ne_zero.mpr ((sampledMixedProfile.mem_support_iff _).mp hsupport)
  have hevent : exploitableMixed ∈ event := exploitableMixed_not_isOneNash
  have hpositive : 0 < sampledMixedProfile.toOuterMeasure event := by
    rw [PMF.toOuterMeasure_apply]
    have hterm : 0 < event.indicator sampledMixedProfile exploitableMixed := by
      simpa [Set.indicator_of_mem hevent] using hmass
    exact lt_of_lt_of_le hterm (ENNReal.le_tsum exploitableMixed)
  have hfinite : sampledMixedProfile.toOuterMeasure event ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    have hle : (∑' profile, event.indicator sampledMixedProfile profile) ≤
        ∑' profile, sampledMixedProfile profile := by
      apply ENNReal.tsum_le_tsum
      intro profile
      by_cases h : profile ∈ event <;> simp [Set.indicator, h]
    rw [PMF.tsum_coe] at hle
    exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
  exact ENNReal.toReal_pos hpositive.ne' hfinite

/-! ## Independent reuse: posterior concentration -/

/-- Bayes plausibility and the same event bound limit how often posteriors can
assign a rare state a large probability.  This consumer is independent of
games, deviations, and equilibrium. -/
theorem posterior_state_tail_le {State : Type*} (prior : PMF State)
    (law : PosteriorLaw State) (hplausible : law.IsBayesPlausible prior)
    (state : State) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (law.toOuterMeasure
      {belief | threshold ≤ (belief state).toReal}).toReal ≤
      (prior state).toReal / threshold := by
  have hobs : PayoffIntegrable law (fun belief => (belief state).toReal) := by
    apply payoffIntegrable_of_bounded law _ (C := 1)
    intro belief
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (by simp) (belief.coe_le_one state)
  have hmean : expect law (fun belief => (belief state).toReal) hobs =
      (prior state).toReal := by
    have hmass := congrArg (fun μ : PMF State => (μ state).toReal) hplausible
    rw [PosteriorLaw.mean_apply, ENNReal.tsum_toReal_eq (fun belief =>
      ENNReal.mul_ne_top (law.apply_ne_top belief)
        (belief.apply_ne_top state))] at hmass
    simpa only [ENNReal.toReal_mul, expect] using hmass
  calc
    (law.toOuterMeasure {belief | threshold ≤ (belief state).toReal}).toReal ≤
        expect law (fun belief => (belief state).toReal) hobs / threshold := by
      exact markov_inequality law _ hthreshold hobs
        (fun belief _ => ENNReal.toReal_nonneg)
    _ = (prior state).toReal / threshold := by rw [hmean]

def fairPrior : PMF Bool := PMF.uniformOfFintype Bool

def revealingPosteriorLaw : PosteriorLaw Bool :=
  PosteriorLaw.fullRevelation fairPrior

/-- Under full revelation of a fair state, posteriors assigning at least
three-quarters to `true` occur with probability at most two-thirds. -/
theorem revealing_true_tail_le_two_thirds :
    (revealingPosteriorLaw.toOuterMeasure
      {belief | 3 / 4 ≤ (belief true).toReal}).toReal ≤ 2 / 3 := by
  have h := posterior_state_tail_le fairPrior revealingPosteriorLaw
    (PosteriorLaw.isBayesPlausible_fullRevelation fairPrior) true
    (threshold := 3 / 4) (by norm_num)
  norm_num [fairPrior, PMF.uniformOfFintype_apply] at h
  exact h

end GameTheory.Experimental.PostArchitecture.ProbabilityTailAdequacy
