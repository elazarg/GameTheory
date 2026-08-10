/-
# Correlated and independent rationalizability

For finite games, correlated rationalizability admits an iterated-deletion
characterization: eliminate a pure strategy when a finite mixture of surviving
own strategies strictly improves against every surviving joint opponents'
profile.  Unlike Bernheim--Pearce independent rationalizability for games with
three or more players, this characterization does not impose a product-belief
restriction across opponents.

The correlated mixture and every independent marginal use the canonical
`FinDist`; no second profile, probability, or equilibrium layer is introduced.
Pure-strategy elimination remains the separately named `pureSurvivors` /
`SurvivesAllPureEliminationRounds` surface in `Core.Response`.

Reference: A. Brandenburger and E. Dekel, “Rationalizability and Correlated
Equilibria,” *Econometrica* 55 (1987), 1391–1402, DOI: 10.2307/1913562.
-/

import GameTheory.Core.Mixed
import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open Probability

universe uι

variable {ι : Type uι} [DecidableEq ι]

/-- The outcome law after randomizing only `who`'s replacement at a pure
profile. -/
def randomizedDeviationOutcome (F : GameForm ι) (profile : Profile F.sig)
    (who : ι) (replacement : FinDist (F.sig.Strategy who)) :
    FinDist F.sig.Outcome :=
  F.outcomeLaw
    ((DeviationScheme.unilateralRandomized F.sig).apply
      (FinDist.pure profile) who replacement)

@[simp]
theorem randomizedDeviationOutcome_pure (F : GameForm ι)
    (profile : Profile F.sig) (who : ι) (replacement : F.sig.Strategy who) :
    randomizedDeviationOutcome F profile who (FinDist.pure replacement) =
      F.play (Profile.update profile who replacement) := by
  simp [randomizedDeviationOutcome, GameForm.outcomeLaw, FinDist.map_eq_bind]

/-- Expected utility of a randomized unilateral replacement is the finite
average of its pure-replacement utilities. -/
theorem expectedUtility_randomizedDeviationOutcome (F : GameForm ι)
    (utility : Utility F.sig) (profile : Profile F.sig) (who : ι)
    (replacement : FinDist (F.sig.Strategy who)) :
    expectedUtility utility who
        (randomizedDeviationOutcome F profile who replacement) =
      replacement.expect fun action =>
        expectedUtility utility who
          (F.play (Profile.update profile who action)) := by
  simp [randomizedDeviationOutcome, GameForm.outcomeLaw,
    FinDist.map_eq_bind, expectedUtility_bind]

/-- A pure strategy is strictly dominated by a mixed strategy when some
finite-support randomized replacement is strictly preferred at every pure
profile. -/
def StrictlyDominatedByMixed (F : GameForm ι)
    (weaklyPrefers : WeakPreference ι F.sig.Outcome) (who : ι)
    (alternative : F.sig.Strategy who) : Prop :=
  ∃ replacement : FinDist (F.sig.Strategy who),
    ∀ profile : Profile F.sig,
      Preference.strict weaklyPrefers who
        (randomizedDeviationOutcome F profile who replacement)
        (F.play (Profile.update profile who alternative))

/-- Pure strict dominance is the point-mass case of mixed strict dominance. -/
theorem StrictlyDominates.toStrictlyDominatedByMixed
    {F : GameForm ι} {weaklyPrefers : WeakPreference ι F.sig.Outcome}
    {who : ι} {preferred alternative : F.sig.Strategy who}
    (hdom : StrictlyDominates F weaklyPrefers who preferred alternative) :
    StrictlyDominatedByMixed F weaklyPrefers who alternative :=
  ⟨FinDist.pure preferred, fun profile => by
    rw [randomizedDeviationOutcome_pure]
    exact hdom profile (fun _ => Set.mem_univ _)⟩

/-- Mixed strict dominance rules out best-response status under expected
utility. -/
theorem StrictlyDominatedByMixed.not_isBestResponse
    {F : GameForm ι} {utility : Utility F.sig} {who : ι}
    {alternative : F.sig.Strategy who}
    (hdom : StrictlyDominatedByMixed F (euPreference utility) who alternative)
    (profile : Profile F.sig) :
    ¬ IsBestResponse F (euPreference utility) who profile alternative := by
  obtain ⟨replacement, hreplacement⟩ := hdom
  intro hbest
  have hstrict := (euPreference_strict_iff utility who _ _).1
    (hreplacement profile)
  have hle :
      expectedUtility utility who
          (randomizedDeviationOutcome F profile who replacement) ≤
        expectedUtility utility who
          (F.play (Profile.update profile who alternative)) := by
    rw [expectedUtility_randomizedDeviationOutcome]
    calc
      (replacement.expect fun action =>
          expectedUtility utility who
            (F.play (Profile.update profile who action))) ≤
          replacement.expect fun _ =>
            expectedUtility utility who
              (F.play (Profile.update profile who alternative)) :=
        FinDist.expect_mono fun action _ => by
          simpa only [euPreference_apply] using hbest action
      _ = expectedUtility utility who
            (F.play (Profile.update profile who alternative)) :=
        FinDist.expect_const ..
  exact (not_lt_of_ge hle) hstrict

section Survivors

variable (F : GameForm ι) (weaklyPrefers : WeakPreference ι F.sig.Outcome)

/-- Strategies surviving `round` rounds of elimination by mixed dominators.
Every action in the dominating mixture and every opponents' action profile must
survive the preceding round. -/
def correlatedSurvivors : ℕ → ∀ who, Set (F.sig.Strategy who)
  | 0, _ => Set.univ
  | round + 1, who =>
      { alternative |
        alternative ∈ correlatedSurvivors round who ∧
          ¬ ∃ replacement : FinDist (F.sig.Strategy who),
            (∀ action ∈ replacement.support,
              action ∈ correlatedSurvivors round who) ∧
              ∀ profile : Profile F.sig,
                (∀ player,
                  profile player ∈ correlatedSurvivors round player) →
                  Preference.strict weaklyPrefers who
                    (randomizedDeviationOutcome F profile who replacement)
                    (F.play (Profile.update profile who alternative)) }

/-- Correlated rationalizability's mixed-dominator elimination property:
survival of every finite elimination round.  The independent-belief
Bernheim--Pearce notion is intentionally not represented by this name. -/
def IsCorrelatedRationalizable (who : ι)
    (strategy : F.sig.Strategy who) : Prop :=
  ∀ round, strategy ∈ correlatedSurvivors F weaklyPrefers round who

end Survivors

section IndependentSurvivors

variable [Fintype ι]
variable (F : GameForm ι) (weaklyPrefers : WeakPreference ι F.sig.Outcome)

/-- `strategy` is a best response to an independent profile of beliefs.  The
focal player's marginal is overwritten by a point mass, so only the opponents'
marginals affect either outcome law. -/
def IsIndependentBestResponse (who : ι) (strategy : F.sig.Strategy who)
    (beliefs : Profile F.sig.mixed) : Prop :=
  ∀ alternative : F.sig.Strategy who,
    weaklyPrefers who
      (F.mixed.play
        (Profile.update beliefs who (FinDist.pure strategy)))
      (F.mixed.play
        (Profile.update beliefs who (FinDist.pure alternative)))

/-- Expected utility against independent beliefs is the expectation, over the
product profile law, of the corresponding pure-profile replacement. -/
theorem expectedUtility_mixed_play_update_pure
    (utility : Utility F.sig) (beliefs : Profile F.sig.mixed)
    (who : ι) (strategy : F.sig.Strategy who) :
    expectedUtility utility who
        (F.mixed.play
          (Profile.update beliefs who (FinDist.pure strategy))) =
      (FinDist.pi beliefs).expect fun profile =>
        expectedUtility utility who
          (F.play (Profile.update profile who strategy)) := by
  rw [GameForm.mixed_play]
  rw [show FinDist.pure strategy =
      (beliefs who).map (fun _ => strategy) by simp]
  rw [← GameForm.pi_map_recommendation, expectedUtility_bind,
    FinDist.expect_map]

/-- Strategies surviving iterated independent-belief best response.  Each
opponent's marginal must be supported on the preceding round; the product law
is supplied by the canonical mixed extension. -/
def independentSurvivors : ℕ → ∀ who, Set (F.sig.Strategy who)
  | 0, _ => Set.univ
  | round + 1, who =>
      { strategy |
        strategy ∈ independentSurvivors round who ∧
          ∃ beliefs : Profile F.sig.mixed,
            (∀ player, player ≠ who →
              ∀ action ∈ (beliefs player).support,
                action ∈ independentSurvivors round player) ∧
              IsIndependentBestResponse F weaklyPrefers who strategy beliefs }

/-- Bernheim--Pearce independent rationalizability: survival of every
independent-belief best-response round. -/
def IsIndependentRationalizable (who : ι)
    (strategy : F.sig.Strategy who) : Prop :=
  ∀ round, strategy ∈ independentSurvivors F weaklyPrefers round who

end IndependentSurvivors

section Theorems

variable {F : GameForm ι} {weaklyPrefers : WeakPreference ι F.sig.Outcome}

@[simp]
theorem correlatedSurvivors_zero (who : ι) :
    correlatedSurvivors F weaklyPrefers 0 who = Set.univ :=
  rfl

theorem mem_correlatedSurvivors_succ {round : ℕ} {who : ι}
    {strategy : F.sig.Strategy who} :
    strategy ∈ correlatedSurvivors F weaklyPrefers (round + 1) who ↔
      strategy ∈ correlatedSurvivors F weaklyPrefers round who ∧
        ¬ ∃ replacement : FinDist (F.sig.Strategy who),
          (∀ action ∈ replacement.support,
            action ∈ correlatedSurvivors F weaklyPrefers round who) ∧
            ∀ profile : Profile F.sig,
              (∀ player,
                profile player ∈
                  correlatedSurvivors F weaklyPrefers round player) →
                Preference.strict weaklyPrefers who
                  (randomizedDeviationOutcome F profile who replacement)
                  (F.play (Profile.update profile who strategy)) :=
  Iff.rfl

theorem correlatedSurvivors_antitone (round : ℕ) (who : ι) :
    correlatedSurvivors F weaklyPrefers (round + 1) who ⊆
      correlatedSurvivors F weaklyPrefers round who :=
  fun _ h => h.1

theorem mem_correlatedSurvivors_of_le {earlier later : ℕ}
    (hround : earlier ≤ later)
    {who : ι} {strategy : F.sig.Strategy who}
    (h : strategy ∈ correlatedSurvivors F weaklyPrefers later who) :
    strategy ∈ correlatedSurvivors F weaklyPrefers earlier who := by
  induction hround with
  | refl => exact h
  | step _ ih => exact ih h.1

/-- A Nash action survives every round of mixed elimination.  Expected-utility
linearity turns every randomized replacement into an allowed deviation from
the point-mass coarse-correlated equilibrium. -/
theorem IsNash.survivesCorrelatedElimination
    {utility : Utility F.sig} {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile) :
    ∀ round who,
      profile who ∈
        correlatedSurvivors F (euPreference utility) round who := by
  have hrandomized :
      IsEquilibrium F (euPreference utility) (FinDist.pure profile)
        (DeviationScheme.unilateralRandomized F.sig) :=
    isCoarseCorrelatedEq_randomized
      ((isNash_iff_isCoarseCorrelatedEq_pure profile).1 hnash)
  intro round
  induction round with
  | zero => intro who; exact Set.mem_univ _
  | succ round ih =>
      intro who
      refine ⟨ih who, ?_⟩
      rintro ⟨replacement, _, hdominates⟩
      have hstrict := hdominates profile ih
      apply hstrict.2
      simpa [randomizedDeviationOutcome, GameForm.outcomeLaw,
        Profile.update_eq_self] using hrandomized who replacement

/-- Every action played at a Nash equilibrium is correlated rationalizable. -/
theorem IsNash.isCorrelatedRationalizable {utility : Utility F.sig}
    {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile) (who : ι) :
    IsCorrelatedRationalizable F (euPreference utility) who (profile who) :=
  fun round => hnash.survivesCorrelatedElimination round who

/-- Every action in a dominant expected-utility profile survives mixed
elimination. -/
theorem dominantProfile_survives {utility : Utility F.sig}
    (profile : Profile F.sig)
    (hdom : IsDominantProfile F (euPreference utility) profile) :
    ∀ round who,
      profile who ∈
        correlatedSurvivors F (euPreference utility) round who :=
  hdom.isNash.survivesCorrelatedElimination

/-- A dominant action is rationalizable when the other players can be filled
out by dominant actions. -/
theorem IsDominant.isCorrelatedRationalizable {utility : Utility F.sig}
    {who : ι} {strategy : F.sig.Strategy who}
    (hdom : IsDominant F (euPreference utility) who strategy)
    (base : Profile F.sig)
    (hother : ∀ player, player ≠ who →
      IsDominant F (euPreference utility) player (base player)) :
    IsCorrelatedRationalizable F (euPreference utility) who strategy := by
  let profile := Profile.update base who strategy
  have hall : IsDominantProfile F (euPreference utility) profile := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simpa [profile] using hdom
    · have hvalue : profile player = base player := by
        simp [profile, hplayer]
      rw [hvalue]
      exact hother player hplayer
  intro round
  have hsurvives := dominantProfile_survives profile hall round who
  simpa [profile] using hsurvives

/-- A rationalizable strategy cannot be globally mixed dominated: the first
round would remove it. -/
theorem IsCorrelatedRationalizable.not_strictlyDominatedByMixed
    {who : ι} {strategy : F.sig.Strategy who}
    (hrat : IsCorrelatedRationalizable F weaklyPrefers who strategy) :
    ¬ StrictlyDominatedByMixed F weaklyPrefers who strategy := by
  rintro ⟨replacement, hdominates⟩
  exact (hrat 1).2
    ⟨replacement, fun action _ => Set.mem_univ action,
      fun profile _ => hdominates profile⟩

/-- Pure strict dominance already supplies a mixed dominator, so a purely
dominated strategy is not rationalizable. -/
theorem StrictlyDominates.not_isCorrelatedRationalizable
    {who : ι} {preferred alternative : F.sig.Strategy who}
    (hdom : StrictlyDominates F weaklyPrefers who preferred alternative) :
    ¬ IsCorrelatedRationalizable F weaklyPrefers who alternative :=
  fun hrat => hrat.not_strictlyDominatedByMixed
    hdom.toStrictlyDominatedByMixed

/-- Under a strictly dominant action, every distinct alternative fails
correlated rationalizability in the first round. -/
theorem IsStrictDominant.not_isCorrelatedRationalizable_of_ne
    {who : ι} {preferred alternative : F.sig.Strategy who}
    (hdom : IsStrictDominant F weaklyPrefers who preferred)
    (hne : alternative ≠ preferred) :
    ¬ IsCorrelatedRationalizable F weaklyPrefers who alternative :=
  (hdom alternative hne).not_isCorrelatedRationalizable

end Theorems

section IndependentTheorems

variable [Fintype ι]
variable {F : GameForm ι} {weaklyPrefers : WeakPreference ι F.sig.Outcome}

@[simp]
theorem independentSurvivors_zero (who : ι) :
    independentSurvivors F weaklyPrefers 0 who = Set.univ :=
  rfl

theorem mem_independentSurvivors_succ {round : ℕ} {who : ι}
    {strategy : F.sig.Strategy who} :
    strategy ∈ independentSurvivors F weaklyPrefers (round + 1) who ↔
      strategy ∈ independentSurvivors F weaklyPrefers round who ∧
        ∃ beliefs : Profile F.sig.mixed,
          (∀ player, player ≠ who →
            ∀ action ∈ (beliefs player).support,
              action ∈ independentSurvivors F weaklyPrefers round player) ∧
            IsIndependentBestResponse F weaklyPrefers who strategy beliefs :=
  Iff.rfl

theorem independentSurvivors_antitone (round : ℕ) (who : ι) :
    independentSurvivors F weaklyPrefers (round + 1) who ⊆
      independentSurvivors F weaklyPrefers round who :=
  fun _ h => h.1

theorem mem_independentSurvivors_of_le {earlier later : ℕ}
    (hround : earlier ≤ later) {who : ι} {strategy : F.sig.Strategy who}
    (h : strategy ∈ independentSurvivors F weaklyPrefers later who) :
    strategy ∈ independentSurvivors F weaklyPrefers earlier who := by
  induction hround with
  | refl => exact h
  | step _ ih => exact ih h.1

/-- Independent-belief survival implies correlated mixed-dominator survival.
The proof averages any purported pointwise mixed dominator against the product
belief witnessing independent best response. -/
theorem independentSurvivors_subset_correlatedSurvivors
    {utility : Utility F.sig} :
    ∀ round who,
      independentSurvivors F (euPreference utility) round who ⊆
        correlatedSurvivors F (euPreference utility) round who := by
  intro round
  induction round with
  | zero => intro who _ _; exact Set.mem_univ _
  | succ round ih =>
      intro who strategy survives
      obtain ⟨survivesEarlier, beliefs, beliefsSupported, best⟩ := survives
      refine ⟨ih who survivesEarlier, ?_⟩
      rintro ⟨replacement, _, dominates⟩
      let profileLaw := FinDist.pi beliefs
      have bestValue (alternative : F.sig.Strategy who) :
          profileLaw.expect (fun profile =>
              expectedUtility utility who
                (F.play (Profile.update profile who alternative))) ≤
            profileLaw.expect fun profile =>
              expectedUtility utility who
                (F.play (Profile.update profile who strategy)) := by
        have hbest := best alternative
        rw [euPreference_apply,
          expectedUtility_mixed_play_update_pure,
          expectedUtility_mixed_play_update_pure] at hbest
        exact hbest
      have averageReplacement_le :
          profileLaw.expect (fun profile =>
              expectedUtility utility who
                (randomizedDeviationOutcome F profile who replacement)) ≤
            profileLaw.expect fun profile =>
              expectedUtility utility who
                (F.play (Profile.update profile who strategy)) := by
        simp_rw [expectedUtility_randomizedDeviationOutcome]
        rw [FinDist.expect_comm]
        calc
          replacement.expect (fun alternative =>
              profileLaw.expect fun profile =>
                expectedUtility utility who
                  (F.play (Profile.update profile who alternative))) ≤
              replacement.expect (fun _ =>
                profileLaw.expect fun profile =>
                  expectedUtility utility who
                    (F.play (Profile.update profile who strategy))) :=
            FinDist.expect_mono fun alternative _ => bestValue alternative
          _ = profileLaw.expect fun profile =>
                expectedUtility utility who
                  (F.play (Profile.update profile who strategy)) :=
            FinDist.expect_const ..
      have pointwiseStrict (profile : Profile F.sig)
          (hprofile : profile ∈ profileLaw.support) :
          expectedUtility utility who
              (F.play (Profile.update profile who strategy)) <
            expectedUtility utility who
              (randomizedDeviationOutcome F profile who replacement) := by
        have allSurvive :
            ∀ player,
              Profile.update profile who strategy player ∈
                correlatedSurvivors F (euPreference utility) round player := by
          intro player
          by_cases hplayer : player = who
          · subst player
            simpa only [Profile.update_same] using ih who survivesEarlier
          · rw [Profile.update_of_ne _ _ hplayer]
            apply ih player
            exact beliefsSupported player hplayer (profile player)
              ((FinDist.mem_support_pi.mp hprofile) player)
        have hstrict := dominates (Profile.update profile who strategy) allSurvive
        rw [euPreference_strict_iff] at hstrict
        simpa [randomizedDeviationOutcome, Profile.update_idem] using hstrict
      have averageStrict :
          profileLaw.expect (fun profile =>
              expectedUtility utility who
                (F.play (Profile.update profile who strategy))) <
            profileLaw.expect fun profile =>
              expectedUtility utility who
                (randomizedDeviationOutcome F profile who replacement) := by
        let difference := fun profile =>
          expectedUtility utility who
              (F.play (Profile.update profile who strategy)) -
            expectedUtility utility who
              (randomizedDeviationOutcome F profile who replacement)
        obtain ⟨witness, hwitness⟩ := profileLaw.support_nonempty
        have hnegative : profileLaw.expect difference < 0 :=
          FinDist.expect_lt_of_mem_support profileLaw difference 0
            (fun profile hprofile => sub_nonpos.mpr (pointwiseStrict profile hprofile).le)
            hwitness (sub_neg.mpr (pointwiseStrict witness hwitness))
        dsimp only [difference] at hnegative
        rw [FinDist.expect_sub] at hnegative
        linarith
      exact (not_lt_of_ge averageReplacement_le) averageStrict

/-- Independent rationalizability is contained in correlated
rationalizability for finite expected-utility games. -/
theorem IsIndependentRationalizable.isCorrelatedRationalizable
    {utility : Utility F.sig} {who : ι} {strategy : F.sig.Strategy who}
    (hindependent :
      IsIndependentRationalizable F (euPreference utility) who strategy) :
    IsCorrelatedRationalizable F (euPreference utility) who strategy :=
  fun round => independentSurvivors_subset_correlatedSurvivors round who
    (hindependent round)

/-- Every pure Nash action survives every independent-belief round.  Point-mass
opponent marginals are supported on the preceding Nash actions. -/
theorem IsNash.survivesIndependentElimination
    {utility : Utility F.sig} {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile) :
    ∀ round who,
      profile who ∈
        independentSurvivors F (euPreference utility) round who := by
  intro round
  induction round with
  | zero => intro who; exact Set.mem_univ _
  | succ round ih =>
      intro who
      refine ⟨ih who, F.purify profile, ?_, ?_⟩
      · intro player _ action haction
        have haction_eq : action = profile player := by
          simpa only [GameForm.purify, FinDist.mem_support_pure] using haction
        simpa only [haction_eq] using ih player
      · intro alternative
        rw [purify_update, purify_update, GameForm.mixed_play_purify,
          GameForm.mixed_play_purify]
        simpa only [Profile.update_eq_self] using
          (isNash_iff profile).1 hnash who alternative

/-- Every action played at a pure Nash equilibrium is independently
rationalizable. -/
theorem IsNash.isIndependentRationalizable
    {utility : Utility F.sig} {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile) (who : ι) :
    IsIndependentRationalizable F (euPreference utility) who (profile who) :=
  fun round => hnash.survivesIndependentElimination round who

end IndependentTheorems

end GameTheory
