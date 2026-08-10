/-
# Correlated rationalizability by mixed-dominator elimination

For finite games, correlated rationalizability admits an iterated-deletion
characterization: eliminate a pure strategy when a finite mixture of surviving
own strategies strictly improves against every surviving joint opponents'
profile.  Unlike Bernheim--Pearce independent rationalizability for games with
three or more players, this characterization does not impose a product-belief
restriction across opponents.

The mixture is the canonical `FinDist` randomized unilateral deviation; no
second profile, probability, or equilibrium layer is introduced.
Pure-strategy elimination remains the separately named `pureSurvivors` /
`SurvivesAllPureEliminationRounds` surface in `Core.Response`.

Reference: A. Brandenburger and E. Dekel, “Rationalizability and Correlated
Equilibria,” *Econometrica* 55 (1987), 1391–1402, DOI: 10.2307/1913562.
-/

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

end GameTheory
