/-
# Correlated and independent rationalizability

Correlated rationalizability admits an iterated-deletion characterization:
eliminate a pure strategy when a PMF mixture of surviving
own strategies strictly improves against every surviving joint opponents'
profile.  Unlike Bernheim--Pearce independent rationalizability for games with
three or more players, this characterization does not impose a product-belief
restriction across opponents.

The correlated mixture and every independent marginal use the canonical
`PMF`; no second profile, probability, or equilibrium layer is introduced.
Pure-strategy elimination remains the separately named `pureSurvivors` /
`SurvivesAllPureEliminationRounds` surface in `Core.Response`.

Reference: A. Brandenburger and E. Dekel, “Rationalizability and Correlated
Equilibria,” *Econometrica* 55 (1987), 1391–1402, DOI: 10.2307/1913562.
-/

import GameTheory.Core.Mixed
import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} [DecidableEq ι]

/-- The outcome law after randomizing only `who`'s replacement at a pure
profile. -/
def randomizedDeviationOutcome (F : GameForm ι) (profile : Profile F.sig)
    (who : ι) (replacement : PMF (F.sig.Strategy who)) :
    PMF F.sig.Outcome :=
  F.outcomeLaw
    ((DeviationScheme.unilateralRandomized F.sig).apply
      (PMF.pure profile) who replacement)

@[simp]
theorem randomizedDeviationOutcome_pure (F : GameForm ι)
    (profile : Profile F.sig) (who : ι) (replacement : F.sig.Strategy who) :
    randomizedDeviationOutcome F profile who (PMF.pure replacement) =
      F.play (Profile.update profile who replacement) := by
  simp [randomizedDeviationOutcome, DeviationScheme.unilateralRandomized_apply,
    GameForm.outcomeLaw]

/-- Randomizing one player's action binds the corresponding pure play laws. -/
theorem randomizedDeviationOutcome_eq_bind (F : GameForm ι)
    (profile : Profile F.sig) (who : ι)
    (replacement : PMF (F.sig.Strategy who)) :
    randomizedDeviationOutcome F profile who replacement =
      replacement.bind fun action => F.play (Profile.update profile who action) := by
  simp [randomizedDeviationOutcome, DeviationScheme.unilateralRandomized_apply,
    GameForm.outcomeLaw, PMF.bind_map]
  rfl

/-- Integrating the actual randomized deviation gives its supported pure
conditional values and their outer expectation. -/
theorem expectedUtility_randomizedDeviationOutcome (F : GameForm ι)
    (utility : Utility F.sig) (profile : Profile F.sig) (who : ι)
    (replacement : PMF (F.sig.Strategy who))
    (hmixed : UtilityIntegrable utility who
      (randomizedDeviationOutcome F profile who replacement)) :
    ∃ hconditional : ∀ action, action ∈ replacement.support →
        UtilityIntegrable utility who (F.play (Profile.update profile who action)),
      ∃ values : F.sig.Strategy who → ℝ,
        (∀ action, ∀ ha : action ∈ replacement.support,
          values action = expectedUtility utility who
            (F.play (Profile.update profile who action)) (hconditional action ha)) ∧
        ∃ houter : PayoffIntegrable replacement values,
          expectedUtility utility who
              (randomizedDeviationOutcome F profile who replacement) hmixed =
            expect replacement values houter := by
  classical
  let kernel := fun action => F.play (Profile.update profile who action)
  have hbind : PayoffIntegrable (replacement.bind kernel)
      (fun outcome => utility outcome who) := by
    rw [← randomizedDeviationOutcome_eq_bind]
    exact hmixed
  let hconditional := payoffIntegrable_bind_conditional_on_support replacement kernel
    (fun outcome => utility outcome who) hbind
  let values : F.sig.Strategy who → ℝ := fun action =>
    if ha : action ∈ replacement.support then
      expectedUtility utility who (kernel action) (hconditional action ha) else 0
  have hvalues (action : F.sig.Strategy who) (ha : action ∈ replacement.support) :
      values action = expect (kernel action) (fun outcome => utility outcome who)
        (hconditional action ha) := by
    have hne : replacement action ≠ 0 :=
      (PMF.mem_support_iff replacement action).mp ha
    simp [values, hne, expectedUtility]
  have houter := payoffIntegrable_bind_conditionalValue_on_support replacement kernel
    (fun outcome => utility outcome who) hbind values hvalues
  refine ⟨hconditional, values, ?_, houter, ?_⟩
  · intro action ha
    simpa only [expectedUtility] using hvalues action ha
  have htower := expect_bind_tower_on_support replacement kernel
    (fun outcome => utility outcome who) hbind values hvalues
  simpa only [expectedUtility, randomizedDeviationOutcome_eq_bind] using htower

/-- A pure strategy is strictly dominated by a mixed strategy when some
randomized replacement is strictly preferred at every pure
profile. -/
def StrictlyDominatedByMixed (F : GameForm ι)
    (weaklyPrefers : WeakPreference ι F.sig.Outcome) (who : ι)
    (alternative : F.sig.Strategy who) : Prop :=
  ∃ replacement : PMF (F.sig.Strategy who),
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
  ⟨PMF.pure preferred, fun profile => by
    rw [randomizedDeviationOutcome_pure]
    exact hdom profile (fun _ => Set.mem_univ _)⟩

private theorem strictRandomized_not_isBestResponse
    {F : GameForm ι} {utility : Utility F.sig} {who : ι}
    {alternative : F.sig.Strategy who}
    {profile : Profile F.sig} {replacement : PMF (F.sig.Strategy who)}
    (hstrict : Preference.strict (euPreference utility) who
      (randomizedDeviationOutcome F profile who replacement)
      (F.play (Profile.update profile who alternative)))
    (hbest : IsBestResponse F (euPreference utility) who profile alternative) :
    False := by
  obtain ⟨hmixed, hbase, _⟩ := hstrict.1
  have hlt := (euPreference_strict_iff utility who _ _ hmixed hbase).mp hstrict
  obtain ⟨hconditional, values, hvalues, houter, heq⟩ :=
    expectedUtility_randomizedDeviationOutcome F utility profile who replacement hmixed
  have hle : expect replacement values houter ≤
      expectedUtility utility who (F.play (Profile.update profile who alternative))
        hbase := by
    calc
      expect replacement values houter ≤
          expect replacement
            (fun _ => expectedUtility utility who
              (F.play (Profile.update profile who alternative)) hbase)
            (payoffIntegrable_constant replacement _) := by
        apply expect_mono (μ := replacement)
        · intro action ha
          rw [hvalues action ha]
          exact (euPreference_iff utility who _ _ hbase (hconditional action ha)).mp
            (hbest action)
      _ = expectedUtility utility who
            (F.play (Profile.update profile who alternative)) hbase :=
        expect_constant replacement _ _
  rw [← heq] at hle
  exact (not_lt_of_ge hle) hlt

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
  exact strictRandomized_not_isBestResponse (hreplacement profile) hbest

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
          ¬ ∃ replacement : PMF (F.sig.Strategy who),
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
        (Profile.update beliefs who (PMF.pure strategy)))
      (F.mixed.play
        (Profile.update beliefs who (PMF.pure alternative)))

/-- Mixing one coordinate before play equals averaging its pure randomized
deviation law over the original independent profile belief. -/
theorem mixed_play_update_eq_bind_randomizedDeviation
    (beliefs : Profile F.sig.mixed) (who : ι)
    (replacement : PMF (F.sig.Strategy who)) :
    F.mixed.play (Profile.update beliefs who replacement) =
      (independentProduct beliefs).bind fun profile =>
        randomizedDeviationOutcome F profile who replacement := by
  calc
    F.mixed.play (Profile.update beliefs who replacement) =
        replacement.bind fun action =>
          F.mixed.play (Profile.update beliefs who (PMF.pure action)) :=
      GameForm.mixed_play_update F beliefs who replacement
    _ = replacement.bind fun action =>
          (independentProduct beliefs).bind fun profile =>
            F.play (Profile.update profile who action) := by
      congr 1
      funext action
      exact mixed_play_update_pure_eq_bind (F := F) beliefs who action
    _ = (independentProduct beliefs).bind fun profile =>
          replacement.bind fun action => F.play (Profile.update profile who action) :=
      (PMF.bind_comm (independentProduct beliefs) replacement
        (fun profile action => F.play (Profile.update profile who action))).symm
    _ = (independentProduct beliefs).bind fun profile =>
          randomizedDeviationOutcome F profile who replacement := by
      congr 1
      funext profile
      exact (randomizedDeviationOutcome_eq_bind F profile who replacement).symm

/-- Actual mixed-law integration supplies the supported pure-profile values
and their expectation over the independent product belief. -/
theorem expectedUtility_mixed_play_update_pure
    (utility : Utility F.sig) (beliefs : Profile F.sig.mixed)
    (who : ι) (strategy : F.sig.Strategy who)
    (hmixed : UtilityIntegrable utility who
      (F.mixed.play (Profile.update beliefs who (PMF.pure strategy)))) :
    ∃ hconditional : ∀ profile, profile ∈ (independentProduct beliefs).support →
        UtilityIntegrable utility who (F.play (Profile.update profile who strategy)),
      ∃ values : Profile F.sig → ℝ,
        (∀ profile, ∀ hp : profile ∈ (independentProduct beliefs).support,
          values profile = expectedUtility utility who
            (F.play (Profile.update profile who strategy)) (hconditional profile hp)) ∧
        ∃ houter : PayoffIntegrable (independentProduct beliefs) values,
          expectedUtility utility who
              (F.mixed.play (Profile.update beliefs who (PMF.pure strategy))) hmixed =
            expect (independentProduct beliefs) values houter := by
  classical
  let profileLaw := independentProduct beliefs
  let kernel := fun profile => F.play (Profile.update profile who strategy)
  have hbind : PayoffIntegrable (profileLaw.bind kernel)
      (fun outcome => utility outcome who) := by
    rw [← mixed_play_update_pure_eq_bind]
    exact hmixed
  let hconditional := payoffIntegrable_bind_conditional_on_support profileLaw kernel
    (fun outcome => utility outcome who) hbind
  let values : Profile F.sig → ℝ := fun profile =>
    if hp : profile ∈ profileLaw.support then
      expectedUtility utility who (kernel profile) (hconditional profile hp) else 0
  have hvalues (profile : Profile F.sig) (hp : profile ∈ profileLaw.support) :
      values profile = expect (kernel profile) (fun outcome => utility outcome who)
        (hconditional profile hp) := by
    have hne : profileLaw profile ≠ 0 := (PMF.mem_support_iff profileLaw profile).mp hp
    simp [values, hne, expectedUtility]
  have houter := payoffIntegrable_bind_conditionalValue_on_support profileLaw kernel
    (fun outcome => utility outcome who) hbind values hvalues
  refine ⟨hconditional, values, ?_, houter, ?_⟩
  · intro profile hp
    simpa only [expectedUtility] using hvalues profile hp
  have htower := expect_bind_tower_on_support profileLaw kernel
    (fun outcome => utility outcome who) hbind values hvalues
  calc
    expectedUtility utility who
        (F.mixed.play (Profile.update beliefs who (PMF.pure strategy))) hmixed =
        expect (profileLaw.bind kernel) (fun outcome => utility outcome who) hbind := by
      exact expectedUtility_congr_law utility who
        (mixed_play_update_pure_eq_bind (F := F) beliefs who strategy) hmixed hbind
    _ = expect profileLaw values houter := htower

/-- A pointwise strict mixed improvement on the supported product belief
contradicts independent best response when its actual joint outcome law is
integrable. Separate conditional integrals do not supply this guard. -/
theorem IsIndependentBestResponse.not_strict_mixed_on_support
    {utility : Utility F.sig} {beliefs : Profile F.sig.mixed}
    {who : ι} {strategy : F.sig.Strategy who}
    (hbest : IsIndependentBestResponse F (euPreference utility) who strategy beliefs)
    (replacement : PMF (F.sig.Strategy who))
    (hjoint : UtilityIntegrable utility who
      (F.mixed.play (Profile.update beliefs who replacement)))
    (hstrict : ∀ profile, profile ∈ (independentProduct beliefs).support →
      Preference.strict (euPreference utility) who
        (randomizedDeviationOutcome F profile who replacement)
        (F.play (Profile.update profile who strategy))) : False := by
  let profileLaw := independentProduct beliefs
  let f : F.sig.Outcome → ℝ := fun outcome => utility outcome who
  let baseKernel := fun profile => F.play (Profile.update profile who strategy)
  let mixedKernel := fun profile => randomizedDeviationOutcome F profile who replacement
  let actionKernel := fun action : F.sig.Strategy who =>
    F.mixed.play (Profile.update beliefs who (PMF.pure action))
  have hbase : UtilityIntegrable utility who
      (F.mixed.play (Profile.update beliefs who (PMF.pure strategy))) :=
    (hbest strategy).1
  have hbaseBind : PayoffIntegrable (profileLaw.bind baseKernel) f := by
    rw [← mixed_play_update_pure_eq_bind]
    exact hbase
  have hjointProfile : PayoffIntegrable (profileLaw.bind mixedKernel) f := by
    rw [← mixed_play_update_eq_bind_randomizedDeviation]
    exact hjoint
  have hjointAction : PayoffIntegrable (replacement.bind actionKernel) f := by
    rw [← GameForm.mixed_play_update]
    exact hjoint
  have hleAction :
      expectedUtility utility who
          (F.mixed.play (Profile.update beliefs who replacement)) hjoint ≤
        expectedUtility utility who
          (F.mixed.play (Profile.update beliefs who (PMF.pure strategy))) hbase := by
    have hbound := expect_bind_le_of_forall_on_support replacement actionKernel f
      hjointAction
      (expectedUtility utility who
        (F.mixed.play (Profile.update beliefs who (PMF.pure strategy))) hbase)
      (fun action ha => by
        have hconditional := payoffIntegrable_bind_conditional_on_support
          replacement actionKernel f hjointAction action ha
        exact (euPreference_iff utility who _ _ hbase hconditional).mp
          (hbest action))
    calc
      expectedUtility utility who
          (F.mixed.play (Profile.update beliefs who replacement)) hjoint =
          expect (replacement.bind actionKernel) f hjointAction := by
        exact expectedUtility_congr_law utility who
          (GameForm.mixed_play_update F beliefs who replacement)
          hjoint hjointAction
      _ ≤ expectedUtility utility who
            (F.mixed.play (Profile.update beliefs who (PMF.pure strategy))) hbase :=
        hbound
  have hpoint (profile : Profile F.sig) (hp : profile ∈ profileLaw.support) :
      expect (baseKernel profile) f
          (payoffIntegrable_bind_conditional_on_support profileLaw baseKernel f
            hbaseBind profile hp) <
        expect (mixedKernel profile) f
          (payoffIntegrable_bind_conditional_on_support profileLaw mixedKernel f
            hjointProfile profile hp) := by
    exact (euPreference_strict_iff utility who _ _
      (payoffIntegrable_bind_conditional_on_support profileLaw mixedKernel f
        hjointProfile profile hp)
      (payoffIntegrable_bind_conditional_on_support profileLaw baseKernel f
        hbaseBind profile hp)).mp (hstrict profile hp)
  obtain ⟨witness, hwitness⟩ := profileLaw.support_nonempty
  have hstrictBind := expect_bind_lt_on_support profileLaw baseKernel mixedKernel f
    hbaseBind hjointProfile
    (fun profile hp => (hpoint profile hp).le) witness hwitness
    (hpoint witness hwitness)
  have hstrictMean :
      expectedUtility utility who
          (F.mixed.play (Profile.update beliefs who (PMF.pure strategy))) hbase <
        expectedUtility utility who
          (F.mixed.play (Profile.update beliefs who replacement)) hjoint := by
    calc
      expectedUtility utility who
          (F.mixed.play (Profile.update beliefs who (PMF.pure strategy))) hbase =
          expect (profileLaw.bind baseKernel) f hbaseBind := by
        exact expectedUtility_congr_law utility who
          (mixed_play_update_pure_eq_bind (F := F) beliefs who strategy)
          hbase hbaseBind
      _ < expect (profileLaw.bind mixedKernel) f hjointProfile := hstrictBind
      _ = expectedUtility utility who
            (F.mixed.play (Profile.update beliefs who replacement)) hjoint := by
        exact (expectedUtility_congr_law utility who
          (mixed_play_update_eq_bind_randomizedDeviation (F := F)
            beliefs who replacement) hjoint hjointProfile).symm
  exact (not_lt_of_ge hleAction) hstrictMean

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
        ¬ ∃ replacement : PMF (F.sig.Strategy who),
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
  have hbest (who : ι) :
      IsBestResponse F (euPreference utility) who profile (profile who) :=
    (isNash_iff_isBestResponse profile).mp hnash who
  intro round
  induction round with
  | zero => intro who; exact Set.mem_univ _
  | succ round ih =>
      intro who
      refine ⟨ih who, ?_⟩
      rintro ⟨replacement, _, hdominates⟩
      have hstrict := hdominates profile ih
      exact strictRandomized_not_isBestResponse hstrict (hbest who)

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

/-- Independent-belief survival implies correlated mixed-dominator survival
when each putative dominator's actual product-belief outcome law is integrable.
The condition concerns only the belief and replacement used in the comparison. -/
theorem independentSurvivors_subset_correlatedSurvivors
    {utility : Utility F.sig}
    (hjoint : ∀ who strategy (beliefs : Profile F.sig.mixed)
      (replacement : PMF (F.sig.Strategy who)),
      IsIndependentBestResponse F (euPreference utility) who strategy beliefs →
      (∀ profile, profile ∈ (independentProduct beliefs).support →
        Preference.strict (euPreference utility) who
          (randomizedDeviationOutcome F profile who replacement)
          (F.play (Profile.update profile who strategy))) →
      UtilityIntegrable utility who
        (F.mixed.play (Profile.update beliefs who replacement))) :
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
      have hstrict (profile : Profile F.sig)
          (hprofile : profile ∈ (independentProduct beliefs).support) :
          Preference.strict (euPreference utility) who
            (randomizedDeviationOutcome F profile who replacement)
            (F.play (Profile.update profile who strategy)) := by
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
              ((independentProduct_support_iff beliefs profile).mp hprofile player)
        have hdom := dominates (Profile.update profile who strategy) allSurvive
        simpa [randomizedDeviationOutcome_eq_bind, Profile.update_idem] using hdom
      exact IsIndependentBestResponse.not_strict_mixed_on_support F best replacement
        (hjoint who strategy beliefs replacement best hstrict) hstrict

/-- The guarded roundwise inclusion passes to all finite elimination rounds. -/
theorem IsIndependentRationalizable.isCorrelatedRationalizable
    {utility : Utility F.sig} {who : ι} {strategy : F.sig.Strategy who}
    (hindependent :
      IsIndependentRationalizable F (euPreference utility) who strategy)
    (hjoint : ∀ who strategy (beliefs : Profile F.sig.mixed)
      (replacement : PMF (F.sig.Strategy who)),
      IsIndependentBestResponse F (euPreference utility) who strategy beliefs →
      (∀ profile, profile ∈ (independentProduct beliefs).support →
        Preference.strict (euPreference utility) who
          (randomizedDeviationOutcome F profile who replacement)
          (F.play (Profile.update profile who strategy))) →
      UtilityIntegrable utility who
        (F.mixed.play (Profile.update beliefs who replacement))) :
    IsCorrelatedRationalizable F (euPreference utility) who strategy :=
  fun round => independentSurvivors_subset_correlatedSurvivors hjoint round who
    (hindependent round)

/-- Finite strategy carriers derive every needed product-belief/mixed-deviator
guard from pure-play integration. The outcome carrier remains arbitrary. -/
theorem independentSurvivors_subset_correlatedSurvivors_of_finite
    {utility : Utility F.sig}
    [∀ i, Finite (F.sig.Strategy i)]
    (hintegrable : GameForm.HasIntegrableUtility F utility) :
    ∀ round who,
      independentSurvivors F (euPreference utility) round who ⊆
        correlatedSurvivors F (euPreference utility) round who := by
  apply independentSurvivors_subset_correlatedSurvivors
  intro who strategy beliefs replacement _ _
  exact hintegrable.mixed_of_finite who
    (Profile.update beliefs who replacement)

theorem IsIndependentRationalizable.isCorrelatedRationalizable_of_finite
    {utility : Utility F.sig} {who : ι} {strategy : F.sig.Strategy who}
    [∀ i, Finite (F.sig.Strategy i)]
    (hindependent :
      IsIndependentRationalizable F (euPreference utility) who strategy)
    (hintegrable : GameForm.HasIntegrableUtility F utility) :
    IsCorrelatedRationalizable F (euPreference utility) who strategy :=
  fun round => independentSurvivors_subset_correlatedSurvivors_of_finite
    hintegrable round who (hindependent round)

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
          simpa only [GameForm.purify, PMF.mem_support_pure_iff] using haction
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
