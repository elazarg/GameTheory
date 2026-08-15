/-
# Utility evaluation and expected-utility preference

Utility is separate data from the game form. `euPreference` is a *derived*
weak preference, so every equilibrium concept keeps exactly one logical
definition: `IsNash F (euPreference u) σ` is expected-utility Nash, and there is
no second predicate to rewrite between.

Expected utility stays specialized to `ℝ`. The executable frontend evaluates
rational payoffs and connects to this layer by a proved compilation, not by a
scalar parameter threaded through the core.
-/

import GameTheory.Core.Equilibrium

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uo'

variable {ι : Type uι} {sig : GameSignature ι} {Outcome : Type uo} {Outcome' : Type uo'}

/-- A real utility for each outcome and player. -/
abbrev Utility (sig : GameSignature ι) := sig.Outcome → ι → ℝ

set_option linter.checkUnivs false in
/-- The dependent pair of a form and an evaluation. It repeats no strategy,
outcome, or play field; generic concepts still take the form and preference
explicitly, so bundling stays an ergonomic option rather than a second semantic
definition. -/
structure UtilityGame (ι : Type uι) where
  /-- The utility-free semantics. -/
  form : GameForm.{uι, us, uo} ι
  /-- How each player values an outcome. -/
  utility : Utility form.sig

/-- Expected utility of an outcome law. Finite support makes this
unconditional: no summability or boundedness hypothesis is needed. -/
def expectedUtility (utility : Outcome → ι → ℝ) (agent : ι) (law : FinDist Outcome) : ℝ :=
  law.expect fun outcome => utility outcome agent

@[simp]
theorem expectedUtility_pure (utility : Outcome → ι → ℝ) (agent : ι) (outcome : Outcome) :
    expectedUtility utility agent (FinDist.pure outcome) = utility outcome agent :=
  FinDist.expect_pure ..

theorem expectedUtility_bind (utility : Outcome → ι → ℝ) (agent : ι) {α : Type*}
    (μ : FinDist α) (f : α → FinDist Outcome) :
    expectedUtility utility agent (μ.bind f) =
      μ.expect fun a => expectedUtility utility agent (f a) :=
  FinDist.expect_bind ..

/-- Expected utility of a correlated profile law is the profile-law
expectation of the utility generated at each recommended profile. -/
theorem expectedUtility_outcomeLaw (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (agent : ι)
    (μ : FinDist (Profile F.sig)) :
    expectedUtility utility agent (F.outcomeLaw μ) =
      μ.expect fun profile => expectedUtility utility agent (F.play profile) := by
  unfold GameForm.outcomeLaw
  exact expectedUtility_bind ..

/-- Mapping every recommendation before play maps the integrand in the same
way. This covers both constant and recommendation-dependent deviations. -/
theorem expectedUtility_outcomeLaw_map (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (agent : ι)
    (μ : FinDist (Profile F.sig)) (respond : Profile F.sig → Profile F.sig) :
    expectedUtility utility agent (F.outcomeLaw (μ.map respond)) =
      μ.expect fun profile =>
        expectedUtility utility agent (F.play (respond profile)) := by
  rw [expectedUtility_outcomeLaw, FinDist.expect_map]

@[simp]
theorem expectedUtility_map (utility : Outcome' → ι → ℝ) (agent : ι)
    (relabel : Outcome → Outcome') (law : FinDist Outcome) :
    expectedUtility utility agent (law.map relabel) =
      expectedUtility (fun outcome => utility (relabel outcome)) agent law :=
  FinDist.expect_map ..

/-- The expected-utility weak preference. `euPreference u agent preferred
alternative` holds exactly when `alternative` has no greater expected utility. -/
def euPreference (utility : Outcome → ι → ℝ) : WeakPreference ι Outcome :=
  fun agent preferred alternative =>
    expectedUtility utility agent alternative ≤ expectedUtility utility agent preferred

@[simp]
theorem euPreference_apply (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : FinDist Outcome) :
    euPreference utility agent preferred alternative =
      (expectedUtility utility agent alternative ≤
        expectedUtility utility agent preferred) := rfl

/-- Expected-utility preference with an additive deviation allowance. -/
def euPreferenceWithin (ε : ℝ) (utility : Outcome → ι → ℝ) :
    WeakPreference ι Outcome :=
  fun agent preferred alternative =>
    expectedUtility utility agent alternative ≤ expectedUtility utility agent preferred + ε

@[simp]
theorem euPreferenceWithin_apply (ε : ℝ) (utility : Outcome → ι → ℝ)
    (agent : ι) (preferred alternative : FinDist Outcome) :
    euPreferenceWithin ε utility agent preferred alternative =
      (expectedUtility utility agent alternative ≤
        expectedUtility utility agent preferred + ε) := rfl

/-- The preference package of a bundled utility game. -/
def UtilityGame.preference (G : UtilityGame ι) : WeakPreference ι G.form.sig.Outcome :=
  euPreference G.utility

theorem euPreference_reflexive (utility : Outcome → ι → ℝ) :
    Preference.Reflexive (euPreference utility) := fun _ _ => le_refl _

theorem euPreference_transitive (utility : Outcome → ι → ℝ) :
    Preference.Transitive (euPreference utility) :=
  fun _ _ _ _ hfirst hsecond => le_trans hsecond hfirst

theorem euPreference_total (utility : Outcome → ι → ℝ) :
    Preference.Total (euPreference utility) :=
  fun _ _ _ => (le_total _ _).symm.imp id id

/-! ## Team utilities -/

/-- A team (identical-interest) utility assigns every player the same value at
each outcome. This property belongs to utility evaluation itself; potential
games and zero-sum games consume it without owning a duplicate definition. -/
def IsTeamGame (utility : Outcome → ι → ℝ) : Prop :=
  ∀ outcome first second, utility outcome first = utility outcome second

/-- Team players have equal expected utility under every finite outcome law. -/
theorem IsTeamGame.expectedUtility_eq {utility : Outcome → ι → ℝ}
    (hteam : IsTeamGame utility) (law : FinDist Outcome) (first second : ι) :
    expectedUtility utility first law = expectedUtility utility second law := by
  unfold expectedUtility
  apply FinDist.expect_congr
  intro outcome _
  exact hteam outcome first second

/-- At a Nash profile of a team game, a unilateral deviation cannot improve
any player's expected utility, not only the deviator's. -/
theorem IsTeamGame.isNash_deviation_nonimproving [DecidableEq ι]
    {F : GameForm ι} {utility : F.sig.Outcome → ι → ℝ}
    (hteam : IsTeamGame utility) {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile)
    (who : ι) (replacement : F.sig.Strategy who) (observer : ι) :
    expectedUtility utility observer (F.play (Profile.update profile who replacement)) ≤
      expectedUtility utility observer (F.play profile) := by
  calc
    expectedUtility utility observer (F.play (Profile.update profile who replacement)) =
        expectedUtility utility who (F.play (Profile.update profile who replacement)) :=
      hteam.expectedUtility_eq _ observer who
    _ ≤ expectedUtility utility who (F.play profile) :=
      (isNash_iff profile).1 hnash who replacement
    _ = expectedUtility utility observer (F.play profile) :=
      hteam.expectedUtility_eq _ who observer

theorem euPreference_strict_iff (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : FinDist Outcome) :
    Preference.strict (euPreference utility) agent preferred alternative ↔
      expectedUtility utility agent alternative <
        expectedUtility utility agent preferred :=
  lt_iff_le_not_ge.symm

theorem euPreference_convex (utility : Outcome → ι → ℝ) :
    Preference.Convex (euPreference utility) := by
  intro agent t h0 h1 firstPreferred firstAlternative secondPreferred secondAlternative
    hfirst hsecond
  show expectedUtility utility agent (FinDist.mix t h0 h1 _ _) ≤
    expectedUtility utility agent (FinDist.mix t h0 h1 _ _)
  unfold expectedUtility
  rw [FinDist.expect_mix, FinDist.expect_mix]
  exact add_le_add (mul_le_mul_of_nonneg_left hfirst h0)
    (mul_le_mul_of_nonneg_left hsecond (by linarith))

/-! ## Positive-affine invariance -/

/-- Rescale and shift each player's utility. -/
def affineUtility (utility : Outcome → ι → ℝ) (scale shift : ι → ℝ) : Outcome → ι → ℝ :=
  fun outcome agent => scale agent * utility outcome agent + shift agent

theorem expectedUtility_affine (utility : Outcome → ι → ℝ) (scale shift : ι → ℝ)
    (agent : ι) (law : FinDist Outcome) :
    expectedUtility (affineUtility utility scale shift) agent law =
      scale agent * expectedUtility utility agent law + shift agent := by
  unfold expectedUtility affineUtility
  rw [FinDist.expect_add, FinDist.expect_smul, FinDist.expect_const]

/-- A positive affine rescaling does not change the expected-utility
preference, hence changes no solution concept defined from it. -/
theorem euPreference_affine (utility : Outcome → ι → ℝ) {scale shift : ι → ℝ}
    (hscale : ∀ agent, 0 < scale agent) (agent : ι)
    (preferred alternative : FinDist Outcome) :
    euPreference (affineUtility utility scale shift) agent preferred alternative ↔
      euPreference utility agent preferred alternative := by
  simp only [euPreference_apply, expectedUtility_affine, add_le_add_iff_right]
  exact ⟨fun h => le_of_mul_le_mul_left h (hscale agent),
    fun h => mul_le_mul_of_nonneg_left h (hscale agent).le⟩

/-! ## Outcome relabeling and utility pullback -/

section Relabel

variable [DecidableEq ι]

/-- Relabeling outcomes and pulling the utility back along the relabeling leaves
Nash equilibrium unchanged. No cast appears in the statement because the
relabeled signature keeps the original strategy carriers. -/
theorem isNash_mapOutcome (F : GameForm ι) (relabel : F.sig.Outcome → Outcome')
    (utility : Outcome' → ι → ℝ) (profile : Profile F.sig) :
    IsNash (F.mapOutcome relabel) (euPreference utility) profile ↔
      IsNash F (euPreference fun outcome => utility (relabel outcome)) profile := by
  rw [isNash_iff, isNash_iff]
  refine forall_congr' fun who => forall_congr' fun replacement => ?_
  -- `(F.mapOutcome relabel).sig.Outcome` and `Outcome'` are definitionally equal
  -- but not equal at `instances` transparency, so restate the goal rather than
  -- rewriting the relabeled play law in place.
  show expectedUtility utility who
        ((F.play (Profile.update profile who replacement)).map relabel) ≤
      expectedUtility utility who ((F.play profile).map relabel) ↔
    expectedUtility (fun outcome => utility (relabel outcome)) who
        (F.play (Profile.update profile who replacement)) ≤
      expectedUtility (fun outcome => utility (relabel outcome)) who (F.play profile)
  rw [expectedUtility_map, expectedUtility_map]

end Relabel

/-! ## Expected-utility linearity in deviations

A randomized replacement is a convex combination of deterministic ones, so it
cannot beat all of them. This is why the standard equilibrium concepts may be
defined with deterministic deviations without weakening them. -/

section Linearity

variable [DecidableEq ι] {F : GameForm ι} {utility : Utility F.sig}

theorem isCoarseCorrelatedEq_randomized {statusQuo : FinDist (Profile F.sig)}
    (h : IsCoarseCorrelatedEq F (euPreference utility) statusQuo) :
    IsEquilibrium F (euPreference utility) statusQuo
      (DeviationScheme.unilateralRandomized F.sig) := by
  intro who replacement
  have key : ∀ s : F.sig.Strategy who,
      statusQuo.expect
          (fun profile =>
            expectedUtility utility who (F.play (Profile.update profile who s))) ≤
        expectedUtility utility who (F.outcomeLaw statusQuo) := by
    intro s
    simpa [GameForm.outcomeLaw, FinDist.map_eq_bind, expectedUtility_bind] using h who s
  have hswap :
      expectedUtility utility who
          (F.outcomeLaw
            ((DeviationScheme.unilateralRandomized F.sig).apply statusQuo who replacement)) =
        replacement.expect fun s =>
          statusQuo.expect fun profile =>
            expectedUtility utility who (F.play (Profile.update profile who s)) := by
    simp only [GameForm.outcomeLaw, DeviationScheme.unilateralRandomized_apply,
      FinDist.bind_bind, expectedUtility_bind, FinDist.expect_map]
    exact FinDist.expect_comm ..
  rw [euPreference_apply, hswap]
  calc
    (replacement.expect fun s =>
        statusQuo.expect fun profile =>
          expectedUtility utility who (F.play (Profile.update profile who s)))
        ≤ replacement.expect fun _ =>
            expectedUtility utility who (F.outcomeLaw statusQuo) :=
      FinDist.expect_mono fun s _ => key s
    _ = expectedUtility utility who (F.outcomeLaw statusQuo) := FinDist.expect_const ..

/-- In the mixed extension a randomized deviation is a mixture of pure ones, so
mixed Nash is decided by pure deviations alone. This is what lets an executable
checker verify a supplied mixed profile against finitely many tests. -/
theorem isNash_mixed_iff [Fintype ι] (mixedProfile : Profile F.sig.mixed) :
    IsNash F.mixed (euPreference utility) mixedProfile ↔
      ∀ (who : ι) (s : F.sig.Strategy who),
        expectedUtility utility who
            (F.mixed.play (Profile.update mixedProfile who (FinDist.pure s))) ≤
          expectedUtility utility who (F.mixed.play mixedProfile) := by
  rw [isNash_iff]
  refine ⟨fun h who s => h who (FinDist.pure s), fun h who replacement => ?_⟩
  rw [euPreference_apply, GameForm.mixed_play_update, expectedUtility_bind]
  calc
    (replacement.expect fun s =>
        expectedUtility utility who
          (F.mixed.play (Profile.update mixedProfile who (FinDist.pure s))))
        ≤ replacement.expect fun _ =>
            expectedUtility utility who (F.mixed.play mixedProfile) :=
      FinDist.expect_mono fun s _ => h who s
    _ = expectedUtility utility who (F.mixed.play mixedProfile) := FinDist.expect_const ..

end Linearity

end GameTheory
