/-
# Guarded expected utility and preference

The payoff law is a PMF. Numerical expectation and expected-utility preference
carry integration certificates only for the compared laws.
-/

import GameTheory.Core.Preference
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationMap
import GameTheory.Math.Probability.ExpectationMixture

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι uo uo'

variable {ι : Type uι} {Outcome : Type uo} {Outcome' : Type uo'}

/-- The player's realized payoff is integrable under the specified outcome law. -/
abbrev UtilityIntegrable {Outcome : Type*} (utility : Outcome → ι → ℝ)
    (agent : ι) (law : PMF Outcome) : Prop :=
  PayoffIntegrable law (fun outcome => utility outcome agent)


/-- Expected utility is defined only when the payoff is absolutely integrable
under the outcome law. -/
def expectedUtility (utility : Outcome → ι → ℝ) (agent : ι)
    (law : PMF Outcome) (h : UtilityIntegrable utility agent law) : ℝ :=
  expect law (fun outcome => utility outcome agent) h

theorem expectedUtility_congr_law (utility : Outcome → ι → ℝ) (agent : ι)
    {law law' : PMF Outcome} (hlaw : law = law')
    (h : UtilityIntegrable utility agent law)
    (h' : UtilityIntegrable utility agent law') :
    expectedUtility utility agent law h = expectedUtility utility agent law' h' := by
  cases hlaw
  rfl

@[simp]
theorem expectedUtility_pure (utility : Outcome → ι → ℝ) (agent : ι)
    (outcome : Outcome) :
    expectedUtility utility agent (PMF.pure outcome)
      (payoffIntegrable_pure outcome (fun outcome => utility outcome agent)) =
        utility outcome agent := by
  exact expect_pure outcome (fun outcome => utility outcome agent) _

theorem expectedUtility_bind (utility : Outcome → ι → ℝ) (agent : ι)
    {α : Type*} (μ : PMF α) (f : α → PMF Outcome)
    (hbind : UtilityIntegrable utility agent (μ.bind f))
    (hcond : ∀ a, UtilityIntegrable utility agent (f a)) :
    expectedUtility utility agent (μ.bind f) hbind =
      expect μ (fun a => expectedUtility utility agent (f a) (hcond a))
        (payoffIntegrable_bind_conditionalExpectation μ f
          (fun outcome => utility outcome agent) hbind hcond) := by
  exact expect_bind_tower μ f (fun outcome => utility outcome agent) hbind hcond


@[simp]
theorem expectedUtility_map (utility : Outcome' → ι → ℝ) (agent : ι)
    (relabel : Outcome → Outcome') (law : PMF Outcome)
    (h : UtilityIntegrable utility agent (law.map relabel)) :
    expectedUtility utility agent (law.map relabel) h =
      expectedUtility (fun outcome => utility (relabel outcome)) agent law
        ((payoffIntegrable_map_iff relabel law
          (fun outcome => utility outcome agent)).mp h) := by
  exact expect_map relabel law (fun outcome => utility outcome agent)
    ((payoffIntegrable_map_iff relabel law
      (fun outcome => utility outcome agent)).mp h) h

theorem expectedUtility_mix (utility : Outcome → ι → ℝ) (agent : ι)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (first second : PMF Outcome)
    (hfirst : UtilityIntegrable utility agent first)
    (hsecond : UtilityIntegrable utility agent second) :
    expectedUtility utility agent (mix t h0 h1 first second)
        (payoffIntegrable_mix t h0 h1 first second
          (fun outcome => utility outcome agent) hfirst hsecond) =
      t * expectedUtility utility agent first hfirst +
        (1 - t) * expectedUtility utility agent second hsecond :=
  expect_mix t h0 h1 first second (fun outcome => utility outcome agent)
    hfirst hsecond

/-- The expected-utility weak preference. `euPreference u agent preferred
alternative` holds exactly when `alternative` has no greater expected utility. -/
def euPreference (utility : Outcome → ι → ℝ) : WeakPreference ι Outcome :=
  fun agent preferred alternative =>
    ∃ hpreferred : UtilityIntegrable utility agent preferred,
      ∃ halternative : UtilityIntegrable utility agent alternative,
        expectedUtility utility agent alternative halternative ≤
          expectedUtility utility agent preferred hpreferred

@[simp]
theorem euPreference_apply (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : PMF Outcome) :
    euPreference utility agent preferred alternative =
      (∃ hpreferred : UtilityIntegrable utility agent preferred,
        ∃ halternative : UtilityIntegrable utility agent alternative,
          expectedUtility utility agent alternative halternative ≤
            expectedUtility utility agent preferred hpreferred) := rfl

/-- Expected-utility preference with an additive deviation allowance. -/
def euPreferenceWithin (ε : ℝ) (utility : Outcome → ι → ℝ) :
    WeakPreference ι Outcome :=
  fun agent preferred alternative =>
    ∃ hpreferred : UtilityIntegrable utility agent preferred,
      ∃ halternative : UtilityIntegrable utility agent alternative,
        expectedUtility utility agent alternative halternative ≤
          expectedUtility utility agent preferred hpreferred + ε

@[simp]
theorem euPreferenceWithin_apply (ε : ℝ) (utility : Outcome → ι → ℝ)
    (agent : ι) (preferred alternative : PMF Outcome) :
    euPreferenceWithin ε utility agent preferred alternative =
      (∃ hpreferred : UtilityIntegrable utility agent preferred,
        ∃ halternative : UtilityIntegrable utility agent alternative,
          expectedUtility utility agent alternative halternative ≤
            expectedUtility utility agent preferred hpreferred + ε) := rfl

theorem euPreference_iff (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : PMF Outcome)
    (hpreferred : UtilityIntegrable utility agent preferred)
    (halternative : UtilityIntegrable utility agent alternative) :
    euPreference utility agent preferred alternative ↔
      expectedUtility utility agent alternative halternative ≤
        expectedUtility utility agent preferred hpreferred := by
  constructor
  · rintro ⟨hpreferred', halternative', hle⟩
    have hpeq : expectedUtility utility agent preferred hpreferred' =
        expectedUtility utility agent preferred hpreferred := by
      unfold expectedUtility
      exact expect_proof_irrel preferred _ hpreferred' hpreferred
    have haeq : expectedUtility utility agent alternative halternative' =
        expectedUtility utility agent alternative halternative := by
      unfold expectedUtility
      exact expect_proof_irrel alternative _ halternative' halternative
    rw [haeq, hpeq] at hle
    exact hle
  · exact fun hle => ⟨hpreferred, halternative, hle⟩

theorem euPreference_iff_of_bounded (utility : Outcome → ι → ℝ)
    (agent : ι) (preferred alternative : PMF Outcome) {C : ℝ}
    (hbound : ∀ outcome, |utility outcome agent| ≤ C) :
    euPreference utility agent preferred alternative ↔
      expectedUtility utility agent alternative
        (payoffIntegrable_of_bounded alternative _ hbound) ≤
      expectedUtility utility agent preferred
        (payoffIntegrable_of_bounded preferred _ hbound) :=
  euPreference_iff utility agent preferred alternative
    (payoffIntegrable_of_bounded preferred _ hbound)
    (payoffIntegrable_of_bounded alternative _ hbound)

theorem euPreference_pure_iff (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : Outcome) :
    euPreference utility agent (PMF.pure preferred) (PMF.pure alternative) ↔
      utility alternative agent ≤ utility preferred agent := by
  constructor
  · intro h
    rcases h with ⟨_, _, hle⟩
    simpa only [expectedUtility_pure] using hle
  · intro hle
    exact ⟨payoffIntegrable_pure preferred (fun outcome => utility outcome agent),
      payoffIntegrable_pure alternative (fun outcome => utility outcome agent),
      by simpa only [expectedUtility_pure] using hle⟩

theorem euPreference_map (utility : Outcome' → ι → ℝ) (agent : ι)
    (relabel : Outcome → Outcome') (preferred alternative : PMF Outcome) :
    euPreference utility agent (preferred.map relabel) (alternative.map relabel) ↔
      euPreference (fun outcome => utility (relabel outcome))
        agent preferred alternative := by
  constructor
  · rintro ⟨hp, ha, hle⟩
    refine ⟨(payoffIntegrable_map_iff relabel preferred
      (fun outcome => utility outcome agent)).mp hp,
      (payoffIntegrable_map_iff relabel alternative
        (fun outcome => utility outcome agent)).mp ha, ?_⟩
    simpa only [expectedUtility_map] using hle
  · rintro ⟨hp, ha, hle⟩
    refine ⟨(payoffIntegrable_map_iff relabel preferred
      (fun outcome => utility outcome agent)).mpr hp,
      (payoffIntegrable_map_iff relabel alternative
        (fun outcome => utility outcome agent)).mpr ha, ?_⟩
    simpa only [expectedUtility_map] using hle


theorem euPreference_reflexive (utility : Outcome → ι → ℝ) :
    (∀ agent law, UtilityIntegrable utility agent law) →
      Preference.Reflexive (euPreference utility) := by
  intro hintegrable agent law
  exact ⟨hintegrable agent law, hintegrable agent law, le_rfl⟩

theorem euPreference_transitive (utility : Outcome → ι → ℝ) :
    Preference.Transitive (euPreference utility) := by
  intro agent first middle last hfirst hsecond
  rcases hfirst with ⟨hfirst, hmiddle₁, hle₁⟩
  rcases hsecond with ⟨_, hlast, hle₂⟩
  exact ⟨hfirst, hlast, le_trans hle₂ hle₁⟩

theorem euPreference_total (utility : Outcome → ι → ℝ) :
    (∀ agent law, UtilityIntegrable utility agent law) →
      Preference.Total (euPreference utility) := by
  intro hintegrable agent preferred alternative
  have hpref := hintegrable agent preferred
  have halt := hintegrable agent alternative
  rcases le_total (expectedUtility utility agent preferred hpref)
      (expectedUtility utility agent alternative halt) with h | h
  · exact Or.inr ⟨halt, hpref, h⟩
  · exact Or.inl ⟨hpref, halt, h⟩


/-- A team (identical-interest) utility assigns every player the same value at
each outcome. This property belongs to utility evaluation itself; potential
games and zero-sum games consume it without owning a duplicate definition. -/
def IsTeamGame (utility : Outcome → ι → ℝ) : Prop :=
  ∀ outcome first second, utility outcome first = utility outcome second

/-- Team players have equal expected utility whenever both expectations exist. -/
theorem IsTeamGame.expectedUtility_eq {utility : Outcome → ι → ℝ}
    (hteam : IsTeamGame utility) (law : PMF Outcome) (first second : ι)
    (hfirst : UtilityIntegrable utility first law)
    (hsecond : UtilityIntegrable utility second law) :
    expectedUtility utility first law hfirst =
      expectedUtility utility second law hsecond := by
  unfold expectedUtility
  apply expect_congr_on_support (fun outcome _ => hteam outcome first second)


theorem euPreference_strict_iff (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : PMF Outcome)
    (hpreferred : UtilityIntegrable utility agent preferred)
    (halternative : UtilityIntegrable utility agent alternative) :
    Preference.strict (euPreference utility) agent preferred alternative ↔
    expectedUtility utility agent alternative halternative <
        expectedUtility utility agent preferred hpreferred := by
  simp only [Preference.strict, Rank.strict]
  rw [euPreference_iff utility agent preferred alternative hpreferred halternative,
    euPreference_iff utility agent alternative preferred halternative hpreferred]
  exact lt_iff_le_not_ge.symm

theorem euPreference_convex (utility : Outcome → ι → ℝ) :
    Preference.Convex (euPreference utility) := by
  intro agent t h0 h1 firstPreferred firstAlternative secondPreferred secondAlternative
    hfirst hsecond
  rcases hfirst with ⟨hp₁, ha₁, hle₁⟩
  rcases hsecond with ⟨hp₂, ha₂, hle₂⟩
  let hp := payoffIntegrable_mix t h0 h1 firstPreferred secondPreferred
    (fun outcome => utility outcome agent) hp₁ hp₂
  let ha := payoffIntegrable_mix t h0 h1 firstAlternative secondAlternative
    (fun outcome => utility outcome agent) ha₁ ha₂
  refine ⟨hp, ha, ?_⟩
  calc
    expectedUtility utility agent (mix t h0 h1 firstAlternative secondAlternative) ha =
        t * expectedUtility utility agent firstAlternative ha₁ +
          (1 - t) * expectedUtility utility agent secondAlternative ha₂ :=
      expectedUtility_mix utility agent t h0 h1 firstAlternative secondAlternative
        ha₁ ha₂
    _ ≤ t * expectedUtility utility agent firstPreferred hp₁ +
          (1 - t) * expectedUtility utility agent secondPreferred hp₂ :=
      add_le_add (mul_le_mul_of_nonneg_left hle₁ h0)
        (mul_le_mul_of_nonneg_left hle₂ (by linarith))
    _ = expectedUtility utility agent (mix t h0 h1 firstPreferred secondPreferred) hp :=
      (expectedUtility_mix utility agent t h0 h1 firstPreferred secondPreferred
        hp₁ hp₂).symm

/-! ## Positive-affine invariance -/

/-- Rescale and shift each player's utility. -/
def affineUtility (utility : Outcome → ι → ℝ) (scale shift : ι → ℝ) : Outcome → ι → ℝ :=
  fun outcome agent => scale agent * utility outcome agent + shift agent

theorem expectedUtility_affine (utility : Outcome → ι → ℝ) (scale shift : ι → ℝ)
    (agent : ι) (law : PMF Outcome)
    (hutility : UtilityIntegrable utility agent law) :
    expectedUtility (affineUtility utility scale shift) agent law
        (payoffIntegrable_add
          (payoffIntegrable_const_mul (c := scale agent) hutility)
          (payoffIntegrable_of_bounded law (fun _ => shift agent)
            (C := |shift agent|) (fun _ => by simp))) =
      scale agent * expectedUtility utility agent law hutility + shift agent := by
  let hshift := payoffIntegrable_of_bounded law (fun _ => shift agent)
    (C := |shift agent|) (fun _ => by simp)
  let hscaled := payoffIntegrable_const_mul (c := scale agent) hutility
  calc
    expectedUtility (affineUtility utility scale shift) agent law
        (payoffIntegrable_add hscaled hshift) =
      expect law (fun outcome => scale agent * utility outcome agent)
          hscaled + expect law (fun _ => shift agent) hshift := by
        unfold expectedUtility affineUtility
        exact expect_add hscaled hshift
    _ = scale agent * expectedUtility utility agent law hutility + shift agent := by
      unfold expectedUtility
      rw [expect_const_mul hutility, expect_constant law (shift agent) hshift]

private theorem expectedUtility_affine_of_cert
    (utility : Outcome → ι → ℝ) (scale shift : ι → ℝ)
    (agent : ι) (law : PMF Outcome)
    (hutility : UtilityIntegrable utility agent law)
    (haffine : UtilityIntegrable (affineUtility utility scale shift) agent law) :
    expectedUtility (affineUtility utility scale shift) agent law haffine =
      scale agent * expectedUtility utility agent law hutility + shift agent := by
  have hcanonical := payoffIntegrable_add
    (payoffIntegrable_const_mul (c := scale agent) hutility)
    (payoffIntegrable_of_bounded law (fun _ => shift agent)
      (C := |shift agent|) (fun _ => by simp))
  calc
    expectedUtility (affineUtility utility scale shift) agent law haffine =
        expectedUtility (affineUtility utility scale shift) agent law hcanonical := by
      unfold expectedUtility
      exact expect_proof_irrel law _ haffine hcanonical
    _ = scale agent * expectedUtility utility agent law hutility + shift agent :=
      expectedUtility_affine utility scale shift agent law hutility

theorem utilityIntegrable_affine_iff (utility : Outcome → ι → ℝ)
    (scale shift : ι → ℝ) (agent : ι) (law : PMF Outcome)
    (hscale : 0 < scale agent) :
    UtilityIntegrable (affineUtility utility scale shift) agent law ↔
      UtilityIntegrable utility agent law := by
  let c := shift agent
  let k := scale agent
  have hc : PayoffIntegrable law (fun _ => c) :=
    payoffIntegrable_of_bounded law (fun _ => c) (C := |c|) (fun _ => by simp)
  constructor
  · intro haffine
    have hdiff := payoffIntegrable_add haffine (payoffIntegrable_neg hc)
    have hback := payoffIntegrable_const_mul (c := k⁻¹) hdiff
    have hback' : PayoffIntegrable law
        (fun outcome => k⁻¹ * ((k * utility outcome agent + c) - c)) := by
      simpa [affineUtility, c, k, sub_eq_add_neg] using hback
    have hidentity :
        (fun outcome => k⁻¹ * ((k * utility outcome agent + c) - c)) =
          (fun outcome => utility outcome agent) := by
      funext outcome
      calc
        k⁻¹ * ((k * utility outcome agent + c) - c) =
            k⁻¹ * (k * utility outcome agent) := by ring
        _ = (k⁻¹ * k) * utility outcome agent := by ring
        _ = utility outcome agent := by
          rw [inv_mul_cancel₀ (ne_of_gt hscale), one_mul]
    apply hback'.congr
    intro outcome
    rw [hidentity]
  · intro hutility
    have hscaled := payoffIntegrable_const_mul (c := k) hutility
    have hsum := payoffIntegrable_add hscaled hc
    simpa only [UtilityIntegrable, PayoffIntegrable, affineUtility, c, k] using hsum

/-- A positive affine rescaling does not change the expected-utility
preference, hence changes no solution concept defined from it. -/
theorem euPreference_affine (utility : Outcome → ι → ℝ) {scale shift : ι → ℝ}
    (hscale : ∀ agent, 0 < scale agent) (agent : ι)
    (preferred alternative : PMF Outcome) :
    euPreference (affineUtility utility scale shift) agent preferred alternative ↔
      euPreference utility agent preferred alternative := by
  constructor
  · rintro ⟨hpAffine, haAffine, hle⟩
    have hp := (utilityIntegrable_affine_iff utility scale shift agent preferred
      (hscale agent)).mp hpAffine
    have ha := (utilityIntegrable_affine_iff utility scale shift agent alternative
      (hscale agent)).mp haAffine
    have hscaled : scale agent * expectedUtility utility agent alternative ha +
        shift agent ≤ scale agent * expectedUtility utility agent preferred hp +
          shift agent := by
      simpa only [expectedUtility_affine_of_cert utility scale shift agent alternative
          ha haAffine,
        expectedUtility_affine_of_cert utility scale shift agent preferred hp hpAffine]
        using hle
    have hmul := (add_le_add_iff_right (shift agent)).mp hscaled
    exact ⟨hp, ha, le_of_mul_le_mul_left hmul (hscale agent)⟩
  · rintro ⟨hp, ha, hle⟩
    have hpAffine := (utilityIntegrable_affine_iff utility scale shift agent preferred
      (hscale agent)).mpr hp
    have haAffine := (utilityIntegrable_affine_iff utility scale shift agent alternative
      (hscale agent)).mpr ha
    refine ⟨hpAffine, haAffine, ?_⟩
    calc
      expectedUtility (affineUtility utility scale shift) agent alternative haAffine =
          scale agent * expectedUtility utility agent alternative ha + shift agent :=
        expectedUtility_affine_of_cert utility scale shift agent alternative ha haAffine
      _ ≤ scale agent * expectedUtility utility agent preferred hp + shift agent :=
        by
          simpa [add_comm] using add_le_add_right
            (mul_le_mul_of_nonneg_left hle (le_of_lt (hscale agent)))
              (shift agent)
      _ = expectedUtility (affineUtility utility scale shift) agent preferred hpAffine :=
        (expectedUtility_affine_of_cert utility scale shift agent preferred hp hpAffine).symm

/-! ## Outcome relabeling and utility pullback -/

/-- Two encodings of one draw have equal guarded values when their realized
payoffs agree pointwise. -/
theorem expectedUtility_two_maps {α β γ : Type*}
    (μ : PMF α) (f : α → β) (g : α → γ)
    (u : β → ι → ℝ) (v : γ → ι → ℝ) (who : ι)
    (heq : ∀ a, u (f a) who = v (g a) who)
    (hf : UtilityIntegrable u who (μ.map f)) :
    ∃ hg : UtilityIntegrable v who (μ.map g),
      expectedUtility u who (μ.map f) hf =
        expectedUtility v who (μ.map g) hg := by
  have hsource : PayoffIntegrable μ (fun a => u (f a) who) :=
    (payoffIntegrable_map_iff f μ (fun b => u b who)).mp hf
  have hsource' : PayoffIntegrable μ (fun a => v (g a) who) :=
    payoffIntegrable_congr_on_support (fun a _ => heq a) hsource
  let hg : UtilityIntegrable v who (μ.map g) :=
    (payoffIntegrable_map_iff g μ (fun c => v c who)).mpr hsource'
  refine ⟨hg, ?_⟩
  calc
    expectedUtility u who (μ.map f) hf =
        expect μ (fun a => u (f a) who) hsource := by
          exact expectedUtility_map u who f μ hf
    _ = expect μ (fun a => v (g a) who) hsource' :=
      expect_congr_on_support (fun a _ => heq a) hsource hsource'
    _ = expectedUtility v who (μ.map g) hg := by
      exact (expectedUtility_map v who g μ hg).symm

theorem utilityIntegrable_two_maps_iff {α β γ : Type*}
    (μ : PMF α) (f : α → β) (g : α → γ)
    (u : β → ι → ℝ) (v : γ → ι → ℝ) (who : ι)
    (heq : ∀ a, u (f a) who = v (g a) who) :
    UtilityIntegrable u who (μ.map f) ↔
      UtilityIntegrable v who (μ.map g) := by
  constructor
  · intro hf
    exact (expectedUtility_two_maps μ f g u v who heq hf).choose
  · intro hg
    exact (expectedUtility_two_maps μ g f v u who
      (fun a => (heq a).symm) hg).choose

theorem expectedUtility_two_maps_eq {α β γ : Type*}
    (μ : PMF α) (f : α → β) (g : α → γ)
    (u : β → ι → ℝ) (v : γ → ι → ℝ) (who : ι)
    (heq : ∀ a, u (f a) who = v (g a) who)
    (hf : UtilityIntegrable u who (μ.map f))
    (hg : UtilityIntegrable v who (μ.map g)) :
    expectedUtility u who (μ.map f) hf =
      expectedUtility v who (μ.map g) hg := by
  obtain ⟨hg', heqValue⟩ := expectedUtility_two_maps μ f g u v who heq hf
  exact heqValue

theorem euPreference_two_maps_iff {α β γ : Type*}
    (μ : PMF α) (f₁ f₂ : α → β) (g₁ g₂ : α → γ)
    (u : β → ι → ℝ) (v : γ → ι → ℝ) (who : ι)
    (h₁ : ∀ a, u (f₁ a) who = v (g₁ a) who)
    (h₂ : ∀ a, u (f₂ a) who = v (g₂ a) who) :
    euPreference u who (μ.map f₁) (μ.map f₂) ↔
      euPreference v who (μ.map g₁) (μ.map g₂) := by
  constructor
  · rintro ⟨hp, ha, hle⟩
    obtain ⟨hp', hpeq⟩ := expectedUtility_two_maps μ f₁ g₁ u v who h₁ hp
    obtain ⟨ha', haeq⟩ := expectedUtility_two_maps μ f₂ g₂ u v who h₂ ha
    exact ⟨hp', ha', by simpa only [hpeq, haeq] using hle⟩
  · rintro ⟨hp, ha, hle⟩
    obtain ⟨hp', hpeq⟩ :=
      expectedUtility_two_maps μ g₁ f₁ v u who (fun a => (h₁ a).symm) hp
    obtain ⟨ha', haeq⟩ :=
      expectedUtility_two_maps μ g₂ f₂ v u who (fun a => (h₂ a).symm) ha
    exact ⟨hp', ha', by simpa only [hpeq, haeq] using hle⟩



end GameTheory
