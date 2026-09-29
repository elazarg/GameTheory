/-
# Expected utility and preference

The payoff law is a PMF. Expected utility is a total real value, defined as the
expectation when the payoff is integrable (and `0` otherwise). Preferences
compare laws by their expected utility in the extended reals, so a law whose
expectation is `+∞` or `−∞` is ranked like any other; only a law whose gains
and losses both have infinite expectation has no expected utility and is never
ranked.
-/

import GameTheory.Core.Preference
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationMap
import GameTheory.Math.Probability.ExpectationMixture
import GameTheory.Math.Probability.ExtendedExpectation

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι uo uo'

variable {ι : Type uι} {Outcome : Type uo} {Outcome' : Type uo'}

/-- The player's realized payoff is integrable under the specified outcome law. -/
abbrev UtilityIntegrable {Outcome : Type*} (utility : Outcome → ι → ℝ)
    (agent : ι) (law : PMF Outcome) : Prop :=
  PayoffIntegrable law (fun outcome => utility outcome agent)

/-- The expected utility of an outcome law. It is meaningful exactly when
`UtilityIntegrable utility agent law` holds. -/
def expectedUtility (utility : Outcome → ι → ℝ) (agent : ι)
    (law : PMF Outcome) : ℝ :=
  expect law (fun outcome => utility outcome agent)

theorem expectedUtility_congr_law (utility : Outcome → ι → ℝ) (agent : ι)
    {law law' : PMF Outcome} (hlaw : law = law') :
    expectedUtility utility agent law = expectedUtility utility agent law' := by
  rw [hlaw]

@[simp]
theorem expectedUtility_pure (utility : Outcome → ι → ℝ) (agent : ι)
    (outcome : Outcome) :
    expectedUtility utility agent (PMF.pure outcome) = utility outcome agent :=
  expect_pure outcome (fun outcome => utility outcome agent)

theorem expectedUtility_bind (utility : Outcome → ι → ℝ) (agent : ι)
    {α : Type*} (μ : PMF α) (f : α → PMF Outcome)
    (hbind : UtilityIntegrable utility agent (μ.bind f)) :
    expectedUtility utility agent (μ.bind f) =
      expect μ (fun a => expectedUtility utility agent (f a)) :=
  expect_bind_tower μ f (fun outcome => utility outcome agent) hbind

@[simp]
theorem expectedUtility_map (utility : Outcome' → ι → ℝ) (agent : ι)
    (relabel : Outcome → Outcome') (law : PMF Outcome) :
    expectedUtility utility agent (law.map relabel) =
      expectedUtility (fun outcome => utility (relabel outcome)) agent law :=
  expect_map relabel law (fun outcome => utility outcome agent)

theorem expectedUtility_mix (utility : Outcome → ι → ℝ) (agent : ι)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (first second : PMF Outcome)
    (hfirst : UtilityIntegrable utility agent first)
    (hsecond : UtilityIntegrable utility agent second) :
    expectedUtility utility agent (mix t h0 h1 first second) =
      t * expectedUtility utility agent first +
        (1 - t) * expectedUtility utility agent second :=
  expect_mix t h0 h1 first second (fun outcome => utility outcome agent)
    hfirst hsecond

/-- The player's payoff has an expectation, possibly infinite, under the law:
its gains and losses do not both have infinite expectation. -/
abbrev UtilityHasExpectation {Outcome : Type*} (utility : Outcome → ι → ℝ)
    (agent : ι) (law : PMF Outcome) : Prop :=
  HasExpectation law (fun outcome => utility outcome agent)

/-- Expected utility in the extended reals. It is meaningful exactly when
`UtilityHasExpectation utility agent law` holds. -/
def extendedExpectedUtility (utility : Outcome → ι → ℝ) (agent : ι)
    (law : PMF Outcome) : EReal :=
  extendedExpect law (fun outcome => utility outcome agent)

theorem UtilityIntegrable.hasExpectation {utility : Outcome → ι → ℝ} {agent : ι}
    {law : PMF Outcome} (h : UtilityIntegrable utility agent law) :
    UtilityHasExpectation utility agent law :=
  hasExpectation_of_payoffIntegrable h

theorem extendedExpectedUtility_eq {utility : Outcome → ι → ℝ} {agent : ι}
    {law : PMF Outcome} (h : UtilityIntegrable utility agent law) :
    extendedExpectedUtility utility agent law = expectedUtility utility agent law :=
  extendedExpect_eq_expect h

/-- Between integrable laws, extended expected utilities order as the real ones. -/
theorem extendedExpectedUtility_le_iff {utility : Outcome → ι → ℝ} {agent : ι}
    {first second : PMF Outcome} (hfirst : UtilityIntegrable utility agent first)
    (hsecond : UtilityIntegrable utility agent second) :
    extendedExpectedUtility utility agent first ≤ extendedExpectedUtility utility agent second ↔
      expectedUtility utility agent first ≤ expectedUtility utility agent second := by
  rw [extendedExpectedUtility_eq hfirst, extendedExpectedUtility_eq hsecond,
    EReal.coe_le_coe_iff]

theorem extendedExpectedUtility_lt_iff {utility : Outcome → ι → ℝ} {agent : ι}
    {first second : PMF Outcome} (hfirst : UtilityIntegrable utility agent first)
    (hsecond : UtilityIntegrable utility agent second) :
    extendedExpectedUtility utility agent first < extendedExpectedUtility utility agent second ↔
      expectedUtility utility agent first < expectedUtility utility agent second := by
  rw [extendedExpectedUtility_eq hfirst, extendedExpectedUtility_eq hsecond,
    EReal.coe_lt_coe_iff]

theorem extendedExpectedUtility_congr_law (utility : Outcome → ι → ℝ) (agent : ι)
    {law law' : PMF Outcome} (hlaw : law = law') :
    extendedExpectedUtility utility agent law =
      extendedExpectedUtility utility agent law' := by
  rw [hlaw]

@[simp]
theorem extendedExpectedUtility_pure (utility : Outcome → ι → ℝ) (agent : ι)
    (outcome : Outcome) :
    extendedExpectedUtility utility agent (PMF.pure outcome) = utility outcome agent :=
  extendedExpect_pure outcome (fun outcome => utility outcome agent)

@[simp]
theorem extendedExpectedUtility_map (utility : Outcome' → ι → ℝ) (agent : ι)
    (relabel : Outcome → Outcome') (law : PMF Outcome) :
    extendedExpectedUtility utility agent (law.map relabel) =
      extendedExpectedUtility (fun outcome => utility (relabel outcome)) agent law :=
  extendedExpect_map relabel law (fun outcome => utility outcome agent)

/-- The expected-utility weak preference. `euPreference u agent preferred
alternative` holds exactly when both laws have an expected utility, possibly
infinite, and `alternative` has no greater expected utility. -/
def euPreference (utility : Outcome → ι → ℝ) : WeakPreference ι Outcome :=
  fun agent preferred alternative =>
    UtilityHasExpectation utility agent preferred ∧
      UtilityHasExpectation utility agent alternative ∧
        extendedExpectedUtility utility agent alternative ≤
          extendedExpectedUtility utility agent preferred

@[simp]
theorem euPreference_apply (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : PMF Outcome) :
    euPreference utility agent preferred alternative =
      (UtilityHasExpectation utility agent preferred ∧
        UtilityHasExpectation utility agent alternative ∧
          extendedExpectedUtility utility agent alternative ≤
            extendedExpectedUtility utility agent preferred) := rfl

/-- Expected-utility preference with an additive deviation allowance. -/
def euPreferenceWithin (ε : ℝ) (utility : Outcome → ι → ℝ) :
    WeakPreference ι Outcome :=
  fun agent preferred alternative =>
    UtilityHasExpectation utility agent preferred ∧
      UtilityHasExpectation utility agent alternative ∧
        extendedExpectedUtility utility agent alternative ≤
          extendedExpectedUtility utility agent preferred + ε

@[simp]
theorem euPreferenceWithin_apply (ε : ℝ) (utility : Outcome → ι → ℝ)
    (agent : ι) (preferred alternative : PMF Outcome) :
    euPreferenceWithin ε utility agent preferred alternative =
      (UtilityHasExpectation utility agent preferred ∧
        UtilityHasExpectation utility agent alternative ∧
          extendedExpectedUtility utility agent alternative ≤
            extendedExpectedUtility utility agent preferred + ε) := rfl

/-- Between integrable laws the preference is the real comparison. -/
theorem euPreference_iff (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : PMF Outcome)
    (hpreferred : UtilityIntegrable utility agent preferred)
    (halternative : UtilityIntegrable utility agent alternative) :
    euPreference utility agent preferred alternative ↔
      expectedUtility utility agent alternative ≤
        expectedUtility utility agent preferred := by
  rw [euPreference_apply, extendedExpectedUtility_eq hpreferred,
    extendedExpectedUtility_eq halternative, EReal.coe_le_coe_iff]
  exact ⟨fun h => h.2.2, fun hle => ⟨hpreferred.hasExpectation,
    halternative.hasExpectation, hle⟩⟩

/-- Between integrable laws the relaxed preference is the real comparison. -/
theorem euPreferenceWithin_iff (ε : ℝ) (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : PMF Outcome)
    (hpreferred : UtilityIntegrable utility agent preferred)
    (halternative : UtilityIntegrable utility agent alternative) :
    euPreferenceWithin ε utility agent preferred alternative ↔
      expectedUtility utility agent alternative ≤
        expectedUtility utility agent preferred + ε := by
  rw [euPreferenceWithin_apply, extendedExpectedUtility_eq hpreferred,
    extendedExpectedUtility_eq halternative, ← EReal.coe_add, EReal.coe_le_coe_iff]
  exact ⟨fun h => h.2.2, fun hle => ⟨hpreferred.hasExpectation,
    halternative.hasExpectation, hle⟩⟩

/-- A mixture of alternatives, each weakly dispreferred to `base`, is weakly
dispreferred to `base` whenever the mixture has an expected utility. -/
theorem euPreference_bind {utility : Outcome → ι → ℝ} {agent : ι}
    {base : PMF Outcome} {α : Type*} (μ : PMF α) (q : α → PMF Outcome)
    (hall : ∀ a ∈ μ.support, euPreference utility agent base (q a))
    (hbind : UtilityHasExpectation utility agent (μ.bind q)) :
    euPreference utility agent base (μ.bind q) := by
  obtain ⟨a₀, ha₀⟩ := μ.support_nonempty
  exact ⟨(hall a₀ ha₀).1, hbind, extendedExpect_bind_le fun a ha => (hall a ha).2.2⟩

/-- A mixture of alternatives, each weakly preferred to `base`, is weakly
preferred to `base` whenever the mixture has an expected utility. -/
theorem euPreference_bind_left {utility : Outcome → ι → ℝ} {agent : ι}
    {base : PMF Outcome} {α : Type*} (μ : PMF α) (q : α → PMF Outcome)
    (hall : ∀ a ∈ μ.support, euPreference utility agent (q a) base)
    (hbind : UtilityHasExpectation utility agent (μ.bind q)) :
    euPreference utility agent (μ.bind q) base := by
  obtain ⟨a₀, ha₀⟩ := μ.support_nonempty
  exact ⟨hbind, (hall a₀ ha₀).2.1, le_extendedExpect_bind (fun a ha => (hall a ha).2.2) hbind⟩

theorem euPreference_iff_of_bounded (utility : Outcome → ι → ℝ)
    (agent : ι) (preferred alternative : PMF Outcome) {C : ℝ}
    (hbound : ∀ outcome, |utility outcome agent| ≤ C) :
    euPreference utility agent preferred alternative ↔
      expectedUtility utility agent alternative ≤
        expectedUtility utility agent preferred :=
  euPreference_iff utility agent preferred alternative
    (payoffIntegrable_of_bounded preferred _ hbound)
    (payoffIntegrable_of_bounded alternative _ hbound)

theorem euPreference_pure_iff (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : Outcome) :
    euPreference utility agent (PMF.pure preferred) (PMF.pure alternative) ↔
      utility alternative agent ≤ utility preferred agent := by
  rw [euPreference_iff utility agent _ _
    (payoffIntegrable_pure preferred (fun outcome => utility outcome agent))
    (payoffIntegrable_pure alternative (fun outcome => utility outcome agent)),
    expectedUtility_pure, expectedUtility_pure]

theorem euPreference_map (utility : Outcome' → ι → ℝ) (agent : ι)
    (relabel : Outcome → Outcome') (preferred alternative : PMF Outcome) :
    euPreference utility agent (preferred.map relabel) (alternative.map relabel) ↔
      euPreference (fun outcome => utility (relabel outcome))
        agent preferred alternative := by
  simp only [euPreference_apply, UtilityHasExpectation, hasExpectation_map_iff,
    extendedExpectedUtility_map]
  rfl

theorem euPreference_reflexive (utility : Outcome → ι → ℝ) :
    (∀ agent law, UtilityHasExpectation utility agent law) →
      Preference.Reflexive (euPreference utility) := by
  intro hexpect agent law
  exact ⟨hexpect agent law, hexpect agent law, le_rfl⟩

theorem euPreference_transitive (utility : Outcome → ι → ℝ) :
    Preference.Transitive (euPreference utility) := by
  intro agent first middle last hfirst hsecond
  rcases hfirst with ⟨hfirst, _, hle₁⟩
  rcases hsecond with ⟨_, hlast, hle₂⟩
  exact ⟨hfirst, hlast, le_trans hle₂ hle₁⟩

theorem euPreference_total (utility : Outcome → ι → ℝ) :
    (∀ agent law, UtilityHasExpectation utility agent law) →
      Preference.Total (euPreference utility) := by
  intro hexpect agent preferred alternative
  have hpref := hexpect agent preferred
  have halt := hexpect agent alternative
  rcases le_total (extendedExpectedUtility utility agent preferred)
      (extendedExpectedUtility utility agent alternative) with h | h
  · exact Or.inr ⟨halt, hpref, h⟩
  · exact Or.inl ⟨hpref, halt, h⟩


/-- A team (identical-interest) utility assigns every player the same value at
each outcome. This property belongs to utility evaluation itself; potential
games and zero-sum games consume it without owning a duplicate definition. -/
def IsTeamGame (utility : Outcome → ι → ℝ) : Prop :=
  ∀ outcome first second, utility outcome first = utility outcome second

/-- Team players have equal extended expected utility. -/
theorem IsTeamGame.extendedExpectedUtility_eq {utility : Outcome → ι → ℝ}
    (hteam : IsTeamGame utility) (law : PMF Outcome) (first second : ι) :
    extendedExpectedUtility utility first law = extendedExpectedUtility utility second law :=
  extendedExpect_congr_on_support (fun outcome _ => hteam outcome first second)

/-- Team players have equal expected utility. -/
theorem IsTeamGame.expectedUtility_eq {utility : Outcome → ι → ℝ}
    (hteam : IsTeamGame utility) (law : PMF Outcome) (first second : ι) :
    expectedUtility utility first law = expectedUtility utility second law :=
  expect_congr_on_support (fun outcome _ => hteam outcome first second)


theorem euPreference_strict_iff (utility : Outcome → ι → ℝ) (agent : ι)
    (preferred alternative : PMF Outcome)
    (hpreferred : UtilityIntegrable utility agent preferred)
    (halternative : UtilityIntegrable utility agent alternative) :
    Preference.strict (euPreference utility) agent preferred alternative ↔
    expectedUtility utility agent alternative <
        expectedUtility utility agent preferred := by
  simp only [Preference.strict, Rank.strict]
  rw [euPreference_iff utility agent preferred alternative hpreferred halternative,
    euPreference_iff utility agent alternative preferred halternative hpreferred]
  exact lt_iff_le_not_ge.symm

/-- Expected-utility preference is convex when every law is integrable. Laws
with infinite expected utility break convexity: mixing a law worth `+∞` with
one worth `−∞` leaves a law with no expected utility. -/
theorem euPreference_convex (utility : Outcome → ι → ℝ)
    (hintegrable : ∀ agent law, UtilityIntegrable utility agent law) :
    Preference.Convex (euPreference utility) := by
  intro agent t h0 h1 firstPreferred firstAlternative secondPreferred secondAlternative
    hfirst hsecond
  have hp₁ := hintegrable agent firstPreferred
  have ha₁ := hintegrable agent firstAlternative
  have hp₂ := hintegrable agent secondPreferred
  have ha₂ := hintegrable agent secondAlternative
  rw [euPreference_iff utility agent _ _ hp₁ ha₁] at hfirst
  rw [euPreference_iff utility agent _ _ hp₂ ha₂] at hsecond
  rw [euPreference_iff utility agent _ _ (hintegrable _ _) (hintegrable _ _),
    expectedUtility_mix utility agent t h0 h1 firstAlternative secondAlternative ha₁ ha₂,
    expectedUtility_mix utility agent t h0 h1 firstPreferred secondPreferred hp₁ hp₂]
  exact add_le_add (mul_le_mul_of_nonneg_left hfirst h0)
    (mul_le_mul_of_nonneg_left hsecond (by linarith))

/-! ## Positive-affine invariance -/

/-- Rescale and shift each player's utility. -/
def affineUtility (utility : Outcome → ι → ℝ) (scale shift : ι → ℝ) : Outcome → ι → ℝ :=
  fun outcome agent => scale agent * utility outcome agent + shift agent

theorem expectedUtility_affine (utility : Outcome → ι → ℝ) (scale shift : ι → ℝ)
    (agent : ι) (law : PMF Outcome)
    (hutility : UtilityIntegrable utility agent law) :
    expectedUtility (affineUtility utility scale shift) agent law =
      scale agent * expectedUtility utility agent law + shift agent := by
  unfold expectedUtility affineUtility
  rw [expect_add (payoffIntegrable_const_mul hutility) (payoffIntegrable_constant law _),
    expect_const_mul, expect_constant]

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

private theorem coe_mul_le_coe_mul_iff {c : ℝ} (hc : 0 < c) {x y : EReal} :
    (c : EReal) * x ≤ c * y ↔ x ≤ y := by
  induction x using EReal.rec <;> induction y using EReal.rec <;>
    simp [EReal.coe_mul_bot_of_pos hc, EReal.coe_mul_top_of_pos hc, ← EReal.coe_mul,
      mul_le_mul_iff_of_pos_left hc]

/-- A positive affine rescaling does not change the expected-utility
preference, hence changes no solution concept defined from it. -/
theorem euPreference_affine (utility : Outcome → ι → ℝ) {scale shift : ι → ℝ}
    (hscale : ∀ agent, 0 < scale agent) (agent : ι)
    (preferred alternative : PMF Outcome) :
    euPreference (affineUtility utility scale shift) agent preferred alternative ↔
      euPreference utility agent preferred alternative := by
  have hvalue (law : PMF Outcome) :
      extendedExpectedUtility (affineUtility utility scale shift) agent law =
        scale agent * extendedExpectedUtility utility agent law + shift agent :=
    extendedExpect_affine law (fun outcome => utility outcome agent) (shift agent)
      (hscale agent)
  have hexpect (law : PMF Outcome) :
      UtilityHasExpectation (affineUtility utility scale shift) agent law ↔
        UtilityHasExpectation utility agent law :=
    hasExpectation_affine_iff (shift agent) (hscale agent)
  simp only [euPreference_apply, hexpect, hvalue]
  rw [(EReal.addLECancellable_coe (shift agent)).add_le_add_iff_right,
    coe_mul_le_coe_mul_iff (hscale agent)]

/-! ## Outcome relabeling and utility pullback -/

/-- Two encodings of one draw have equal expected utilities when their realized
payoffs agree pointwise. -/
theorem expectedUtility_two_maps {α β γ : Type*}
    (μ : PMF α) (f : α → β) (g : α → γ)
    (u : β → ι → ℝ) (v : γ → ι → ℝ) (who : ι)
    (heq : ∀ a, u (f a) who = v (g a) who) :
    expectedUtility u who (μ.map f) = expectedUtility v who (μ.map g) := by
  rw [expectedUtility_map, expectedUtility_map]
  exact expect_congr_on_support (fun a _ => heq a)

theorem utilityIntegrable_two_maps_iff {α β γ : Type*}
    (μ : PMF α) (f : α → β) (g : α → γ)
    (u : β → ι → ℝ) (v : γ → ι → ℝ) (who : ι)
    (heq : ∀ a, u (f a) who = v (g a) who) :
    UtilityIntegrable u who (μ.map f) ↔
      UtilityIntegrable v who (μ.map g) := by
  rw [UtilityIntegrable, UtilityIntegrable, payoffIntegrable_map_iff,
    payoffIntegrable_map_iff]
  exact ⟨payoffIntegrable_congr_on_support (fun a _ => heq a),
    payoffIntegrable_congr_on_support (fun a _ => (heq a).symm)⟩

theorem extendedExpectedUtility_two_maps {α β γ : Type*}
    (μ : PMF α) (f : α → β) (g : α → γ)
    (u : β → ι → ℝ) (v : γ → ι → ℝ) (who : ι)
    (heq : ∀ a, u (f a) who = v (g a) who) :
    extendedExpectedUtility u who (μ.map f) = extendedExpectedUtility v who (μ.map g) := by
  rw [extendedExpectedUtility_map, extendedExpectedUtility_map]
  exact extendedExpect_congr_on_support (fun a _ => heq a)

theorem utilityHasExpectation_two_maps_iff {α β γ : Type*}
    (μ : PMF α) (f : α → β) (g : α → γ)
    (u : β → ι → ℝ) (v : γ → ι → ℝ) (who : ι)
    (heq : ∀ a, u (f a) who = v (g a) who) :
    UtilityHasExpectation u who (μ.map f) ↔ UtilityHasExpectation v who (μ.map g) := by
  rw [UtilityHasExpectation, UtilityHasExpectation, hasExpectation_map_iff,
    hasExpectation_map_iff]
  have hfun : (fun outcome => u outcome who) ∘ f = (fun outcome => v outcome who) ∘ g :=
    funext heq
  rw [hfun]

theorem euPreference_two_maps_iff {α β γ : Type*}
    (μ : PMF α) (f₁ f₂ : α → β) (g₁ g₂ : α → γ)
    (u : β → ι → ℝ) (v : γ → ι → ℝ) (who : ι)
    (h₁ : ∀ a, u (f₁ a) who = v (g₁ a) who)
    (h₂ : ∀ a, u (f₂ a) who = v (g₂ a) who) :
    euPreference u who (μ.map f₁) (μ.map f₂) ↔
      euPreference v who (μ.map g₁) (μ.map g₂) := by
  rw [euPreference_apply, euPreference_apply,
    utilityHasExpectation_two_maps_iff μ f₁ g₁ u v who h₁,
    utilityHasExpectation_two_maps_iff μ f₂ g₂ u v who h₂,
    extendedExpectedUtility_two_maps μ f₁ g₁ u v who h₁,
    extendedExpectedUtility_two_maps μ f₂ g₂ u v who h₂]

end GameTheory
