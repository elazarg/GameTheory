/-
# Evolutionary stability against mixed mutants

Population strategies are ordinary PMFs. An encounter draws the actor and
opponent independently, retaining both draws in the actual joint law.

Actual small-invasion stability compares extended-real fitness in the actual
invaded population, so an infinite fitness is still ranked and only an
undefined one is left incomparable. The classical static mixed ESS compares
finite fitness values and so requires every pair encounter to be integrable.
With infinite fitness the two notions come apart: a mutant with an infinite
self encounter wins every positive invasion even when the static first-order
test favours the resident. Under integrability they coincide.
-/

import GameTheory.Evolutionary.Basic
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationMixture
import GameTheory.Math.Probability.ExtendedExpectation

noncomputable section

namespace GameTheory.Evolutionary

open GameTheory.Math.Probability

universe uS

variable {S : Type uS}

/-- The actual population met at a positive mutant share below one. -/
def invasionPopulation (resident mutant : PMF S) (share : ℝ)
    (hpositive : 0 < share) (hunit : share < 1) : PMF S :=
  mix (1 - share) (by linarith) (by linarith) resident mutant

private theorem mix_half_weight {α : Type*} (μ ν : PMF α) (a : α) :
    (mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν a).toReal =
      ((μ a).toReal + (ν a).toReal) / 2 := by
  rw [mix_apply, ENNReal.toReal_add]
  · norm_num [ENNReal.toReal_mul]
    ring
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (μ.apply_ne_top a)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ν.apply_ne_top a)

/-- A half-and-half population's self encounter charges either ordered cross
encounter with at least a quarter of its weight. -/
private theorem half_self_weight_le (μ ν : PMF S) (pair : S × S) :
    (1 / 4 : ℝ) * (bindPairLaw μ (fun _ => ν) pair).toReal ≤
      (bindPairLaw (mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν)
        (fun _ => mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν) pair).toReal := by
  rcases pair with ⟨a, b⟩
  rw [bindPairLaw_apply, bindPairLaw_apply]
  simp only [ENNReal.toReal_mul]
  rw [mix_half_weight μ ν a, mix_half_weight μ ν b]
  have haμ : 0 ≤ (μ a).toReal := ENNReal.toReal_nonneg
  have hbμ : 0 ≤ (μ b).toReal := ENNReal.toReal_nonneg
  have haν : 0 ≤ (ν a).toReal := ENNReal.toReal_nonneg
  have hbν : 0 ≤ (ν b).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg haμ hbμ, mul_nonneg haν hbμ,
    mul_nonneg haν hbν]

/-- A mutant's encounter with an invaded population charges its self encounter
with at least the invasion share of its weight. -/
private theorem positive_invasion_weight_le (resident mutant : PMF S)
    (share : ℝ) (hpositive : 0 < share) (hunit : share < 1) (pair : S × S) :
    share * (bindPairLaw mutant (fun _ => mutant) pair).toReal ≤
      (bindPairLaw mutant (fun _ =>
        invasionPopulation resident mutant share hpositive hunit) pair).toReal := by
  let invasion := invasionPopulation resident mutant share hpositive hunit
  rcases pair with ⟨a, b⟩
  rw [bindPairLaw_apply, bindPairLaw_apply]
  simp only [ENNReal.toReal_mul]
  have hmass : (invasion b).toReal =
      (1 - share) * (resident b).toReal +
        share * (mutant b).toReal := by
    dsimp [invasion, invasionPopulation]
    rw [ENNReal.toReal_add]
    · simp [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (show 0 ≤ 1 - share by linarith),
        ENNReal.toReal_ofReal (le_of_lt hpositive)]
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (resident.apply_ne_top b)
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (mutant.apply_ne_top b)
  change share * ((mutant a).toReal * (mutant b).toReal) ≤
    (mutant a).toReal * (invasion b).toReal
  rw [hmass]
  have hfirst : 0 ≤ (mutant a).toReal := ENNReal.toReal_nonneg
  have hsecond : 0 ≤ (resident b).toReal := ENNReal.toReal_nonneg
  have hcoefficient : 0 ≤ 1 - share := by linarith
  nlinarith [mul_nonneg hfirst (mul_nonneg hcoefficient hsecond)]

/-- A half-and-half population's self encounter controls either ordered
cross encounter, even for unbounded payoffs on infinite carriers. -/
theorem pairPayoffIntegrable_of_half_self (payoff : S → S → ℝ)
    (μ ν : PMF S)
    (hself : PayoffIntegrable
      (bindPairLaw (mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν)
        (fun _ => mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν))
      (fun pair => payoff pair.1 pair.2)) :
    PayoffIntegrable (bindPairLaw μ (fun _ => ν))
      (fun pair => payoff pair.1 pair.2) :=
  payoffIntegrable_of_scaled_weight_le _ _ _ (1 / 4) (by norm_num)
    (half_self_weight_le μ ν) hself

/-- The same control for the existence of an expectation. -/
theorem pairHasExpectation_of_half_self (payoff : S → S → ℝ)
    (μ ν : PMF S)
    (hself : HasExpectation
      (bindPairLaw (mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν)
        (fun _ => mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν))
      (fun pair => payoff pair.1 pair.2)) :
    HasExpectation (bindPairLaw μ (fun _ => ν))
      (fun pair => payoff pair.1 pair.2) :=
  hasExpectation_of_scaled_weight_le (by norm_num) (half_self_weight_le μ ν) hself

/-- Any positive mutant share charges every mutant self encounter. -/
theorem pairPayoffIntegrable_self_of_positive_invasion
    (payoff : S → S → ℝ) (resident mutant : PMF S)
    (share : ℝ) (hpositive : 0 < share) (hunit : share < 1)
    (hinvasion : PayoffIntegrable
      (bindPairLaw mutant (fun _ =>
        invasionPopulation resident mutant share hpositive hunit))
      (fun pair => payoff pair.1 pair.2)) :
    PayoffIntegrable (bindPairLaw mutant (fun _ => mutant))
      (fun pair => payoff pair.1 pair.2) :=
  payoffIntegrable_of_scaled_weight_le _ _ _ share hpositive
    (positive_invasion_weight_le resident mutant share hpositive hunit) hinvasion

/-- The same charge for the existence of an expectation. -/
theorem pairHasExpectation_self_of_positive_invasion
    (payoff : S → S → ℝ) (resident mutant : PMF S)
    (share : ℝ) (hpositive : 0 < share) (hunit : share < 1)
    (hinvasion : HasExpectation
      (bindPairLaw mutant (fun _ =>
        invasionPopulation resident mutant share hpositive hunit))
      (fun pair => payoff pair.1 pair.2)) :
    HasExpectation (bindPairLaw mutant (fun _ => mutant))
      (fun pair => payoff pair.1 pair.2) :=
  hasExpectation_of_scaled_weight_le hpositive
    (positive_invasion_weight_le resident mutant share hpositive hunit) hinvasion

/-- Actual encounter payoff for two population laws. -/
def mixedPayoff (payoff : S → S → ℝ) (own opponent : PMF S) : ℝ :=
  expect (bindPairLaw own (fun _ => opponent))
    (fun pair => payoff pair.1 pair.2)

/-- Actual encounter fitness in the extended reals. -/
def extendedMixedPayoff (payoff : S → S → ℝ) (own opponent : PMF S) : EReal :=
  extendedExpect (bindPairLaw own (fun _ => opponent))
    (fun pair => payoff pair.1 pair.2)

theorem extendedMixedPayoff_eq {payoff : S → S → ℝ} {own opponent : PMF S}
    (h : PayoffIntegrable (bindPairLaw own (fun _ => opponent))
      (fun pair => payoff pair.1 pair.2)) :
    extendedMixedPayoff payoff own opponent = mixedPayoff payoff own opponent :=
  extendedExpect_eq_expect h

/-- The resident self encounter has an expectation, and every distinct mutant
has both actual invasion fitnesses defined throughout a positive interval. -/
def HasActualSmallInvasionPayoffs (payoff : S → S → ℝ)
    (resident : PMF S) : Prop :=
  HasExpectation (bindPairLaw resident (fun _ => resident))
      (fun pair => payoff pair.1 pair.2) ∧
    ∀ mutant, resident ≠ mutant →
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ share : ℝ, (hpositive : 0 < share) →
          (hunit : share < 1) → share < threshold →
          HasExpectation
              (bindPairLaw resident (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2) ∧
            HasExpectation
              (bindPairLaw mutant (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2)

/-- Defined actual fitness at arbitrarily small positive mutant shares is
equivalent to an expectation for every ordered pair encounter. In particular,
it cannot omit an undefined mutant self encounter. -/
theorem actualSmallInvasionPayoffs_iff_allPairs
    (payoff : S → S → ℝ) (resident : PMF S) :
    HasActualSmallInvasionPayoffs payoff resident ↔
      ∀ own opponent : PMF S,
        HasExpectation (bindPairLaw own (fun _ => opponent))
          (fun pair => payoff pair.1 pair.2) := by
  constructor
  · intro h own opponent
    let κ := mix (1 / 2 : ℝ) (by norm_num) (by norm_num)
      own opponent
    have hself : HasExpectation (bindPairLaw κ (fun _ => κ))
        (fun pair => payoff pair.1 pair.2) := by
      by_cases hsame : resident = κ
      · rw [← hsame]
        exact h.1
      · obtain ⟨threshold, hthreshold, hguard⟩ := h.2 κ hsame
        let share := min (threshold / 2) (1 / 2 : ℝ)
        have hpositive : 0 < share := by
          dsimp [share]
          exact lt_min (by linarith) (by norm_num)
        have hsmall : share < threshold := by
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hunit : share < 1 := by
          exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
        exact pairHasExpectation_self_of_positive_invasion
          payoff resident κ share hpositive hunit
          (hguard share hpositive hunit hsmall).2
    exact pairHasExpectation_of_half_self payoff own opponent hself
  · intro hall
    refine ⟨hall resident resident, ?_⟩
    intro mutant _
    refine ⟨1, by norm_num, ?_⟩
    intro share hpositive hunit hsmall
    exact ⟨hall resident _, hall mutant _⟩

/-- The actual encounter value against an invaded population is affine in
the invasion share, provided the pair encounters have their own guards. -/
theorem mixedPayoff_invasionPopulation
    (payoff : S → S → ℝ) (own resident mutant : PMF S)
    (share : ℝ) (hpositive : 0 < share) (hunit : share < 1)
    (hresident : PayoffIntegrable
      (bindPairLaw own (fun _ => resident))
      (fun pair => payoff pair.1 pair.2))
    (hmutant : PayoffIntegrable
      (bindPairLaw own (fun _ => mutant))
      (fun pair => payoff pair.1 pair.2)) :
    mixedPayoff payoff own
        (invasionPopulation resident mutant share hpositive hunit) =
      (1 - share) * mixedPayoff payoff own resident +
        share * mixedPayoff payoff own mutant := by
  let invaded := invasionPopulation resident mutant share hpositive hunit
  let first := bindPairLaw own (fun _ => resident)
  let second := bindPairLaw own (fun _ => mutant)
  let score : S × S → ℝ := fun pair => payoff pair.1 pair.2
  have hlaw : bindPairLaw own (fun _ => invaded) =
      mix (1 - share) (by linarith) (by linarith) first second := by
    ext pair
    rcases pair with ⟨a, b⟩
    simp only [bindPairLaw_apply, mix_apply]
    dsimp [first, second, invaded, invasionPopulation]
    rw [bindPairLaw_apply, bindPairLaw_apply]
    ring
  calc
    mixedPayoff payoff own invaded =
        expect (mix (1 - share) (by linarith) (by linarith)
          first second) score :=
      expect_congr_law hlaw score
    _ = (1 - share) * mixedPayoff payoff own resident +
        share * mixedPayoff payoff own mutant := by
      simpa only [mixedPayoff, score, first, second,
        show 1 - (1 - share) = share by ring] using
        (expect_mix (1 - share) (by linarith) (by linarith)
          first second score hresident hmutant)

/-- The classical static ESS of the mixed-extension fitness. Its first- and
second-order tests compare finite fitness values, so every actual pair
encounter, including each mutant's self encounter, is integrable. -/
def IsMixedESS (payoff : S → S → ℝ) (resident : PMF S) : Prop :=
  (∀ own opponent : PMF S,
      PayoffIntegrable (bindPairLaw own (fun _ => opponent))
        (fun pair => payoff pair.1 pair.2)) ∧
    IsESS (fun own opponent => mixedPayoff payoff own opponent) resident

/-- Classical neutral stability with integrable fitness for every mixed pair
encounter. -/
def IsMixedNSS (payoff : S → S → ℝ) (resident : PMF S) : Prop :=
  (∀ own opponent : PMF S,
      PayoffIntegrable (bindPairLaw own (fun _ => opponent))
        (fun pair => payoff pair.1 pair.2)) ∧
    IsNSS (fun own opponent => mixedPayoff payoff own opponent) resident

/-- Actual small-invasion fitness must exist on both populations, and the
resident must win every sufficiently small positive invasion. -/
def IsActualSmallInvasionESS (payoff : S → S → ℝ)
    (resident : PMF S) : Prop :=
  HasExpectation (bindPairLaw resident (fun _ => resident))
      (fun pair => payoff pair.1 pair.2) ∧
    ∀ mutant, resident ≠ mutant →
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ share : ℝ, (hpositive : 0 < share) →
          (hunit : share < 1) → share < threshold →
          HasExpectation
              (bindPairLaw resident (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2) ∧
            HasExpectation
              (bindPairLaw mutant (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2) ∧
              extendedMixedPayoff payoff resident
                  (invasionPopulation resident mutant share hpositive hunit) >
                extendedMixedPayoff payoff mutant
                  (invasionPopulation resident mutant share hpositive hunit)

/-- The static mixed ESS is exactly strict fitness against every actual small
positive invasion, for games whose pair encounters are all integrable. -/
theorem isMixedESS_iff_actualSmallInvasion
    (payoff : S → S → ℝ) (resident : PMF S) :
    IsMixedESS payoff resident ↔
      (∀ own opponent : PMF S,
        PayoffIntegrable (bindPairLaw own (fun _ => opponent))
          (fun pair => payoff pair.1 pair.2)) ∧
        IsActualSmallInvasionESS payoff resident := by
  constructor
  · rintro ⟨hall, hess⟩
    refine ⟨hall, hasExpectation_of_payoffIntegrable (hall resident resident), ?_⟩
    intro mutant hne
    obtain ⟨threshold, hthreshold, hsmall⟩ :=
      ((isESS_iff_small_invasion
        (fun own opponent => mixedPayoff payoff own opponent)
        resident).1 hess) mutant hne
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hunit hbelow
    refine ⟨hasExpectation_of_payoffIntegrable (hall resident _),
      hasExpectation_of_payoffIntegrable (hall mutant _), ?_⟩
    rw [extendedMixedPayoff_eq (hall resident _), extendedMixedPayoff_eq (hall mutant _),
      gt_iff_lt, EReal.coe_lt_coe_iff,
      mixedPayoff_invasionPopulation payoff resident resident mutant
      share hpositive hunit (hall resident resident) (hall resident mutant),
      mixedPayoff_invasionPopulation payoff mutant resident mutant
      share hpositive hunit (hall mutant resident) (hall mutant mutant)]
    exact hsmall share hpositive hbelow hunit
  · rintro ⟨hall, -, hactual⟩
    refine ⟨hall, (isESS_iff_small_invasion
      (fun own opponent => mixedPayoff payoff own opponent)
      resident).2 ?_⟩
    intro mutant hne
    obtain ⟨threshold, hthreshold, hsmall⟩ := hactual mutant hne
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hbelow hunit
    obtain ⟨-, -, hgt⟩ := hsmall share hpositive hunit hbelow
    rw [extendedMixedPayoff_eq (hall resident _), extendedMixedPayoff_eq (hall mutant _),
      gt_iff_lt, EReal.coe_lt_coe_iff,
      mixedPayoff_invasionPopulation payoff resident resident mutant
        share hpositive hunit (hall resident resident)
        (hall resident mutant),
      mixedPayoff_invasionPopulation payoff mutant resident mutant
        share hpositive hunit (hall mutant resident)
        (hall mutant mutant)] at hgt
    exact hgt

/-- Neutral stability uses defined actual fitness for every small positive
invasion and permits equality in the comparison. -/
def IsActualSmallInvasionNSS (payoff : S → S → ℝ)
    (resident : PMF S) : Prop :=
  HasExpectation (bindPairLaw resident (fun _ => resident))
      (fun pair => payoff pair.1 pair.2) ∧
    ∀ mutant, resident ≠ mutant →
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ share : ℝ, (hpositive : 0 < share) →
          (hunit : share < 1) → share < threshold →
          HasExpectation
              (bindPairLaw resident (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2) ∧
            HasExpectation
              (bindPairLaw mutant (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2) ∧
              extendedMixedPayoff payoff resident
                  (invasionPopulation resident mutant share hpositive hunit) ≥
                extendedMixedPayoff payoff mutant
                  (invasionPopulation resident mutant share hpositive hunit)

/-- The same characterization for neutral stability. -/
theorem isMixedNSS_iff_actualSmallInvasion
    (payoff : S → S → ℝ) (resident : PMF S) :
    IsMixedNSS payoff resident ↔
      (∀ own opponent : PMF S,
        PayoffIntegrable (bindPairLaw own (fun _ => opponent))
          (fun pair => payoff pair.1 pair.2)) ∧
        IsActualSmallInvasionNSS payoff resident := by
  constructor
  · rintro ⟨hall, hnss⟩
    refine ⟨hall, hasExpectation_of_payoffIntegrable (hall resident resident), ?_⟩
    intro mutant hne
    obtain ⟨threshold, hthreshold, hsmall⟩ :=
      ((isNSS_iff_small_invasion
        (fun own opponent => mixedPayoff payoff own opponent)
        resident).1 hnss) mutant hne
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hunit hbelow
    refine ⟨hasExpectation_of_payoffIntegrable (hall resident _),
      hasExpectation_of_payoffIntegrable (hall mutant _), ?_⟩
    rw [extendedMixedPayoff_eq (hall resident _), extendedMixedPayoff_eq (hall mutant _),
      ge_iff_le, EReal.coe_le_coe_iff,
      mixedPayoff_invasionPopulation payoff resident resident mutant
      share hpositive hunit (hall resident resident) (hall resident mutant),
      mixedPayoff_invasionPopulation payoff mutant resident mutant
      share hpositive hunit (hall mutant resident) (hall mutant mutant)]
    exact hsmall share hpositive hbelow hunit
  · rintro ⟨hall, -, hactual⟩
    refine ⟨hall, (isNSS_iff_small_invasion
      (fun own opponent => mixedPayoff payoff own opponent)
      resident).2 ?_⟩
    intro mutant hne
    obtain ⟨threshold, hthreshold, hsmall⟩ := hactual mutant hne
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hbelow hunit
    obtain ⟨-, -, hge⟩ := hsmall share hpositive hunit hbelow
    rw [extendedMixedPayoff_eq (hall resident _), extendedMixedPayoff_eq (hall mutant _),
      ge_iff_le, EReal.coe_le_coe_iff,
      mixedPayoff_invasionPopulation payoff resident resident mutant
        share hpositive hunit (hall resident resident)
        (hall resident mutant),
      mixedPayoff_invasionPopulation payoff mutant resident mutant
        share hpositive hunit (hall mutant resident)
        (hall mutant mutant)] at hge
    exact hge

theorem IsMixedESS.isNSS {payoff : S → S → ℝ} {resident : PMF S}
    (h : IsMixedESS payoff resident) : IsMixedNSS payoff resident := by
  obtain ⟨hall, hess⟩ := h
  exact ⟨hall, hess.isNSS⟩

end GameTheory.Evolutionary
