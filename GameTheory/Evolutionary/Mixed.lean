/-
# Evolutionary stability against mixed mutants

Population strategies are ordinary PMFs. An encounter draws the actor and
opponent independently, retaining both draws in the actual joint law. A mixed
ESS requires every pair encounter used by the mutant family to have a defined
payoff; the guarded numerical ESS then uses the unchanged static definition.
-/

import GameTheory.Evolutionary.Basic
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationMixture

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

/-- A half-and-half population's self encounter controls either ordered
cross encounter, even for unbounded payoffs on infinite carriers. -/
theorem pairPayoffIntegrable_of_half_self (payoff : S → S → ℝ)
    (μ ν : PMF S)
    (hself : PayoffIntegrable
      (bindPairLaw (mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν)
        (fun _ => mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν))
      (fun pair => payoff pair.1 pair.2)) :
    PayoffIntegrable (bindPairLaw μ (fun _ => ν))
      (fun pair => payoff pair.1 pair.2) := by
  let κ := mix (1 / 2 : ℝ) (by norm_num) (by norm_num) μ ν
  apply payoffIntegrable_of_scaled_weight_le
    (bindPairLaw μ (fun _ => ν)) (bindPairLaw κ (fun _ => κ))
    (fun pair => payoff pair.1 pair.2) (1 / 4) (by norm_num) ?_ hself
  rintro ⟨a, b⟩
  rw [bindPairLaw_apply, bindPairLaw_apply]
  simp only [ENNReal.toReal_mul]
  rw [show (κ a).toReal = ((μ a).toReal + (ν a).toReal) / 2 from
    mix_half_weight μ ν a]
  rw [show (κ b).toReal = ((μ b).toReal + (ν b).toReal) / 2 from
    mix_half_weight μ ν b]
  have haμ : 0 ≤ (μ a).toReal := ENNReal.toReal_nonneg
  have hbμ : 0 ≤ (μ b).toReal := ENNReal.toReal_nonneg
  have haν : 0 ≤ (ν a).toReal := ENNReal.toReal_nonneg
  have hbν : 0 ≤ (ν b).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg haμ hbμ, mul_nonneg haν hbμ,
    mul_nonneg haν hbν]

/-- Any positive mutant share charges every mutant self encounter. -/
theorem pairPayoffIntegrable_self_of_positive_invasion
    (payoff : S → S → ℝ) (resident mutant : PMF S)
    (share : ℝ) (hpositive : 0 < share) (hunit : share < 1)
    (hinvasion : PayoffIntegrable
      (bindPairLaw mutant (fun _ =>
        invasionPopulation resident mutant share hpositive hunit))
      (fun pair => payoff pair.1 pair.2)) :
    PayoffIntegrable (bindPairLaw mutant (fun _ => mutant))
      (fun pair => payoff pair.1 pair.2) := by
  let invasion := invasionPopulation resident mutant share hpositive hunit
  apply payoffIntegrable_of_scaled_weight_le
    (bindPairLaw mutant (fun _ => mutant))
    (bindPairLaw mutant (fun _ => invasion))
    (fun pair => payoff pair.1 pair.2) share hpositive ?_ hinvasion
  rintro ⟨a, b⟩
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
  rw [hmass]
  have hfirst : 0 ≤ (mutant a).toReal := ENNReal.toReal_nonneg
  have hsecond : 0 ≤ (resident b).toReal := ENNReal.toReal_nonneg
  have hcoefficient : 0 ≤ 1 - share := by linarith
  nlinarith [mul_nonneg hfirst (mul_nonneg hcoefficient hsecond)]

/-- Actual encounter payoff for two population laws. -/
def mixedPayoff (payoff : S → S → ℝ) (own opponent : PMF S)
    (hintegrable : PayoffIntegrable
      (bindPairLaw own (fun _ => opponent))
      (fun pair => payoff pair.1 pair.2)) : ℝ :=
  expect (bindPairLaw own (fun _ => opponent))
    (fun pair => payoff pair.1 pair.2) hintegrable

/-- The resident self encounter is defined, and every distinct mutant has
both actual invasion fitnesses defined throughout a positive interval. -/
def HasActualSmallInvasionPayoffs (payoff : S → S → ℝ)
    (resident : PMF S) : Prop :=
  PayoffIntegrable (bindPairLaw resident (fun _ => resident))
      (fun pair => payoff pair.1 pair.2) ∧
    ∀ mutant, resident ≠ mutant →
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ share : ℝ, (hpositive : 0 < share) →
          (hunit : share < 1) → share < threshold →
          PayoffIntegrable
              (bindPairLaw resident (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2) ∧
            PayoffIntegrable
              (bindPairLaw mutant (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2)

/-- Defined actual fitness at arbitrarily small positive mutant shares is
equivalent to integration of every ordered pair encounter. In particular,
integrability cannot omit a divergent mutant self encounter. -/
theorem actualSmallInvasionPayoffs_iff_allPairs
    (payoff : S → S → ℝ) (resident : PMF S) :
    HasActualSmallInvasionPayoffs payoff resident ↔
      ∀ own opponent : PMF S,
        PayoffIntegrable (bindPairLaw own (fun _ => opponent))
          (fun pair => payoff pair.1 pair.2) := by
  constructor
  · intro h own opponent
    let κ := mix (1 / 2 : ℝ) (by norm_num) (by norm_num)
      own opponent
    have hself : PayoffIntegrable (bindPairLaw κ (fun _ => κ))
        (fun pair => payoff pair.1 pair.2) := by
      by_cases hsame : resident = κ
      · exact payoffIntegrable_congr_law
          (by rw [← hsame]) h.1
      · obtain ⟨threshold, hthreshold, hguard⟩ := h.2 κ hsame
        let share := min (threshold / 2) (1 / 2 : ℝ)
        have hpositive : 0 < share := by
          dsimp [share]
          exact lt_min (by linarith) (by norm_num)
        have hsmall : share < threshold := by
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hunit : share < 1 := by
          exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
        exact pairPayoffIntegrable_self_of_positive_invasion
          payoff resident κ share hpositive hunit
          (hguard share hpositive hunit hsmall).2
    exact pairPayoffIntegrable_of_half_self payoff own opponent hself
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
      (fun pair => payoff pair.1 pair.2))
    (hinvaded : PayoffIntegrable
      (bindPairLaw own (fun _ =>
        invasionPopulation resident mutant share hpositive hunit))
      (fun pair => payoff pair.1 pair.2)) :
    mixedPayoff payoff own
        (invasionPopulation resident mutant share hpositive hunit)
        hinvaded =
      (1 - share) * mixedPayoff payoff own resident hresident +
        share * mixedPayoff payoff own mutant hmutant := by
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
  have hmix : PayoffIntegrable
      (mix (1 - share) (by linarith) (by linarith) first second)
      score :=
    payoffIntegrable_mix (1 - share) (by linarith) (by linarith)
      first second score hresident hmutant
  calc
    mixedPayoff payoff own invaded hinvaded =
        expect (mix (1 - share) (by linarith) (by linarith)
          first second) score hmix :=
      expect_congr_law hlaw score hinvaded hmix
    _ = (1 - share) * mixedPayoff payoff own resident
          hresident +
        share * mixedPayoff payoff own mutant hmutant := by
      simpa only [mixedPayoff, score, first, second,
        show 1 - (1 - share) = share by ring] using
        (expect_mix (1 - share) (by linarith) (by linarith)
          first second score hresident hmutant)

/-- Every actual pair encounter is defined before a numerical ESS comparison
is made. This also covers each mutant's self encounter at positive invasion
shares. -/
def IsMixedESS (payoff : S → S → ℝ) (resident : PMF S) : Prop :=
  ∃ hall : ∀ own opponent : PMF S,
      PayoffIntegrable (bindPairLaw own (fun _ => opponent))
        (fun pair => payoff pair.1 pair.2),
    IsESS (fun own opponent => mixedPayoff payoff own opponent (hall own opponent))
      resident

/-- Neutral stability with defined fitness for every mixed pair encounter. -/
def IsMixedNSS (payoff : S → S → ℝ) (resident : PMF S) : Prop :=
  ∃ hall : ∀ own opponent : PMF S,
      PayoffIntegrable (bindPairLaw own (fun _ => opponent))
        (fun pair => payoff pair.1 pair.2),
    IsNSS (fun own opponent => mixedPayoff payoff own opponent (hall own opponent))
      resident

/-- Actual small-invasion fitness must be defined on both populations, and
the resident must win every sufficiently small positive invasion. -/
def IsActualSmallInvasionESS (payoff : S → S → ℝ)
    (resident : PMF S) : Prop :=
  PayoffIntegrable (bindPairLaw resident (fun _ => resident))
      (fun pair => payoff pair.1 pair.2) ∧
    ∀ mutant, resident ≠ mutant →
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ share : ℝ, (hpositive : 0 < share) →
          (hunit : share < 1) → share < threshold →
          ∃ hresident : PayoffIntegrable
              (bindPairLaw resident (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2),
            ∃ hmutant : PayoffIntegrable
              (bindPairLaw mutant (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2),
              mixedPayoff payoff resident
                  (invasionPopulation resident mutant share hpositive hunit)
                  hresident >
                mixedPayoff payoff mutant
                  (invasionPopulation resident mutant share hpositive hunit)
                  hmutant

/-- The guarded all-pair ESS is exactly strict fitness against every actual
small positive invasion, with the resident baseline defined. -/
theorem isMixedESS_iff_actualSmallInvasion
    (payoff : S → S → ℝ) (resident : PMF S) :
    IsMixedESS payoff resident ↔
      IsActualSmallInvasionESS payoff resident := by
  constructor
  · rintro ⟨hall, hess⟩
    refine ⟨hall resident resident, ?_⟩
    intro mutant hne
    obtain ⟨threshold, hthreshold, hsmall⟩ :=
      ((isESS_iff_small_invasion
        (fun own opponent => mixedPayoff payoff own opponent (hall own opponent))
        resident).1 hess) mutant hne
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hunit hbelow
    refine ⟨hall resident _, hall mutant _, ?_⟩
    rw [mixedPayoff_invasionPopulation payoff resident resident mutant
      share hpositive hunit (hall resident resident) (hall resident mutant)
      (hall resident _),
      mixedPayoff_invasionPopulation payoff mutant resident mutant
      share hpositive hunit (hall mutant resident) (hall mutant mutant)
      (hall mutant _)]
    exact hsmall share hpositive hbelow hunit
  · intro hactual
    have hdefined : HasActualSmallInvasionPayoffs payoff resident := by
      refine ⟨hactual.1, ?_⟩
      intro mutant hne
      obtain ⟨threshold, hthreshold, hsmall⟩ := hactual.2 mutant hne
      refine ⟨threshold, hthreshold, ?_⟩
      intro share hpositive hunit hbelow
      obtain ⟨hresident, hmutant, _⟩ :=
        hsmall share hpositive hunit hbelow
      exact ⟨hresident, hmutant⟩
    let hall := (actualSmallInvasionPayoffs_iff_allPairs payoff resident).1 hdefined
    refine ⟨hall, (isESS_iff_small_invasion
      (fun own opponent => mixedPayoff payoff own opponent (hall own opponent))
      resident).2 ?_⟩
    intro mutant hne
    obtain ⟨threshold, hthreshold, hsmall⟩ := hactual.2 mutant hne
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hbelow hunit
    obtain ⟨hresident, hmutant, hgt⟩ :=
      hsmall share hpositive hunit hbelow
    have hresidentEq :
        mixedPayoff payoff resident
            (invasionPopulation resident mutant share hpositive hunit)
            hresident =
          mixedPayoff payoff resident
            (invasionPopulation resident mutant share hpositive hunit)
            (hall resident _) := rfl
    have hmutantEq :
        mixedPayoff payoff mutant
            (invasionPopulation resident mutant share hpositive hunit)
            hmutant =
          mixedPayoff payoff mutant
            (invasionPopulation resident mutant share hpositive hunit)
            (hall mutant _) := rfl
    rw [hresidentEq, hmutantEq,
      mixedPayoff_invasionPopulation payoff resident resident mutant
        share hpositive hunit (hall resident resident)
        (hall resident mutant) (hall resident _),
      mixedPayoff_invasionPopulation payoff mutant resident mutant
        share hpositive hunit (hall mutant resident)
        (hall mutant mutant) (hall mutant _)] at hgt
    exact hgt

/-- Neutral stability uses defined actual fitness for every small positive
invasion and permits equality in the comparison. -/
def IsActualSmallInvasionNSS (payoff : S → S → ℝ)
    (resident : PMF S) : Prop :=
  PayoffIntegrable (bindPairLaw resident (fun _ => resident))
      (fun pair => payoff pair.1 pair.2) ∧
    ∀ mutant, resident ≠ mutant →
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ share : ℝ, (hpositive : 0 < share) →
          (hunit : share < 1) → share < threshold →
          ∃ hresident : PayoffIntegrable
              (bindPairLaw resident (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2),
            ∃ hmutant : PayoffIntegrable
              (bindPairLaw mutant (fun _ =>
                invasionPopulation resident mutant share hpositive hunit))
              (fun pair => payoff pair.1 pair.2),
              mixedPayoff payoff resident
                  (invasionPopulation resident mutant share hpositive hunit)
                  hresident ≥
                mixedPayoff payoff mutant
                  (invasionPopulation resident mutant share hpositive hunit)
                  hmutant

/-- The same all-pair necessity applies to neutral stability. -/
theorem isMixedNSS_iff_actualSmallInvasion
    (payoff : S → S → ℝ) (resident : PMF S) :
    IsMixedNSS payoff resident ↔
      IsActualSmallInvasionNSS payoff resident := by
  constructor
  · rintro ⟨hall, hnss⟩
    refine ⟨hall resident resident, ?_⟩
    intro mutant hne
    obtain ⟨threshold, hthreshold, hsmall⟩ :=
      ((isNSS_iff_small_invasion
        (fun own opponent => mixedPayoff payoff own opponent (hall own opponent))
        resident).1 hnss) mutant hne
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hunit hbelow
    refine ⟨hall resident _, hall mutant _, ?_⟩
    rw [mixedPayoff_invasionPopulation payoff resident resident mutant
      share hpositive hunit (hall resident resident) (hall resident mutant)
      (hall resident _),
      mixedPayoff_invasionPopulation payoff mutant resident mutant
      share hpositive hunit (hall mutant resident) (hall mutant mutant)
      (hall mutant _)]
    exact hsmall share hpositive hbelow hunit
  · intro hactual
    have hdefined : HasActualSmallInvasionPayoffs payoff resident := by
      refine ⟨hactual.1, ?_⟩
      intro mutant hne
      obtain ⟨threshold, hthreshold, hsmall⟩ := hactual.2 mutant hne
      refine ⟨threshold, hthreshold, ?_⟩
      intro share hpositive hunit hbelow
      obtain ⟨hresident, hmutant, _⟩ :=
        hsmall share hpositive hunit hbelow
      exact ⟨hresident, hmutant⟩
    let hall := (actualSmallInvasionPayoffs_iff_allPairs payoff resident).1 hdefined
    refine ⟨hall, (isNSS_iff_small_invasion
      (fun own opponent => mixedPayoff payoff own opponent (hall own opponent))
      resident).2 ?_⟩
    intro mutant hne
    obtain ⟨threshold, hthreshold, hsmall⟩ := hactual.2 mutant hne
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hbelow hunit
    obtain ⟨hresident, hmutant, hge⟩ :=
      hsmall share hpositive hunit hbelow
    have hresidentEq :
        mixedPayoff payoff resident
            (invasionPopulation resident mutant share hpositive hunit)
            hresident =
          mixedPayoff payoff resident
            (invasionPopulation resident mutant share hpositive hunit)
            (hall resident _) := rfl
    have hmutantEq :
        mixedPayoff payoff mutant
            (invasionPopulation resident mutant share hpositive hunit)
            hmutant =
          mixedPayoff payoff mutant
            (invasionPopulation resident mutant share hpositive hunit)
            (hall mutant _) := rfl
    rw [hresidentEq, hmutantEq,
      mixedPayoff_invasionPopulation payoff resident resident mutant
        share hpositive hunit (hall resident resident)
        (hall resident mutant) (hall resident _),
      mixedPayoff_invasionPopulation payoff mutant resident mutant
        share hpositive hunit (hall mutant resident)
        (hall mutant mutant) (hall mutant _)] at hge
    exact hge

theorem IsMixedESS.isNSS {payoff : S → S → ℝ} {resident : PMF S}
    (h : IsMixedESS payoff resident) : IsMixedNSS payoff resident := by
  obtain ⟨hall, hess⟩ := h
  exact ⟨hall, hess.isNSS⟩

end GameTheory.Evolutionary
