/-
# Static evolutionary stability

ESS and NSS are properties of a homogeneous two-argument payoff kernel. The
strategy carrier may contain pure actions, mixed population strategies, or
another explicitly chosen phenotype; the generic definition does not silently
choose among them. No population state, dynamics, finite carrier, topology, or
game form is part of the definition.

Primary reference: J. Maynard Smith and G. R. Price, “The Logic of Animal
Conflict,” *Nature* 246 (1973).
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace GameTheory.Evolutionary

universe uS

variable {S : Type uS}

/-- A positive payoff advantage for all sufficiently small positive invasion
shares is exactly a nonnegative first-order advantage with a strictly positive
second-order advantage at a tie. -/
theorem small_invasion_positive_iff (first second : ℝ) :
    (∃ threshold : ℝ, 0 < threshold ∧
      ∀ share : ℝ, 0 < share → share < threshold → share < 1 →
        0 < (1 - share) * first + share * second) ↔
      0 ≤ first ∧ (first = 0 → 0 < second) := by
  constructor
  · rintro ⟨threshold, hthreshold, hsmall⟩
    have hfirst : 0 ≤ first := by
      by_contra hnegative
      have hnegative' : first < 0 := lt_of_not_ge hnegative
      let bound := |second - first| + 1
      have hbound : 0 < bound := by dsimp [bound]; linarith [abs_nonneg (second - first)]
      let share := min (threshold / 2)
        (min ((-first) / (2 * bound)) (1 / 2 : ℝ))
      have hpositive : 0 < share := by
        dsimp [share]
        exact lt_min (by linarith)
          (lt_min (div_pos (by linarith) (by positivity)) (by norm_num))
      have hbelow : share < threshold :=
        lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hunit : share < 1 := by
        exact lt_of_le_of_lt
          ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
      have hcomparison := hsmall share hpositive hbelow hunit
      have hupper : second - first ≤ bound := by
        dsimp [bound]
        linarith [le_abs_self (second - first)]
      have hproduct : share * (second - first) ≤ share * bound :=
        mul_le_mul_of_nonneg_left hupper (le_of_lt hpositive)
      have hboundshare : share * bound ≤ -first / 2 := by
        have hshare : share ≤ (-first) / (2 * bound) :=
          (min_le_right _ _).trans (min_le_left _ _)
        have hdenom : 0 < 2 * bound := by positivity
        have := (le_div_iff₀ hdenom).mp hshare
        nlinarith
      nlinarith

    refine ⟨hfirst, ?_⟩
    intro hzero
    let share := min (threshold / 2) (1 / 2 : ℝ)
    have hpositive : 0 < share := by
      dsimp [share]
      exact lt_min (by linarith) (by norm_num)
    have hbelow : share < threshold :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hunit : share < 1 :=
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hcomparison := hsmall share hpositive hbelow hunit
    by_contra hnot
    have hsecond : second ≤ 0 := le_of_not_gt hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt hpositive) hsecond
    rw [hzero] at hcomparison
    nlinarith
  · rintro ⟨hfirst, htie⟩
    by_cases hzero : first = 0
    · refine ⟨1, by norm_num, ?_⟩
      intro share hpositive _ _
      have hsecond := htie hzero
      rw [hzero]
      nlinarith [mul_pos hpositive hsecond]
    · have hstrict : 0 < first := lt_of_le_of_ne hfirst (Ne.symm hzero)
      let bound := |second - first| + 1
      have hbound : 0 < bound := by dsimp [bound]; linarith [abs_nonneg (second - first)]
      let threshold := min 1 (first / (2 * bound))
      have hthreshold : 0 < threshold := by
        dsimp [threshold]
        exact lt_min (by norm_num) (by positivity)
      refine ⟨threshold, hthreshold, ?_⟩
      intro share hpositive hbelow _
      have hshare : share < first / (2 * bound) :=
        lt_of_lt_of_le hbelow (min_le_right _ _)
      have hscaled : share * bound < first / 2 := by
        have hdenom : 0 < 2 * bound := by positivity
        have := (lt_div_iff₀ hdenom).mp hshare
        nlinarith
      have hlower : -bound ≤ second - first := by
        dsimp [bound]
        linarith [neg_abs_le (second - first)]
      have hproduct : -(share * bound) ≤ share * (second - first) := by
        nlinarith [mul_le_mul_of_nonneg_left hlower (le_of_lt hpositive)]
      nlinarith

/-- Weak small-invasion comparisons characterize the two NSS inequalities. -/
theorem small_invasion_nonnegative_iff (first second : ℝ) :
    (∃ threshold : ℝ, 0 < threshold ∧
      ∀ share : ℝ, 0 < share → share < threshold → share < 1 →
        0 ≤ (1 - share) * first + share * second) ↔
      0 ≤ first ∧ (first = 0 → 0 ≤ second) := by
  constructor
  · rintro ⟨threshold, hthreshold, hsmall⟩
    have hfirst : 0 ≤ first := by
      apply le_of_forall_pos_le_add
      intro margin hmargin
      have hshift : ∃ threshold : ℝ, 0 < threshold ∧
          ∀ share : ℝ, 0 < share → share < threshold → share < 1 →
            0 < (1 - share) * (first + margin) +
              share * (second + margin) := by
        refine ⟨threshold, hthreshold, ?_⟩
        intro share hpositive hbelow hunit
        have hvalue := hsmall share hpositive hbelow hunit
        nlinarith
      exact ((small_invasion_positive_iff (first + margin)
        (second + margin)).1 hshift).1
    refine ⟨hfirst, ?_⟩
    intro hzero
    let share := min (threshold / 2) (1 / 2 : ℝ)
    have hpositive : 0 < share := by
      dsimp [share]
      exact lt_min (by linarith) (by norm_num)
    have hbelow : share < threshold :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hunit : share < 1 :=
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hvalue := hsmall share hpositive hbelow hunit
    rw [hzero] at hvalue
    by_contra hnegative
    have hnegative' : second < 0 := lt_of_not_ge hnegative
    nlinarith [mul_neg_of_pos_of_neg hpositive hnegative']
  · rintro ⟨hfirst, htie⟩
    by_cases hzero : first = 0
    · refine ⟨1, by norm_num, ?_⟩
      intro share hpositive _ _
      rw [hzero]
      nlinarith [mul_nonneg (le_of_lt hpositive) (htie hzero)]
    · have hstrict : 0 < first := lt_of_le_of_ne hfirst (Ne.symm hzero)
      obtain ⟨threshold, hthreshold, hsmall⟩ :=
        (small_invasion_positive_iff first second).2
          ⟨hfirst, fun heq => False.elim (hzero heq)⟩
      exact ⟨threshold, hthreshold, fun share hp hb hu =>
        le_of_lt (hsmall share hp hb hu)⟩
/-- A resident strategy is evolutionarily stable when no mutant does better
against it, and every tying distinct mutant loses the second-order test. -/
def IsESS (payoff : S → S → ℝ) (resident : S) : Prop :=
  (∀ mutant, payoff resident resident ≥ payoff mutant resident) ∧
  (∀ mutant,
    payoff resident resident = payoff mutant resident →
      resident ≠ mutant →
        payoff resident mutant > payoff mutant mutant)

/-- Neutral stability weakens the second-order ESS comparison. -/
def IsNSS (payoff : S → S → ℝ) (resident : S) : Prop :=
  (∀ mutant, payoff resident resident ≥ payoff mutant resident) ∧
  (∀ mutant,
    payoff resident resident = payoff mutant resident →
      payoff resident mutant ≥ payoff mutant mutant)

/-- The ordinary ESS clauses are equivalent to winning every sufficiently
small positive invasion, against each distinct mutant. -/
theorem isESS_iff_small_invasion (payoff : S → S → ℝ) (resident : S) :
    IsESS payoff resident ↔
      ∀ mutant, resident ≠ mutant →
        ∃ threshold : ℝ, 0 < threshold ∧
          ∀ share : ℝ, 0 < share → share < threshold → share < 1 →
            (1 - share) * payoff resident resident +
                share * payoff resident mutant >
              (1 - share) * payoff mutant resident +
                share * payoff mutant mutant := by
  constructor
  · intro hess mutant hne
    let first := payoff resident resident - payoff mutant resident
    let second := payoff resident mutant - payoff mutant mutant
    have hfirst : 0 ≤ first := by dsimp [first]; linarith [hess.1 mutant]
    have hsecond : first = 0 → 0 < second := by
      intro hzero
      have heq : payoff resident resident = payoff mutant resident := by
        dsimp [first] at hzero
        linarith
      dsimp [second]
      linarith [hess.2 mutant heq hne]
    obtain ⟨threshold, hthreshold, hsmall⟩ :=
      (small_invasion_positive_iff first second).2 ⟨hfirst, hsecond⟩
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hbelow hunit
    have hvalue := hsmall share hpositive hbelow hunit
    dsimp [first, second] at hvalue
    nlinarith
  · intro hsmall
    constructor
    · intro mutant
      by_cases hne : resident = mutant
      · subst mutant
        exact le_refl _
      · obtain ⟨threshold, hthreshold, hcomparison⟩ := hsmall mutant hne
        let first := payoff resident resident - payoff mutant resident
        let second := payoff resident mutant - payoff mutant mutant
        have hnumeric : ∃ threshold : ℝ, 0 < threshold ∧
            ∀ share : ℝ, 0 < share → share < threshold → share < 1 →
              0 < (1 - share) * first + share * second := by
          refine ⟨threshold, hthreshold, ?_⟩
          intro share hpositive hbelow hunit
          have := hcomparison share hpositive hbelow hunit
          dsimp [first, second]
          nlinarith
        have := (small_invasion_positive_iff first second).1 hnumeric
        dsimp [first] at this
        linarith [this.1]
    · intro mutant heq hne
      obtain ⟨threshold, hthreshold, hcomparison⟩ := hsmall mutant hne
      let first := payoff resident resident - payoff mutant resident
      let second := payoff resident mutant - payoff mutant mutant
      have hnumeric : ∃ threshold : ℝ, 0 < threshold ∧
          ∀ share : ℝ, 0 < share → share < threshold → share < 1 →
            0 < (1 - share) * first + share * second := by
        refine ⟨threshold, hthreshold, ?_⟩
        intro share hpositive hbelow hunit
        have := hcomparison share hpositive hbelow hunit
        dsimp [first, second]
        nlinarith
      have hpair := (small_invasion_positive_iff first second).1 hnumeric
      have hzero : first = 0 := by dsimp [first]; linarith
      dsimp [second] at hpair
      linarith [hpair.2 hzero]

/-- The ordinary NSS clauses are equivalent to weak fitness against every
sufficiently small positive invasion by a distinct mutant. -/
theorem isNSS_iff_small_invasion (payoff : S → S → ℝ) (resident : S) :
    IsNSS payoff resident ↔
      ∀ mutant, resident ≠ mutant →
        ∃ threshold : ℝ, 0 < threshold ∧
          ∀ share : ℝ, 0 < share → share < threshold → share < 1 →
            (1 - share) * payoff resident resident +
                share * payoff resident mutant ≥
              (1 - share) * payoff mutant resident +
                share * payoff mutant mutant := by
  constructor
  · intro hnss mutant hne
    let first := payoff resident resident - payoff mutant resident
    let second := payoff resident mutant - payoff mutant mutant
    have hfirst : 0 ≤ first := by dsimp [first]; linarith [hnss.1 mutant]
    have hsecond : first = 0 → 0 ≤ second := by
      intro hzero
      have heq : payoff resident resident = payoff mutant resident := by
        dsimp [first] at hzero
        linarith
      dsimp [second]
      linarith [hnss.2 mutant heq]
    obtain ⟨threshold, hthreshold, hsmall⟩ :=
      (small_invasion_nonnegative_iff first second).2 ⟨hfirst, hsecond⟩
    refine ⟨threshold, hthreshold, ?_⟩
    intro share hpositive hbelow hunit
    have hvalue := hsmall share hpositive hbelow hunit
    dsimp [first, second] at hvalue
    nlinarith
  · intro hsmall
    constructor
    · intro mutant
      by_cases hne : resident = mutant
      · subst mutant
        exact le_refl _
      · obtain ⟨threshold, hthreshold, hcomparison⟩ := hsmall mutant hne
        let first := payoff resident resident - payoff mutant resident
        let second := payoff resident mutant - payoff mutant mutant
        have hnumeric : ∃ threshold : ℝ, 0 < threshold ∧
            ∀ share : ℝ, 0 < share → share < threshold → share < 1 →
              0 ≤ (1 - share) * first + share * second := by
          refine ⟨threshold, hthreshold, ?_⟩
          intro share hpositive hbelow hunit
          have := hcomparison share hpositive hbelow hunit
          dsimp [first, second]
          nlinarith
        have := (small_invasion_nonnegative_iff first second).1 hnumeric
        dsimp [first] at this
        linarith [this.1]
    · intro mutant heq
      by_cases hsame : resident = mutant
      · subst mutant
        exact le_refl _
      · obtain ⟨threshold, hthreshold, hcomparison⟩ :=
          hsmall mutant hsame
        let first := payoff resident resident - payoff mutant resident
        let second := payoff resident mutant - payoff mutant mutant
        have hnumeric : ∃ threshold : ℝ, 0 < threshold ∧
            ∀ share : ℝ, 0 < share → share < threshold → share < 1 →
              0 ≤ (1 - share) * first + share * second := by
          refine ⟨threshold, hthreshold, ?_⟩
          intro share hpositive hbelow hunit
          have := hcomparison share hpositive hbelow hunit
          dsimp [first, second]
          nlinarith
        have hpair :=
          (small_invasion_nonnegative_iff first second).1 hnumeric
        have hzero : first = 0 := by dsimp [first]; linarith
        dsimp [second] at hpair
        linarith [hpair.2 hzero]

/-- Every ESS is neutrally stable. -/
theorem IsESS.isNSS {payoff : S → S → ℝ} {resident : S}
    (h : IsESS payoff resident) : IsNSS payoff resident := by
  refine ⟨h.1, fun mutant heq => ?_⟩
  by_cases hsame : resident = mutant
  · subst mutant
    exact le_refl _
  · exact le_of_lt (h.2 mutant heq hsame)

/-- The first ESS clause is the symmetric Nash condition. -/
theorem IsESS.nash_condition {payoff : S → S → ℝ} {resident : S}
    (h : IsESS payoff resident) :
    ∀ mutant, payoff resident resident ≥ payoff mutant resident :=
  h.1

/-- A distinct mutant tying against the resident loses the stability test. -/
theorem IsESS.stability {payoff : S → S → ℝ} {resident mutant : S}
    (h : IsESS payoff resident)
    (heq : payoff resident resident = payoff mutant resident)
    (hne : resident ≠ mutant) :
    payoff resident mutant > payoff mutant mutant :=
  h.2 mutant heq hne

/-- A strict symmetric Nash strategy is automatically an ESS. -/
theorem isESS_of_strict_nash {payoff : S → S → ℝ} {resident : S}
    (hstrict :
      ∀ mutant, mutant ≠ resident →
        payoff resident resident > payoff mutant resident) :
    IsESS payoff resident := by
  refine ⟨fun mutant => ?_, fun mutant heq hne => ?_⟩
  · by_cases hsame : mutant = resident
    · subst mutant
      exact le_refl _
    · exact le_of_lt (hstrict mutant hsame)
  · exact absurd heq (ne_of_gt (hstrict mutant hne.symm))

/-- Distinct ESS are strictly separated against the first resident. -/
theorem IsESS.strict_against_other_ess
    {payoff : S → S → ℝ} {first second : S}
    (hfirst : IsESS payoff first) (hsecond : IsESS payoff second)
    (hne : first ≠ second) :
    payoff first first > payoff second first := by
  rcases lt_or_eq_of_le (hfirst.1 second) with hstrict | hequal
  · exact hstrict
  · have hstability := hfirst.2 second hequal.symm hne
    exact (not_lt_of_ge (hsecond.1 first) hstability).elim

end GameTheory.Evolutionary
