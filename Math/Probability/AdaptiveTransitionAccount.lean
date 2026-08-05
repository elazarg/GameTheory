/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AdaptiveOccupationSetDeflation
import Math.Probability.HarmonicStateAccount

/-!
# Adaptive transition accounts with exceptional columns

A potential need not be harmonic for one fixed Markov kernel in order to
give a useful realized account.  For both pure history-dependent choices and
predictable mixtures of source-compatible transitions, the potential
increment splits exactly into

* a successor score centered under the selected transition law; and
* the selected transition's potential drift.

This formulation is stable under finite deflation.  A later potential may
have controlled drift only on the retained transition family.  If every
exceptional transition belongs to an earlier set whose total use or
predictable selection mass is sublinear, then the cumulative uncontrolled
drift is sublinear as well.
Thus deleting a prescribed transition row does not require falsely claiming
that a later potential is harmonic for the original full kernel.
-/

noncomputable section

namespace Math
namespace Probability

variable {S I : Type*}

/-- A scalar cost accumulated along history-selected transition indices. -/
def selectedTransitionCostSum
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (cost : I → ℝ) :
    ∀ T, (Fin (T + 1) → S) → ℝ
  | 0, _ => 0
  | T + 1, history =>
      selectedTransitionCostSum choice cost T (Fin.init history) +
        cost (choice T (Fin.init history))

@[simp]
theorem selectedTransitionCostSum_zero
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (cost : I → ℝ) (history : Fin 1 → S) :
    selectedTransitionCostSum choice cost 0 history = 0 := rfl

@[simp]
theorem selectedTransitionCostSum_snoc
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (cost : I → ℝ) (T : ℕ)
    (history : Fin (T + 1) → S) (successor : S) :
    selectedTransitionCostSum choice cost (T + 1)
        (Fin.snoc history successor) =
      selectedTransitionCostSum choice cost T history +
        cost (choice T history) := by
  simp [selectedTransitionCostSum]

/-- Finite occupation expansion of an index-dependent cumulative cost. -/
theorem selectedTransitionCostSum_eq_sum_useCount
    [Fintype I] [DecidableEq I]
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (cost : I → ℝ) (T : ℕ)
    (history : Fin (T + 1) → S) :
    selectedTransitionCostSum choice cost T history =
      ∑ index,
        cost index *
          selectedTransitionUseCount choice index T history := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [← Fin.snoc_init_self history,
        selectedTransitionCostSum_snoc]
      simp only [selectedTransitionUseCount_snoc, ih]
      have selected :
          (∑ index,
            cost index *
              if choice T (Fin.init history) = index then 1 else 0) =
            cost (choice T (Fin.init history)) := by
        rw [Fintype.sum_eq_single (choice T (Fin.init history))]
        · simp
        · intro index hne
          simp [hne.symm]
      calc
        (∑ index,
              cost index *
                selectedTransitionUseCount choice index T
                  (Fin.init history)) +
            cost (choice T (Fin.init history)) =
            (∑ index,
              cost index *
                selectedTransitionUseCount choice index T
                  (Fin.init history)) +
              ∑ index,
                cost index *
                  if choice T (Fin.init history) = index then 1 else 0 := by
            rw [selected]
        _ =
            ∑ index,
              (cost index *
                  selectedTransitionUseCount choice index T
                    (Fin.init history) +
                cost index *
                  if choice T (Fin.init history) = index then 1 else 0) := by
            rw [Finset.sum_add_distrib]
        _ =
            ∑ index,
              cost index *
                (selectedTransitionUseCount choice index T
                    (Fin.init history) +
                  if choice T (Fin.init history) = index then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro index _
            ring

/-- Pointwise comparison of transition costs is preserved by every
history-selected cumulative sum. -/
theorem selectedTransitionCostSum_mono
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    {left right : I → ℝ}
    (cost_le : ∀ index, left index ≤ right index)
    (T : ℕ) (history : Fin (T + 1) → S) :
    selectedTransitionCostSum choice left T history ≤
      selectedTransitionCostSum choice right T history := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [← Fin.snoc_init_self history,
        selectedTransitionCostSum_snoc,
        selectedTransitionCostSum_snoc]
      exact add_le_add (ih (Fin.init history))
        (cost_le (choice T (Fin.init history)))

/-- The observation centered under one selected transition law. -/
def transitionCenteredPotentialScore
    (kernel : I → PMF S) (potential : S → ℝ)
    (index : I) (successor : S) : ℝ :=
  potential successor - expect (kernel index) potential

/-- The potential drift of one transition from its declared source. -/
def transitionPotentialDrift
    (kernel : I → PMF S) (source : I → S)
    (potential : S → ℝ) (index : I) : ℝ :=
  expect (kernel index) potential - potential (source index)

/-- The predictable score centered under the transition selected from the
current finite history.  The initial term is zero. -/
def adaptiveSelectedTransitionCenteredScore
    (kernel : I → PMF S) (potential : S → ℝ)
    (choice : ∀ n, (Fin (n + 1) → S) → I) :
    ∀ n, (Fin n → S) → S → ℝ
  | 0, _, _ => 0
  | n + 1, history, successor =>
      transitionCenteredPotentialScore kernel potential
        (choice n history) successor

@[simp]
theorem adaptiveSelectedTransitionCenteredScore_zero
    (kernel : I → PMF S) (potential : S → ℝ)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (history : Fin 0 → S) (successor : S) :
    adaptiveSelectedTransitionCenteredScore
      kernel potential choice 0 history successor = 0 := rfl

@[simp]
theorem adaptiveSelectedTransitionCenteredScore_succ
    (kernel : I → PMF S) (potential : S → ℝ)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (n : ℕ) (history : Fin (n + 1) → S) (successor : S) :
    adaptiveSelectedTransitionCenteredScore
        kernel potential choice (n + 1) history successor =
      transitionCenteredPotentialScore kernel potential
        (choice n history) successor := rfl

/-- Exact pathwise account identity for a changing selected transition.
The centered scores plus the selected drifts telescope to the endpoint
motion of the state potential. -/
theorem selectedTransitionCenteredScore_add_drift_eq_accountIncrement
    (kernel : I → PMF S) (source : I → S)
    (potential : S → ℝ)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (source_compatible :
      ∀ n history,
        source (choice n history) = history (Fin.last n))
    (T : ℕ) (history : Fin (T + 1) → S) :
    predictableScoreSum
          (adaptiveSelectedTransitionCenteredScore
            kernel potential choice)
          (T + 1) history +
        selectedTransitionCostSum choice
          (transitionPotentialDrift kernel source potential)
          T history =
      potential (history (Fin.last T)) - potential (history 0) := by
  induction T with
  | zero =>
      simp [predictableScoreSum,
        adaptiveSelectedTransitionCenteredScore,
        selectedTransitionCostSum]
  | succ T ih =>
      rw [← Fin.snoc_init_self history]
      rw [predictableScoreSum_snoc,
        selectedTransitionCostSum_snoc]
      simp only [adaptiveSelectedTransitionCenteredScore_succ,
        transitionCenteredPotentialScore, transitionPotentialDrift]
      rw [source_compatible T (Fin.init history)]
      have hprevious := ih (Fin.init history)
      change
        predictableScoreSum
              (adaptiveSelectedTransitionCenteredScore
                kernel potential choice)
              (T + 1) (Fin.init history) +
              (potential (history (Fin.last (T + 1))) -
                expect (kernel (choice T (Fin.init history))) potential) +
            (selectedTransitionCostSum choice
                (fun index =>
                  expect (kernel index) potential -
                    potential (source index))
                T (Fin.init history) +
              (expect (kernel (choice T (Fin.init history))) potential -
                potential ((Fin.init history) (Fin.last T)))) =
          potential
              (Fin.snoc (Fin.init history)
                (history (Fin.last (T + 1))) (Fin.last (T + 1))) -
            potential
              (Fin.snoc (Fin.init history)
                (history (Fin.last (T + 1))) 0)
      change
        predictableScoreSum
              (adaptiveSelectedTransitionCenteredScore
                kernel potential choice)
              (T + 1) (Fin.init history) +
            selectedTransitionCostSum choice
              (fun index =>
                expect (kernel index) potential -
                  potential (source index))
              T (Fin.init history) =
          potential ((Fin.init history) (Fin.last T)) -
            potential ((Fin.init history) 0) at hprevious
      calc
        predictableScoreSum
              (adaptiveSelectedTransitionCenteredScore
                kernel potential choice)
              (T + 1) (Fin.init history) +
              (potential (history (Fin.last (T + 1))) -
                expect (kernel (choice T (Fin.init history))) potential) +
            (selectedTransitionCostSum choice
                (fun index =>
                  expect (kernel index) potential -
                    potential (source index))
                T (Fin.init history) +
              (expect (kernel (choice T (Fin.init history))) potential -
                potential ((Fin.init history) (Fin.last T)))) =
            (predictableScoreSum
                (adaptiveSelectedTransitionCenteredScore
                  kernel potential choice)
                (T + 1) (Fin.init history) +
              selectedTransitionCostSum choice
                (fun index =>
                  expect (kernel index) potential -
                    potential (source index))
                T (Fin.init history)) +
              (potential (history (Fin.last (T + 1))) -
                potential ((Fin.init history) (Fin.last T))) := by
            ring
        _ =
            (potential ((Fin.init history) (Fin.last T)) -
                potential ((Fin.init history) 0)) +
              (potential (history (Fin.last (T + 1))) -
                potential ((Fin.init history) (Fin.last T))) := by
            rw [hprevious]
        _ =
            potential
                (Fin.snoc (Fin.init history)
                  (history (Fin.last (T + 1))) (Fin.last (T + 1))) -
              potential
                (Fin.snoc (Fin.init history)
                  (history (Fin.last (T + 1))) 0) := by
            simp

/-- If a lower comparison cost is supported on previously exceptional
transitions, the centered score is bounded above by endpoint account motion
plus the absolute exceptional cost. -/
theorem selectedTransitionCenteredScore_le_accountIncrement_add_cost
    (kernel : I → PMF S) (source : I → S)
    (potential : S → ℝ)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (source_compatible :
      ∀ n history,
        source (choice n history) = history (Fin.last n))
    (lowerCost : I → ℝ)
    (lowerCost_le_drift :
      ∀ index,
        lowerCost index ≤
          transitionPotentialDrift kernel source potential index)
    (T : ℕ) (history : Fin (T + 1) → S) :
    predictableScoreSum
        (adaptiveSelectedTransitionCenteredScore
          kernel potential choice)
        (T + 1) history ≤
      potential (history (Fin.last T)) - potential (history 0) +
        |selectedTransitionCostSum
          choice lowerCost T history| := by
  have account :=
    selectedTransitionCenteredScore_add_drift_eq_accountIncrement
      kernel source potential choice source_compatible T history
  have cost_le :
      selectedTransitionCostSum choice lowerCost T history ≤
        selectedTransitionCostSum choice
          (transitionPotentialDrift kernel source potential)
          T history :=
    selectedTransitionCostSum_mono choice lowerCost_le_drift T history
  have neg_cost_le_abs :
      -selectedTransitionCostSum choice lowerCost T history ≤
        |selectedTransitionCostSum choice lowerCost T history| :=
    neg_le_abs _
  linarith

/-- Every selected centered score has conditional mean zero under its own
selected transition kernel. -/
theorem expect_adaptiveSelectedTransitionCenteredScore_succ
    [Finite S]
    (kernel : I → PMF S) (potential : S → ℝ)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (n : ℕ) (history : Fin (n + 1) → S) :
    expect
        (selectedTransitionComparison kernel choice n history)
        (adaptiveSelectedTransitionCenteredScore
          kernel potential choice (n + 1) history) =
      0 := by
  change
    expect (kernel (choice n history))
        (fun successor =>
          potential successor -
            expect (kernel (choice n history)) potential) =
      0
  rw [expect_sub, expect_const, sub_self]

/-- A cost supported on a finite exceptional set is bounded by the number
of uses of that set. -/
theorem abs_selectedTransitionCostSum_le_exceptionalUse
    [Finite I] [DecidableEq I]
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (cost : I → ℝ) (exceptional : Finset I) (bound : ℝ)
    (cost_zero :
      ∀ index, index ∉ exceptional → cost index = 0)
    (cost_bound :
      ∀ index, index ∈ exceptional → |cost index| ≤ bound)
    (T : ℕ) (history : Fin (T + 1) → S) :
    |selectedTransitionCostSum choice cost T history| ≤
      bound *
        ∑ index : {index // index ∈ exceptional},
          selectedTransitionUseCount choice index.1 T history := by
  letI := Fintype.ofFinite I
  rw [selectedTransitionCostSum_eq_sum_useCount]
  calc
    |∑ index,
        cost index *
          selectedTransitionUseCount choice index T history| ≤
        ∑ index,
          |cost index *
            selectedTransitionUseCount choice index T history| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ =
        ∑ index : {index // index ∈ exceptional},
          |cost index *
            selectedTransitionUseCount choice index.1 T history| := by
      rw [← Finset.sum_subtype exceptional
        (fun _ => Iff.rfl)
        (fun index =>
          |cost index *
            selectedTransitionUseCount choice index T history|)]
      symm
      apply Finset.sum_subset (Finset.subset_univ exceptional)
      intro index _ hindex
      rw [cost_zero index hindex, zero_mul, abs_zero]
    _ ≤
        ∑ index : {index // index ∈ exceptional},
          bound *
            selectedTransitionUseCount choice index.1 T history := by
      apply Finset.sum_le_sum
      intro index _
      rw [abs_mul, abs_of_nonneg
        (selectedTransitionUseCount_nonneg
          choice index.1 T history)]
      exact mul_le_mul_of_nonneg_right
        (cost_bound index.1 index.2)
        (selectedTransitionUseCount_nonneg
          choice index.1 T history)
    _ =
        bound *
          ∑ index : {index // index ∈ exceptional},
            selectedTransitionUseCount choice index.1 T history := by
      rw [Finset.mul_sum]

/-- If uses of the exceptional set are sublinear, every uniformly bounded
cumulative transition cost supported on that set is sublinear in expected
absolute value. -/
theorem exceptionalTransitionCost_isAsymptoticallySublinear
    [Finite S] [Finite I] [DecidableEq I]
    (initial : S) (kernel : I → PMF S)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (cost : I → ℝ) (exceptional : Finset I) (bound : ℝ)
    (cost_zero :
      ∀ index, index ∉ exceptional → cost index = 0)
    (cost_bound :
      ∀ index, index ∈ exceptional → |cost index| ≤ bound)
    (exceptional_use :
      IsAsymptoticallySublinear
        (transitionSetExpectedUse
          initial kernel choice exceptional)) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (selectedTransitionComparison kernel choice))
            (T + 1))
          (fun history =>
            |selectedTransitionCostSum
              choice cost T history|)) := by
  letI := Fintype.ofFinite I
  exact transitionSetUseContribution_isAsymptoticallySublinear
    initial kernel choice exceptional
    (fun T history =>
      selectedTransitionCostSum choice cost T history)
    bound
    (abs_selectedTransitionCostSum_le_exceptionalUse
      choice cost exceptional bound cost_zero cost_bound)
    exceptional_use

/-! ## Predictable mixed selectors -/

/-- Predictable cumulative expected cost under a history-dependent mixture
of transition indices. -/
def mixedTransitionCostSum
    [Finite I]
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (cost : I → ℝ) :
    ∀ T, (Fin (T + 1) → S) → ℝ
  | 0, _ => 0
  | T + 1, history =>
      mixedTransitionCostSum selection cost T (Fin.init history) +
        expect (selection T (Fin.init history)) cost

@[simp]
theorem mixedTransitionCostSum_zero
    [Finite I]
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (cost : I → ℝ) (history : Fin 1 → S) :
    mixedTransitionCostSum selection cost 0 history = 0 :=
  rfl

@[simp]
theorem mixedTransitionCostSum_snoc
    [Finite I]
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (cost : I → ℝ) (T : ℕ)
    (history : Fin (T + 1) → S) (successor : S) :
    mixedTransitionCostSum selection cost (T + 1)
        (Fin.snoc history successor) =
      mixedTransitionCostSum selection cost T history +
        expect (selection T history) cost := by
  simp [mixedTransitionCostSum]

/-- Finite predictable-mass expansion of a mixed transition cost. -/
theorem mixedTransitionCostSum_eq_sum_mass
    [Fintype I]
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (cost : I → ℝ) (T : ℕ)
    (history : Fin (T + 1) → S) :
    mixedTransitionCostSum selection cost T history =
      ∑ index,
        cost index *
          selectedTransitionMassSum selection index T history := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [← Fin.snoc_init_self history,
        mixedTransitionCostSum_snoc]
      simp only [selectedTransitionMassSum_snoc, ih]
      rw [expect_eq_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro index _
      ring

/-- Pointwise comparison of index costs is preserved by every predictable
mixed cumulative cost. -/
theorem mixedTransitionCostSum_mono
    [Finite I]
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    {left right : I → ℝ}
    (cost_le : ∀ index, left index ≤ right index)
    (T : ℕ) (history : Fin (T + 1) → S) :
    mixedTransitionCostSum selection left T history ≤
      mixedTransitionCostSum selection right T history := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [← Fin.snoc_init_self history,
        mixedTransitionCostSum_snoc,
        mixedTransitionCostSum_snoc]
      apply add_le_add (ih (Fin.init history))
      exact expect_mono _ _ _ cost_le

/-- Score centered under the complete mixed transition selected from the
current history. -/
def adaptiveMixedTransitionCenteredScore
    [Finite I]
    (kernel : I → PMF S) (potential : S → ℝ)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I) :
    ∀ n, (Fin n → S) → S → ℝ
  | 0, _, _ => 0
  | n + 1, history, successor =>
      potential successor -
        expect ((selection n history).bind kernel) potential

@[simp]
theorem adaptiveMixedTransitionCenteredScore_zero
    [Finite I]
    (kernel : I → PMF S) (potential : S → ℝ)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (history : Fin 0 → S) (successor : S) :
    adaptiveMixedTransitionCenteredScore
      kernel potential selection 0 history successor = 0 :=
  rfl

@[simp]
theorem adaptiveMixedTransitionCenteredScore_succ
    [Finite I]
    (kernel : I → PMF S) (potential : S → ℝ)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (n : ℕ) (history : Fin (n + 1) → S) (successor : S) :
    adaptiveMixedTransitionCenteredScore
        kernel potential selection (n + 1) history successor =
      potential successor -
        expect ((selection n history).bind kernel) potential :=
  rfl

/-- Under a source-compatible mixture, the expected indexwise potential
drift is the drift of the mixed transition from the current state. -/
theorem expect_transitionPotentialDrift_eq_mixedDrift
    [Finite S] [Finite I]
    (kernel : I → PMF S) (source : I → S)
    (potential : S → ℝ) (selection : PMF I) (current : S)
    (source_compatible :
      ∀ index, selection index ≠ 0 → source index = current) :
    expect selection
        (transitionPotentialDrift kernel source potential) =
      expect (selection.bind kernel) potential - potential current := by
  classical
  letI := Fintype.ofFinite I
  rw [expect_bind]
  unfold transitionPotentialDrift
  calc
    expect selection
          (fun index =>
            expect (kernel index) potential -
              potential (source index)) =
        expect selection
          (fun index =>
            expect (kernel index) potential -
              potential current) := by
      rw [expect_eq_sum, expect_eq_sum]
      apply Finset.sum_congr rfl
      intro index _
      by_cases index_zero : selection index = 0
      · simp [index_zero]
      · rw [source_compatible index index_zero]
    _ =
        expect selection
            (fun index => expect (kernel index) potential) -
          potential current := by
      rw [expect_sub, expect_const]

/-- Exact pathwise account identity under a changing mixed transition.
The mixed centered scores plus the predictable expected index drifts
telescope to the endpoint motion of the state potential. -/
theorem mixedTransitionCenteredScore_add_drift_eq_accountIncrement
    [Finite S] [Finite I]
    (kernel : I → PMF S) (source : I → S)
    (potential : S → ℝ)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          source index = history (Fin.last n))
    (T : ℕ) (history : Fin (T + 1) → S) :
    predictableScoreSum
          (adaptiveMixedTransitionCenteredScore
            kernel potential selection)
          (T + 1) history +
        mixedTransitionCostSum selection
          (transitionPotentialDrift kernel source potential)
          T history =
      potential (history (Fin.last T)) - potential (history 0) := by
  induction T with
  | zero =>
      simp [predictableScoreSum,
        adaptiveMixedTransitionCenteredScore,
        mixedTransitionCostSum]
  | succ T ih =>
      rw [← Fin.snoc_init_self history,
        predictableScoreSum_snoc,
        mixedTransitionCostSum_snoc]
      simp only [adaptiveMixedTransitionCenteredScore_succ]
      have mixed_drift :=
        expect_transitionPotentialDrift_eq_mixedDrift
          kernel source potential
          (selection T (Fin.init history))
          ((Fin.init history) (Fin.last T))
          (fun index hindex =>
            source_compatible T (Fin.init history) index hindex)
      have previous := ih (Fin.init history)
      rw [mixed_drift]
      change
        predictableScoreSum
              (adaptiveMixedTransitionCenteredScore
                kernel potential selection)
              (T + 1) (Fin.init history) +
              (potential (history (Fin.last (T + 1))) -
                expect
                  ((selection T (Fin.init history)).bind kernel)
                  potential) +
            (mixedTransitionCostSum selection
                (transitionPotentialDrift
                  kernel source potential)
                T (Fin.init history) +
              (expect
                  ((selection T (Fin.init history)).bind kernel)
                  potential -
                potential ((Fin.init history) (Fin.last T)))) =
          potential
              (Fin.snoc (Fin.init history)
                (history (Fin.last (T + 1)))
                (Fin.last (T + 1))) -
            potential
              (Fin.snoc (Fin.init history)
                (history (Fin.last (T + 1))) 0)
      change
        predictableScoreSum
              (adaptiveMixedTransitionCenteredScore
                kernel potential selection)
              (T + 1) (Fin.init history) +
            mixedTransitionCostSum selection
              (transitionPotentialDrift
                kernel source potential)
              T (Fin.init history) =
          potential ((Fin.init history) (Fin.last T)) -
            potential ((Fin.init history) 0) at previous
      calc
        _ =
            (predictableScoreSum
                (adaptiveMixedTransitionCenteredScore
                  kernel potential selection)
                (T + 1) (Fin.init history) +
              mixedTransitionCostSum selection
                (transitionPotentialDrift
                  kernel source potential)
                T (Fin.init history)) +
              (potential (history (Fin.last (T + 1))) -
                potential ((Fin.init history) (Fin.last T))) := by
            ring
        _ =
            (potential ((Fin.init history) (Fin.last T)) -
                potential ((Fin.init history) 0)) +
              (potential (history (Fin.last (T + 1))) -
                potential ((Fin.init history) (Fin.last T))) := by
            rw [previous]
        _ = _ := by
            simp

/-- Mixed-selector account inequality with an exceptional lower drift
comparison. -/
theorem mixedTransitionCenteredScore_le_accountIncrement_add_cost
    [Finite S] [Finite I]
    (kernel : I → PMF S) (source : I → S)
    (potential : S → ℝ)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          source index = history (Fin.last n))
    (lowerCost : I → ℝ)
    (lowerCost_le_drift :
      ∀ index,
        lowerCost index ≤
          transitionPotentialDrift kernel source potential index)
    (T : ℕ) (history : Fin (T + 1) → S) :
    predictableScoreSum
        (adaptiveMixedTransitionCenteredScore
          kernel potential selection)
        (T + 1) history ≤
      potential (history (Fin.last T)) - potential (history 0) +
        |mixedTransitionCostSum
          selection lowerCost T history| := by
  have account :=
    mixedTransitionCenteredScore_add_drift_eq_accountIncrement
      kernel source potential selection source_compatible T history
  have cost_le :
      mixedTransitionCostSum selection lowerCost T history ≤
        mixedTransitionCostSum selection
          (transitionPotentialDrift kernel source potential)
          T history :=
    mixedTransitionCostSum_mono
      selection lowerCost_le_drift T history
  have neg_cost_le_abs :
      -mixedTransitionCostSum selection lowerCost T history ≤
        |mixedTransitionCostSum selection lowerCost T history| :=
    neg_le_abs _
  linarith

/-- The mixed transition-centered score has conditional mean zero. -/
theorem expect_adaptiveMixedTransitionCenteredScore_succ
    [Finite S] [Finite I]
    (kernel : I → PMF S) (potential : S → ℝ)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (n : ℕ) (history : Fin (n + 1) → S) :
    expect
        (mixedTransitionComparison kernel selection n history)
        (adaptiveMixedTransitionCenteredScore
          kernel potential selection (n + 1) history) =
      0 := by
  change
    expect ((selection n history).bind kernel)
        (fun successor =>
          potential successor -
            expect ((selection n history).bind kernel) potential) =
      0
  rw [expect_sub, expect_const, sub_self]

/-- A mixed cost supported on an exceptional finite set is bounded by the
predictable mass placed on that set. -/
theorem abs_mixedTransitionCostSum_le_exceptionalMass
    [Finite I]
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (cost : I → ℝ) (exceptional : Finset I) (bound : ℝ)
    (cost_zero :
      ∀ index, index ∉ exceptional → cost index = 0)
    (cost_bound :
      ∀ index, index ∈ exceptional → |cost index| ≤ bound)
    (T : ℕ) (history : Fin (T + 1) → S) :
    |mixedTransitionCostSum selection cost T history| ≤
      bound *
        ∑ index : {index // index ∈ exceptional},
          selectedTransitionMassSum selection index.1 T history := by
  classical
  letI := Fintype.ofFinite I
  rw [mixedTransitionCostSum_eq_sum_mass]
  calc
    |∑ index,
        cost index *
          selectedTransitionMassSum selection index T history| ≤
        ∑ index,
          |cost index *
            selectedTransitionMassSum selection index T history| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ =
        ∑ index : {index // index ∈ exceptional},
          |cost index *
            selectedTransitionMassSum
              selection index.1 T history| := by
      rw [← Finset.sum_subtype exceptional
        (fun _ => Iff.rfl)
        (fun index =>
          |cost index *
            selectedTransitionMassSum
              selection index T history|)]
      symm
      apply Finset.sum_subset (Finset.subset_univ exceptional)
      intro index _ hindex
      rw [cost_zero index hindex, zero_mul, abs_zero]
    _ ≤
        ∑ index : {index // index ∈ exceptional},
          bound *
            selectedTransitionMassSum
              selection index.1 T history := by
      apply Finset.sum_le_sum
      intro index _
      rw [abs_mul, abs_of_nonneg
        (selectedTransitionMassSum_nonneg
          selection index.1 T history)]
      exact mul_le_mul_of_nonneg_right
        (cost_bound index.1 index.2)
        (selectedTransitionMassSum_nonneg
          selection index.1 T history)
    _ =
        bound *
          ∑ index : {index // index ∈ exceptional},
            selectedTransitionMassSum
              selection index.1 T history := by
      rw [Finset.mul_sum]

/-- If predictable mass on the exceptional set is sublinear, every
uniformly bounded mixed transition cost supported there is sublinear in
expected absolute value. -/
theorem exceptionalMixedTransitionCost_isAsymptoticallySublinear
    [Finite S] [Finite I]
    (initial : S) (kernel : I → PMF S)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (cost : I → ℝ) (exceptional : Finset I) (bound : ℝ)
    (cost_zero :
      ∀ index, index ∉ exceptional → cost index = 0)
    (cost_bound :
      ∀ index, index ∈ exceptional → |cost index| ≤ bound)
    (exceptional_mass :
      IsAsymptoticallySublinear
        (transitionSetExpectedMass
          initial kernel selection exceptional)) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (mixedTransitionComparison kernel selection))
            (T + 1))
          (fun history =>
            |mixedTransitionCostSum
              selection cost T history|)) := by
  exact transitionSetMassContribution_isAsymptoticallySublinear
    initial kernel selection exceptional
    (fun T history =>
      mixedTransitionCostSum selection cost T history)
    bound
    (abs_mixedTransitionCostSum_le_exceptionalMass
      selection cost exceptional bound cost_zero cost_bound)
    exceptional_mass

end Probability
end Math
