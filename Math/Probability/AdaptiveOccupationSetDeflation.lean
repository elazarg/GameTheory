/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AdaptiveOccupationSetBudget
import Math.Probability.SublinearLedger

/-!
# Asymptotic deflation of a strictly separated transition set

A horizon-uniform occupation budget for a finite transition set immediately
implies that its expected total use, or expected predictable mixed mass, is
sublinear in the horizon.  This file records that asymptotic consequence and
the corresponding domination result for cumulative contributions supported
on the budgeted set.

These are accounting statements.  They do not remove a transition from a
strategy, construct a child game, or prove that a remaining transition is
reachable.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter

variable {S I : Type*}

/-- A pure selected-transition use count is nonnegative. -/
theorem selectedTransitionUseCount_nonneg
    [DecidableEq I]
    (choice : ∀ n, (Fin (n + 1) → S) → I) (i₀ : I) :
    ∀ T history,
      0 ≤ selectedTransitionUseCount choice i₀ T history := by
  intro T
  induction T with
  | zero =>
      intro history
      simp
  | succ T ih =>
      intro history
      rw [← Fin.snoc_init_self history,
        selectedTransitionUseCount_snoc]
      exact add_nonneg (ih _) (by split <;> simp)

/-- A predictable selected-transition mass sum is nonnegative. -/
theorem selectedTransitionMassSum_nonneg
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I) (i₀ : I) :
    ∀ T history,
      0 ≤ selectedTransitionMassSum selection i₀ T history := by
  intro T
  induction T with
  | zero =>
      intro history
      simp
  | succ T ih =>
      intro history
      rw [← Fin.snoc_init_self history,
        selectedTransitionMassSum_snoc]
      exact add_nonneg (ih _) ENNReal.toReal_nonneg

/-- Expected total pure use of a finite transition set up to horizon `T`. -/
def transitionSetExpectedUse
    [DecidableEq I]
    (initial : S) (kernel : I → PMF S)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (active : Finset I) (T : ℕ) : ℝ :=
  expect
    (adaptiveHistoryLaw
      (adaptiveMarkovStep initial
        (selectedTransitionComparison kernel choice))
      (T + 1))
    (fun history =>
      ∑ i : {i // i ∈ active},
        selectedTransitionUseCount choice i.1 T history)

/-- Expected predictable mixed mass placed on a finite transition set up to
horizon `T`. -/
def transitionSetExpectedMass
    (initial : S) (kernel : I → PMF S)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (active : Finset I) (T : ℕ) : ℝ :=
  expect
    (adaptiveHistoryLaw
      (adaptiveMarkovStep initial
        (mixedTransitionComparison kernel selection))
      (T + 1))
    (fun history =>
      ∑ i : {i // i ∈ active},
        selectedTransitionMassSum selection i.1 T history)

theorem transitionSetExpectedUse_nonneg
    [DecidableEq I]
    (initial : S) (kernel : I → PMF S)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (active : Finset I) (T : ℕ) :
    0 ≤ transitionSetExpectedUse initial kernel choice active T := by
  apply expect_nonneg
  intro history
  exact Finset.sum_nonneg fun i _ =>
    selectedTransitionUseCount_nonneg choice i.1 T history

theorem transitionSetExpectedMass_nonneg
    (initial : S) (kernel : I → PMF S)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (active : Finset I) (T : ℕ) :
    0 ≤ transitionSetExpectedMass initial kernel selection active T := by
  apply expect_nonneg
  intro history
  exact Finset.sum_nonneg fun i _ =>
    selectedTransitionMassSum_nonneg selection i.1 T history

/-- A finite transition set with a common positive drift margin has
sublinear expected pure use. -/
theorem transitionSetExpectedUse_isAsymptoticallySublinear
    [Finite S] [DecidableEq I]
    (initial : S) (kernel : I → PMF S) (source : I → S)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (active : Finset I) (potential : S → ℝ) {eta : ℝ}
    (heta : 0 < eta)
    (hpotential :
      ∀ s, 0 ≤ potential s ∧ potential s ≤ 1)
    (hsource :
      ∀ n history,
        source (choice n history) = history (Fin.last n))
    (hdrift :
      ∀ i,
        0 ≤ expect (kernel i) potential - potential (source i))
    (hmargin :
      ∀ i ∈ active,
        eta ≤ expect (kernel i) potential - potential (source i)) :
    IsAsymptoticallySublinear
      (transitionSetExpectedUse initial kernel choice active) := by
  let upper : ℝ := (active.card : ℝ) / eta
  have hnonneg :
      ∀ T,
        0 ≤ transitionSetExpectedUse initial kernel choice active T :=
    transitionSetExpectedUse_nonneg initial kernel choice active
  have hupper :
      ∀ T,
        transitionSetExpectedUse initial kernel choice active T ≤ upper := by
    intro T
    apply (le_div_iff₀ heta).2
    simpa only [transitionSetExpectedUse, mul_comm] using
      margin_mul_expect_transitionSetUseCount_le_card
        initial kernel source choice active potential hpotential hsource
        hdrift hmargin T
  have hupper_sublinear :
      IsAsymptoticallySublinear (fun _ : ℕ => upper) :=
    IsAsymptoticallySublinear.const upper
  change Tendsto
    (fun T : ℕ =>
      (T : ℝ)⁻¹ *
        transitionSetExpectedUse initial kernel choice active T)
    atTop (nhds 0)
  change Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * upper)
    atTop (nhds 0) at hupper_sublinear
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T)) (hnonneg T)
  · exact Filter.Eventually.of_forall fun T =>
      mul_le_mul_of_nonneg_left (hupper T)
        (inv_nonneg.mpr (Nat.cast_nonneg T))
  · exact hupper_sublinear

/-- A finite transition set with a common positive drift margin has
sublinear expected predictable mixed mass. -/
theorem transitionSetExpectedMass_isAsymptoticallySublinear
    [Finite S] [Finite I]
    (initial : S) (kernel : I → PMF S) (source : I → S)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (active : Finset I) (potential : S → ℝ) {eta : ℝ}
    (heta : 0 < eta)
    (hpotential :
      ∀ s, 0 ≤ potential s ∧ potential s ≤ 1)
    (hsource :
      ∀ n history i,
        selection n history i ≠ 0 →
          source i = history (Fin.last n))
    (hdrift :
      ∀ i,
        0 ≤ expect (kernel i) potential - potential (source i))
    (hmargin :
      ∀ i ∈ active,
        eta ≤ expect (kernel i) potential - potential (source i)) :
    IsAsymptoticallySublinear
      (transitionSetExpectedMass initial kernel selection active) := by
  let upper : ℝ := (active.card : ℝ) / eta
  have hnonneg :
      ∀ T,
        0 ≤ transitionSetExpectedMass initial kernel selection active T :=
    transitionSetExpectedMass_nonneg initial kernel selection active
  have hupper :
      ∀ T,
        transitionSetExpectedMass initial kernel selection active T ≤ upper := by
    intro T
    apply (le_div_iff₀ heta).2
    simpa only [transitionSetExpectedMass, mul_comm] using
      margin_mul_expect_transitionSetMassSum_le_card
        initial kernel source selection active potential hpotential hsource
        hdrift hmargin T
  have hupper_sublinear :
      IsAsymptoticallySublinear (fun _ : ℕ => upper) :=
    IsAsymptoticallySublinear.const upper
  change Tendsto
    (fun T : ℕ =>
      (T : ℝ)⁻¹ *
        transitionSetExpectedMass initial kernel selection active T)
    atTop (nhds 0)
  change Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * upper)
    atTop (nhds 0) at hupper_sublinear
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T)) (hnonneg T)
  · exact Filter.Eventually.of_forall fun T =>
      mul_le_mul_of_nonneg_left (hupper T)
        (inv_nonneg.mpr (Nat.cast_nonneg T))
  · exact hupper_sublinear

/-- Direct ratio form of pure strict-set deflation. -/
theorem tendsto_transitionSetExpectedUse_div_horizon_zero
    [Finite S] [DecidableEq I]
    (initial : S) (kernel : I → PMF S) (source : I → S)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (active : Finset I) (potential : S → ℝ) {eta : ℝ}
    (heta : 0 < eta)
    (hpotential :
      ∀ s, 0 ≤ potential s ∧ potential s ≤ 1)
    (hsource :
      ∀ n history,
        source (choice n history) = history (Fin.last n))
    (hdrift :
      ∀ i,
        0 ≤ expect (kernel i) potential - potential (source i))
    (hmargin :
      ∀ i ∈ active,
        eta ≤ expect (kernel i) potential - potential (source i)) :
    Tendsto
      (fun T : ℕ =>
        transitionSetExpectedUse initial kernel choice active T / T)
      atTop (nhds 0) := by
  have h := transitionSetExpectedUse_isAsymptoticallySublinear
    initial kernel source choice active potential heta hpotential hsource
    hdrift hmargin
  simpa only [IsAsymptoticallySublinear, div_eq_mul_inv, mul_comm] using h

/-- Direct ratio form of mixed strict-set deflation. -/
theorem tendsto_transitionSetExpectedMass_div_horizon_zero
    [Finite S] [Finite I]
    (initial : S) (kernel : I → PMF S) (source : I → S)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (active : Finset I) (potential : S → ℝ) {eta : ℝ}
    (heta : 0 < eta)
    (hpotential :
      ∀ s, 0 ≤ potential s ∧ potential s ≤ 1)
    (hsource :
      ∀ n history i,
        selection n history i ≠ 0 →
          source i = history (Fin.last n))
    (hdrift :
      ∀ i,
        0 ≤ expect (kernel i) potential - potential (source i))
    (hmargin :
      ∀ i ∈ active,
        eta ≤ expect (kernel i) potential - potential (source i)) :
    Tendsto
      (fun T : ℕ =>
        transitionSetExpectedMass initial kernel selection active T / T)
      atTop (nhds 0) := by
  have h := transitionSetExpectedMass_isAsymptoticallySublinear
    initial kernel source selection active potential heta hpotential hsource
    hdrift hmargin
  simpa only [IsAsymptoticallySublinear, div_eq_mul_inv, mul_comm] using h

/-- Any expected absolute cumulative contribution dominated pathwise by a
constant times the pure strict-set use count is sublinear. -/
theorem transitionSetUseContribution_isAsymptoticallySublinear
    [Finite S] [DecidableEq I]
    (initial : S) (kernel : I → PMF S)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (active : Finset I)
    (contribution : ∀ T, (Fin (T + 1) → S) → ℝ)
    (L : ℝ)
    (hdominated :
      ∀ T history,
        |contribution T history| ≤
          L *
            ∑ i : {i // i ∈ active},
              selectedTransitionUseCount choice i.1 T history)
    (huse :
      IsAsymptoticallySublinear
        (transitionSetExpectedUse initial kernel choice active)) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (selectedTransitionComparison kernel choice))
            (T + 1))
          (fun history => |contribution T history|)) := by
  let absoluteContribution : ℕ → ℝ := fun T =>
    expect
      (adaptiveHistoryLaw
        (adaptiveMarkovStep initial
          (selectedTransitionComparison kernel choice))
        (T + 1))
      (fun history => |contribution T history|)
  have hnonneg : ∀ T, 0 ≤ absoluteContribution T := by
    intro T
    exact expect_nonneg _ _ fun history => abs_nonneg _
  have hupper :
      ∀ T,
        absoluteContribution T ≤
          L * transitionSetExpectedUse initial kernel choice active T := by
    intro T
    let law :=
      adaptiveHistoryLaw
        (adaptiveMarkovStep initial
          (selectedTransitionComparison kernel choice))
        (T + 1)
    calc
      absoluteContribution T ≤
          expect law
            (fun history =>
              L *
                ∑ i : {i // i ∈ active},
                  selectedTransitionUseCount choice i.1 T history) := by
        exact expect_mono _ _ _ (hdominated T)
      _ = L * transitionSetExpectedUse initial kernel choice active T := by
        exact expect_const_mul _ _ _
  have hscaled :
      IsAsymptoticallySublinear
        (fun T =>
          L * transitionSetExpectedUse initial kernel choice active T) :=
    huse.const_mul L
  change Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * absoluteContribution T)
    atTop (nhds 0)
  change Tendsto
    (fun T : ℕ =>
      (T : ℝ)⁻¹ *
        (L * transitionSetExpectedUse initial kernel choice active T))
    atTop (nhds 0) at hscaled
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T)) (hnonneg T)
  · exact Filter.Eventually.of_forall fun T =>
      mul_le_mul_of_nonneg_left (hupper T)
        (inv_nonneg.mpr (Nat.cast_nonneg T))
  · exact hscaled

/-- Any expected absolute cumulative contribution dominated pathwise by a
constant times the mixed strict-set mass is sublinear. -/
theorem transitionSetMassContribution_isAsymptoticallySublinear
    [Finite S] [Finite I]
    (initial : S) (kernel : I → PMF S)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (active : Finset I)
    (contribution : ∀ T, (Fin (T + 1) → S) → ℝ)
    (L : ℝ)
    (hdominated :
      ∀ T history,
        |contribution T history| ≤
          L *
            ∑ i : {i // i ∈ active},
              selectedTransitionMassSum selection i.1 T history)
    (hmass :
      IsAsymptoticallySublinear
        (transitionSetExpectedMass initial kernel selection active)) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (mixedTransitionComparison kernel selection))
            (T + 1))
          (fun history => |contribution T history|)) := by
  let absoluteContribution : ℕ → ℝ := fun T =>
    expect
      (adaptiveHistoryLaw
        (adaptiveMarkovStep initial
          (mixedTransitionComparison kernel selection))
        (T + 1))
      (fun history => |contribution T history|)
  have hnonneg : ∀ T, 0 ≤ absoluteContribution T := by
    intro T
    exact expect_nonneg _ _ fun history => abs_nonneg _
  have hupper :
      ∀ T,
        absoluteContribution T ≤
          L * transitionSetExpectedMass initial kernel selection active T := by
    intro T
    let law :=
      adaptiveHistoryLaw
        (adaptiveMarkovStep initial
          (mixedTransitionComparison kernel selection))
        (T + 1)
    calc
      absoluteContribution T ≤
          expect law
            (fun history =>
              L *
                ∑ i : {i // i ∈ active},
                  selectedTransitionMassSum selection i.1 T history) := by
        exact expect_mono _ _ _ (hdominated T)
      _ = L * transitionSetExpectedMass initial kernel selection active T := by
        exact expect_const_mul _ _ _
  have hscaled :
      IsAsymptoticallySublinear
        (fun T =>
          L * transitionSetExpectedMass initial kernel selection active T) :=
    hmass.const_mul L
  change Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * absoluteContribution T)
    atTop (nhds 0)
  change Tendsto
    (fun T : ℕ =>
      (T : ℝ)⁻¹ *
        (L * transitionSetExpectedMass initial kernel selection active T))
    atTop (nhds 0) at hscaled
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T)) (hnonneg T)
  · exact Filter.Eventually.of_forall fun T =>
      mul_le_mul_of_nonneg_left (hupper T)
        (inv_nonneg.mpr (Nat.cast_nonneg T))
  · exact hscaled

end Probability
end Math
