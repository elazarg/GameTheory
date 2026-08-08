/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Math.ProbabilityMassFunction
import Math.SurvivalProduct

/-! # Discrete hazard stopping laws

The game-independent law of the first `true` in a sequence of Boolean
Bernoulli hazards.  `none` is the atom for never stopping.  The scalar API is
the primary interface; the Boolean API is the adapter used by live-spine game
behaviours. -/

noncomputable section

open scoped BigOperators

namespace Math.Probability.DiscreteHazard

open Filter Math.ProbabilityMassFunction

/-- A scalar discrete hazard. -/
structure ScalarHazard where
  stop : ℕ → ℝ
  stop_nonneg : ∀ time, 0 ≤ stop time
  stop_le_one : ∀ time, stop time ≤ 1

/-- A Boolean hazard, where `true` means stop. -/
abbrev BooleanHazard := ℕ → PMF Bool

def stopProbability (hazard : BooleanHazard) (time : ℕ) : ℝ :=
  (hazard time true).toReal

def continueProbability (hazard : BooleanHazard) (time : ℕ) : ℝ :=
  (hazard time false).toReal

theorem continue_add_stop (hazard : BooleanHazard) (time : ℕ) :
    continueProbability hazard time + stopProbability hazard time = 1 := by
  simpa [continueProbability, stopProbability, Fintype.sum_bool, add_comm] using
    pmf_toReal_sum_one (hazard time)

theorem continue_nonneg (hazard : BooleanHazard) (time : ℕ) :
    0 ≤ continueProbability hazard time := ENNReal.toReal_nonneg

theorem stop_nonneg (hazard : BooleanHazard) (time : ℕ) :
    0 ≤ stopProbability hazard time := ENNReal.toReal_nonneg

theorem continue_le_one (hazard : BooleanHazard) (time : ℕ) :
    continueProbability hazard time ≤ 1 := by
  linarith [continue_add_stop hazard time, stop_nonneg hazard time]

namespace ScalarHazard

/-- Survival over a window, deliberately using the canonical product. -/
def survival (hazard : ScalarHazard) (start fuel : ℕ) : ℝ :=
  Math.survivalProduct (fun time => 1 - hazard.stop time) start fuel

def stopMass (hazard : ScalarHazard) (time : ℕ) : ℝ :=
  hazard.survival 0 time * hazard.stop time

theorem survival_zero (hazard : ScalarHazard) (start : ℕ := 0) :
    hazard.survival start 0 = 1 := Math.survivalProduct_zero _ _

theorem survival_succ (hazard : ScalarHazard) (start fuel : ℕ) :
    hazard.survival start (fuel + 1) =
      hazard.survival start fuel * (1 - hazard.stop (start + fuel)) :=
  Math.survivalProduct_succ _ _ _

theorem survival_nonneg (hazard : ScalarHazard) (start fuel : ℕ) :
    0 ≤ hazard.survival start fuel :=
  Math.survivalProduct_nonneg _ (fun t => sub_nonneg.mpr (hazard.stop_le_one t)) _ _

theorem survival_le_one (hazard : ScalarHazard) (start fuel : ℕ) :
    hazard.survival start fuel ≤ 1 :=
  Math.survivalProduct_le_one _
    (fun t => sub_nonneg.mpr (hazard.stop_le_one t))
    (fun t => sub_le_self _ (hazard.stop_nonneg t)) _ _

theorem stopMass_nonneg (hazard : ScalarHazard) (time : ℕ) :
    0 ≤ hazard.stopMass time :=
  mul_nonneg (survival_nonneg hazard 0 time) (hazard.stop_nonneg time)

theorem stopMass_eq_survival_sub_succ (hazard : ScalarHazard) (time : ℕ) :
    hazard.stopMass time = hazard.survival 0 time - hazard.survival 0 (time + 1) := by
  rw [survival_succ]
  dsimp [stopMass]
  ring_nf

theorem sum_stopMass (hazard : ScalarHazard) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff, hazard.stopMass time) = 1 - hazard.survival 0 cutoff := by
  induction cutoff with
  | zero => simp [survival_zero]
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih, stopMass_eq_survival_sub_succ]
      ring

private theorem survival_antitone_zero (hazard : ScalarHazard) :
    Antitone (hazard.survival 0) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [survival_succ]
  exact mul_le_of_le_one_right (survival_nonneg hazard 0 n)
    (by simpa using sub_le_self 1 (hazard.stop_nonneg n))

/-- The mass of never stopping. -/
def neverMass (hazard : ScalarHazard) : ℝ := ⨅ cutoff : ℕ, hazard.survival 0 cutoff

private theorem survival_bddBelow (hazard : ScalarHazard) :
    BddBelow (Set.range (hazard.survival 0)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact survival_nonneg hazard 0 n

theorem neverMass_nonneg (hazard : ScalarHazard) : 0 ≤ hazard.neverMass :=
  le_ciInf fun cutoff => survival_nonneg hazard 0 cutoff

theorem neverMass_le_survival (hazard : ScalarHazard) (cutoff : ℕ) :
    hazard.neverMass ≤ hazard.survival 0 cutoff :=
  ciInf_le (survival_bddBelow hazard) cutoff

theorem tendsto_survival_neverMass (hazard : ScalarHazard) :
    Tendsto (hazard.survival 0) atTop (nhds hazard.neverMass) := by
  apply tendsto_atTop_ciInf (survival_antitone_zero hazard)
  exact survival_bddBelow hazard

theorem hasSum_stopMass (hazard : ScalarHazard) :
    HasSum hazard.stopMass (1 - hazard.neverMass) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (stopMass_nonneg hazard)
    (1 - hazard.neverMass)).2
  simpa only [sum_stopMass] using tendsto_const_nhds.sub
    (tendsto_survival_neverMass hazard)

private def encodedMass (hazard : ScalarHazard) : ℕ → ℝ
  | 0 => hazard.neverMass
  | time + 1 => hazard.stopMass time

private theorem encodedMass_nonneg (hazard : ScalarHazard) : ∀ n, 0 ≤ encodedMass hazard n
  | 0 => neverMass_nonneg hazard
  | _ + 1 => stopMass_nonneg hazard _

private theorem sum_encodedMass_succ (hazard : ScalarHazard) (cutoff : ℕ) :
    (∑ code ∈ Finset.range (cutoff + 1), encodedMass hazard code) =
      hazard.neverMass + ∑ time ∈ Finset.range cutoff, hazard.stopMass time := by
  induction cutoff with
  | zero => simp [encodedMass]
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [encodedMass]
      ring

private theorem hasSum_encodedMass (hazard : ScalarHazard) : HasSum (encodedMass hazard) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (encodedMass_nonneg hazard) 1).2
  apply (tendsto_add_atTop_iff_nat 1).1
  have hs := (hasSum_stopMass hazard).tendsto_sum_nat
  have hc : Tendsto (fun _ : ℕ => hazard.neverMass) atTop (nhds hazard.neverMass) :=
    tendsto_const_nhds
  have h := hc.add hs
  have hlimit : hazard.neverMass + (1 - hazard.neverMass) = 1 := by ring
  rw [hlimit] at h
  simpa only [sum_encodedMass_succ] using h

private def encodedLaw (hazard : ScalarHazard) : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (encodedMass hazard n), by
    apply ENNReal.summable.hasSum_iff.2
    rw [← ENNReal.ofReal_tsum_of_nonneg (encodedMass_nonneg hazard)
      (hasSum_encodedMass hazard).summable]
    rw [(hasSum_encodedMass hazard).tsum_eq]
    norm_num⟩

private def choiceEquivNat : Option ℕ ≃ ℕ where
  toFun | none => 0 | some n => n + 1
  invFun | 0 => none | n + 1 => some n
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

/-- The probability mass function of the first stopping date. -/
def stoppingLaw (hazard : ScalarHazard) : PMF (Option ℕ) :=
  (encodedLaw hazard).map choiceEquivNat.symm

@[simp] theorem stoppingLaw_none_toReal (hazard : ScalarHazard) :
    (hazard.stoppingLaw none).toReal = hazard.neverMass := by
  rw [stoppingLaw, Math.ProbabilityMassFunction.map_equiv_apply]
  exact ENNReal.toReal_ofReal (neverMass_nonneg hazard)

@[simp] theorem stoppingLaw_some_toReal (hazard : ScalarHazard) (time : ℕ) :
    (hazard.stoppingLaw (some time)).toReal = hazard.stopMass time := by
  rw [stoppingLaw, Math.ProbabilityMassFunction.map_equiv_apply]
  exact ENNReal.toReal_ofReal (stopMass_nonneg hazard time)

theorem stoppingLaw_expect (hazard : ScalarHazard) (value : Option ℕ → ℝ)
    {M : ℝ} (hvalue : ∀ choice, |value choice| ≤ M) :
    expect hazard.stoppingLaw value = hazard.neverMass * value none +
      ∑' time : ℕ, hazard.stopMass time * value (some time) := by
  rw [stoppingLaw, expect_map]
  have hs := expect_summable_of_bounded (encodedLaw hazard)
    (fun n => value (choiceEquivNat.symm n)) (fun n => hvalue (choiceEquivNat.symm n))
  unfold expect
  rw [hs.tsum_eq_zero_add]
  congr 1
  · change (ENNReal.ofReal hazard.neverMass).toReal * value none = _
    rw [ENNReal.toReal_ofReal (neverMass_nonneg hazard)]
  · apply tsum_congr
    intro n
    change (ENNReal.ofReal (hazard.stopMass n)).toReal * value (some n) = _
    rw [ENNReal.toReal_ofReal (stopMass_nonneg hazard n)]

/-- Divergent cumulative hazard forces the survival probability to vanish. -/
theorem tendsto_survival_zero_of_tendsto_sum_atTop (hazard : ScalarHazard)
    (hdiv : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, hazard.stop i) atTop atTop) :
    Tendsto (hazard.survival 0) atTop (nhds 0) := by
  have hprod : ∀ n : ℕ, hazard.survival 0 n ≤
      Real.exp (-∑ i ∈ Finset.range n, hazard.stop i) := by
    intro n
    unfold survival Math.survivalProduct
    simp only [zero_add]
    calc
      (∏ i ∈ Finset.range n, (1 - hazard.stop i)) ≤
          ∏ i ∈ Finset.range n, Real.exp (-hazard.stop i) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact sub_nonneg.mpr (hazard.stop_le_one i)
        · intro i hi
          exact Real.one_sub_le_exp_neg _
      _ = Real.exp (-∑ i ∈ Finset.range n, hazard.stop i) := by
        rw [← Finset.sum_neg_distrib, ← Real.exp_sum]
  have hexp : Tendsto (fun n : ℕ => Real.exp (-∑ i ∈ Finset.range n, hazard.stop i))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
  · filter_upwards with n
    exact survival_nonneg hazard 0 n
  · filter_upwards with n
    exact hprod n

theorem neverMass_eq_zero_of_tendsto_sum_atTop (hazard : ScalarHazard)
    (hdiv : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, hazard.stop i) atTop atTop) :
    hazard.neverMass = 0 := by
  rw [← tendsto_nhds_unique (tendsto_survival_neverMass hazard)
    (tendsto_survival_zero_of_tendsto_sum_atTop hazard hdiv)]

end ScalarHazard

/-- View a Boolean hazard as its scalar stop-probability hazard. -/
def BooleanHazard.toScalar (hazard : BooleanHazard) : ScalarHazard where
  stop := stopProbability hazard
  stop_nonneg := stop_nonneg hazard
  stop_le_one := fun t => by linarith [continue_add_stop hazard t, continue_nonneg hazard t]

theorem BooleanHazard.survival_eq_scalar (hazard : BooleanHazard) (cutoff : ℕ) :
    Math.survivalProduct (continueProbability hazard) 0 cutoff =
      hazard.toScalar.survival 0 cutoff := by
  unfold ScalarHazard.survival BooleanHazard.toScalar
  congr 2
  funext t
  linarith [continue_add_stop hazard t]

/-- Deterministically attach a mark to each finite stopping date. -/
def markedStoppingLaw {Mark : Type} (hazard : ScalarHazard) (mark : ℕ → Mark) :
    PMF (Option (ℕ × Mark)) :=
  hazard.stoppingLaw.map (Option.map fun time => (time, mark time))

theorem markedStoppingLaw_expect {Mark : Type} (hazard : ScalarHazard)
    (mark : ℕ → Mark) (value : Option (ℕ × Mark) → ℝ) :
    expect (markedStoppingLaw hazard mark) value = expect hazard.stoppingLaw
      (fun choice => value (Option.map (fun time => (time, mark time)) choice)) := by
  rw [markedStoppingLaw, expect_map]

end Math.Probability.DiscreteHazard
