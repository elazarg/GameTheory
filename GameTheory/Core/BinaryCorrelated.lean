/-
# Binary correlated games

The correlated-equilibrium calculation for a Matching-Pennies-like form. Four
recommendation-dependent deviations force a cycle of inequalities among the
four pure-profile masses; normalization then makes every mass one quarter.
-/

import GameTheory.Core.BinaryMixed
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory

open Probability

namespace GameForm.MatchingPenniesLike

variable {F : GameForm (Fin 2)} {utility : F.sig.Outcome → Fin 2 → ℝ}
  (h : F.MatchingPenniesLike utility)

theorem encodeProfile_injective : Function.Injective h.encodeProfile := by
  intro first second heq
  rw [← h.profile_encodeProfile first, ← h.profile_encodeProfile second, heq]

/-- Reindex an expectation over pure profiles by the four Boolean labels. -/
theorem expect_eq_sum_profile (law : FinDist (Profile F.sig))
    (observable : Profile F.sig → ℝ) :
    law.expect observable =
      ∑ bits : Fin 2 → Bool,
        law.prob (h.profile bits) * observable (h.profile bits) := by
  classical
  calc
    law.expect observable =
        (law.map h.encodeProfile).expect fun bits =>
          observable (h.profile bits) := by
      rw [FinDist.expect_map]
      apply FinDist.expect_congr
      intro pureProfile _
      rw [h.profile_encodeProfile]
    _ = ∑ bits : Fin 2 → Bool,
          law.prob (h.profile bits) * observable (h.profile bits) := by
      rw [FinDist.expect_eq_sum]
      apply Finset.sum_congr rfl
      intro bits _
      have hprob : (law.map h.encodeProfile).prob bits =
          law.prob (h.profile bits) := by
        simpa using FinDist.prob_map_of_injective h.encodeProfile
          h.encodeProfile_injective law (h.profile bits)
      rw [hprob]

@[simp]
theorem update_profile_zero (bits : Fin 2 → Bool) (bit : Bool) :
    Profile.update (h.profile bits) 0 (h.action 0 bit) =
      h.profile ![bit, bits 1] := by
  apply h.encodeProfile_injective
  funext i
  fin_cases i
  · simp [encodeProfile, profile]
    rfl
  · simp [encodeProfile, profile]
    rfl

@[simp]
theorem update_profile_one (bits : Fin 2 → Bool) (bit : Bool) :
    Profile.update (h.profile bits) 1 (h.action 1 bit) =
      h.profile ![bits 0, bit] := by
  apply h.encodeProfile_injective
  funext i
  fin_cases i
  · simp [encodeProfile, profile]
    rfl
  · simp [encodeProfile, profile]
    rfl

private def bitsTT : Fin 2 → Bool := ![true, true]
private def bitsTF : Fin 2 → Bool := ![true, false]
private def bitsFT : Fin 2 → Bool := ![false, true]
private def bitsFF : Fin 2 → Bool := ![false, false]

private theorem boolProfiles :
    (Finset.univ : Finset (Fin 2 → Bool)) =
      {bitsTT, bitsTF, bitsFT, bitsFF} := by
  decide

private theorem expect_eq_four (law : FinDist (Profile F.sig))
    (observable : Profile F.sig → ℝ) :
    law.expect observable =
      law.prob (h.profile bitsTT) * observable (h.profile bitsTT) +
      (law.prob (h.profile bitsTF) * observable (h.profile bitsTF) +
      (law.prob (h.profile bitsFT) * observable (h.profile bitsFT) +
       law.prob (h.profile bitsFF) * observable (h.profile bitsFF))) := by
  rw [h.expect_eq_sum_profile, boolProfiles,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem ce_prob_true_true_ge_true_false
    {law : FinDist (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    law.prob (h.profile bitsTT) ≥ law.prob (h.profile bitsTF) := by
  rw [isCorrelatedEq_iff] at hCE
  let dev : F.sig.Strategy 0 → F.sig.Strategy 0 := fun action =>
    if (h.action 0).symm action then h.action 0 false else action
  have hineq := hCE 0 dev
  rw [euPreference_apply, expectedUtility_outcomeLaw, expectedUtility_bind,
    h.expect_eq_four, h.expect_eq_four] at hineq
  simp only [profile, bitsTT, bitsTF, bitsFT, bitsFF,
    Matrix.cons_val_zero, dev, Equiv.symm_apply_apply, if_true,
    Bool.false_eq_true, if_false, h.update_profile_zero] at hineq
  simp_rw [h.expectedUtility_profile_zero] at hineq
  norm_num at hineq
  simp only [bitsTT, bitsTF] at ⊢
  nlinarith [h.scale_pos]

private theorem ce_prob_true_false_ge_false_false
    {law : FinDist (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    law.prob (h.profile bitsTF) ≥ law.prob (h.profile bitsFF) := by
  rw [isCorrelatedEq_iff] at hCE
  let dev : F.sig.Strategy 1 → F.sig.Strategy 1 := fun action =>
    if (h.action 1).symm action then action else h.action 1 true
  have hineq := hCE 1 dev
  rw [euPreference_apply, expectedUtility_outcomeLaw, expectedUtility_bind,
    h.expect_eq_four, h.expect_eq_four] at hineq
  simp only [profile, bitsTT, bitsTF, bitsFT, bitsFF,
    Matrix.cons_val_zero, Matrix.cons_val_one, dev,
    Equiv.symm_apply_apply, if_true,
    Bool.false_eq_true, if_false, h.update_profile_one] at hineq
  simp_rw [h.expectedUtility_profile_one] at hineq
  norm_num at hineq
  simp only [bitsTF, bitsFF] at ⊢
  nlinarith [h.scale_pos]

private theorem ce_prob_false_false_ge_false_true
    {law : FinDist (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    law.prob (h.profile bitsFF) ≥ law.prob (h.profile bitsFT) := by
  rw [isCorrelatedEq_iff] at hCE
  let dev : F.sig.Strategy 0 → F.sig.Strategy 0 := fun action =>
    if (h.action 0).symm action then action else h.action 0 true
  have hineq := hCE 0 dev
  rw [euPreference_apply, expectedUtility_outcomeLaw, expectedUtility_bind,
    h.expect_eq_four, h.expect_eq_four] at hineq
  simp only [profile, bitsTT, bitsTF, bitsFT, bitsFF,
    Matrix.cons_val_zero, dev, Equiv.symm_apply_apply, if_true,
    Bool.false_eq_true, if_false, h.update_profile_zero] at hineq
  simp_rw [h.expectedUtility_profile_zero] at hineq
  norm_num at hineq
  simp only [bitsFF, bitsFT] at ⊢
  nlinarith [h.scale_pos]

private theorem ce_prob_false_true_ge_true_true
    {law : FinDist (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    law.prob (h.profile bitsFT) ≥ law.prob (h.profile bitsTT) := by
  rw [isCorrelatedEq_iff] at hCE
  let dev : F.sig.Strategy 1 → F.sig.Strategy 1 := fun action =>
    if (h.action 1).symm action then h.action 1 false else action
  have hineq := hCE 1 dev
  rw [euPreference_apply, expectedUtility_outcomeLaw, expectedUtility_bind,
    h.expect_eq_four, h.expect_eq_four] at hineq
  simp only [profile, bitsTT, bitsTF, bitsFT, bitsFF,
    Matrix.cons_val_zero, Matrix.cons_val_one, dev,
    Equiv.symm_apply_apply, if_true,
    Bool.false_eq_true, if_false, h.update_profile_one] at hineq
  simp_rw [h.expectedUtility_profile_one] at hineq
  norm_num at hineq
  simp only [bitsFT, bitsTT] at ⊢
  nlinarith [h.scale_pos]

/-- Every pure profile receives probability one quarter in a correlated
equilibrium of a Matching-Pennies-like game. -/
theorem correlatedEq_profile_prob_eq_quarter
    {law : FinDist (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law)
    (bits : Fin 2 → Bool) :
    law.prob (h.profile bits) = (1 / 4 : ℝ) := by
  classical
  have hTT_TF := h.ce_prob_true_true_ge_true_false hCE
  have hTF_FF := h.ce_prob_true_false_ge_false_false hCE
  have hFF_FT := h.ce_prob_false_false_ge_false_true hCE
  have hFT_TT := h.ce_prob_false_true_ge_true_true hCE
  have hall :
      law.prob (h.profile bitsTT) = law.prob (h.profile bitsTF) ∧
      law.prob (h.profile bitsTF) = law.prob (h.profile bitsFF) ∧
      law.prob (h.profile bitsFF) = law.prob (h.profile bitsFT) := by
    constructor
    · linarith
    constructor <;> linarith
  have hsum : ∑ labels : Fin 2 → Bool, law.prob (h.profile labels) = 1 := by
    calc
      _ = ∑ labels : Fin 2 → Bool,
          (law.map h.encodeProfile).prob labels := by
        apply Finset.sum_congr rfl
        intro labels _
        symm
        simpa using FinDist.prob_map_of_injective h.encodeProfile
          h.encodeProfile_injective law (h.profile labels)
      _ = 1 := FinDist.sum_prob (law.map h.encodeProfile)
  rw [boolProfiles,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  have hquarter : law.prob (h.profile bitsTT) = (1 / 4 : ℝ) := by
    linarith
  have hlabels : bits ∈
      ({bitsTT, bitsTF, bitsFT, bitsFF} : Finset (Fin 2 → Bool)) := by
    rw [← boolProfiles]
    exact Finset.mem_univ bits
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlabels
  rcases hlabels with rfl | rfl | rfl | rfl
  · exact hquarter
  · linarith [hall.1]
  · linarith [hall.1, hall.2.1, hall.2.2]
  · linarith [hall.1, hall.2.1]

/-- A Matching-Pennies-like game has exactly one correlated equilibrium: the
independent product of its fair marginals. -/
theorem correlatedEq_unique
    {law : FinDist (Profile F.sig)}
    (hCE : IsCorrelatedEq F (euPreference utility) law) :
    law = FinDist.pi h.fairProfile := by
  apply FinDist.ext_of_prob
  intro pureProfile
  rw [← h.profile_encodeProfile pureProfile,
    h.correlatedEq_profile_prob_eq_quarter hCE, FinDist.prob_pi,
    Fin.prod_univ_two]
  simp only [profile]
  rw [h.fairProfile_prob_action,
    h.fairProfile_prob_action]
  norm_num

end GameForm.MatchingPenniesLike

end GameTheory
