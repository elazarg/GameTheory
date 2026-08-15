/-
# Strategyproof direct mechanisms

Solution concepts for direct mechanisms are transparent specializations of the
canonical response API.  The syntax module remains capability-light and does
not import this file.
-/

import GameTheory.Languages.Mechanism
import GameTheory.Core.Response
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Languages

open GameTheory GameTheory.Math.Probability

universe uι us

namespace Mechanism

variable {ι : Type uι} [DecidableEq ι] (M : Mechanism ι)

/-- Strategyproofness is dominance of the designated truthful report profile
in the compiled deterministic form. -/
def IsStrategyproof (utility : M.Outcome → ι → ℝ)
    (truth : ∀ i, M.Report i) : Prop :=
  IsDominantProfile M.toForm (euPreference utility) truth

omit [DecidableEq ι] in
/-- Expected utility of the deterministic mechanism is utility of its chosen
outcome. -/
theorem utility_toForm (utility : M.Outcome → ι → ℝ)
    (reports : ∀ i, M.Report i) (who : ι) :
    expectedUtility utility who (M.toForm.play reports) =
      utility (M.choose reports) who :=
  FinDist.expect_pure ..

/-- Strategyproofness unfolded to its reportwise incentive inequalities. -/
theorem isStrategyproof_iff (utility : M.Outcome → ι → ℝ)
    (truth : ∀ i, M.Report i) :
    M.IsStrategyproof utility truth ↔
      ∀ (who : ι) (misreport : M.Report who)
        (reports : Profile M.toForm.sig),
        utility (M.choose (Profile.update reports who misreport)) who ≤
          utility (M.choose
            (Profile.update reports who (truth who))) who := by
  constructor
  · intro hproof who misreport reports
    have := hproof who misreport reports
    rwa [euPreference_apply, utility_toForm, utility_toForm] at this
  · intro hbeat who misreport reports
    rw [euPreference_apply, utility_toForm, utility_toForm]
    exact hbeat who misreport reports

end Mechanism

/-! ## Discriminating two-bidder examples -/

/-- Who won and what they pay. -/
abbrev Award := Fin 2 × ℝ

/-- The winner's surplus is private value less price; the loser gets zero. -/
def surplus (value : Fin 2 → ℝ) (award : Award) (who : Fin 2) : ℝ :=
  if award.1 = who then value who - award.2 else 0

/-- A two-bidder second-price mechanism with ties awarded to bidder zero. -/
@[reducible]
def vickrey : Mechanism (Fin 2) where
  Report _ := ℝ
  Outcome := Award
  choose bids := if bids 0 < bids 1 then (1, bids 0) else (0, bids 1)

/-- A two-bidder first-price mechanism with the same tie rule. -/
@[reducible]
def firstPrice : Mechanism (Fin 2) where
  Report _ := ℝ
  Outcome := Award
  choose bids := if bids 0 < bids 1 then (1, bids 1) else (0, bids 0)

/-- Truthful bidding is dominant in the second-price mechanism. -/
theorem vickrey_isStrategyproof (value : Fin 2 → ℝ) :
    vickrey.IsStrategyproof (surplus value) value := by
  rw [Mechanism.isStrategyproof_iff]
  intro who misreport bids
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · show surplus value (if _ < _ then _ else _) 0 ≤
      surplus value (if _ < _ then _ else _) 0
    rw [Profile.update_same, Profile.update_of_ne _ _ (by decide),
      Profile.update_same, Profile.update_of_ne _ _ (by decide)]
    unfold surplus
    split_ifs <;> (simp_all; try linarith)
  · show surplus value (if _ < _ then _ else _) 1 ≤
      surplus value (if _ < _ then _ else _) 1
    rw [Profile.update_same, Profile.update_of_ne _ _ (by decide),
      Profile.update_same, Profile.update_of_ne _ _ (by decide)]
    unfold surplus
    split_ifs <;> (simp_all; try linarith)

/-- What bidder zero receives after replacing only their own first-price bid. -/
theorem firstPrice_choose_zero (reports : Profile firstPrice.toForm.sig)
    (bid : ℝ) :
    firstPrice.choose (Profile.update reports 0 bid) =
      if bid < reports 1 then (1, reports 1) else (0, bid) := by
  show (if Profile.update reports 0 bid 0 <
      Profile.update reports 0 bid 1 then _ else _) = _
  rw [Profile.update_same, Profile.update_of_ne _ _ (by decide)]

/-- Truthful reporting is not dominant in the first-price mechanism: bidder
zero can shade a value-one bid against a zero bid. -/
theorem firstPrice_not_isStrategyproof :
    ¬ firstPrice.IsStrategyproof (surplus ![1, 1]) ![1, 1] := by
  rw [Mechanism.isStrategyproof_iff]
  intro hproof
  have hbeat := hproof 0 (1 / 2) ![1, 0]
  rw [firstPrice_choose_zero, firstPrice_choose_zero] at hbeat
  norm_num [surplus] at hbeat

end GameTheory.Languages
