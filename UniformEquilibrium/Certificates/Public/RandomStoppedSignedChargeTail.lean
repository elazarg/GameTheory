/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.RandomStoppedAdaptiveSplice
import Math.Probability.SublinearLedger

/-!
# Signed child-charge tails after bounded public stopping

Ordinary child Cesàro bounds do not control a stopped suffix for arbitrary
signed charges: removing an initial segment can remove a large negative
amount.  A uniform lower bound is the exact elementary repair needed for a
bounded stopping time.

If every scalar charge is at least `-B`, removing at most `fuel` terms costs
at most `fuel * B`.  This is a fixed cumulative cost, so its normalized
effect is eventually smaller than any prescribed positive slack.  The
result below upgrades ordinary finite-child adaptive-system bounds to the
common-root signed-tail interface at error `childError + slack`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability

variable {ι Child : Type} {G : StochasticGame ι}

/-- A common lower bound for all three stopped-child scalar charge
families, uniform over bases, players, deviations, and local times. -/
structure ChildScalarChargesBoundedBelow
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (lowerCharge upperCharge :
      G.BoundedStoppedHistory fuel → ι → ℕ → ℝ)
    (deviationCharge :
      ∀ (_base : G.BoundedStoppedHistory fuel) (who : ι),
        G.BehaviorStrategy who → ℕ → ℝ)
    (bound : ℝ) : Prop where
  bound_nonneg : 0 ≤ bound
  lower : ∀ (base : G.BoundedStoppedHistory fuel)
    (who : ι) (time : ℕ), -bound ≤ lowerCharge base who time
  upper : ∀ (base : G.BoundedStoppedHistory fuel)
    (who : ι) (time : ℕ), -bound ≤ upperCharge base who time
  deviation :
    ∀ (base : G.BoundedStoppedHistory fuel) (who : ι)
      (strategy : G.BehaviorStrategy who) (time : ℕ),
      -bound ≤ deviationCharge base who strategy time

/-- Removing the bounded initial segment of a sequence bounded below by
`-bound` increases its sum by at most `fuel * bound`. -/
theorem sum_Ico_sub_le_sum_range_add_of_boundedBelow
    (charge : ℕ → ℝ) (stop fuel total : ℕ) (bound : ℝ)
    (stop_le_fuel : stop ≤ fuel) (fuel_le_total : fuel ≤ total)
    (charge_lower : ∀ time, -bound ≤ charge time) :
    ∑ rootTime ∈ Finset.Ico fuel total,
        charge (rootTime - stop) ≤
      (∑ time ∈ Finset.range total, charge time) +
        (fuel : ℝ) * bound := by
  have shifted_nonneg :
      ∀ time, 0 ≤ charge time + bound := by
    intro time
    linarith [charge_lower time]
  have shifted :=
    sum_Ico_sub_le_sum_range_of_nonneg
      (fun time => charge time + bound)
      stop fuel total stop_le_fuel fuel_le_total shifted_nonneg
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Ico, Finset.card_range, nsmul_eq_mul] at shifted
  have cast_sub :
      ((total - fuel : ℕ) : ℝ) + (fuel : ℝ) = (total : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel fuel_le_total
  have bound_split :
      (total : ℝ) * bound =
        ((total - fuel : ℕ) : ℝ) * bound +
          (fuel : ℝ) * bound := by
    rw [← cast_sub]
    ring
  linarith

/-- Average the signed-tail estimate over a finite stopped-base law. -/
theorem normalized_expect_Ico_sub_le_add_of_boundedBelow
    {Base : Type} [Finite Base]
    (law : PMF Base) (stop : Base → ℕ)
    (charge : Base → ℕ → ℝ)
    (fuel total : ℕ) (bound error : ℝ)
    (stop_le_fuel : ∀ base, stop base ≤ fuel)
    (fuel_le_total : fuel ≤ total)
    (charge_lower : ∀ base time, -bound ≤ charge base time)
    (full_bound : ∀ base,
      (total : ℝ)⁻¹ *
          ∑ time ∈ Finset.range total, charge base time ≤
        error) :
    (total : ℝ)⁻¹ *
        ∑ rootTime ∈ Finset.Ico fuel total,
          expect law (fun base =>
            charge base (rootTime - stop base)) ≤
      error + (total : ℝ)⁻¹ * ((fuel : ℝ) * bound) := by
  classical
  letI : Fintype Base := Fintype.ofFinite Base
  have sum_expect :
      ∑ rootTime ∈ Finset.Ico fuel total,
          expect law (fun base =>
            charge base (rootTime - stop base)) =
        expect law (fun base =>
          ∑ rootTime ∈ Finset.Ico fuel total,
            charge base (rootTime - stop base)) := by
    simp only [expect_eq_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro base _
    rw [Finset.mul_sum]
  rw [sum_expect, ← expect_const_mul]
  calc
    expect law (fun base =>
        (total : ℝ)⁻¹ *
          ∑ rootTime ∈ Finset.Ico fuel total,
            charge base (rootTime - stop base)) ≤
      expect law (fun _ =>
        error + (total : ℝ)⁻¹ * ((fuel : ℝ) * bound)) := by
          apply expect_mono
          intro base
          have tail_le :=
            sum_Ico_sub_le_sum_range_add_of_boundedBelow
              (charge base) (stop base) fuel total bound
              (stop_le_fuel base) fuel_le_total
              (charge_lower base)
          calc
            (total : ℝ)⁻¹ *
                ∑ rootTime ∈ Finset.Ico fuel total,
                  charge base (rootTime - stop base) ≤
              (total : ℝ)⁻¹ *
                ((∑ time ∈ Finset.range total,
                    charge base time) +
                  (fuel : ℝ) * bound) :=
              mul_le_mul_of_nonneg_left tail_le (by positivity)
            _ =
                ((total : ℝ)⁻¹ *
                  ∑ time ∈ Finset.range total,
                    charge base time) +
                  (total : ℝ)⁻¹ * ((fuel : ℝ) * bound) := by
                    ring
            _ ≤
                error +
                  (total : ℝ)⁻¹ * ((fuel : ℝ) * bound) :=
              add_le_add (full_bound base) (le_refl _)
    _ =
        error + (total : ℝ)⁻¹ * ((fuel : ℝ) * bound) :=
      expect_const _ _

namespace FiniteChildAdaptivePotentialFamily

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {childError : ℝ}

/-- Uniformly lower-bounded signed child charges acquire the common-root
tail bound after any bounded stopping time, at arbitrarily small additional
error. -/
def commonRootChildChargeTailBound_of_boundedBelow
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (observe : G.BoundedStoppedHistory fuel → Child)
    (bound : ℝ)
    (boundedBelow :
      G.ChildScalarChargesBoundedBelow
        (family.stoppedLowerCharge observe)
        (family.stoppedUpperCharge observe)
        (family.stoppedDeviationCharge observe) bound)
    (slack : ℝ) (slack_pos : 0 < slack) :
    G.CommonRootChildChargeTailBound
      profile initial selector
      (family.stoppedLowerCharge observe)
      (family.stoppedUpperCharge observe)
      (family.stoppedDeviationCharge observe)
      (childError + slack) := by
  let prefixCost : ℝ := (fuel : ℝ) * bound
  have prefixCost_sublinear :
      IsAsymptoticallySublinear (fun _ : ℕ => prefixCost) :=
    IsAsymptoticallySublinear.const prefixCost
  have prefixHorizon_exists :
      ∃ prefixHorizon : ℕ, ∀ total,
        prefixHorizon ≤ total →
          (total : ℝ)⁻¹ * prefixCost ≤ slack :=
    eventually_atTop.mp
      (prefixCost_sublinear.eventually_average_le slack_pos)
  let prefixHorizon : ℕ := Classical.choose prefixHorizon_exists
  have prefixHorizon_spec :
      ∀ total, prefixHorizon ≤ total →
        (total : ℝ)⁻¹ * prefixCost ≤ slack :=
    Classical.choose_spec prefixHorizon_exists
  let horizon :=
    max 2 (max fuel (max family.commonHorizon prefixHorizon))
  refine {
    horizon := horizon
    horizon_ge_two := Nat.le_max_left 2 _
    lower := ?_
    upper := ?_
    deviation := ?_
  }
  · intro who total htotal
    have fuel_le_total : fuel ≤ total :=
      le_trans
        (le_trans (Nat.le_max_left fuel _) (Nat.le_max_right 2 _))
        htotal
    have childHorizon_le_total : family.commonHorizon ≤ total :=
      le_trans
        (le_trans
          (Nat.le_max_left family.commonHorizon prefixHorizon)
          (Nat.le_max_right fuel _))
        (le_trans (Nat.le_max_right 2 _) htotal)
    have prefixHorizon_le_total : prefixHorizon ≤ total :=
      le_trans
        (le_trans
          (Nat.le_max_right family.commonHorizon prefixHorizon)
          (Nat.le_max_right fuel _))
        (le_trans (Nat.le_max_right 2 _) htotal)
    have tail :=
      normalized_expect_Ico_sub_le_add_of_boundedBelow
        (G.stoppedHistoryLaw profile initial selector)
        (fun base => base.1.val)
        (fun base time =>
          family.stoppedLowerCharge observe base who time)
        fuel total bound childError
        (fun base => Nat.lt_succ_iff.mp base.1.isLt)
        fuel_le_total
        (fun base time => boundedBelow.lower base who time)
        (fun base =>
          (family.system (observe base)).lower_charge_cesaro
            who total
            (le_trans (family.horizon_le_common _) childHorizon_le_total))
    exact tail.trans
      (add_le_add (le_refl childError)
        (by
          simpa [prefixCost] using
            prefixHorizon_spec total prefixHorizon_le_total))
  · intro who total htotal
    have fuel_le_total : fuel ≤ total :=
      le_trans
        (le_trans (Nat.le_max_left fuel _) (Nat.le_max_right 2 _))
        htotal
    have childHorizon_le_total : family.commonHorizon ≤ total :=
      le_trans
        (le_trans
          (Nat.le_max_left family.commonHorizon prefixHorizon)
          (Nat.le_max_right fuel _))
        (le_trans (Nat.le_max_right 2 _) htotal)
    have prefixHorizon_le_total : prefixHorizon ≤ total :=
      le_trans
        (le_trans
          (Nat.le_max_right family.commonHorizon prefixHorizon)
          (Nat.le_max_right fuel _))
        (le_trans (Nat.le_max_right 2 _) htotal)
    have tail :=
      normalized_expect_Ico_sub_le_add_of_boundedBelow
        (G.stoppedHistoryLaw profile initial selector)
        (fun base => base.1.val)
        (fun base time =>
          family.stoppedUpperCharge observe base who time)
        fuel total bound childError
        (fun base => Nat.lt_succ_iff.mp base.1.isLt)
        fuel_le_total
        (fun base time => boundedBelow.upper base who time)
        (fun base =>
          (family.system (observe base)).upper_charge_cesaro
            who total
            (le_trans (family.horizon_le_common _) childHorizon_le_total))
    exact tail.trans
      (add_le_add (le_refl childError)
        (by
          simpa [prefixCost] using
            prefixHorizon_spec total prefixHorizon_le_total))
  · intro who strategy total htotal
    have fuel_le_total : fuel ≤ total :=
      le_trans
        (le_trans (Nat.le_max_left fuel _) (Nat.le_max_right 2 _))
        htotal
    have childHorizon_le_total : family.commonHorizon ≤ total :=
      le_trans
        (le_trans
          (Nat.le_max_left family.commonHorizon prefixHorizon)
          (Nat.le_max_right fuel _))
        (le_trans (Nat.le_max_right 2 _) htotal)
    have prefixHorizon_le_total : prefixHorizon ≤ total :=
      le_trans
        (le_trans
          (Nat.le_max_right family.commonHorizon prefixHorizon)
          (Nat.le_max_right fuel _))
        (le_trans (Nat.le_max_right 2 _) htotal)
    have tail :=
      normalized_expect_Ico_sub_le_add_of_boundedBelow
        (G.stoppedHistoryLaw
          (Function.update profile who strategy) initial selector)
        (fun base => base.1.val)
        (fun base time =>
          family.stoppedDeviationCharge observe base who
            (G.afterHistoryStrategy strategy base.2) time)
        fuel total bound childError
        (fun base => Nat.lt_succ_iff.mp base.1.isLt)
        fuel_le_total
        (fun base time =>
          boundedBelow.deviation base who
            (G.afterHistoryStrategy strategy base.2) time)
        (fun base =>
          (family.system (observe base)).deviation_charge_cesaro
            who (G.afterHistoryStrategy strategy base.2) total
            (le_trans (family.horizon_le_common _) childHorizon_le_total))
    exact tail.trans
      (add_le_add (le_refl childError)
        (by
          simpa [prefixCost] using
            prefixHorizon_spec total prefixHorizon_le_total))

end FiniteChildAdaptivePotentialFamily
end StochasticGame
end GameTheory
