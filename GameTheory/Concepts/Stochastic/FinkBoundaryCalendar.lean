/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkLimit

/-!
# Boundary-rate tests for Fink calendars

This file isolates two facts about the remaining projective-boundary calendar
problem.  First, waiting cannot in general be preloaded for free: for a
decreasing positive hold cost, summable total hold cost bounds activation time
times the preceding hold cost.  Thus sufficiently fast growth of the next
endpoint cost is incompatible with terminal amortization.

Second, the genuine exact-tail branch has no rate obstruction.  If the next
reference exposed by the root correction is exact from some point onward, the
verified fast corrected branch survives annealing and gives corrected calendar
selectability without any dilation hypothesis.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter

/-- The activation time is the sum of all preceding slow-calendar block
lengths. -/
theorem sum_slowCalendarBlockLength (B : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (slowCalendarBlockLength B n : ℝ) =
      (slowCalendarStart B N : ℝ) := by
  induction N with
  | zero => simp [slowCalendarStart]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact_mod_cast slowCalendarStart_add_blockLength B N

/-- A preload obstruction for every slow unit-step calendar.  If `h` is a
positive decreasing hold cost and the block-weighted hold bill is summable,
then activation time for layer `n + 1` times `h n` stays bounded.  Consequently
an endpoint cost `A (n + 1)` with `A (n + 1) * h n → ∞` cannot be amortized at
the activation times.  This shows that pointwise vanishing of the hierarchy
defect alone cannot imply the missing calendar compatibility. -/
theorem not_tendsto_slowUnitStepCalendar_terminal_zero_of_preloadObstruction
    (B A h : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hh : Antitone h) (hhpos : ∀ n, 0 < h n)
    (hbill : Summable (fun n =>
      (slowCalendarBlockLength B n : ℝ) * h n))
    (hgrowth : Tendsto (fun n => A (n + 1) * h n) atTop atTop) :
    ¬ Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      A (slowUnitStepCalendar B T)) atTop (nhds 0) := by
  intro hterminal
  let S : ℕ → ℕ := fun n => slowCalendarStart B (n + 1)
  let q : ℕ → ℝ := fun n => (S n : ℝ)⁻¹ * A (n + 1)
  have hSlim : Tendsto S atTop atTop := by
    exact (strictMono_slowCalendarStart B).tendsto_atTop.comp
      (tendsto_add_atTop_nat 1)
  have hq : Tendsto q atTop (nhds 0) := by
    have hcomp := hterminal.comp hSlim
    change Tendsto (fun n => (slowCalendarStart B (n + 1) : ℝ)⁻¹ *
      A (slowUnitStepCalendar B (slowCalendarStart B (n + 1))))
        atTop (nhds 0) at hcomp
    simpa only [q, S, slowUnitStepCalendar_slowCalendarStart] using hcomp
  let C : ℝ := ∑' n, (slowCalendarBlockLength B n : ℝ) * h n
  have hterm0 : ∀ n,
      0 ≤ (slowCalendarBlockLength B n : ℝ) * h n := fun n =>
    mul_nonneg (Nat.cast_nonneg _) (hhpos n).le
  have hprefix : ∀ n, (S n : ℝ) * h n ≤ C := by
    intro n
    calc
      (S n : ℝ) * h n =
          ∑ j ∈ Finset.range (n + 1),
            (slowCalendarBlockLength B j : ℝ) * h n := by
        rw [← Finset.sum_mul]
        simp only [S, sum_slowCalendarBlockLength]
      _ ≤ ∑ j ∈ Finset.range (n + 1),
            (slowCalendarBlockLength B j : ℝ) * h j := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left
        · exact hh (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        · exact Nat.cast_nonneg _
      _ ≤ C := hbill.sum_le_tsum _ (fun j _ => hterm0 j)
  have hSpos : ∀ n, 0 < S n := by
    intro n
    dsimp only [S]
    have hstrict := strictMono_slowCalendarStart B (Nat.zero_lt_succ n)
    simpa only [slowCalendarStart] using hstrict
  have hq0 : ∀ n, 0 ≤ q n := fun n => by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hA0 (n + 1))
  have hprodLe : ∀ n, A (n + 1) * h n ≤ q n * C := by
    intro n
    calc
      A (n + 1) * h n = q n * ((S n : ℝ) * h n) := by
        dsimp only [q]
        have hSneNat : S n ≠ 0 := Nat.ne_of_gt (hSpos n)
        have hSne : (S n : ℝ) ≠ 0 := by exact_mod_cast hSneNat
        field_simp [hSne]
      _ ≤ q n * C := mul_le_mul_of_nonneg_left (hprefix n) (hq0 n)
  have hprod0 : Tendsto (fun n => A (n + 1) * h n) atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact mul_nonneg (hA0 (n + 1)) (hhpos n).le
    · exact hprodLe
    · simpa only [zero_mul] using hq.mul_const C
  have hsmall : ∀ᶠ n in atTop, A (n + 1) * h n < 1 := by
    have h := hprod0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    simpa only [Set.mem_Iio] using h
  have hlarge : ∀ᶠ n in atTop, 1 ≤ A (n + 1) * h n :=
    tendsto_atTop.1 hgrowth 1
  obtain ⟨Ns, hNs⟩ := eventually_atTop.1 hsmall
  obtain ⟨Nl, hNl⟩ := eventually_atTop.1 hlarge
  let n := max Ns Nl
  exact (not_lt_of_ge (hNl n (le_max_right _ _)))
    (hNs n (le_max_left _ _))

/-- Eventual exactness makes an arbitrary nonnegative weighted root bill
summable.  No comparison between the weight and the rate of convergence is
needed in this branch. -/
theorem summable_mul_of_eventually_eq_zero
    (L f : ℕ → ℝ) (hf : ∀ᶠ n in atTop, f n = 0) :
    Summable (fun n => L n * f n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hf
  apply (summable_nat_add_iff N).mp
  have hzero : (fun n => L (n + N) * f (n + N)) = fun _ => 0 := by
    funext n
    rw [hN (n + N) (Nat.le_add_left N n), mul_zero]
  rw [hzero]
  exact summable_zero

/-- The scalar next-reference hold error is exactly zero when its on-profile
residual vanishes and all of its pure-deviation gains are nonpositive. -/
theorem finkNextReferenceHoldError_eq_zero_of_residual_eq_zero_of_gain_nonpos
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (W K : G.State → Payoff ι) {U : ℝ}
    (z : ℕ → G.finkDomain U) (n : ℕ)
    (hresidual : G.finkContinuationResidualVector
      (G.finkNextReferenceVector (β n / (1 - β n))
        (G.finkRelativeBias (β n) W (z n)) W K) (z n) = 0)
    (hgain : ∀ s who (d : G.Act who),
      G.finkContinuationGain
        (G.finkNextReferenceVector (β n / (1 - β n))
          (G.finkRelativeBias (β n) W (z n)) W K)
        (z n) s who d ≤ 0) :
    G.finkNextReferenceHoldError β W K z n = 0 := by
  unfold finkNextReferenceHoldError finkPositiveContinuationGainSum
  rw [hresidual, norm_zero, zero_add]
  apply Finset.sum_eq_zero
  intro p hp
  exact max_eq_right (hgain p.1 p.2.1 p.2.2)

/-- Exact-tail closure of the projective boundary branch.  Once the exposed
next reference has zero hold error on a tail, annealing may thin the already
summable corrected branch arbitrarily: the repeated root bill remains
eventually zero, so corrected calendar selectability follows with no dilation
or adjacent-growth assumption. -/
theorem isIndexedFinkCorrectedCalendarSelectable_of_eventuallyExactNextReference
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1))
    (M : ℝ) (hM : 0 ≤ M) {U : ℝ} (z : ℕ → G.finkDomain U)
    (W K : G.State → Payoff ι) (q : ℕ → ℝ)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hq : Tendsto q atTop (nhds 0))
    (hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      (G.finkRootCorrection β W K z) z n))
    (hexact : ∀ᶠ n in atTop,
      G.finkNextReferenceHoldError β W K z n = 0) :
    G.IsIndexedFinkCorrectedCalendarSelectable β M z W
      (G.finkRootCorrection β W K z) q := by
  let R : ℕ → G.State → Payoff ι := G.finkRootCorrection β W K z
  let aux : ℕ → ℝ := G.finkNextReferenceHoldError β W K z
  have haux0 : ∀ n, 0 ≤ aux n := by
    intro n
    unfold aux finkNextReferenceHoldError finkPositiveContinuationGainSum
    exact add_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun p hp => le_max_right _ _)
  have haux : Summable aux := by
    simpa only [one_mul] using
      (summable_mul_of_eventually_eq_zero (fun _ => (1 : ℝ)) aux (by
        simpa only [aux] using hexact))
  obtain ⟨θ, B, hκ, hterminal, hswitch, hfast',
      hfastTotal, haux', hauxTotal⟩ :=
    G.exists_finkRelativeAnnealingCalendar_preservingErrors
      β M z W R aux hM (fun n => (hβpos n).le) hβ1 hβlim
      (by simpa only [R] using hfast) haux0 haux
  have hθlim : Tendsto θ atTop atTop := by
    have hstart := (strictMono_slowCalendarStart B).tendsto_atTop
    have hcomp := hκ.comp hstart
    simpa only [Function.comp_def,
      slowUnitStepCalendar_slowCalendarStart] using hcomp
  have hexactθ : ∀ᶠ n in atTop,
      G.finkNextReferenceHoldError β W K z (θ n) = 0 :=
    hθlim.eventually hexact
  have hbill : Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      (((1 - β (θ n)) / β (θ n) +
          ‖G.finkValue (z (θ n)) - W‖) *
        G.finkNextReferenceHoldError β W K z (θ n))) := by
    apply summable_mul_of_eventually_eq_zero
    filter_upwards [hexactθ] with n hn
    rw [hn, mul_zero]
  apply G.isIndexedFinkCorrectedCalendarSelectable_of_oneSummableRootBillBranch
    β hβpos hβ1 hβlim M z W K q hV hq θ B hκ hterminal hswitch
  · simpa only [R] using hfast'
  · exact hbill

end StochasticGame
end GameTheory
