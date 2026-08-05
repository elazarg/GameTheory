/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticStationaryClass
import Math.Probability.HarmonicClosedClass
import Math.Probability.HittingTimePotential
import Math.Probability.StationaryCommunicatingClass

/-!
# Pole-cleared centered Poisson equations for analytic finite kernels

A pole-cleared stationary weight gives an analytic centered forcing without
dividing by its normalizing power.  If the corresponding gauge-fixed Poisson
system is solvable on a punctured neighborhood, the analytic linear-system
selector clears one further pole and produces an analytic potential.

The resulting equation has one explicit total power.  A standard Poisson
telescope then bounds every finite Cesàro error by the oscillation of that
potential divided by the same power.  Periodicity causes no correction:
the argument uses Cesàro sums and an exact one-step coboundary identity, not
convergence of the unaveraged kernel powers.
-/

noncomputable section

namespace Math
namespace Probability

open Filter Finset Set
open Math.LinearAlgebra

variable {S : Type*}

/-- Gauge-fixed Poisson matrix.  The state rows encode `u - K u`; the final
row fixes the potential at `anchor` to zero. -/
def stationaryPoissonMatrix [DecidableEq S]
    (kernel : S → PMF S) (anchor : S) :
    Matrix (Sum S Unit) S ℝ
  | Sum.inl source, destination =>
      (if source = destination then 1 else 0) -
        (kernel source destination).toReal
  | Sum.inr _, destination =>
      if destination = anchor then 1 else 0

/-- Analytic centered forcing formed before dividing a pole-cleared
stationary weight by its mass. -/
def scaledStationaryCenteredCharge [Fintype S]
    (weight : S → ℝ) (observable : S → ℝ) (state : S) : ℝ :=
  (∑ source, weight source) * observable state -
    ∑ source, weight source * observable source

/-- Add the zero gauge coordinate to a centered Poisson right-hand side. -/
def stationaryPoissonRhs
    (charge : S → ℝ) : Sum S Unit → ℝ
  | Sum.inl state => charge state
  | Sum.inr _ => 0

/-- The state rows of the gauge-fixed matrix are the one-step Poisson
operator. -/
theorem stationaryPoissonMatrix_mulVec_inl
    [Fintype S] [DecidableEq S]
    (kernel : S → PMF S) (anchor : S)
    (potential : S → ℝ) (state : S) :
    Matrix.mulVec (stationaryPoissonMatrix kernel anchor)
        potential (Sum.inl state) =
      potential state - expect (kernel state) potential := by
  classical
  rw [Matrix.mulVec, dotProduct, expect_eq_sum]
  simp only [stationaryPoissonMatrix]
  calc
    (∑ destination,
        ((if state = destination then 1 else 0) -
            (kernel state destination).toReal) *
          potential destination) =
        (∑ destination,
          (if state = destination then 1 else 0) *
            potential destination) -
          ∑ destination,
            (kernel state destination).toReal *
              potential destination := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro destination _
      ring
    _ =
        potential state -
          ∑ destination,
            (kernel state destination).toReal *
              potential destination := by
      simp

/-- The final matrix row is the gauge value at the anchor. -/
theorem stationaryPoissonMatrix_mulVec_inr
    [Fintype S] [DecidableEq S]
    (kernel : S → PMF S) (anchor : S)
    (potential : S → ℝ) :
    Matrix.mulVec (stationaryPoissonMatrix kernel anchor)
        potential (Sum.inr PUnit.unit) =
      potential anchor := by
  classical
  rw [Matrix.mulVec, dotProduct]
  simp [stationaryPoissonMatrix]

/-- On a finite communicating kernel, centering by any normalized stationary
weight makes the gauge-fixed Poisson system solvable. -/
theorem exists_gaugeFixed_centeredPoisson_of_communicates
    [Fintype S] [DecidableEq S]
    (kernel : S → PMF S) (weight observable : S → ℝ)
    (anchor : S)
    (hweight : IsNormalizedStationaryWeight kernel weight)
    (hcommunicates :
      ∀ source destination,
        PMFReachable kernel source destination) :
    ∃ potential : S → ℝ,
      Matrix.mulVec
          (stationaryPoissonMatrix kernel anchor) potential =
        stationaryPoissonRhs
          (scaledStationaryCenteredCharge weight observable) := by
  letI : Nonempty S := ⟨anchor⟩
  let C : ReachableClosedClass kernel anchor := {
    states := Finset.univ
    states_nonempty := Finset.univ_nonempty
    closed := by
      intro source _ destination _
      exact Finset.mem_univ destination
    communicates := by
      intro left _ right _
      exact hcommunicates left right
    entry := anchor
    entry_mem := Finset.mem_univ anchor
    reachable_entry := Relation.ReflTransGen.refl
  }
  obtain ⟨harmonic, rawPotential, hharmonic,
      hdecomposition, _⟩ :=
    Math.MeanErgodic.exists_harmonic_add_poisson
      kernel observable
  have hharmonicConstant :
      ∀ state, harmonic state = harmonic anchor := by
    intro state
    exact C.harmonic_eq_on_class harmonic
      (fun current _ => (hharmonic current).symm)
      (Finset.mem_univ state) (Finset.mem_univ anchor)
  have hweightedPoisson :
      (∑ state,
          weight state *
            expect (kernel state) rawPotential) =
        ∑ state, weight state * rawPotential state :=
    stationary_expectation kernel weight hweight.2.1 rawPotential
  have hmean :
      (∑ state, weight state * observable state) =
        harmonic anchor := by
    calc
      (∑ state, weight state * observable state) =
          ∑ state,
            weight state *
              (harmonic state +
                (expect (kernel state) rawPotential -
                  rawPotential state)) := by
        apply Finset.sum_congr rfl
        intro state _
        rw [hdecomposition state]
      _ =
          (∑ state, weight state * harmonic state) +
            ((∑ state,
                weight state *
                  expect (kernel state) rawPotential) -
              ∑ state,
                weight state * rawPotential state) := by
        rw [← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro state _
        ring
      _ = ∑ state, weight state * harmonic state := by
        rw [hweightedPoisson, sub_self, add_zero]
      _ = ∑ state, weight state * harmonic anchor := by
        apply Finset.sum_congr rfl
        intro state _
        rw [hharmonicConstant state]
      _ = harmonic anchor := by
        rw [← Finset.sum_mul, hweight.2.2, one_mul]
  let potential : S → ℝ :=
    fun state => -rawPotential state + rawPotential anchor
  refine ⟨potential, ?_⟩
  funext row
  cases row with
  | inl state =>
      rw [stationaryPoissonMatrix_mulVec_inl]
      change
        potential state - expect (kernel state) potential =
          scaledStationaryCenteredCharge weight observable state
      rw [scaledStationaryCenteredCharge, hweight.2.2, one_mul,
        hmean]
      change
        (-rawPotential state + rawPotential anchor) -
            expect (kernel state)
              (fun next =>
                -rawPotential next + rawPotential anchor) =
          observable state - harmonic anchor
      have hneg :
          expect (kernel state) (fun next => -rawPotential next) =
            -expect (kernel state) rawPotential := by
        rw [expect_eq_sum, expect_eq_sum,
          ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro next _
        ring
      rw [expect_add, hneg, expect_const]
      calc
        -rawPotential state + rawPotential anchor -
              (-expect (kernel state) rawPotential +
                rawPotential anchor) =
            expect (kernel state) rawPotential -
              rawPotential state := by ring
        _ = observable state - harmonic state := by
          linarith [hdecomposition state]
        _ = observable state - harmonic anchor := by
          rw [hharmonicConstant state]
  | inr index =>
      cases index
      rw [stationaryPoissonMatrix_mulVec_inr]
      simp [potential, stationaryPoissonRhs]

/-- Pole-cleared analytic data for a centered, gauge-fixed Poisson
equation. -/
structure PoleClearedAnalyticStationaryPoisson
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (x₀ : ℝ)
    (stationary :
      PoleClearedAnalyticStationaryWeight kernel x₀)
    (observable : S → ℝ) (anchor : S) where
  additionalPoleOrder : ℕ
  scaledPotential : ℝ → S → ℝ
  analytic_scaledPotential : AnalyticAt ℝ scaledPotential x₀
  eventually_equation :
    ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
      (∀ state,
        scaledPotential x state -
            expect (kernel x state) (scaledPotential x) =
          (x - x₀) ^ additionalPoleOrder *
            scaledStationaryCenteredCharge
              (stationary.scaledWeight x) observable state) ∧
      scaledPotential x anchor = 0

namespace PoleClearedAnalyticStationaryPoisson

variable [Fintype S] [DecidableEq S]
  {kernel : ℝ → S → PMF S} {x₀ : ℝ}
  {stationary :
    PoleClearedAnalyticStationaryWeight kernel x₀}
  {observable : S → ℝ} {anchor : S}

/-- Total power appearing after both the stationary normalization pole and
the Poisson-solver pole are cleared. -/
def totalPoleOrder
    (data :
      PoleClearedAnalyticStationaryPoisson
        kernel x₀ stationary observable anchor) : ℕ :=
  stationary.poleOrder + data.additionalPoleOrder

/-- Relative to the selected normalized stationary quotient, the analytic
potential solves the centered Poisson equation multiplied by the total
clearing power. -/
theorem eventually_centered_equation
    (data :
      PoleClearedAnalyticStationaryPoisson
        kernel x₀ stationary observable anchor) :
    ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
      ∀ state,
        data.scaledPotential x state -
            expect (kernel x state) (data.scaledPotential x) =
          (x - x₀) ^ data.totalPoleOrder *
            (observable state -
              ∑ source,
                (((x - x₀) ^ stationary.poleOrder)⁻¹ *
                    stationary.scaledWeight x source) *
                  observable source) := by
  filter_upwards [data.eventually_equation,
    stationary.eventually_properties,
    self_mem_nhdsWithin] with x hequation hstationary hxx₀
  intro state
  rw [hequation.1 state]
  have hpower :
      (x - x₀) ^ stationary.poleOrder ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hxx₀.ne')
  rw [scaledStationaryCenteredCharge, hstationary.2.2.1]
  have hmean :
      (∑ source,
          (((x - x₀) ^ stationary.poleOrder)⁻¹ *
              stationary.scaledWeight x source) *
            observable source) =
        ((x - x₀) ^ stationary.poleOrder)⁻¹ *
          ∑ source,
            stationary.scaledWeight x source *
              observable source := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [hmean]
  simp only [totalPoleOrder, pow_add]
  let stationaryPower :=
    (x - x₀) ^ stationary.poleOrder
  let poissonPower :=
    (x - x₀) ^ data.additionalPoleOrder
  change
    poissonPower *
        (stationaryPower * observable state -
          ∑ source,
            stationary.scaledWeight x source * observable source) =
      stationaryPower * poissonPower *
        (observable state -
          stationaryPower⁻¹ *
            ∑ source,
              stationary.scaledWeight x source * observable source)
  field_simp [stationaryPower, hpower]

/-- Finite Cesàro numerator of an observable centered at a scalar mean. -/
def centeredIterSum
    (kernel : S → PMF S) (observable : S → ℝ)
    (mean : ℝ) (initial : S) (horizon : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    expect (Math.PMFIter.iter kernel time initial)
      (fun state => observable state - mean)

omit [DecidableEq S] in
/-- An exact scaled Poisson equation bounds every finite centered Cesàro
numerator by twice the potential norm.  No aperiodicity is used. -/
theorem scale_mul_abs_centeredIterSum_le
    [Finite S]
    (kernel : S → PMF S) (observable : S → ℝ)
    (mean scale : ℝ) (potential : S → ℝ)
    (hscale : 0 ≤ scale)
    (hequation :
      ∀ state,
        potential state - expect (kernel state) potential =
          scale * (observable state - mean))
    (initial : S) (horizon : ℕ) :
    scale *
        |centeredIterSum
          kernel observable mean initial horizon| ≤
      2 * ‖potential‖ := by
  let charge : S → ℝ :=
    fun state => scale * (observable state - mean)
  have htelescope :=
    poissonPotential_eq_sum_expect_add_expect_iter
      (kernel := kernel) (potential := potential)
      (charge := charge) hequation horizon initial
  have hsumCharge :
      (∑ time ∈ Finset.range horizon,
          expect (Math.PMFIter.iter kernel time initial) charge) =
        scale *
          centeredIterSum
            kernel observable mean initial horizon := by
    rw [centeredIterSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro time _
    rw [expect_const_mul]
  have hscaledSum :
      scale *
          centeredIterSum
            kernel observable mean initial horizon =
        potential initial -
          expect (Math.PMFIter.iter kernel horizon initial)
            potential := by
    rw [← hsumCharge]
    linarith
  have hinitial :
      |potential initial| ≤ ‖potential‖ := by
    simpa [Real.norm_eq_abs] using
      norm_le_pi_norm potential initial
  have htail :
      |expect (Math.PMFIter.iter kernel horizon initial)
          potential| ≤ ‖potential‖ := by
    calc
      |expect (Math.PMFIter.iter kernel horizon initial)
          potential| ≤
          expect (Math.PMFIter.iter kernel horizon initial)
            (fun state => |potential state|) :=
        abs_expect_le_expect_abs _ _
      _ ≤
          expect (Math.PMFIter.iter kernel horizon initial)
            (fun _ => ‖potential‖) := by
        apply expect_mono
        intro state
        simpa [Real.norm_eq_abs] using
          norm_le_pi_norm potential state
      _ = ‖potential‖ := by rw [expect_const]
  calc
    scale *
        |centeredIterSum
          kernel observable mean initial horizon| =
        |scale *
          centeredIterSum
            kernel observable mean initial horizon| := by
      rw [abs_mul, abs_of_nonneg hscale]
    _ =
        |potential initial -
          expect (Math.PMFIter.iter kernel horizon initial)
            potential| := by
      rw [hscaledSum]
    _ ≤
        |potential initial| +
          |expect (Math.PMFIter.iter kernel horizon initial)
            potential| := abs_sub _ _
    _ ≤ 2 * ‖potential‖ := by linarith

/-- The analytic pole-cleared potential is uniformly bounded near the
endpoint.  Hence one constant and the single total pole order control every
initial state and every finite horizon. -/
theorem exists_eventual_uniform_power_cesaroBound
    (data :
      PoleClearedAnalyticStationaryPoisson
        kernel x₀ stationary observable anchor) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
        ∀ initial horizon,
          (x - x₀) ^ data.totalPoleOrder *
              |centeredIterSum
                (kernel x) observable
                (∑ source,
                  (((x - x₀) ^ stationary.poleOrder)⁻¹ *
                      stationary.scaledWeight x source) *
                    observable source)
                initial horizon| ≤
            constant := by
  let normBound : ℝ := ‖data.scaledPotential x₀‖ + 1
  let constant : ℝ := 2 * normBound
  have hnormBoundPos : 0 < normBound := by
    dsimp only [normBound]
    linarith [norm_nonneg (data.scaledPotential x₀)]
  have hconstantPos : 0 < constant := by
    dsimp only [constant]
    positivity
  have hnorm :
      ∀ᶠ x in nhds x₀,
        ‖data.scaledPotential x‖ < normBound := by
    exact
      data.analytic_scaledPotential.continuousAt.norm.tendsto
        |>.eventually_lt_const
          (by
            dsimp only [normBound]
            linarith)
  refine ⟨constant, hconstantPos, ?_⟩
  filter_upwards [data.eventually_centered_equation,
    hnorm.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hequation hnormAt hxx₀
  intro initial horizon
  have hscale :
      0 ≤ (x - x₀) ^ data.totalPoleOrder :=
    (pow_pos (sub_pos.mpr hxx₀) _).le
  have hbound :=
    scale_mul_abs_centeredIterSum_le
      (kernel x) observable
      (∑ source,
        (((x - x₀) ^ stationary.poleOrder)⁻¹ *
            stationary.scaledWeight x source) *
          observable source)
      ((x - x₀) ^ data.totalPoleOrder)
      (data.scaledPotential x) hscale hequation
      initial horizon
  exact hbound.trans (by
    dsimp only [constant]
    exact mul_lt_mul_of_pos_left hnormAt (by positivity) |>.le)

end PoleClearedAnalyticStationaryPoisson

/-- A pole-cleared stationary selector and eventual solvability of its
analytic centered Poisson system produce a pole-cleared analytic
potential. -/
theorem exists_poleClearedAnalyticStationaryPoisson
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) {x₀ : ℝ}
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun x => (kernel x source destination).toReal) x₀)
    (stationary :
      PoleClearedAnalyticStationaryWeight kernel x₀)
    (observable : S → ℝ) (anchor : S)
    (hsolvable :
      ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
        ∃ potential : S → ℝ,
          Matrix.mulVec
              (stationaryPoissonMatrix (kernel x) anchor)
              potential =
            stationaryPoissonRhs
              (scaledStationaryCenteredCharge
                (stationary.scaledWeight x) observable)) :
    Nonempty
      (PoleClearedAnalyticStationaryPoisson
        kernel x₀ stationary observable anchor) := by
  classical
  let A : ℝ → Matrix (Sum S Unit) S ℝ :=
    fun x => stationaryPoissonMatrix (kernel x) anchor
  let b : ℝ → Sum S Unit → ℝ :=
    fun x =>
      stationaryPoissonRhs
        (scaledStationaryCenteredCharge
          (stationary.scaledWeight x) observable)
  have hA :
      ∀ row destination,
        AnalyticAt ℝ (fun x => A x row destination) x₀ := by
    intro row destination
    cases row with
    | inl source =>
        change
          AnalyticAt ℝ
            (fun x =>
              (if source = destination then 1 else 0) -
                (kernel x source destination).toReal) x₀
        exact analyticAt_const.sub (hanalytic source destination)
    | inr index =>
        cases index
        exact analyticAt_const
  have hscaledCoordinate :
      ∀ state,
        AnalyticAt ℝ
          (fun x => stationary.scaledWeight x state) x₀ :=
    analyticAt_pi_iff.mp stationary.analytic_scaledWeight
  have hmassAnalytic :
      AnalyticAt ℝ
        (fun x => ∑ source, stationary.scaledWeight x source) x₀ := by
    apply Finset.univ.analyticAt_fun_sum
    intro source _
    exact hscaledCoordinate source
  have hmeanAnalytic :
      AnalyticAt ℝ
        (fun x =>
          ∑ source,
            stationary.scaledWeight x source *
              observable source) x₀ := by
    apply Finset.univ.analyticAt_fun_sum
    intro source _
    exact (hscaledCoordinate source).mul analyticAt_const
  have hb :
      ∀ row, AnalyticAt ℝ (fun x => b x row) x₀ := by
    intro row
    cases row with
    | inl state =>
        exact
          (hmassAnalytic.mul analyticAt_const).sub
            hmeanAnalytic
    | inr index =>
        cases index
        exact analyticAt_const
  obtain ⟨additionalPoleOrder, scaledPotential,
      hanalyticPotential, hequation⟩ :=
    exists_analytic_scaled_eventual_linearSolution
      A b hA hb (by simpa [A, b] using hsolvable)
  refine ⟨{
    additionalPoleOrder := additionalPoleOrder
    scaledPotential := scaledPotential
    analytic_scaledPotential := hanalyticPotential
    eventually_equation := ?_
  }⟩
  filter_upwards [hequation] with x hx
  constructor
  · intro state
    have hrow := congrFun hx (Sum.inl state)
    change
      Matrix.mulVec
          (stationaryPoissonMatrix (kernel x) anchor)
          (scaledPotential x) (Sum.inl state) =
        (x - x₀) ^ additionalPoleOrder *
          scaledStationaryCenteredCharge
            (stationary.scaledWeight x) observable state at hrow
    simpa [stationaryPoissonMatrix_mulVec_inl] using hrow
  · have hrow := congrFun hx (Sum.inr PUnit.unit)
    dsimp only [A, b] at hrow
    simpa [stationaryPoissonMatrix_mulVec_inr,
      stationaryPoissonRhs] using hrow

/-- For an eventually communicating finite kernel, the centered Poisson
solvability premise is automatic.  This is the fixed punctured-support
closed-class specialization: the type `S` is the class itself. -/
theorem exists_poleClearedAnalyticStationaryPoisson_of_communicates
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) {x₀ : ℝ}
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun x => (kernel x source destination).toReal) x₀)
    (stationary :
      PoleClearedAnalyticStationaryWeight kernel x₀)
    (observable : S → ℝ) (anchor : S)
    (hcommunicates :
      ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
        ∀ source destination,
          PMFReachable (kernel x) source destination) :
    Nonempty
      (PoleClearedAnalyticStationaryPoisson
        kernel x₀ stationary observable anchor) := by
  apply exists_poleClearedAnalyticStationaryPoisson
    kernel hanalytic stationary observable anchor
  filter_upwards [stationary.eventually_properties,
    hcommunicates] with x hstationary hcommunicatesAt
  let normalized : S → ℝ :=
    supportCramerVector
      (normalizedFarkasMatrix
        (stationaryBalance (kernel x)) stationaryMass)
      normalizedFarkasRhs stationary.support
  obtain ⟨potential, hpotential⟩ :=
    exists_gaugeFixed_centeredPoisson_of_communicates
      (kernel x) normalized observable anchor
      hstationary.2.2.2.1 hcommunicatesAt
  let scale := (x - x₀) ^ stationary.poleOrder
  refine ⟨scale • potential, ?_⟩
  have hcharge :
      ∀ state,
        scaledStationaryCenteredCharge
            (stationary.scaledWeight x) observable state =
          scale *
            scaledStationaryCenteredCharge
              normalized observable state := by
    intro state
    rw [← hstationary.2.2.2.2]
    simp only [scaledStationaryCenteredCharge,
      Pi.smul_apply, smul_eq_mul]
    have hweighted :
        (∑ source,
            (x - x₀) ^ stationary.poleOrder *
                normalized source *
              observable source) =
          scale *
            ∑ source, normalized source * observable source := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source _
      dsimp only [scale]
      ring
    have hmassWeighted :
        (∑ source,
            (x - x₀) ^ stationary.poleOrder *
              normalized source) =
          scale * ∑ source, normalized source := by
      rw [Finset.mul_sum]
    rw [hweighted, hmassWeighted]
    dsimp only [scale]
    ring
  rw [Matrix.mulVec_smul, hpotential]
  funext row
  cases row with
  | inl state =>
      change
        scale *
            scaledStationaryCenteredCharge
              normalized observable state =
          scaledStationaryCenteredCharge
            (stationary.scaledWeight x) observable state
      exact (hcharge state).symm
  | inr index =>
      cases index
      simp [stationaryPoissonRhs]

end Probability
end Math
