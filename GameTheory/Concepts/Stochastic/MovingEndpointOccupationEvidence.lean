/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FiniteBiasPrescribedCalendarPayoffBoundary

/-!
# Moving endpoint transport: a fixed occupation witness

For an arbitrary sequence of state laws, cumulative transport of a fixed
endpoint target is a finite linear combination of state occupation masses.
Consequently there is an exact first reduction:

* if every state with nonzero endpoint displacement has sublinear
  occupation, then the absolute endpoint transport is sublinear;
* otherwise one fixed state and one fixed orientation have positive
  endpoint displacement and non-sublinear cumulative occupation.

The result is then instantiated with the actual state marginals of the
prescribed shifted universal Fink calendar.  It is valid for the moving,
time-inhomogeneous analytic calendar; no frozen-kernel class is inserted.

The occupation witness is deliberately weaker than a recursive child.
It does not assert that the selected state belongs to a legally closed
continuation class, preserves the whole payoff target, or decreases rank.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MovingEndpointOccupationEvidence

open Filter Math Math.OnlineLearning Math.Probability Set

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- Cumulative mass assigned to one state by a sequence of state laws. -/
def cumulativeOccupation
    (law : ℕ → PMF State) (state : State) (horizon : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range horizon, (law stage state).toReal

omit [Fintype State] [DecidableEq State] in
/-- Cumulative state occupation is nonnegative. -/
theorem cumulativeOccupation_nonneg
    (law : ℕ → PMF State) (state : State) (horizon : ℕ) :
    0 ≤ cumulativeOccupation law state horizon := by
  unfold cumulativeOccupation
  exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- Cumulative expected displacement of a fixed target from its entry
value under a sequence of state laws. -/
def cumulativeEndpointTransport
    (law : ℕ → PMF State)
    (target : State → ℝ) (entry : State) (horizon : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range horizon,
    expect (law stage) (fun state => target state - target entry)

/-- Endpoint displacement with a fixed statistical orientation. -/
def orientedDisplacement
    (target : State → ℝ) (entry : State)
    (forward : Bool) (state : State) : ℝ :=
  if forward then target state - target entry
  else target entry - target state

/-- Cumulative charge carried by one fixed oriented state. -/
def cumulativeOrientedOccupationCharge
    (law : ℕ → PMF State)
    (target : State → ℝ) (entry : State)
    (forward : Bool) (state : State) (horizon : ℕ) : ℝ :=
  orientedDisplacement target entry forward state *
    cumulativeOccupation law state horizon

/-- Failure of the transport account exposes a fixed state that is occupied
at non-sublinear rate and has strictly positive displacement in one fixed
orientation. -/
structure OrientedOccupation
    (law : ℕ → PMF State)
    (target : State → ℝ) (entry : State) where
  state : State
  forward : Bool
  displacement_pos :
    0 < orientedDisplacement target entry forward state
  occupation_not_sublinear :
    ¬IsAsymptoticallySublinear
      (cumulativeOccupation law state)

namespace OrientedOccupation

omit [Fintype State] [DecidableEq State] in
/-- The selected state is distinct from the entry state. -/
theorem state_ne_entry
    {law : ℕ → PMF State}
    {target : State → ℝ} {entry : State}
    (evidence : OrientedOccupation law target entry) :
    evidence.state ≠ entry := by
  intro hstate
  have hpositive := evidence.displacement_pos
  rw [hstate] at hpositive
  simp [orientedDisplacement] at hpositive

omit [Fintype State] [DecidableEq State] in
/-- The fixed oriented charge carried by the selected state is itself
non-sublinear. -/
theorem charge_not_sublinear
    {law : ℕ → PMF State}
    {target : State → ℝ} {entry : State}
    (evidence : OrientedOccupation law target entry) :
    ¬IsAsymptoticallySublinear fun horizon =>
      cumulativeOrientedOccupationCharge
        law target entry evidence.forward evidence.state horizon := by
  intro hcharge
  apply evidence.occupation_not_sublinear
  have hscaled :=
    hcharge.const_mul
      (orientedDisplacement
        target entry evidence.forward evidence.state)⁻¹
  unfold cumulativeOrientedOccupationCharge at hscaled
  convert hscaled using 1
  funext horizon
  rw [← mul_assoc,
    inv_mul_cancel₀ evidence.displacement_pos.ne', one_mul]

omit [Fintype State] [DecidableEq State] in
/-- Non-sublinear nonnegative occupation has a positive linear average
along arbitrarily late horizons. -/
theorem exists_frequently_average_ge
    {law : ℕ → PMF State}
    {target : State → ℝ} {entry : State}
    (evidence : OrientedOccupation law target entry) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ᶠ horizon : ℕ in atTop,
        ε ≤ (horizon : ℝ)⁻¹ *
          cumulativeOccupation law evidence.state horizon := by
  have hnot := evidence.occupation_not_sublinear
  change
    ¬Tendsto
      (fun horizon : ℕ =>
        (horizon : ℝ)⁻¹ *
          cumulativeOccupation law evidence.state horizon)
      atTop (nhds 0) at hnot
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfailure⟩ := hnot
  refine ⟨ε, hε, frequently_atTop.2 ?_⟩
  intro threshold
  obtain ⟨horizon, hthreshold, hfar⟩ :=
    hfailure threshold
  refine ⟨horizon, hthreshold, ?_⟩
  have haverage :
      0 ≤ (horizon : ℝ)⁻¹ *
        cumulativeOccupation law evidence.state horizon :=
    mul_nonneg
      (inv_nonneg.mpr (Nat.cast_nonneg horizon))
      (cumulativeOccupation_nonneg
        law evidence.state horizon)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg haverage] at hfar
  exact hfar

end OrientedOccupation

/-- The exact finite-state alternatives for moving endpoint transport. -/
inductive Alternative
    (law : ℕ → PMF State)
    (target : State → ℝ) (entry : State)
  | sublinearTransport
      (account :
        IsAsymptoticallySublinear fun horizon =>
          |cumulativeEndpointTransport law target entry horizon|)
  | orientedOccupation
      (evidence : OrientedOccupation law target entry)

private theorem sublinear_abs
    {budget : ℕ → ℝ}
    (hbudget : IsAsymptoticallySublinear budget) :
    IsAsymptoticallySublinear fun horizon => |budget horizon| := by
  change
    Tendsto
      (fun horizon : ℕ => (horizon : ℝ)⁻¹ * |budget horizon|)
      atTop (nhds 0)
  change
    Tendsto
      (fun horizon : ℕ => (horizon : ℝ)⁻¹ * budget horizon)
      atTop (nhds 0) at hbudget
  have habs := hbudget.abs
  simpa [abs_mul, abs_inv, abs_of_nonneg] using habs

private theorem sublinear_finset_sum
    {Index : Type*}
    (indices : Finset Index)
    (budget : Index → ℕ → ℝ)
    (hbudget :
      ∀ index ∈ indices,
        IsAsymptoticallySublinear (budget index)) :
    IsAsymptoticallySublinear fun horizon =>
      ∑ index ∈ indices, budget index horizon := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using IsAsymptoticallySublinear.const 0
  | @insert index indices index_not_mem inductionHypothesis =>
      simpa only [Finset.sum_insert index_not_mem] using
        (hbudget index (Finset.mem_insert_self index indices)).add
          (inductionHypothesis fun other other_mem =>
            hbudget other
              (Finset.mem_insert_of_mem other_mem))

omit [DecidableEq State] in
/-- Moving endpoint transport is the target-displacement pairing with
cumulative state occupation. -/
theorem cumulativeEndpointTransport_eq_sum_occupation
    (law : ℕ → PMF State)
    (target : State → ℝ) (entry : State) (horizon : ℕ) :
    cumulativeEndpointTransport law target entry horizon =
      ∑ state,
        (target state - target entry) *
          cumulativeOccupation law state horizon := by
  classical
  unfold cumulativeEndpointTransport cumulativeOccupation
  calc
    (∑ stage ∈ Finset.range horizon,
        expect (law stage)
          (fun state => target state - target entry)) =
        ∑ stage ∈ Finset.range horizon,
          ∑ state,
            (law stage state).toReal *
              (target state - target entry) := by
      apply Finset.sum_congr rfl
      intro stage _
      rw [expect_eq_sum]
    _ =
        ∑ state,
          ∑ stage ∈ Finset.range horizon,
            (law stage state).toReal *
              (target state - target entry) := by
      rw [Finset.sum_comm]
    _ =
        ∑ state,
          (target state - target entry) *
            ∑ stage ∈ Finset.range horizon,
              (law stage state).toReal := by
      apply Finset.sum_congr rfl
      intro state _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro stage _
      ring

omit [Fintype State] [DecidableEq State] in
/-- If every state with nonzero endpoint displacement has sublinear
occupation, then absolute moving endpoint transport is sublinear. -/
theorem sublinear_abs_transport_of_sublinear_occupation
    [Finite State]
    (law : ℕ → PMF State)
    (target : State → ℝ) (entry : State)
    (hoccupation :
      ∀ state, target state ≠ target entry →
        IsAsymptoticallySublinear
          (cumulativeOccupation law state)) :
    IsAsymptoticallySublinear fun horizon =>
      |cumulativeEndpointTransport law target entry horizon| := by
  letI := Fintype.ofFinite State
  have hterm :
      ∀ state,
        IsAsymptoticallySublinear fun horizon =>
          (target state - target entry) *
            cumulativeOccupation law state horizon := by
    intro state
    by_cases hsame : target state = target entry
    · simpa [hsame] using IsAsymptoticallySublinear.const 0
    · exact
        (hoccupation state hsame).const_mul
          (target state - target entry)
  have hsum :
      IsAsymptoticallySublinear fun horizon =>
        ∑ state,
          (target state - target entry) *
            cumulativeOccupation law state horizon := by
    simpa only [Finset.sum_const_zero] using
      sublinear_finset_sum Finset.univ
        (fun state horizon =>
          (target state - target entry) *
            cumulativeOccupation law state horizon)
        (fun state _ => hterm state)
  have habs := sublinear_abs hsum
  simpa only [cumulativeEndpointTransport_eq_sum_occupation] using habs

omit [Fintype State] [DecidableEq State] in
/-- Failure of sublinear absolute transport yields one fixed oriented
non-sublinear occupation witness. -/
theorem exists_orientedOccupation_of_not_sublinear
    [Finite State]
    (law : ℕ → PMF State)
    (target : State → ℝ) (entry : State)
    (failure :
      ¬IsAsymptoticallySublinear fun horizon =>
        |cumulativeEndpointTransport law target entry horizon|) :
    Nonempty (OrientedOccupation law target entry) := by
  letI := Fintype.ofFinite State
  have hexists :
      ∃ state,
        target state ≠ target entry ∧
          ¬IsAsymptoticallySublinear
            (cumulativeOccupation law state) := by
    by_contra hnot
    have hoccupation :
        ∀ state, target state ≠ target entry →
          IsAsymptoticallySublinear
            (cumulativeOccupation law state) := by
      intro state hstate
      by_contra hfailure
      exact (not_exists.mp hnot state) ⟨hstate, hfailure⟩
    exact failure
      (sublinear_abs_transport_of_sublinear_occupation
        law target entry hoccupation)
  obtain ⟨state, hstate, hoccupation⟩ := hexists
  by_cases hforward : target entry < target state
  · exact ⟨{
      state := state
      forward := true
      displacement_pos := by
        simpa [orientedDisplacement] using sub_pos.mpr hforward
      occupation_not_sublinear := hoccupation
    }⟩
  · have hreverse : target state < target entry :=
      lt_of_le_of_ne (not_lt.mp hforward) hstate
    exact ⟨{
      state := state
      forward := false
      displacement_pos := by
        simpa [orientedDisplacement] using sub_pos.mpr hreverse
      occupation_not_sublinear := hoccupation
    }⟩

omit [Fintype State] [DecidableEq State] in
/-- Every moving finite-state law has either a sublinear absolute endpoint
transport account or a fixed oriented occupation witness. -/
theorem exists_alternative
    [Finite State]
    (law : ℕ → PMF State)
    (target : State → ℝ) (entry : State) :
    Nonempty (Alternative law target entry) := by
  letI := Fintype.ofFinite State
  by_cases htransport :
      IsAsymptoticallySublinear fun horizon =>
        |cumulativeEndpointTransport law target entry horizon|
  · exact ⟨.sublinearTransport htransport⟩
  · exact ⟨.orientedOccupation
      (exists_orientedOccupation_of_not_sublinear
        law target entry htransport).some⟩

/-! ## The actual prescribed analytic calendar -/

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ who, Fintype (G.Act who)]
  [∀ who, DecidableEq (G.Act who)]

open AnalyticBellmanGerm AnalyticBellmanGerm.FiniteBiasSeed

/-- State marginal of prescribed play on the shifted universal Fink
calendar. -/
def prescribedCalendarStateLaw
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (stage : ℕ) : PMF G.State :=
  (G.histDist
      (prescribedPlayerOwnedFinkCalendarProfile
        germ startEpoch valid)
      entry stage).map Prod.snd

omit [DecidableEq G.State] in
/-- The generic moving-law transport is exactly the named prescribed
calendar endpoint-transport term. -/
theorem cumulativeEndpointTransport_prescribedCalendarStateLaw
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (horizon : ℕ) :
    cumulativeEndpointTransport
        (prescribedCalendarStateLaw
          germ entry startEpoch valid)
        (fun state => germ.endpointValue state who)
        entry horizon =
      expectedPrescribedCalendarEndpointTargetTransport
        germ who entry startEpoch valid horizon := by
  unfold cumulativeEndpointTransport
    prescribedCalendarStateLaw
    expectedPrescribedCalendarEndpointTargetTransport
    expectedHistoryValue
  apply Finset.sum_congr rfl
  intro stage _
  rw [expect_map]

omit [DecidableEq G.State] in
/-- Failure of the named prescribed-calendar transport boundary for one
player exposes a fixed state and fixed orientation whose actual cumulative
occupation under that same universal calendar is non-sublinear. -/
theorem exists_prescribed_orientedOccupation_of_not_sublinear
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (failure :
      ¬IsAsymptoticallySublinear fun horizon =>
        |expectedPrescribedCalendarEndpointTargetTransport
          germ who entry startEpoch valid horizon|) :
    Nonempty
      (OrientedOccupation
        (prescribedCalendarStateLaw
          germ entry startEpoch valid)
        (fun state => germ.endpointValue state who)
        entry) := by
  apply exists_orientedOccupation_of_not_sublinear
  simpa only [
    cumulativeEndpointTransport_prescribedCalendarStateLaw] using failure

omit [DecidableEq G.State] in
/-- Therefore failure of the all-player prescribed transport boundary
selects one player and one fixed oriented non-sublinear state occupation
witness on the exact calendar used by the finite-bias closure. -/
theorem exists_player_prescribed_orientedOccupation_of_not_boundary
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (failure :
      ¬HasSublinearPrescribedCalendarEndpointTargetTransport
        germ entry startEpoch valid) :
    ∃ who,
      Nonempty
        (OrientedOccupation
          (prescribedCalendarStateLaw
            germ entry startEpoch valid)
          (fun state => germ.endpointValue state who)
          entry) := by
  rw [HasSublinearPrescribedCalendarEndpointTargetTransport] at failure
  obtain ⟨who, hwho⟩ := not_forall.mp failure
  exact ⟨who,
    exists_prescribed_orientedOccupation_of_not_sublinear
      germ who entry startEpoch valid hwho⟩

end MovingEndpointOccupationEvidence
end StochasticGame
end GameTheory
