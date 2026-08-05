/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Math.Probability.SublinearLedger

/-!
# Moving endpoint transport: occupation evidence and the exact alternative

For a sequence of state laws and a fixed real target, cumulative endpoint
transport either is asymptotically sublinear, or some fixed state is occupied
at non-sublinear rate with strictly positive displacement in one fixed
orientation.  `OrientedOccupation` packages the second leaf, and
`Alternative` states the exact dichotomy.

This is a statement about `PMF` state laws only: no game, player, strategy or
Bellman datum enters it.  The prescribed analytic calendar that supplies such
a law lives with the stochastic-game development.
-/

noncomputable section

namespace Math
namespace Probability
namespace MovingEndpointOccupationEvidence

open Filter Set

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
  rw [isAsymptoticallySublinear_iff_tendsto] at hnot
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
  rw [isAsymptoticallySublinear_iff_tendsto]
  rw [isAsymptoticallySublinear_iff_tendsto] at hbudget
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

end MovingEndpointOccupationEvidence
end Probability
end Math
