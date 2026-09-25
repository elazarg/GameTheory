/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.SelectiveStopping
import GameTheory.Math.Probability.Uniform

/-! # Finite regressions for information-fiber stopping bounds -/

noncomputable section

namespace GameTheory.Tests.SelectiveStopping

open GameTheory.Math.Probability

def law : PMF (Fin 3) := PMF.uniformOfFintype (Fin 3)

def stopped (state : Fin 3) : Bool := decide (state = 0 ∨ state = 1)

def information (state : Fin 3) : Fin 3 :=
  if state = 0 ∨ state = 1 then 0 else 1

def targetValue (state : Fin 3) : ℝ :=
  if state = 0 then 3 else if state = 1 then 0 else 1

def sourceValue (state : Fin 3) : ℝ :=
  if state = 0 then 1 else if state = 1 then 3 else 1

def margin : ℝ := 1 / 2

/-- The three-state stopping fixture integrates every observable. -/
theorem integrable (f : Fin 3 → ℝ) : PayoffIntegrable law f :=
  payoffIntegrable_of_finite law f

private theorem law_expect (f : Fin 3 → ℝ) (hf : PayoffIntegrable law f) :
    expect law f hf = (∑ state : Fin 3, f state) / 3 := by
  calc
    expect law f hf =
        expect law f (payoffIntegrable_of_finite law f) :=
      expect_proof_irrel law f _ _
    _ = _ := expect_uniformFin f

/-- Information values one and two have no reached stopped state. -/
theorem unsupported_stopped_fibers :
    ¬ (∃ state ∈ law.support,
        stopped state = true ∧ information state = (1 : Fin 3)) ∧
      ¬ (∃ state ∈ law.support,
        stopped state = true ∧ information state = (2 : Fin 3)) := by
  constructor <;> rintro ⟨state, _, hstopped, hinfo⟩ <;>
    fin_cases state <;> simp [stopped, information] at hstopped hinfo

/-- The sole reached stopping fiber balances a positive charge exactly. -/
theorem stopped_fiber_comparison (observed : Fin 3)
    (hobserved : observed ∈ (law.map information).support) :
    expect law ((information ⁻¹' {observed}).indicator
      (stoppingCharge stopped targetValue margin))
      (payoffIntegrable_indicator (information ⁻¹' {observed})
        (stoppingCharge_integrable law stopped targetValue margin
          (integrable targetValue))) ≤
    expect law ((information ⁻¹' {observed}).indicator sourceValue)
      (payoffIntegrable_indicator (information ⁻¹' {observed})
        (integrable sourceValue)) := by
  classical
  rw [law_expect, law_expect]
  fin_cases observed <;>
    norm_num [Fin.sum_univ_succ, information, stopped, stopIndicator,
      stoppingCharge, sourceValue, targetValue, margin, law] at *

theorem reached_stopped_fiber_comparison (observed : Fin 3)
    (hobserved : observed ∈ (law.map information).support) :
    let stoppedFiber : Set (Fin 3) :=
      {state | information state = observed ∧ stopped state = true}
    expect law (stoppedFiber.indicator
      (stoppingCharge stopped targetValue margin))
      (payoffIntegrable_indicator stoppedFiber
        (stoppingCharge_integrable law stopped targetValue margin
          (integrable targetValue))) ≤
    expect law (stoppedFiber.indicator sourceValue)
      (payoffIntegrable_indicator stoppedFiber
        (integrable sourceValue)) := by
  classical
  dsimp only
  rw [law_expect, law_expect]
  fin_cases observed <;>
    norm_num [Fin.sum_univ_succ, information, stopped, stopIndicator,
      stoppingCharge, sourceValue, targetValue, margin, law] at *

theorem outside_stopping_dominance :
    ∀ state ∈ law.support, stopped state = false →
      targetValue state ≤ sourceValue state := by
  intro state _ hstop
  fin_cases state
  all_goals simp_all [stopped, targetValue, sourceValue]

/-- State zero favors the stopped target even after its charge. -/
theorem pointwise_comparison_fails :
    ¬ ∀ state ∈ law.support, stopped state = true →
      targetValue state + margin ≤ sourceValue state := by
  intro h
  have hsupport : (0 : Fin 3) ∈ law.support := by
    simp [law]
  have hbound := h 0 hsupport (by decide)
  norm_num [targetValue, sourceValue, margin] at hbound

/-- A random stopping event with a positive margin satisfies the global
comparison despite failure of stopped-state pointwise dominance. -/
theorem randomized_positive_margin_bound :
    0 < margin ∧ 0 < ((law.map stopped).toOuterMeasure {true}).toReal ∧
      expect law targetValue (integrable targetValue) +
        margin * ((law.map stopped).toOuterMeasure {true}).toReal ≤
      expect law sourceValue (integrable sourceValue) := by
  refine ⟨by norm_num [margin], ?_, ?_⟩
  · rw [← expect_stopIndicator law stopped, law_expect]
    have hsum : (∑ state : Fin 3, stopIndicator stopped state) = 2 := by
      have hcard :
          (Finset.univ.filter (fun state : Fin 3 => state = 0 ∨ state = 1)).card =
            2 := by decide
      norm_num [Fin.sum_univ_succ, stopped, stopIndicator, hcard]
    rw [hsum]
    norm_num
  · exact stopping_information_fiber_bound_of_stopped law stopped information
      sourceValue targetValue margin (integrable sourceValue)
      (integrable targetValue) outside_stopping_dominance
      reached_stopped_fiber_comparison

private def gapEvent (state : Fin 2) : Bool := decide (state = 0)

private def gapSource (state : Fin 2) : ℝ := if state = 0 then -1 else 3

private def gapTarget (state : Fin 2) : ℝ := if state = 0 then 0 else 3

/-- A unit event discrepancy is attained on a half-mass event. -/
theorem event_gap_sharp :
    let pair := PMF.uniformOfFintype (Fin 2)
    let hs := payoffIntegrable_of_finite pair gapSource
    let ht := payoffIntegrable_of_finite pair gapTarget
    ((pair.map gapEvent).toOuterMeasure {true}).toReal = 1 / 2 ∧
      expect pair gapSource hs = 1 ∧ expect pair gapTarget ht = 3 / 2 ∧
      expect pair gapTarget ht ≤
        expect pair gapSource hs +
          ((pair.map gapEvent).toOuterMeasure {true}).toReal := by
  dsimp only
  have hmass : ((PMF.uniformOfFintype (Fin 2)).map gapEvent
      |>.toOuterMeasure {true}).toReal = 1 / 2 := by
    rw [← expect_stopIndicator (PMF.uniformOfFintype (Fin 2)) gapEvent,
      expect_uniformFin]
    norm_num [Fin.sum_univ_succ, gapEvent, stopIndicator]
  refine ⟨hmass, ?_, ?_, ?_⟩
  · rw [expect_uniformFin]
    norm_num [Fin.sum_univ_succ, gapSource]
  · rw [expect_uniformFin]
    norm_num [Fin.sum_univ_succ, gapTarget]
  · rw [expect_uniformFin, expect_uniformFin, hmass]
    norm_num [Fin.sum_univ_succ, gapSource, gapTarget]

private def states2 : PMF (Fin 2) := PMF.uniformOfFintype (Fin 2)

private def quit2 (state : Fin 2) : PMF ℝ :=
  PMF.pure (if state = 0 then 2 else 0)

private def proceed2 (_state : Fin 2) : PMF ℝ := PMF.pure 1

private def stop2 (state : Fin 2) : PMF Bool :=
  PMF.pure (decide (state = 0))

private def quitValue2 (state : Fin 2) : ℝ := if state = 0 then 2 else 0

private def selectedValue2 (state : Fin 2) : ℝ :=
  if state = 0 then 2 else 1

private theorem selectedLaw2 :
    (states2.bind fun state => (stop2 state).bind fun stops =>
      if stops then quit2 state else proceed2 state) =
      states2.map selectedValue2 := by
  calc
    _ = states2.bind (fun state => PMF.pure (selectedValue2 state)) := by
      apply bind_congr_on_support
      intro state _
      fin_cases state <;> simp [stop2, quit2, proceed2, selectedValue2]
    _ = states2.map selectedValue2 := PMF.bind_pure_comp _ _

private theorem expect_map_states2 (f : Fin 2 → ℝ)
    (hf : PayoffIntegrable (states2.map f) id) :
    expect (states2.map f) id hf = (∑ state : Fin 2, f state) / 2 := by
  have hsource : PayoffIntegrable states2 (id ∘ f) :=
    payoffIntegrable_of_finite states2 _
  calc
    expect (states2.map f) id hf = expect states2 (id ∘ f) hsource :=
      expect_map f states2 id hsource hf
    _ = _ := by
      simpa [states2, Function.comp_def] using
        (expect_uniformFin f)

/-- Unconditional quit and continuation means agree, but selecting quit at
the favorable state strictly improves the realized mean. -/
theorem unconditional_comparison_insufficient :
    let hquit := (payoffIntegrable_map_iff quitValue2 states2 id).2
      (payoffIntegrable_of_finite states2 (id ∘ quitValue2))
    let hproceed := (payoffIntegrable_map_iff (fun _ : Fin 2 => (1 : ℝ))
      states2 id).2
      (payoffIntegrable_of_finite states2 (id ∘ fun _ : Fin 2 => (1 : ℝ)))
    let hselected := (payoffIntegrable_map_iff selectedValue2 states2 id).2
      (payoffIntegrable_of_finite states2 (id ∘ selectedValue2))
    expect (states2.map quitValue2) id hquit =
      expect (states2.map fun _ : Fin 2 => (1 : ℝ)) id hproceed ∧
    expect (states2.map fun _ : Fin 2 => (1 : ℝ)) id hproceed <
      expect (states2.map selectedValue2) id hselected ∧
    (states2.bind fun state => (stop2 state).bind fun stops =>
      if stops then quit2 state else proceed2 state) =
      states2.map selectedValue2 := by
  dsimp only
  refine ⟨?_, ?_, selectedLaw2⟩
  · rw [expect_map_states2, expect_map_states2]
    norm_num [Fin.sum_univ_succ, quitValue2]
  · rw [expect_map_states2, expect_map_states2]
    norm_num [Fin.sum_univ_succ, selectedValue2]

/-- A negative event gap is retained exactly. -/
theorem negative_event_gap :
    let states := PMF.uniformOfFintype (Fin 2)
    let event : Set (Fin 2) := {0}
    let target := fun state : Fin 2 => if state = 0 then (-2 : ℝ) else 0
    let ht := payoffIntegrable_of_finite states target
    expect states target ht = -1 ∧
      expect states target ht ≤
        expect states (fun _ => 0) (payoffIntegrable_zero states) +
          (-2) * (states.toOuterMeasure event).toReal := by
  dsimp only
  constructor
  · rw [expect_uniformFin]
    norm_num [Fin.sum_univ_succ]
  · apply expect_le_add_event_gap
    · intro state _ hstate
      simp only [Set.mem_singleton_iff] at hstate
      simp [hstate]
    · intro state _ hstate
      simp only [Set.mem_singleton_iff] at hstate
      simp [hstate]

end GameTheory.Tests.SelectiveStopping
