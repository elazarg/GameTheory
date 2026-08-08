/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.InvisibleResponseCompatibility

/-!
# Oriented endpoint evidence need not be a profitable response

A signed incompatibility can select an actual forward transition and an
orientation with positive public coordinate drift even when every unoriented
quotient level is negative.  Thus the orientation is statistical data; it
does not reverse the operational action or prove a positive unilateral gain.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace InvisibleResponseCompatibilityCounterexample

open Filter Math Math.Probability Set Topology

abbrev State := Fin 3

abbrev Response := Fin 2

def baseline (_source : State) (_t : ℝ) (_destination : State) : ℝ :=
  1 / 3

def source (_response : Response) : State :=
  0

def endpointDifference (destination : State) : ℝ :=
  if destination = 0 then 1 / 6
  else if destination = 1 then -(1 / 6)
  else 0

def responseScale (response : Response) : ℝ :=
  response.val + 1

def perturbation (response : Response) (destination : State) : ℝ :=
  if destination = 1 then responseScale response
  else if destination = 2 then -responseScale response
  else 0

def forward (response : Response) (t : ℝ) (destination : State) : ℝ :=
  baseline (source response) t destination +
    endpointDifference destination + t * perturbation response destination

def endpointValue (destination : State) : ℝ :=
  if destination = 2 then 1 else 0

def quotient (response : Response) (_t : ℝ) : ℝ :=
  -responseScale response

theorem baseline_analytic
    (state destination : State) :
    AnalyticAt ℝ (fun t => baseline state t destination) 0 := by
  exact analyticAt_const

theorem forward_analytic
    (response : Response) (destination : State) :
    AnalyticAt ℝ (fun t => forward response t destination) 0 := by
  change AnalyticAt ℝ
    ((fun _ : ℝ => 1 / 3 + endpointDifference destination) +
      fun t => t * perturbation response destination) 0
  exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)

theorem quotient_analytic
    (response : Response) :
    AnalyticAt ℝ (quotient response) 0 := by
  exact analyticAt_const

theorem forward_mass_eq_baseline
    (response : Response) :
    ∀ t,
      ∑ destination, forward response t destination =
        ∑ destination, baseline (source response) t destination := by
  intro t
  fin_cases response <;>
    simp [forward, baseline, endpointDifference, perturbation,
      responseScale, Fin.sum_univ_succ]
  <;> ring

theorem transitionDrift_factor
    (response : Response) :
    ∀ t,
      finiteStateTransitionDrift
          (baseline (source response))
          (forward response)
          (fun _ => endpointValue) t =
        t ^ (1 : ℕ) * quotient response t := by
  intro t
  fin_cases response <;>
    simp [finiteStateTransitionDrift, finiteStatePairing, forward,
      baseline, endpointDifference, perturbation, responseScale,
      endpointValue, quotient]

theorem quotient_negative (response : Response) :
    quotient response 0 < 0 := by
  fin_cases response <;> norm_num [quotient, responseScale]

theorem no_common_endpointPotential :
    ¬∃ potential : State → ℝ,
      ∀ response,
        dotProduct
            (endpointResponseDifference
              baseline source forward response)
            potential =
          quotient response 0 := by
  rintro ⟨potential, hpotential⟩
  have hzero := hpotential (0 : Response)
  have hone := hpotential (1 : Response)
  have hdifference :
      endpointResponseDifference baseline source forward (0 : Response) =
        endpointResponseDifference baseline source forward (1 : Response) := by
    funext destination
    simp [endpointResponseDifference, forward]
  rw [hdifference] at hzero
  norm_num [quotient, responseScale] at hzero hone
  linarith

/-- The local compatibility theorem selects positive oriented public evidence,
although every actual quotient level is negative. -/
theorem exists_orientedEvidence_but_all_quotients_negative :
    (∃ (coefficient : Response → ℝ) (response : Response)
        (positive : Bool) (destination : State)
        (n : ℕ) (c : ℝ),
      (∀ state,
        ∑ action,
            coefficient action *
              endpointResponseDifference
                baseline source forward action state =
          0) ∧
      0 < ∑ action,
        coefficient action * quotient action 0 ∧
      0 <
        responseOrientation positive *
          coefficient response ∧
      0 <
        responseOrientation positive *
          quotient response 0 ∧
      0 < c ∧
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        c * t ^ n ≤
            responseOrientation positive *
              (forward response t destination -
                baseline (source response) t destination) ∧
          0 <
            responseOrientation positive *
              (forward response t destination -
                baseline (source response) t destination)) ∧
      ∀ response, quotient response 0 < 0 := by
  have halternative :=
    exists_endpointPotential_or_owned_orientedResponse
      baseline source forward endpointValue quotient
      (q := 1)
      baseline_analytic forward_analytic
      (fun response =>
        Filter.Eventually.of_forall
          (forward_mass_eq_baseline response))
      quotient_analytic
      (fun response =>
        Filter.Eventually.of_forall
          (transitionDrift_factor response))
  rcases halternative with hpotential | hevidence
  · exact False.elim (no_common_endpointPotential hpotential)
  · exact ⟨hevidence, quotient_negative⟩

end InvisibleResponseCompatibilityCounterexample
end StochasticGame
end GameTheory
