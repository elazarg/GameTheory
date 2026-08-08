/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.OrientedResponseExtraction
import Math.FiniteLinearCompatibility
import Math.InvisibleNeutralActionDrift

/-!
# Compatibility or public evidence for invisible responses

Suppose every member of a finite response family lies in the high-order
branch of the discount-scale drift dichotomy. Its transition drift is then
`t ^ q` times an analytic quotient. The endpoint quotient levels either are
the pairings of all endpoint transition differences with one common
potential, or finite linear compatibility supplies a signed dependence.

In the incompatible branch, orienting that dependence to have positive
quotient charge selects one fixed response. That response cannot have the
same analytic transition germ as its baseline: otherwise its quotient level
would vanish. Hence one fixed destination-coordinate monitor has a positive
power-law drift in the selected orientation.

This is a local evidence theorem. It does not assert that the selected
response is a credible punishment, nor does it construct a public phase
recursion.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.Probability Set Topology

/-- Endpoint transition difference of one response from its source
baseline. -/
def endpointResponseDifference
    {S E : Type*}
    (baseline : S → ℝ → S → ℝ)
    (source : E → S)
    (forward : E → ℝ → S → ℝ)
    (response : E) (destination : S) : ℝ :=
  forward response 0 destination -
    baseline (source response) 0 destination

/-- If the endpoint quotient levels are not represented by one common
potential, a signed incompatibility witness selects a fixed owned response
and a fixed oriented destination coordinate with positive power-law drift.

The quotient identity is precisely the high-order conclusion supplied by
`analytic_finiteStateTransitionDrift_dichotomy`. The theorem uses the
actual forward transition curve; the Boolean sign orients only the public
coordinate score. -/
theorem
    exists_endpointPotential_or_owned_orientedResponse
    {S E : Type*} [Fintype S] [Fintype E] [Nonempty E]
    (baseline : S → ℝ → S → ℝ)
    (source : E → S)
    (forward : E → ℝ → S → ℝ)
    (endpointValue : S → ℝ)
    (quotient : E → ℝ → ℝ)
    {q : ℕ}
    (hbaseline :
      ∀ state destination,
        AnalyticAt ℝ
          (fun t => baseline state t destination) 0)
    (hforward :
      ∀ response destination,
        AnalyticAt ℝ
          (fun t => forward response t destination) 0)
    (hmass :
      ∀ response,
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ∑ destination, forward response t destination =
            ∑ destination,
              baseline (source response) t destination)
    (hquotient :
      ∀ response, AnalyticAt ℝ (quotient response) 0)
    (hfactor :
      ∀ response,
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          finiteStateTransitionDrift
              (baseline (source response))
              (forward response)
              (fun _ => endpointValue) t =
            t ^ q * quotient response t) :
    (∃ potential : S → ℝ,
      ∀ response,
        dotProduct
            (endpointResponseDifference
              baseline source forward response)
            potential =
          quotient response 0) ∨
      ∃ (coefficient : E → ℝ) (response : E)
          (positive : Bool) (destination : S)
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
                  baseline (source response) t destination) := by
  classical
  let delta : E → S → ℝ :=
    endpointResponseDifference baseline source forward
  let level : E → ℝ := fun response => quotient response 0
  rcases
      exists_potential_or_signed_incompatibility delta level with
    hpotential | hincompatible
  · exact Or.inl hpotential
  · right
    obtain ⟨rawCoefficient, hrawBalance, hrawCharge⟩ :=
      hincompatible
    let rawTotal : ℝ :=
      ∑ response, rawCoefficient response * level response
    let coefficient : E → ℝ :=
      if 0 < rawTotal then rawCoefficient
      else fun response => -rawCoefficient response
    have htotal : 0 <
        ∑ response, coefficient response * level response := by
      by_cases hpositive : 0 < rawTotal
      · simp [coefficient, hpositive, rawTotal]
      · have hrawTotalNe : rawTotal ≠ 0 := by
          simpa only [rawTotal] using hrawCharge
        have hnegative : rawTotal < 0 :=
          lt_of_le_of_ne (le_of_not_gt hpositive) hrawTotalNe
        rw [show coefficient =
          fun response => -rawCoefficient response by
            simp [coefficient, hpositive]]
        calc
          0 < -rawTotal := neg_pos.mpr hnegative
          _ = ∑ response,
              (-rawCoefficient response) * level response := by
            dsimp only [rawTotal]
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro response _
            ring
    have hbalance :
        ∀ state,
          ∑ response, coefficient response * delta response state =
            0 := by
      intro state
      by_cases hpositive : 0 < rawTotal
      · simpa [coefficient, hpositive] using hrawBalance state
      · rw [show coefficient =
          fun response => -rawCoefficient response by
            simp [coefficient, hpositive]]
        calc
          (∑ response,
              (-rawCoefficient response) * delta response state) =
              ∑ response,
                -(rawCoefficient response *
                  delta response state) := by
            apply Finset.sum_congr rfl
            intro response _
            ring
          _ =
              -(∑ response,
                rawCoefficient response * delta response state) := by
            rw [Finset.sum_neg_distrib]
          _ = 0 := by rw [hrawBalance state, neg_zero]
    let weight : E → ℝ → ℝ :=
      fun response _ => coefficient response
    let charge : E → ℝ → ℝ :=
      fun response _ => level response
    have hweight :
        ∀ response, AnalyticAt ℝ (weight response) 0 := by
      intro response
      exact analyticAt_const
    have hcharge :
        ∀ response, AnalyticAt ℝ (charge response) 0 := by
      intro response
      exact analyticAt_const
    have htotalEventual :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          (∑ response, coefficient response * level response) *
              t ^ (0 : ℕ) ≤
            ∑ response, weight response t * charge response t := by
      simp [weight, charge]
    obtain ⟨response, positive, L, kappa, hkappa,
        hextract, htransition⟩ :=
      exists_fixed_oriented_analytic_stochastic_response_curve
        baseline source forward weight charge
        hbaseline hforward hmass hweight hcharge
        htotal htotalEventual
    have hcoefficientPositive :
        0 <
          responseOrientation positive *
            coefficient response := by
      obtain ⟨t, ht, htpositive⟩ :=
        ((hextract.and self_mem_nhdsWithin)).exists
      have hleft : 0 < kappa * t ^ L :=
        mul_pos hkappa (pow_pos (mem_Ioi.mp htpositive) L)
      exact hleft.trans_le (by
        simpa only [weight] using ht.2.1)
    have hlevelPositive :
        0 <
          responseOrientation positive *
            quotient response 0 := by
      obtain ⟨t, ht, htpositive⟩ :=
        ((hextract.and self_mem_nhdsWithin)).exists
      have hleft : 0 < kappa * t ^ L :=
        mul_pos hkappa (pow_pos (mem_Ioi.mp htpositive) L)
      exact hleft.trans_le (by
        simpa only [charge, level] using ht.2.2)
    rcases htransition with hsame | hvisible
    · have hdriftZero :
          ∀ᶠ t in nhdsWithin 0 (Ioi 0),
            finiteStateTransitionDrift
                (baseline (source response))
                (forward response)
                (fun _ => endpointValue) t =
              0 := by
        filter_upwards [hsame] with t ht
        unfold finiteStateTransitionDrift finiteStatePairing
        apply Finset.sum_eq_zero
        intro destination _
        simp [ht destination]
      have hquotientZero :
          ∀ᶠ t in nhdsWithin 0 (Ioi 0),
            quotient response t = 0 := by
        filter_upwards [
          hfactor response,
          hdriftZero,
          self_mem_nhdsWithin] with t hfactorAt hzero htpositive
        rw [hzero] at hfactorAt
        have hpowNe : t ^ q ≠ 0 :=
          pow_ne_zero q (ne_of_gt (mem_Ioi.mp htpositive))
        exact (mul_eq_zero.mp hfactorAt.symm).resolve_left hpowNe
      have hcontinuous :
          Tendsto (quotient response)
              (nhdsWithin 0 (Ioi 0))
              (nhds (quotient response 0)) :=
        (hquotient response).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      have hzeroLimit :
          Tendsto (quotient response)
              (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
        tendsto_const_nhds.congr'
          (hquotientZero.mono fun _ ht => ht.symm)
      have hlevelZero : quotient response 0 = 0 :=
        tendsto_nhds_unique hcontinuous hzeroLimit
      rw [hlevelZero, mul_zero] at hlevelPositive
      exact False.elim (lt_irrefl 0 hlevelPositive)
    · obtain ⟨destination, n, c, hc, hevidence⟩ := hvisible
      exact ⟨coefficient, response, positive, destination, n, c,
        by simpa only [delta] using hbalance,
        by simpa only [level] using htotal,
        hcoefficientPositive, hlevelPositive, hc, hevidence⟩

end StochasticGame
end GameTheory
