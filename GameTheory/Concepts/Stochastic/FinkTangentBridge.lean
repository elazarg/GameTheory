/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkTangentRate

/-!
# From rate-stable Fink tangents to uniform equilibrium payoffs

This file joins the rate-stable supported tangent theorem to the stationary
average-reward verification theorem.  Vanishing discount gives harmonicity
and excessiveness of the limiting value.  The frozen-support drift condition
then supplies a harmonic adjustment satisfying every supported tangent
equation.  The only remaining hypothesis is the lower singular-gain bound on
continuation-neutral actions which vanish from the limiting support.

The off-support hypothesis is stated uniformly over solutions of the
supported tangent system because the finite-dimensional existence theorem
does not choose a canonical solution.  Thus it records exactly the remaining
selection obligation, without adding a choice-dependent definition to the
interface.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter
open Math.Probability Math.PMFProduct

variable {ι : Type}

/-- End-to-end finite-relative-bias bridge from zero frozen-support drift to
a uniform equilibrium payoff.

All limiting on-profile and supported-action conditions are consequences of
the Fink fixed-point family.  What remains explicit is precisely the
off-support condition: a continuation-neutral action which disappears in the
limit must have enough lower singular gain for any harmonic solution of the
supported tangent equations. -/
theorem isUniformEquilibriumPayoff_of_frozenSupportDrift_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s₀ : G.State) (β : ℕ → ℝ) (U : ℝ)
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1))
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hPoisson : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim)
    (hDrift : Tendsto (fun n =>
      (β n / (1 - β n)) •
        G.finkFrozenSupportContinuationVector zlim (z n) W)
      atTop (nhds 0))
    (hoffSupport : ∀ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A zlim = 0 →
      (∀ s who (d : G.Act who), G.finkProfile zlim s who d ≠ 0 →
        G.finkContinuationGain A zlim s who d =
          G.finkStageGain zlim s who d +
            G.finkContinuationGain (H - K) zlim s who d) →
      ∀ s who (d : G.Act who),
        expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) = W s who →
        G.finkProfile zlim s who d = 0 →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in atTop,
            -G.finkContinuationGain (K + A) zlim s who d - ε ≤
              (β n / (1 - β n)) *
                G.finkContinuationGain W (z n) s who d) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  have hW : W = G.finkValue zlim :=
    tendsto_nhds_unique hV (G.tendsto_finkValue hz)
  have hβlim' : Tendsto (β ∘ id) atTop (nhds 1) := by
    simpa only [Function.comp_id] using hβlim
  have hz' : Tendsto (z ∘ id) atTop (nhds zlim) := by
    simpa only [Function.comp_id] using hz
  have hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) := by
    intro s who
    rw [hW]
    exact G.finkValue_harmonic_of_fixedPoint_tendsto
      β U hβ0 (fun n => (hβ1 n).le) hpay z zlim id hfix
        hβlim' hz' s who
  have hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who := by
    intro s who d
    rw [hW]
    exact G.finkValue_excessive_pureDeviation_of_fixedPoint_tendsto
      β U hβ0 (fun n => (hβ1 n).le) hpay z zlim id hfix
        hβlim' hz' s who d
  obtain ⟨A, hAharmonic, hsupportEq⟩ :=
    G.exists_finkSupportHarmonicAdjustment_of_frozenSupportDrift_zero
      β U hβ0 hβ1 hpay z zlim W H K hfix hz hV hH hPoisson hDrift
  have hsupport : ∀ s who (d : G.Act who),
      G.finkProfile zlim s who d ≠ 0 →
        G.finkStageGain zlim s who d +
          G.finkContinuationGain (H - (K + A)) zlim s who d ≤ 0 := by
    intro s who d hd
    have heq := hsupportEq s who d hd
    rw [G.finkContinuationGain_sub] at heq
    rw [G.finkContinuationGain_sub, G.finkContinuationGain_add]
    linarith
  apply G.isUniformEquilibriumPayoff_of_finkInteriorPoissonHarmonicAdjustment_onSupport
    s₀ β U hβ0 hβ1 hpay z zlim W H K A hfix hz hV hH
      hharmonic hexcessive hPoisson hAharmonic hsupport
  exact hoffSupport A hAharmonic hsupportEq

end StochasticGame
end GameTheory
