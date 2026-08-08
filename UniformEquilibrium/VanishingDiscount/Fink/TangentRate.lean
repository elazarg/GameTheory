/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.VanishingDiscount.Fink.Limit

/-!
# Rate-stable supported Fink tangents

The supported tangent system need not be solvable under convergence alone:
actions vanishing at the reciprocal bias scale can leave a nonzero
first-order effect on actions which remain in the limiting support.  This
file isolates the exact finite-vector rate hypothesis which excludes that
rank-drop phenomenon.

When the scaled continuation operator applied to the leading value tends to
zero, the Poisson potential is itself harmonic.  The explicit adjustment
`-K` then solves every supported tangent equation.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter

variable {ι : Type}

/-- The continuation operator at a varying profile, with its pure-action
coordinates masked by the support of a fixed reference profile.  Freezing
the mask is essential: it records exactly the operator drift seen by actions
which survive in the limit. -/
def finkFrozenSupportContinuationVector
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (zref z : G.finkDomain U) (W : G.State → Payoff ι) :
    G.FinkSupportTangentEquationVector :=
  (G.finkContinuationResidualVector W z, fun s who d =>
    if G.finkProfile zref s who d ≠ 0 then
      G.finkContinuationGain W z s who d else 0)

/-- Zero scaled drift of the continuation operator, with support frozen at
the limiting profile, closes the supported tangent problem explicitly.

The fixed-point Bellman equation first identifies the scaled on-profile
residual with `-residual K`; zero drift therefore makes `K` harmonic.  On
every limiting supported action, complementary slackness identifies the
scaled pure continuation gain with the negative stage-plus-bias gain; zero
drift makes that expression vanish.  Consequently `A = -K` is the required
harmonic adjustment. -/
theorem exists_finkSupportHarmonicAdjustment_of_frozenSupportDrift_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
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
      atTop (nhds 0)) :
    ∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A zlim = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile zlim s who d ≠ 0 →
          G.finkContinuationGain A zlim s who d =
            G.finkStageGain zlim s who d +
              G.finkContinuationGain (H - K) zlim s who d := by
  let a : ℕ → ℝ := fun n => β n / (1 - β n)
  let J : ℕ → G.State → Payoff ι := fun n =>
    G.finkRelativeBias (β n) W (z n)
  let E : ℕ → G.State → Payoff ι := fun n =>
    G.finkContinuationResidualVector W (z n)
  have hbellman : ∀ n s who,
      G.finkValue (z n) s who + J n s who =
        G.finkStageEU (z n) s who +
          G.finkContinuationEU (J n) (z n) s who +
            a n * E n s who := by
    intro n s who
    simpa only [J, E, a, finkContinuationResidualVector] using
      G.finkValue_add_relativeBias_eq_finkEU_add
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who
  have hscaledResidual := G.tendsto_smul_finkBellmanForcingVector hz hV
    (by simpa only [J] using hH) a hbellman
  have hscaledResidualPoisson : Tendsto (fun n =>
      a n • G.finkContinuationResidualVector W (z n)) atTop
      (nhds (-G.finkContinuationResidualVector K zlim)) := by
    simpa only [E, hPoisson] using hscaledResidual
  have hDriftParts := (Prod.tendsto_iff _ _).mp hDrift
  have hscaledResidualZero : Tendsto (fun n =>
      a n • G.finkContinuationResidualVector W (z n)) atTop
      (nhds 0) := by
    have hfirst := hDriftParts.1
    change Tendsto (fun n =>
      (β n / (1 - β n)) • G.finkContinuationResidualVector W (z n))
        atTop (nhds (0 : G.State → Payoff ι)) at hfirst
    simpa only [a] using hfirst
  have hKresNeg : -G.finkContinuationResidualVector K zlim = 0 :=
    tendsto_nhds_unique hscaledResidualPoisson hscaledResidualZero
  have hKres : G.finkContinuationResidualVector K zlim = 0 := by
    exact neg_eq_zero.mp hKresNeg
  refine ⟨-K, ?_, ?_⟩
  · rw [G.finkContinuationResidualVector_neg, hKres]
    simp
  · intro s who d hd
    have hDriftAction0 : Tendsto (fun n =>
        a n * G.finkContinuationGain W (z n) s who d)
        atTop (nhds 0) := by
      have hs := (tendsto_pi_nhds.mp hDriftParts.2) s
      have hwho := (tendsto_pi_nhds.mp hs) who
      have hdcoord := (tendsto_pi_nhds.mp hwho) d
      change Tendsto (fun n =>
        ((β n / (1 - β n)) •
          G.finkFrozenSupportContinuationVector zlim (z n) W).2 s who d)
          atTop (nhds (0 : ℝ)) at hdcoord
      have heq : (fun n =>
          ((β n / (1 - β n)) •
            G.finkFrozenSupportContinuationVector zlim (z n) W).2 s who d) =
          (fun n => (β n / (1 - β n)) *
            G.finkContinuationGain W (z n) s who d) := by
        funext n
        change (β n / (1 - β n)) *
            (if G.finkProfile zlim s who d ≠ 0 then
              G.finkContinuationGain W (z n) s who d else 0) = _
        rw [if_pos hd]
      rw [heq] at hdcoord
      simpa only [a] using hdcoord
    have hfixedAction :=
      G.tendsto_scaled_finkContinuationGain_of_limit_support
        hβ0 hβ1 hpay hz hfix W H hH s who d hd
    have hstageBiasNeg :
        -(G.finkStageGain zlim s who d +
          G.finkContinuationGain H zlim s who d) = 0 :=
      tendsto_nhds_unique (by simpa only [a] using hfixedAction)
        hDriftAction0
    have hstageBias : G.finkStageGain zlim s who d +
        G.finkContinuationGain H zlim s who d = 0 := by
      exact neg_eq_zero.mp hstageBiasNeg
    rw [show -K = (-1 : ℝ) • K by ext t i; simp]
    rw [G.finkContinuationGain_smul]
    rw [G.finkContinuationGain_sub]
    simp only [neg_one_mul]
    linarith

end StochasticGame
end GameTheory
