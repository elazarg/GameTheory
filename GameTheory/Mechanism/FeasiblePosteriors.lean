/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.Probability

/-!
# Feasible posterior beliefs

A distribution over *posteriors* (beliefs about the state) is **feasible** — it can
be induced by some information experiment starting from a given prior — exactly when
it is **Bayes plausible**: its average belief equals the prior (the martingale /
"splitting" condition of Aumann–Maschler 1995 and Kamenica–Gentzkow 2011; the
characterization studied by Arieli–Babichenko–Sandomirskiy–Tamuz, *Feasible Joint
Posterior Beliefs*, JPE 2021).

This file works directly with distributions over posteriors `τ : PMF (PMF Ω)` (a
belief is a `PMF Ω`), avoiding measure theory. The information experiment realizing a
`τ` is its **canonical coupling**: draw a belief `b` from `τ`, then a state from `b`,
and emit the pair `(state, b)` — so the public signal *is* the posterior it induces.

## Main definitions

* `meanPosterior τ` — the average belief `τ.bind id` (the predictive distribution)
* `IsBayesPlausible prior τ` — `τ`'s average belief is the prior
* `posteriorCoupling τ` — the experiment `(state, posterior)` realizing `τ`

## Main results

* `posteriorCoupling_snd` — the experiment's signal marginal is exactly `τ` (it realizes `τ`)
* `posteriorCoupling_fst` — the experiment's state marginal is the mean posterior
* `posteriorCoupling_apply` — the joint law factors as `τ(b) · b(ω)`
* `isBayesPlausible_iff_coupling_fst` — **feasibility (via the canonical experiment) ⟺ Bayes plausibility**
* `isBayesPlausible_uninformative` / `isBayesPlausible_fullRevelation` — the two extremes
-/

namespace GameTheory

open Math.Probability

variable {Ω : Type}

/-- The **mean posterior** of a distribution over beliefs: draw a belief from `τ`,
then a state from that belief. This is the predictive distribution over states. -/
noncomputable def meanPosterior (τ : PMF (PMF Ω)) : PMF Ω := τ.bind id

theorem meanPosterior_apply (τ : PMF (PMF Ω)) (ω : Ω) :
    meanPosterior τ ω = ∑' b : PMF Ω, τ b * b ω := by
  unfold meanPosterior
  rw [PMF.bind_apply]
  simp only [id_eq]

/-- A distribution over posteriors is **Bayes plausible** for `prior` when its mean
posterior is the prior — the martingale condition characterizing feasibility. -/
def IsBayesPlausible (prior : PMF Ω) (τ : PMF (PMF Ω)) : Prop :=
  meanPosterior τ = prior

/-- The **canonical coupling** of a distribution over posteriors: draw a belief `b`
from `τ`, then a state `ω` from `b`, and emit `(ω, b)`. The second coordinate (the
public signal) is, by construction, the posterior it induces. -/
noncomputable def posteriorCoupling (τ : PMF (PMF Ω)) : PMF (Ω × PMF Ω) :=
  τ.bind fun b => b.map fun ω => (ω, b)

/-- The joint law of the canonical coupling factors as `τ(b) · b(ω)`: the signal `b`
is drawn with probability `τ(b)`, and the state `ω` is then drawn from `b`. -/
theorem posteriorCoupling_apply (τ : PMF (PMF Ω)) (ω : Ω) (b : PMF Ω) :
    posteriorCoupling τ (ω, b) = τ b * b ω := by
  classical
  unfold posteriorCoupling
  rw [PMF.bind_apply, tsum_eq_single b]
  · have hdiag : (b.map fun ω' => (ω', b)) (ω, b) = b ω := by
      rw [PMF.map_apply, tsum_eq_single ω]
      · simp
      · intro ω' hω'
        split_ifs with hpair
        · cases hpair; exact (hω' rfl).elim
        · rfl
    rw [hdiag]
  · intro b' hb'
    have hzero : (b'.map fun ω' => (ω', b')) (ω, b) = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.2 fun ω' => ?_
      split_ifs with hpair
      · cases hpair; exact (hb' rfl).elim
      · rfl
    rw [hzero, mul_zero]

/-- The signal marginal of the canonical coupling is exactly `τ`: the experiment
genuinely realizes the distribution over posteriors. -/
theorem posteriorCoupling_snd (τ : PMF (PMF Ω)) :
    (posteriorCoupling τ).map Prod.snd = τ := by
  unfold posteriorCoupling
  rw [PMF.map_bind]
  conv_lhs =>
    enter [2, b]
    rw [PMF.map_comp]
    change b.map (Function.const Ω b)
    rw [PMF.map_const]
  rw [PMF.bind_pure]

/-- The state marginal of the canonical coupling is the mean posterior. -/
theorem posteriorCoupling_fst (τ : PMF (PMF Ω)) :
    (posteriorCoupling τ).map Prod.fst = meanPosterior τ := by
  unfold posteriorCoupling meanPosterior
  rw [PMF.map_bind]
  conv_lhs =>
    enter [2, b]
    rw [PMF.map_comp]
    change b.map id
    rw [PMF.map_id]
  rfl

/-- **Feasibility is Bayes plausibility.** A distribution over posteriors is
realized — by its canonical coupling experiment — with the correct prior (the
experiment's state marginal is `prior`) if and only if it is Bayes plausible.
Combined with `posteriorCoupling_snd` (the experiment always realizes `τ` as its
signal distribution), this is the Aumann–Maschler / Kamenica–Gentzkow splitting
characterization. -/
theorem isBayesPlausible_iff_coupling_fst (prior : PMF Ω) (τ : PMF (PMF Ω)) :
    IsBayesPlausible prior τ ↔ (posteriorCoupling τ).map Prod.fst = prior := by
  rw [posteriorCoupling_fst]
  rfl

/-- The uninformative experiment — the point mass at the prior — is Bayes plausible. -/
theorem isBayesPlausible_uninformative (prior : PMF Ω) :
    IsBayesPlausible prior (PMF.pure prior) := by
  unfold IsBayesPlausible meanPosterior
  rw [PMF.pure_bind]
  rfl

/-- Full revelation — pushing the prior onto point-mass beliefs — is Bayes plausible. -/
theorem isBayesPlausible_fullRevelation (prior : PMF Ω) :
    IsBayesPlausible prior (prior.map fun ω => PMF.pure ω) := by
  unfold IsBayesPlausible meanPosterior
  simp only [PMF.bind_map, Function.id_comp, PMF.bind_pure]

end GameTheory
