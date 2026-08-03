/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.TransitionIndependent
import GameTheory.Concepts.Stochastic.AdaptiveCertificate

/-!
# `TransitionIndependent`'s uniform equilibrium payoff, via the certificate

Stage 3 of the adaptive-certificate generalization program: re-derives
`StochasticGame.exists_uniformEquilibriumPayoff_of_isActionIndependent`
(`GameTheory.Concepts.Stochastic.TransitionIndependent`) through the
adaptive certificate machinery of `GameTheory.Concepts.Stochastic.AdaptiveCertificate`,
using a genuinely **non-constant** history potential built from the
relative-value (Poisson equation) of the induced autonomous Markov chain —
instantiating the "decoupled" flavor of the "V2" interface
(`StochasticGame.IsAdaptiveDecoupledEquilibriumCertificate`), because (as with
the Big Match, but for a different reason) no potential *close to the target
everywhere* is available here either: the Poisson potential `u` is bounded
but not close to any single constant unless the chain happens to be flat.

## The Poisson-equation potential

For an action-independent game with autonomous kernel `κ`, per-state mixed
stage-Nash equilibrium `x`, and player `who`, the stage-Nash payoff function
`f who := fun s => G.mixedStageEU s (x s) who` decomposes
(`Math.MeanErgodic.exists_harmonic_add_poisson`, already proved — this file
does *not* need to re-extract the Poisson-solvability statement, since that
theorem already *is* it) as `f who = o who + (κ-step (u who) - u who)` for a
**harmonic** component `o who` (`∀ s, expect (κ s) (o who) = o who s`) and a
**Poisson potential** `u who`. Harmonicity makes the *expectation* of
`o who` along the chain started at `s₀` constant in time
(`expect_iter_of_harmonic`), equal to `o who s₀`, *even when `o who` is not
itself a constant function of state* (e.g. several recurrent classes): this
is the general mechanism, no "single recurrent class" restriction is
actually needed for the certificate construction below. Substituting this
into the decomposition and telescoping over the autonomous chain's one-step
transition gives an **exact** (zero-error) Bellman identity for the history
potential `φ who t h := -(u who h.2)` against the *constant* target
`v who := o who s₀`: `v who + E[φ who t] = payoff t who + E[φ who (t + 1)]`.
Since `u who` is a fixed function on the finite state space it is bounded,
but generally *not* close to `v who` anywhere — exactly the situation
`IsAdaptiveDecoupledCertificateAt` (not `IsAdaptiveCertificateAt`, "V1") was
built for.

The deviation clause reuses `TransitionIndependent.lean`'s own mechanism:
action-independence keeps the state marginal identical under every
deviating profile, so (a) the potential's expectation is unaffected by any
deviation, and (b) stage-Nash optimality caps the deviator's stage payoff by
the on-path stage payoff at the same state — together giving the deviation
clause with zero error too.

## Main results

* `Math.PMFIter.expect_iter_of_harmonic` — a harmonic
  observable's expectation along the chain is constant in time
* `GameTheory.StochasticGame.isAdaptiveDecoupledEquilibriumCertificate_of_isActionIndependent`
  — the Poisson-equation certificate construction
* `GameTheory.StochasticGame.exists_uniformEquilibriumPayoff_of_isActionIndependent_via_certificate`
  — `TransitionIndependent`'s result, re-derived through the certificate

This file is deliberately **not** wired into `GameTheory.lean` (the project
aggregator): it is a standalone validation of the certificate interface
against a second worked example, not a new standing result that other files
depend on. Import it directly if needed.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability Math.PMFProduct

variable {ι : Type}

-- ============================================================================
-- Stage-Nash domination against a deviation, at the expectation level
-- ============================================================================

/-- Against any unilateral deviation from Markov stage-Nash play, the stage
payoff at any fixed epoch is dominated by the on-path (state-Nash) stage
payoff, in expectation. The expectation-level, single-epoch form of the
`hOff`/`hstage` step inside
`isεHorizonNash_markovBehaviorProfile`. -/
theorem expectedStagePayoff_update_markovBehaviorProfile_le
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] {κ : G.State → PMF G.State}
    (hκ : ∀ s a, G.transition s a = κ s)
    {x : (s : G.State) → ∀ i, PMF (G.Act i)} (hx : G.IsMixedStageNash x)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State) (t : ℕ) :
    G.expectedStagePayoff (Function.update (G.markovBehaviorProfile x) who dev)
        s₀ t who ≤
      expect (Math.PMFIter.iter κ t s₀) (fun s => G.mixedStageEU s (x s) who) := by
  rw [← G.expect_snd_histDist_of_forall_transition_eq hκ
    (Function.update (G.markovBehaviorProfile x) who dev) s₀ t
    (fun s => G.mixedStageEU s (x s) who)]
  unfold expectedStagePayoff
  apply expect_mono
  intro h
  unfold stageEUAt
  rw [G.stageActionDist_update_markovBehaviorProfile]
  exact hx h.2 who (dev t h)

-- ============================================================================
-- The Poisson-equation certificate
-- ============================================================================

/-- **The relative-value (Poisson equation) certificate for action-independent
games.** For every action-independent `G`, the "decoupled V2" certificate
holds at `s₀` with target `v who := o who s₀`, the harmonic component of the
Poisson decomposition of the stage-Nash payoff `fun s => G.mixedStageEU s
(x s) who` — with *zero* error (`e ≡ 0`) throughout, since every clause is
an exact algebraic identity or an exact domination fact, not merely an
`O(1/T)`-vanishing approximation. -/
theorem isAdaptiveDecoupledEquilibriumCertificate_of_isActionIndependent
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (hAI : G.IsActionIndependent) (s₀ : G.State) :
    ∃ v : Payoff ι, G.IsAdaptiveDecoupledEquilibriumCertificate s₀ v := by
  classical
  letI : Fintype G.State := Fintype.ofFinite G.State
  obtain ⟨x, hx⟩ := G.exists_isMixedStageNash
  set κ : G.State → PMF G.State :=
    fun s' => G.transition s' (Classical.arbitrary G.JointAct) with hκdef
  have hκ : ∀ s a, G.transition s a = κ s :=
    fun s a => hAI s a (Classical.arbitrary G.JointAct)
  have hex : ∀ who : ι, ∃ o u : G.State → ℝ,
      (∀ s, expect (κ s) o = o s) ∧
      (∀ s, G.mixedStageEU s (x s) who = o s + (expect (κ s) u - u s)) := by
    intro who
    obtain ⟨o, u, ho, hdecomp, -⟩ := Math.MeanErgodic.exists_harmonic_add_poisson κ
      (fun s => G.mixedStageEU s (x s) who)
    exact ⟨o, u, ho, hdecomp⟩
  choose o u ho hdecomp using hex
  refine ⟨fun who => o who s₀, fun δ hδ => ?_⟩
  set φ : ι → G.HistoryPotential := fun who _ h => -(u who h.2) with hφdef
  set C : ι → ℝ := fun who => ∑ s : G.State, |u who s| with hCdef
  have hCnn : ∀ who, 0 ≤ C who := fun who => Finset.sum_nonneg fun s _ => abs_nonneg _
  set Cmax : ℝ := ∑ who, C who with hCmaxdef
  have hCmax : ∀ who, C who ≤ Cmax :=
    fun who => Finset.single_le_sum (fun j _ => hCnn j) (Finset.mem_univ who)
  obtain ⟨T₁, hT₁⟩ := exists_nat_gt (2 * Cmax / δ)
  -- The exact identity behind every clause: `payoff t who = g + U(t+1) - U t`.
  have hkey : ∀ (who : ι) (t : ℕ),
      expect (Math.PMFIter.iter κ t s₀) (fun s => G.mixedStageEU s (x s) who) =
        o who s₀ +
          expect (Math.PMFIter.iter κ (t + 1) s₀) (u who) -
          expect (Math.PMFIter.iter κ t s₀) (u who) := by
    intro who t
    have hcongr : expect (Math.PMFIter.iter κ t s₀)
        (fun s => G.mixedStageEU s (x s) who) =
        expect (Math.PMFIter.iter κ t s₀)
          (fun s => o who s + (expect (κ s) (u who) - u who s)) :=
      Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
        fun s _ => hdecomp who s
    rw [hcongr, expect_add, expect_sub,
      Math.PMFIter.expect_iter_succ κ (u who) t s₀,
      Math.PMFIter.expect_iter_of_harmonic κ (o who) (ho who) t s₀]
    ring
  have hφeq : ∀ (σ' : G.BehaviorProfile) (who : ι) (t : ℕ),
      G.expectedHistoryValue σ' s₀ (φ who) t =
        -(expect (Math.PMFIter.iter κ t s₀) (u who)) := by
    intro σ' who t
    unfold expectedHistoryValue
    rw [hφdef]
    simp only
    have hneg : expect (G.histDist σ' s₀ t) (fun h => -(u who h.2)) =
        -(expect (G.histDist σ' s₀ t) (fun h => u who h.2)) := by
      have := expect_const_mul (G.histDist σ' s₀ t) (-1) (fun h => u who h.2)
      simpa using this
    rw [hneg, G.expect_snd_histDist_of_forall_transition_eq hκ σ' s₀ t (u who)]
  have hFeq : ∀ (who : ι) (t : ℕ),
      G.expectedStagePayoff (G.markovBehaviorProfile x) s₀ t who =
        expect (Math.PMFIter.iter κ t s₀) (fun s => G.mixedStageEU s (x s) who) := by
    intro who t
    unfold expectedStagePayoff
    simp only [G.stageEUAt_markovBehaviorProfile]
    exact G.expect_snd_histDist_of_forall_transition_eq hκ (G.markovBehaviorProfile x) s₀ t
      (fun s => G.mixedStageEU s (x s) who)
  refine ⟨G.markovBehaviorProfile x, max 2 (T₁ + 1), φ, C, fun _ _ => 0,
    le_max_left _ _, ?_, ?_, ?_, ?_, ?_⟩
  · -- boundedness
    intro who t h
    rw [hφdef]
    simp only
    rw [abs_neg]
    exact Finset.single_le_sum (fun s _ => abs_nonneg (u who s)) (Finset.mem_univ h.2)
  · -- on-path lower (equality, `e = 0`)
    intro who t
    rw [hFeq who t, hφeq (G.markovBehaviorProfile x) who t,
      hφeq (G.markovBehaviorProfile x) who (t + 1)]
    have := hkey who t
    linarith [this]
  · -- on-path upper (equality, `e = 0`)
    intro who t
    rw [hFeq who t, hφeq (G.markovBehaviorProfile x) who t,
      hφeq (G.markovBehaviorProfile x) who (t + 1)]
    have := hkey who t
    linarith [this]
  · -- deviation cap (`e = 0`), via stage-Nash domination + state-marginal invariance
    intro who dev t
    have hdomination := G.expectedStagePayoff_update_markovBehaviorProfile_le hκ hx who dev s₀ t
    rw [hφeq (Function.update (G.markovBehaviorProfile x) who dev) who t,
      hφeq (Function.update (G.markovBehaviorProfile x) who dev) who (t + 1)]
    have := hkey who t
    simp only [add_zero]
    linarith [hdomination, this]
  · -- vanishing Cesàro average (trivial, `e = 0`; the horizon threshold
    -- absorbs the boundary-loss term `2 * C who / T`)
    intro who T hT
    have hT1 : T₁ + 1 ≤ T := le_trans (le_max_right _ _) hT
    have hTreal : (0 : ℝ) < T := by
      have h0 : (0 : ℕ) < T₁ + 1 := Nat.succ_pos _
      exact_mod_cast lt_of_lt_of_le h0 hT1
    have hT1real : (T₁ : ℝ) < (T : ℝ) := by
      have : T₁ < T := by omega
      exact_mod_cast this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_zero, add_zero]
    have hstep : 2 * Cmax / (T : ℝ) ≤ δ := by
      rw [div_le_iff₀ hTreal]
      have h2 : 2 * Cmax < (T : ℝ) * δ := by
        rw [div_lt_iff₀ hδ] at hT₁
        calc 2 * Cmax < (T₁ : ℝ) * δ := hT₁
          _ ≤ (T : ℝ) * δ := mul_le_mul_of_nonneg_right hT1real.le hδ.le
      linarith
    have hmono : 2 * C who / (T : ℝ) ≤ 2 * Cmax / (T : ℝ) := by
      gcongr
      exact hCmax who
    linarith [hmono, hstep]

/-- **`TransitionIndependent`'s uniform equilibrium payoff, re-derived
through the certificate.** Same statement as
`exists_uniformEquilibriumPayoff_of_isActionIndependent`, via
`isAdaptiveDecoupledEquilibriumCertificate_of_isActionIndependent` and
`isUniformEquilibriumPayoff_of_isAdaptiveDecoupledEquilibriumCertificate`
instead of the direct mean-ergodic-limit argument. -/
theorem exists_uniformEquilibriumPayoff_of_isActionIndependent_via_certificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (hAI : G.IsActionIndependent) (s₀ : G.State) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  obtain ⟨v, hv⟩ := G.isAdaptiveDecoupledEquilibriumCertificate_of_isActionIndependent hAI s₀
  exact ⟨v, G.isUniformEquilibriumPayoff_of_isAdaptiveDecoupledEquilibriumCertificate s₀ v hv⟩

end StochasticGame
end GameTheory
