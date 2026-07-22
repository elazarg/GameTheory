/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkLimit

/-!
# The scheduled-Markov content of the Fink endpoint

The corrected-calendar endpoint constructs substantially more than an
arbitrary behavior profile: at every accuracy its witness depends only on the
stage number and current state.  This file preserves that information in the
conclusion, so a no-Markov theorem can be compared directly with the Fink
selection hypothesis.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability Math.PMFProduct

/-- A uniform equilibrium payoff witnessed, at every accuracy, by a profile
depending only on calendar time and the current state. -/
def IsUniformScheduledMarkovEquilibriumPayoff (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (x : ℕ → G.StationaryMixedProfile) (T₀ : ℕ),
      ∀ T, T₀ ≤ T →
        G.IsεHorizonNash s₀ T ε (G.scheduledMarkovBehaviorProfile x) ∧
          ∀ who,
            |G.finiteAveragePayoff s₀ T
                (G.scheduledMarkovBehaviorProfile x) who - v who| ≤ ε

/-- Forgetting the scheduled-Markov form of the witnesses recovers the usual
uniform-equilibrium-payoff notion. -/
theorem IsUniformScheduledMarkovEquilibriumPayoff.isUniformEquilibriumPayoff
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    {s₀ : G.State} {v : Payoff ι}
    (h : G.IsUniformScheduledMarkovEquilibriumPayoff s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  intro ε hε
  obtain ⟨x, T₀, hx⟩ := h ε hε
  exact ⟨G.scheduledMarkovBehaviorProfile x, T₀, hx⟩

/-- Lean-ready no-scheduled-Markov interface.  To refute a scheduled-Markov
uniform payoff it is necessary and sufficient to exhibit one positive
accuracy such that every time/state schedule fails, after every proposed
threshold, at some later horizon.  Failure may be either the Nash condition
or convergence to the proposed payoff. -/
theorem not_isUniformScheduledMarkovEquilibriumPayoff_iff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι) :
    ¬ G.IsUniformScheduledMarkovEquilibriumPayoff s₀ v ↔
      ∃ ε : ℝ, 0 < ε ∧
        ∀ (x : ℕ → G.StationaryMixedProfile) (T₀ : ℕ),
          ∃ T, T₀ ≤ T ∧
            (¬ G.IsεHorizonNash s₀ T ε
                (G.scheduledMarkovBehaviorProfile x) ∨
              ∃ who,
                ε < |G.finiteAveragePayoff s₀ T
                    (G.scheduledMarkovBehaviorProfile x) who - v who|) := by
  simp only [IsUniformScheduledMarkovEquilibriumPayoff, not_forall,
    not_exists, not_and_or, not_le]
  constructor
  · rintro ⟨ε, hε, hfail⟩
    refine ⟨ε, hε, ?_⟩
    intro x T₀
    obtain ⟨T, hT, hbad⟩ := hfail x T₀
    exact ⟨T, hT, hbad⟩
  · rintro ⟨ε, hε, hfail⟩
    refine ⟨ε, hε, ?_⟩
    intro x T₀
    obtain ⟨T, hT, hbad⟩ := hfail x T₀
    exact ⟨T, hT, hbad⟩

/-- Proof-facing scheduled-Markov certificate.  This is the witness-preserving
version of `isUniformEquilibriumPayoff_of_deviation_caps`. -/
theorem isUniformScheduledMarkovEquilibriumPayoff_of_deviation_caps
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι)
    (hcert : ∀ δ : ℝ, 0 < δ →
      ∃ (x : ℕ → G.StationaryMixedProfile) (T₀ : ℕ),
        ∀ T, T₀ ≤ T →
          (∀ who,
            |G.finiteAveragePayoff s₀ T
                (G.scheduledMarkovBehaviorProfile x) who - v who| ≤ δ) ∧
          (∀ who (dev : G.BehaviorStrategy who),
            G.finiteAveragePayoff s₀ T
                (Function.update (G.scheduledMarkovBehaviorProfile x)
                  who dev) who ≤ v who + δ)) :
    G.IsUniformScheduledMarkovEquilibriumPayoff s₀ v := by
  intro ε hε
  have hδ : 0 < ε / 2 := by linarith
  obtain ⟨x, T₀, hx⟩ := hcert (ε / 2) hδ
  refine ⟨x, T₀, fun T hT => ?_⟩
  obtain ⟨hon, hdev⟩ := hx T hT
  constructor
  · intro who dev
    have hlower := (abs_le.mp (hon who)).1
    have hupper := hdev who dev
    linarith
  · intro who
    exact (hon who).trans (by linarith)

/-- The target-average Fink verifier preserves its scheduled-Markov witness. -/
theorem isUniformScheduledMarkovEquilibriumPayoff_of_scheduledFink_targetAverages
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι)
    (hcert : ∀ η : ℝ, 0 < η →
      ∃ (β : ℕ → ℝ) (x : ℕ → G.StationaryMixedProfile)
        (V : ℕ → G.State → Payoff ι) (e B : ℕ → ℝ) (T₀ : ℕ),
        G.IsDiscountedStationaryBellmanSchedule β x V ∧
          (∀ t, β t < 1) ∧ G.IsScheduledFinkSwitchBound β V e ∧
          (∀ t s who, |G.scheduledFinkBias β V t s who| ≤ B t) ∧
          ∀ T, T₀ ≤ T → 0 < T ∧
            ((B 0 + B T) / (T : ℝ) +
              (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤ η) ∧
            (∀ who,
              |(T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
                    G.expectedStateValue
                      (G.scheduledMarkovBehaviorProfile x) s₀ t
                      (fun s => V t s who) - v who| ≤ η) ∧
            ∀ who (dev : G.BehaviorStrategy who),
              (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
                  G.expectedStateValue
                    (Function.update
                      (G.scheduledMarkovBehaviorProfile x) who dev)
                    s₀ t (fun s => V t s who) ≤ v who + η) :
    G.IsUniformScheduledMarkovEquilibriumPayoff s₀ v := by
  apply G.isUniformScheduledMarkovEquilibriumPayoff_of_deviation_caps s₀ v
  intro δ hδ
  have hη : 0 < δ / 2 := by linarith
  obtain ⟨β, x, V, e, B, T₀, hF, hβ1, hswitch, hbias, htarget⟩ :=
    hcert (δ / 2) hη
  refine ⟨x, T₀, fun T hT => ?_⟩
  obtain ⟨hTpos, hboundary, hon, hdevTarget⟩ := htarget T hT
  constructor
  · intro who
    have hlo := hF.finiteAveragePayoff_ge_targetAverage
      hβ1 hswitch who s₀ (fun t s => hbias t s who) hTpos
    have hup := hF.finiteAveragePayoff_le_targetAverage
      hβ1 hswitch who s₀ (fun t s => hbias t s who) hTpos
    have hnear := abs_le.mp (hon who)
    rw [abs_le]
    constructor <;> linarith
  · intro who dev
    have hup := hF.deviation_finiteAveragePayoff_le_targetAverage
      hβ1 hswitch who dev s₀ (fun t s => hbias t s who) hTpos
    have htargetDev := hdevTarget who dev
    linarith

/-- The corrected-potential schedule criterion also yields the stronger
scheduled-Markov conclusion. -/
theorem isUniformScheduledMarkovEquilibriumPayoff_of_scheduledFink_correctedTarget
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (W : G.State → Payoff ι)
    (hcert : ∀ η : ℝ, 0 < η →
      ∃ (β : ℕ → ℝ) (x : ℕ → G.StationaryMixedProfile)
        (V R : ℕ → G.State → Payoff ι)
        (e B q c r : ℕ → ℝ) (T₀ : ℕ),
        G.IsDiscountedStationaryBellmanSchedule β x V ∧
          (∀ t, β t < 1) ∧ G.IsScheduledFinkSwitchBound β V e ∧
          (∀ t s who, |G.scheduledFinkBias β V t s who| ≤ B t) ∧
          (∀ t s who, |V t s who - W s who| ≤ q t) ∧
          (∀ t s who, |R t s who| ≤ c t) ∧
          (∀ t s who,
            |expect (pmfPi (x t s)) (fun a =>
                expect (G.transition s a)
                  (fun s' => W s' who + R (t + 1) s' who)) -
              (W s who + R t s who)| ≤ r t) ∧
          (∀ t s who (d : PMF (G.Act who)),
            expect (pmfPi (Function.update (x t s) who d)) (fun a =>
                expect (G.transition s a)
                  (fun s' => W s' who + R (t + 1) s' who)) ≤
              W s who + R t s who + r t) ∧
          ∀ T, T₀ ≤ T → 0 < T ∧
            ((B 0 + B T) / (T : ℝ) +
              (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤ η) ∧
            (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
              (q t + c 0 + c t +
                ∑ k ∈ Finset.range t, r k) ≤ η) :
    G.IsUniformScheduledMarkovEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformScheduledMarkovEquilibriumPayoff_of_scheduledFink_targetAverages
    s₀ (W s₀)
  intro η hη
  obtain ⟨β, x, V, R, e, B, q, c, r, T₀,
      hF, hβ1, hswitch, hbias, hclose, hR,
      hharmonic, hexcessive, hasymp⟩ := hcert η hη
  refine ⟨β, x, V, e, B, T₀, hF, hβ1, hswitch, hbias, ?_⟩
  intro T hT
  obtain ⟨hTpos, hboundary, htarget⟩ := hasymp T hT
  refine ⟨hTpos, hboundary, ?_, ?_⟩
  · intro who
    exact (G.scheduled_targetAverage_close_initial_of_correction
      x V W R q c r who s₀ (fun t s => hclose t s who)
      (fun t s => hR t s who) (fun t s => hharmonic t s who) hTpos).trans
        htarget
  · intro who dev
    have hdev := G.scheduled_deviation_targetAverage_le_initial_of_correction
      x V W R q c r who dev s₀ (fun t s => hclose t s who)
        (fun t s => hR t s who)
        (fun t s d => hexcessive t s who d) hTpos
    linarith

/-- Witness-preserving version of the corrected indexed-Fink endpoint.  Thus
`IsIndexedFinkCorrectedCalendarSelectable` implies a uniform payoff realized
by strategies depending only on time and current state. -/
theorem isUniformScheduledMarkovEquilibriumPayoff_of_indexedFinkFixedPoints_correctedTarget
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s₀ : G.State) (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hW : ∀ s who, |W s who| ≤ U)
    (R : ℕ → G.State → Payoff ι) (q : ℕ → ℝ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hclose : ∀ n s who, |G.finkValue (z n) s who - W s who| ≤ q n)
    (hselect : G.IsIndexedFinkCorrectedCalendarSelectable
      β U z W R q) :
    G.IsUniformScheduledMarkovEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformScheduledMarkovEquilibriumPayoff_of_scheduledFink_correctedTarget
    s₀ W
  intro η hη
  obtain ⟨κ, T₀, hκ⟩ := hselect η hη
  refine ⟨indexedFinkDiscount β κ, G.indexedFinkProfile z κ,
    G.indexedFinkValue z κ, R ∘ κ,
    G.indexedFinkRelativeSwitchError β U z W κ,
    (fun t => finkScaledBiasBound β U (κ t)),
    (q ∘ κ), (fun t => ‖R (κ t)‖),
    (fun t => G.finkCorrectedTargetStepError W (R ∘ κ) (z ∘ κ) t),
    T₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact G.isDiscountedStationaryBellmanSchedule_indexedFink
      β U hβ0 hβ1 hpay z hfix κ
  · exact fun t => hβ1 (κ t)
  · exact G.isScheduledFinkSwitchBound_indexed_relative β U z W hW κ
  · exact G.abs_scheduledFinkBias_indexed_le β U hβ0 hβ1 z κ
  · intro t s who
    exact hclose (κ t) s who
  · intro t s who
    exact G.abs_finkBiasCoordinate_le_norm (R (κ t)) s who
  · intro t s who
    exact G.abs_fink_correctedTarget_onProfile_step_le_stepError
      W (R ∘ κ) (z ∘ κ) t s who
  · intro t s who dev
    exact G.fink_correctedTarget_mixedDeviation_step_le_stepError
      W (R ∘ κ) (z ∘ κ) t s who dev
  · exact hκ

end StochasticGame
end GameTheory
