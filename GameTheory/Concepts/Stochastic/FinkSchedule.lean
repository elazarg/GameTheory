/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Fink

/-!
# Time-Varying Fink Certificates

This file is the verification layer needed after discounted stationary
equilibrium existence.  It permits the strategy and discounted Bellman
certificate to change with calendar time.  The change in the scaled bias

`βₜ / (1 - βₜ) * Vₜ`

is charged as an explicit switching error.  Consequently a schedule with
sublinear terminal bias and sublinear cumulative switching error yields the
same finite-horizon guarantees as one stationary certificate.

This is a direct interface for the block/phase constructions used in uniform
equilibrium arguments.  It does not assume the unresolved selection theorem
needed to construct such a schedule in a general multiplayer stochastic game.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct

variable {ι : Type}

/-- Play the stationary mixed profile `x t` during calendar stage `t`. -/
def scheduledMarkovBehaviorProfile (G : StochasticGame ι)
    (x : ℕ → G.StationaryMixedProfile) : G.BehaviorProfile :=
  fun i t h => x t h.2 i

@[simp] theorem stageActionDist_scheduledMarkovBehaviorProfile
    (G : StochasticGame ι) [Fintype ι]
    (x : ℕ → G.StationaryMixedProfile) {t : ℕ} (h : G.Hist t) :
    G.stageActionDist (G.scheduledMarkovBehaviorProfile x) h =
      pmfPi (x t h.2) :=
  rfl

/-- A unilateral behavior deviation changes only the deviator's current
mixed action in a scheduled Markov profile. -/
theorem stageActionDist_update_scheduledMarkovBehaviorProfile
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (x : ℕ → G.StationaryMixedProfile) (who : ι)
    (dev : G.BehaviorStrategy who) {t : ℕ} (h : G.Hist t) :
    G.stageActionDist
        (Function.update (G.scheduledMarkovBehaviorProfile x) who dev) h =
      pmfPi (Function.update (x t h.2) who (dev t h)) := by
  unfold stageActionDist
  congr 1
  funext j
  by_cases hj : j = who
  · subst hj
    simp
  · simp [Function.update_of_ne hj, scheduledMarkovBehaviorProfile]

/-- A calendar-time family of Fink discounted stationary Bellman
certificates. -/
def IsDiscountedStationaryBellmanSchedule (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] (β : ℕ → ℝ)
    (x : ℕ → G.StationaryMixedProfile)
    (V : ℕ → G.State → Payoff ι) : Prop :=
  ∀ t, G.IsDiscountedStationaryBellmanEq (β t) (x t) (V t)

/-- The average-reward bias associated with the discounted certificate at
calendar stage `t`. -/
def scheduledFinkBias (G : StochasticGame ι) (β : ℕ → ℝ)
    (V : ℕ → G.State → Payoff ι) (t : ℕ) (s : G.State) (who : ι) : ℝ :=
  (β t / (1 - β t)) * V t s who

/-- `e t` bounds the pointwise change in scaled bias between two consecutive
certificates. -/
def IsScheduledFinkSwitchBound (G : StochasticGame ι)
    (β : ℕ → ℝ) (V : ℕ → G.State → Payoff ι) (e : ℕ → ℝ) : Prop :=
  ∀ t s who,
    |G.scheduledFinkBias β V (t + 1) s who -
      G.scheduledFinkBias β V t s who| ≤ e t

theorem IsScheduledFinkSwitchBound.nonneg
    {G : StochasticGame ι} {β : ℕ → ℝ}
    {V : ℕ → G.State → Payoff ι} {e : ℕ → ℝ}
    (hswitch : G.IsScheduledFinkSwitchBound β V e)
    (t : ℕ) (s : G.State) (who : ι) : 0 ≤ e t :=
  le_trans (abs_nonneg _) (hswitch t s who)

/-- Replacing the current bias by the next scheduled bias in a one-step
continuation expectation costs at most `e t`. -/
theorem IsScheduledFinkSwitchBound.expect_current_le_succ_add
    {G : StochasticGame ι} [Finite ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    {β : ℕ → ℝ} {V : ℕ → G.State → Payoff ι} {e : ℕ → ℝ}
    (hswitch : G.IsScheduledFinkSwitchBound β V e)
    (who : ι) (t : ℕ) (s : G.State) (d : PMF G.JointAct) :
    expect d (fun a => expect (G.transition s a)
        (fun s' => G.scheduledFinkBias β V t s' who)) ≤
      expect d (fun a => expect (G.transition s a)
        (fun s' => G.scheduledFinkBias β V (t + 1) s' who)) + e t := by
  have hinner : ∀ a : G.JointAct,
      expect (G.transition s a)
          (fun s' => G.scheduledFinkBias β V t s' who) ≤
        expect (G.transition s a)
          (fun s' => G.scheduledFinkBias β V (t + 1) s' who) + e t := by
    intro a
    calc
      expect (G.transition s a)
          (fun s' => G.scheduledFinkBias β V t s' who)
          ≤ expect (G.transition s a) (fun s' =>
              G.scheduledFinkBias β V (t + 1) s' who + e t) :=
        expect_mono _ _ _ fun s' => by
          have hs := (abs_le.mp (hswitch t s' who)).1
          linarith
      _ = expect (G.transition s a)
            (fun s' => G.scheduledFinkBias β V (t + 1) s' who) + e t := by
        rw [expect_add, expect_const]
  calc
    expect d (fun a => expect (G.transition s a)
        (fun s' => G.scheduledFinkBias β V t s' who))
        ≤ expect d (fun a =>
            expect (G.transition s a)
              (fun s' => G.scheduledFinkBias β V (t + 1) s' who) + e t) :=
      expect_mono _ _ _ hinner
    _ = expect d (fun a => expect (G.transition s a)
          (fun s' => G.scheduledFinkBias β V (t + 1) s' who)) + e t := by
      rw [expect_add, expect_const]

/-- The reverse one-step comparison, also with switching cost `e t`. -/
theorem IsScheduledFinkSwitchBound.expect_succ_le_current_add
    {G : StochasticGame ι} [Finite ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    {β : ℕ → ℝ} {V : ℕ → G.State → Payoff ι} {e : ℕ → ℝ}
    (hswitch : G.IsScheduledFinkSwitchBound β V e)
    (who : ι) (t : ℕ) (s : G.State) (d : PMF G.JointAct) :
    expect d (fun a => expect (G.transition s a)
        (fun s' => G.scheduledFinkBias β V (t + 1) s' who)) ≤
      expect d (fun a => expect (G.transition s a)
        (fun s' => G.scheduledFinkBias β V t s' who)) + e t := by
  have hinner : ∀ a : G.JointAct,
      expect (G.transition s a)
          (fun s' => G.scheduledFinkBias β V (t + 1) s' who) ≤
        expect (G.transition s a)
          (fun s' => G.scheduledFinkBias β V t s' who) + e t := by
    intro a
    calc
      expect (G.transition s a)
          (fun s' => G.scheduledFinkBias β V (t + 1) s' who)
          ≤ expect (G.transition s a) (fun s' =>
              G.scheduledFinkBias β V t s' who + e t) :=
        expect_mono _ _ _ fun s' => by
          have hs := (abs_le.mp (hswitch t s' who)).2
          linarith
      _ = expect (G.transition s a)
            (fun s' => G.scheduledFinkBias β V t s' who) + e t := by
        rw [expect_add, expect_const]
  calc
    expect d (fun a => expect (G.transition s a)
        (fun s' => G.scheduledFinkBias β V (t + 1) s' who))
        ≤ expect d (fun a =>
            expect (G.transition s a)
              (fun s' => G.scheduledFinkBias β V t s' who) + e t) :=
      expect_mono _ _ _ hinner
    _ = expect d (fun a => expect (G.transition s a)
          (fun s' => G.scheduledFinkBias β V t s' who)) + e t := by
      rw [expect_add, expect_const]

/-- Scheduled Fink equalities give the time-varying average-reward lower
Bellman inequality, with the bias switch charged to `e t`. -/
theorem IsDiscountedStationaryBellmanSchedule.onProfile_averageReward_bellman_le
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℕ → ℝ} {x : ℕ → G.StationaryMixedProfile}
    {V : ℕ → G.State → Payoff ι} {e : ℕ → ℝ}
    (hF : G.IsDiscountedStationaryBellmanSchedule β x V)
    (hβ1 : ∀ t, β t < 1) (hswitch : G.IsScheduledFinkSwitchBound β V e)
    (who : ι) (t : ℕ) (h : G.Hist t) :
    V t h.2 who + G.scheduledFinkBias β V t h.2 who ≤
      G.stageEUAt (G.scheduledMarkovBehaviorProfile x) h who +
        expect (G.stageActionDist (G.scheduledMarkovBehaviorProfile x) h)
          (fun a => expect (G.transition h.2 a)
            (fun s' => G.scheduledFinkBias β V (t + 1) s' who)) + e t := by
  have hdisc : ∀ (u : ℕ) (hist : G.Hist u),
      V t hist.2 who ≤
        (1 - β t) * G.stageEUAt (G.markovBehaviorProfile (x t)) hist who +
          β t * expect
            (G.stageActionDist (G.markovBehaviorProfile (x t)) hist)
            (fun a => expect (G.transition hist.2 a) (fun s' => V t s' who)) := by
    intro u hist
    exact le_of_eq ((hF t).onProfile_bellman_eq who u hist)
  have havg := G.averageReward_bellman_le_of_discounted_bellman_le
    (G.markovBehaviorProfile (x t)) who (fun s => V t s who)
      (hβ1 t) (δ := 0) (fun u hist => by simpa using hdisc u hist) t h
  have hswitchE := hswitch.expect_current_le_succ_add who t h.2
    (G.stageActionDist (G.scheduledMarkovBehaviorProfile x) h)
  dsimp [scheduledFinkBias] at hswitchE ⊢
  have havg' : V t h.2 who + (β t / (1 - β t)) * V t h.2 who ≤
      G.stageEUAt (G.scheduledMarkovBehaviorProfile x) h who +
        expect (pmfPi (x t h.2))
          (fun a => expect (G.transition h.2 a)
            (fun s' => (β t / (1 - β t)) * V t s' who)) := by
    simpa [stageEUAt, scheduledMarkovBehaviorProfile,
      markovBehaviorProfile] using havg
  linarith

/-- The same scheduled certificates give an average-reward upper Bellman
inequality against every history-dependent unilateral deviation. -/
theorem IsDiscountedStationaryBellmanSchedule.deviation_averageReward_bellman_ge
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℕ → ℝ} {x : ℕ → G.StationaryMixedProfile}
    {V : ℕ → G.State → Payoff ι} {e : ℕ → ℝ}
    (hF : G.IsDiscountedStationaryBellmanSchedule β x V)
    (hβ1 : ∀ t, β t < 1) (hswitch : G.IsScheduledFinkSwitchBound β V e)
    (who : ι) (dev : G.BehaviorStrategy who) (t : ℕ) (h : G.Hist t) :
    G.stageEUAt
          (Function.update (G.scheduledMarkovBehaviorProfile x) who dev) h who +
        expect
          (G.stageActionDist
            (Function.update (G.scheduledMarkovBehaviorProfile x) who dev) h)
          (fun a => expect (G.transition h.2 a)
            (fun s' => G.scheduledFinkBias β V (t + 1) s' who)) ≤
      V t h.2 who + G.scheduledFinkBias β V t h.2 who + e t := by
  have hdisc : ∀ (u : ℕ) (hist : G.Hist u),
      (1 - β t) * G.stageEUAt
          (Function.update (G.markovBehaviorProfile (x t)) who dev) hist who +
        β t * expect
          (G.stageActionDist
            (Function.update (G.markovBehaviorProfile (x t)) who dev) hist)
          (fun a => expect (G.transition hist.2 a) (fun s' => V t s' who)) ≤
        V t hist.2 who := by
    intro u hist
    exact (hF t).deviation_bellman_ge who dev u hist
  have havg := G.averageReward_bellman_ge_of_discounted_bellman_ge
    (Function.update (G.markovBehaviorProfile (x t)) who dev)
      who (fun s => V t s who) (hβ1 t) (δ := 0)
      (fun u hist => by simpa using hdisc u hist) t h
  have hswitchE := hswitch.expect_succ_le_current_add who t h.2
    (G.stageActionDist
      (Function.update (G.scheduledMarkovBehaviorProfile x) who dev) h)
  dsimp [scheduledFinkBias] at hswitchE ⊢
  unfold stageEUAt at havg ⊢
  rw [G.stageActionDist_update_markovBehaviorProfile] at havg
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile] at hswitchE ⊢
  simp only [zero_div, add_zero] at havg
  linarith

/-- On-path upper Bellman inequality for the scheduled profile. -/
theorem IsDiscountedStationaryBellmanSchedule.onProfile_averageReward_bellman_ge
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℕ → ℝ} {x : ℕ → G.StationaryMixedProfile}
    {V : ℕ → G.State → Payoff ι} {e : ℕ → ℝ}
    (hF : G.IsDiscountedStationaryBellmanSchedule β x V)
    (hβ1 : ∀ t, β t < 1) (hswitch : G.IsScheduledFinkSwitchBound β V e)
    (who : ι) (t : ℕ) (h : G.Hist t) :
    G.stageEUAt (G.scheduledMarkovBehaviorProfile x) h who +
        expect (G.stageActionDist (G.scheduledMarkovBehaviorProfile x) h)
          (fun a => expect (G.transition h.2 a)
            (fun s' => G.scheduledFinkBias β V (t + 1) s' who)) ≤
      V t h.2 who + G.scheduledFinkBias β V t h.2 who + e t := by
  have hdev := hF.deviation_averageReward_bellman_ge hβ1 hswitch who
    (G.scheduledMarkovBehaviorProfile x who) t h
  simpa using hdev

/-- Quantitative lower finite-horizon payoff bound for a scheduled family of
Fink certificates.  Only the initial bias, terminal bias, and accumulated
switching errors survive telescoping. -/
theorem IsDiscountedStationaryBellmanSchedule.finiteAveragePayoff_ge
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℕ → ℝ} {x : ℕ → G.StationaryMixedProfile}
    {V : ℕ → G.State → Payoff ι} {e B : ℕ → ℝ}
    (hF : G.IsDiscountedStationaryBellmanSchedule β x V)
    (hβ1 : ∀ t, β t < 1) (hswitch : G.IsScheduledFinkSwitchBound β V e)
    (who : ι) (s₀ : G.State) (v : ℝ) {η : ℝ}
    (hclose : ∀ t s, |V t s who - v| ≤ η)
    (hbias : ∀ t s, |G.scheduledFinkBias β V t s who| ≤ B t)
    {T : ℕ} (hT : 0 < T) :
    v - η - (B 0 + B T) / (T : ℝ) -
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤
      G.finiteAveragePayoff s₀ T (G.scheduledMarkovBehaviorProfile x) who := by
  apply G.finiteAveragePayoff_ge_of_averageReward_bellman_le_endpoints
    (G.scheduledMarkovBehaviorProfile x) s₀ who
    (fun t s => V t s who)
    (fun t s => G.scheduledFinkBias β V t s who) e
    (c := v - η) (C0 := B 0) (CT := B T)
  · intro t s
    have hs := (abs_le.mp (hclose t s)).1
    linarith
  · exact hbias 0
  · exact hbias T
  · exact hF.onProfile_averageReward_bellman_le hβ1 hswitch who
  · exact hT

/-- Matching upper finite-horizon payoff bound on the scheduled profile. -/
theorem IsDiscountedStationaryBellmanSchedule.finiteAveragePayoff_le
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℕ → ℝ} {x : ℕ → G.StationaryMixedProfile}
    {V : ℕ → G.State → Payoff ι} {e B : ℕ → ℝ}
    (hF : G.IsDiscountedStationaryBellmanSchedule β x V)
    (hβ1 : ∀ t, β t < 1) (hswitch : G.IsScheduledFinkSwitchBound β V e)
    (who : ι) (s₀ : G.State) (v : ℝ) {η : ℝ}
    (hclose : ∀ t s, |V t s who - v| ≤ η)
    (hbias : ∀ t s, |G.scheduledFinkBias β V t s who| ≤ B t)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T (G.scheduledMarkovBehaviorProfile x) who ≤
      v + η + (B 0 + B T) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
  apply G.finiteAveragePayoff_le_of_averageReward_bellman_ge_endpoints
    (G.scheduledMarkovBehaviorProfile x) s₀ who
    (fun t s => V t s who)
    (fun t s => G.scheduledFinkBias β V t s who) e
    (c := v + η) (C0 := B 0) (CT := B T)
  · intro t s
    have hs := (abs_le.mp (hclose t s)).2
    linarith
  · exact hbias 0
  · exact hbias T
  · exact hF.onProfile_averageReward_bellman_ge hβ1 hswitch who
  · exact hT

/-- Every history-dependent unilateral deviation obeys the same scheduled
upper bound. -/
theorem IsDiscountedStationaryBellmanSchedule.deviation_finiteAveragePayoff_le
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℕ → ℝ} {x : ℕ → G.StationaryMixedProfile}
    {V : ℕ → G.State → Payoff ι} {e B : ℕ → ℝ}
    (hF : G.IsDiscountedStationaryBellmanSchedule β x V)
    (hβ1 : ∀ t, β t < 1) (hswitch : G.IsScheduledFinkSwitchBound β V e)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State) (v : ℝ)
    {η : ℝ} (hclose : ∀ t s, |V t s who - v| ≤ η)
    (hbias : ∀ t s, |G.scheduledFinkBias β V t s who| ≤ B t)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T
        (Function.update (G.scheduledMarkovBehaviorProfile x) who dev) who ≤
      v + η + (B 0 + B T) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
  apply G.finiteAveragePayoff_le_of_averageReward_bellman_ge_endpoints
    (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
    s₀ who (fun t s => V t s who)
    (fun t s => G.scheduledFinkBias β V t s who) e
    (c := v + η) (C0 := B 0) (CT := B T)
  · intro t s
    have hs := (abs_le.mp (hclose t s)).2
    linarith
  · exact hbias 0
  · exact hbias T
  · exact hF.deviation_averageReward_bellman_ge hβ1 hswitch who dev
  · exact hT

/-- A direct schedule-to-uniform-payoff criterion.  It reduces the unresolved
existence theorem to constructing, at every precision, one infinite schedule
of Fink certificates whose values stay close to `v` and whose terminal bias
plus cumulative switching loss is sublinear. -/
theorem isUniformEquilibriumPayoff_of_scheduledFink_certificates
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι)
    (hcert : ∀ η : ℝ, 0 < η →
      ∃ (β : ℕ → ℝ) (x : ℕ → G.StationaryMixedProfile)
        (V : ℕ → G.State → Payoff ι) (e B : ℕ → ℝ) (T₀ : ℕ),
        G.IsDiscountedStationaryBellmanSchedule β x V ∧
          (∀ t, β t < 1) ∧ G.IsScheduledFinkSwitchBound β V e ∧
          (∀ t s who, |V t s who - v who| ≤ η) ∧
          (∀ t s who, |G.scheduledFinkBias β V t s who| ≤ B t) ∧
          ∀ T, T₀ ≤ T → 0 < T ∧
            (B 0 + B T) / (T : ℝ) +
              (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤ η) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ v
  intro δ hδ
  have hη : 0 < δ / 2 := by linarith
  obtain ⟨β, x, V, e, B, T₀, hF, hβ1, hswitch,
      hclose, hbias, hasymp⟩ := hcert (δ / 2) hη
  refine ⟨G.scheduledMarkovBehaviorProfile x, T₀, fun T hT => ?_⟩
  obtain ⟨hTpos, herr⟩ := hasymp T hT
  constructor
  · intro who
    have hlo := hF.finiteAveragePayoff_ge hβ1 hswitch who s₀ (v who)
      (fun t s => hclose t s who) (fun t s => hbias t s who) hTpos
    have hup := hF.finiteAveragePayoff_le hβ1 hswitch who s₀ (v who)
      (fun t s => hclose t s who) (fun t s => hbias t s who) hTpos
    rw [abs_le]
    constructor <;> linarith
  · intro who dev
    have hup := hF.deviation_finiteAveragePayoff_le hβ1 hswitch
      who dev s₀ (v who) (fun t s => hclose t s who)
      (fun t s => hbias t s who) hTpos
    linarith

end StochasticGame
end GameTheory
