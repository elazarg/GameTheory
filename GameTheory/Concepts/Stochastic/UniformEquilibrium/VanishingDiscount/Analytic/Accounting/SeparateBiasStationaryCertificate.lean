/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Fink.Limit

/-!
# Stationary Average-Reward Certificates with Separate Biases

A stationary average-reward verification argument does not require the same
bias for both sides of the prescribed payoff estimate.  One bias may certify
the lower Bellman inequality, while a second bias certifies the upper
on-profile inequality and every unilateral-deviation inequality.  Both biases
contribute only bounded endpoint terms.

The second theorem packages a common source of the upper bias.  Starting from
an on-profile bias equation for `B`, a function `C` with nonnegative baseline
drift makes `B - C` an upper on-profile bias.  If deviations satisfy the
corresponding corrected inequality, the separate-bias verifier applies.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type}

/-- A stationary average-reward certificate may use distinct lower and upper
biases.  The lower bias controls only the prescribed payoff from below.  The
upper bias controls the prescribed payoff and every unilateral deviation from
above. -/
theorem isUniformEquilibriumPayoff_of_stationaryAverageRewardSeparateBias
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (s₀ : G.State)
    (x : G.StationaryMixedProfile)
    (W Hlo Hhi : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (dev : PMF (G.Act who)),
      expect (pmfPi (Function.update (x s) who dev)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (honProfileLower : ∀ s who,
      W s who + Hlo s who ≤ G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => Hlo s' who)))
    (honProfileUpper : ∀ s who,
      G.mixedStageEU s (x s) who +
          expect (pmfPi (x s)) (fun a =>
            expect (G.transition s a) (fun s' => Hhi s' who)) ≤
        W s who + Hhi s who)
    (hdeviation : ∀ s who (dev : PMF (G.Act who)),
      G.mixedStageEU s (Function.update (x s) who dev) who +
          expect (pmfPi (Function.update (x s) who dev)) (fun a =>
            expect (G.transition s a) (fun s' => Hhi s' who)) ≤
        W s who + Hhi s who) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : ∀ i, Fintype (G.Act i) := fun i => Fintype.ofFinite (G.Act i)
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ (W s₀)
  intro δ hδ
  let xConst : ℕ → G.StationaryMixedProfile := fun _ => x
  let σ := G.scheduledMarkovBehaviorProfile xConst
  let C : ℝ := max ‖Hlo‖ ‖Hhi‖
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * C / δ)
  refine ⟨σ, N + 1, ?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le (Nat.zero_lt_succ N) hT
  have hTreal : (0 : ℝ) < T := by
    exact_mod_cast hTpos
  have hNT : (N : ℝ) ≤ T := by
    exact_mod_cast (Nat.le_trans (Nat.le_succ N) hT)
  have hratio : 2 * C / δ ≤ (T : ℝ) := hN.trans hNT
  have hboundary : 2 * C / (T : ℝ) ≤ δ := by
    rw [div_le_iff₀ hTreal]
    have hδT : 2 * C ≤ δ * (T : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hδ).mp hratio
    nlinarith
  have hHloBound : ∀ t s who, |(fun _ : ℕ => Hlo) t s who| ≤ C :=
    fun _ s who =>
      (G.abs_finkBiasCoordinate_le_norm Hlo s who).trans
        (le_max_left _ _)
  have hHhiBound : ∀ t s who, |(fun _ : ℕ => Hhi) t s who| ≤ C :=
    fun _ s who =>
      (G.abs_finkBiasCoordinate_le_norm Hhi s who).trans
        (le_max_right _ _)
  have htarget : ∀ who,
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.expectedStateValue σ s₀ t (fun s => W s who) =
        W s₀ who := by
    intro who
    have hclose := G.scheduled_targetAverage_close_initial
      xConst (fun _ => W) W (fun _ => 0) (fun _ => 0) who s₀
      (fun _ _ => by simp)
      (fun _ s => by rw [← hharmonic s]; simp) hTpos
    have hzero : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ((fun _ : ℕ => 0) t +
          ∑ k ∈ Finset.range t, (fun _ : ℕ => 0) k) = 0 := by
      simp
    rw [hzero] at hclose
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hclose (abs_nonneg _)))
  constructor
  · intro who
    have hlo :=
      G.finiteAveragePayoff_ge_targetAverage_of_averageReward_bellman_le
        σ s₀ who (fun _ s => W s who) (fun _ s => Hlo s who)
          (fun _ => 0) (C0 := C) (CT := C)
          (hHloBound 0 · who) (hHloBound T · who) (fun t h => by
            change W h.2 who + Hlo h.2 who ≤
              G.mixedStageEU h.2 (x h.2) who +
                expect (pmfPi (x h.2)) (fun a =>
                  expect (G.transition h.2 a) (fun s' => Hlo s' who)) + 0
            linarith [honProfileLower h.2 who]) hTpos
    have hup :=
      G.finiteAveragePayoff_le_targetAverage_of_averageReward_bellman_ge
        σ s₀ who (fun _ s => W s who) (fun _ s => Hhi s who)
          (fun _ => 0) (C0 := C) (CT := C)
          (hHhiBound 0 · who) (hHhiBound T · who) (fun t h => by
            change G.mixedStageEU h.2 (x h.2) who +
                  expect (pmfPi (x h.2)) (fun a =>
                    expect (G.transition h.2 a) (fun s' => Hhi s' who)) ≤
                W h.2 who + Hhi h.2 who + 0
            linarith [honProfileUpper h.2 who]) hTpos
    rw [htarget who] at hlo hup
    simp only [add_zero, Finset.sum_const_zero, mul_zero] at hlo hup
    have hboundary' : (C + C) / (T : ℝ) ≤ δ := by
      simpa only [two_mul] using hboundary
    rw [abs_le]
    constructor <;> linarith
  · intro who dev
    have hexcessiveConst : ∀ t s (d : PMF (G.Act who)),
        expect (pmfPi (Function.update (xConst t s) who d)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) ≤
            W s who + (fun _ : ℕ => 0) t := by
      intro t s d
      simpa only [xConst, add_zero] using hexcessive s who d
    have htargetDev := G.scheduled_deviation_targetAverage_le_initial
      xConst (fun _ => W) W (fun _ => 0) (fun _ => 0) who dev s₀
      (fun _ _ => by simp)
      hexcessiveConst hTpos
    have hup :=
      G.finiteAveragePayoff_le_targetAverage_of_averageReward_bellman_ge
        (Function.update σ who dev) s₀ who
          (fun _ s => W s who) (fun _ s => Hhi s who) (fun _ => 0)
          (C0 := C) (CT := C) (hHhiBound 0 · who)
          (hHhiBound T · who) (fun t h => by
            unfold stageEUAt
            rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
            dsimp only [xConst]
            change G.mixedStageEU h.2
                  (Function.update (x h.2) who (dev t h)) who +
                expect (pmfPi (Function.update (x h.2) who (dev t h)))
                  (fun a => expect (G.transition h.2 a)
                    (fun s' => Hhi s' who)) ≤
              W h.2 who + Hhi h.2 who + 0
            linarith [hdeviation h.2 who (dev t h)]) hTpos
    simp only [Finset.sum_const_zero, add_zero, mul_zero] at htargetDev hup
    have hboundary' : (C + C) / (T : ℝ) ≤ δ := by
      simpa only [two_mul] using hboundary
    linarith

/-- For a separate upper bias, it is enough to check pure deviations that
preserve the harmonic target.  A sufficiently large multiple of the target is
added only to the upper bias; the lower bias is unchanged. -/
theorem isUniformEquilibriumPayoff_of_stationaryAverageRewardSeparateBias_on_neutral
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (s₀ : G.State)
    (x : G.StationaryMixedProfile)
    (W Hlo Hhi : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (honProfileLower : ∀ s who,
      W s who + Hlo s who ≤ G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => Hlo s' who)))
    (honProfileUpper : ∀ s who,
      G.mixedStageEU s (x s) who +
          expect (pmfPi (x s)) (fun a =>
            expect (G.transition s a) (fun s' => Hhi s' who)) ≤
        W s who + Hhi s who)
    (hneutral : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) = W s who →
        G.mixedStageEU s
              (Function.update (x s) who (PMF.pure d)) who +
            expect (pmfPi (Function.update (x s) who (PMF.pure d)))
              (fun a => expect (G.transition s a) (fun s' => Hhi s' who)) ≤
          W s who + Hhi s who) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  let D := Σ p : G.State × ι, G.Act p.2
  let base : D → ℝ := fun q =>
    G.mixedStageEU q.1.1
          (Function.update (x q.1.1) q.1.2 (PMF.pure q.2)) q.1.2 +
      expect (pmfPi (Function.update (x q.1.1) q.1.2 (PMF.pure q.2)))
        (fun a => expect (G.transition q.1.1 a) (fun s' => Hhi s' q.1.2)) -
      (W q.1.1 q.1.2 + Hhi q.1.1 q.1.2)
  obtain ⟨B, hB⟩ := Math.Probability.exists_abs_bound_of_finite base
  obtain ⟨δ, hδ, hgap⟩ := G.exists_uniform_strictContinuationGap x W
  let c : ℝ := (|B| + 1) / δ
  let Hhi' : G.State → Payoff ι :=
    fun s who => Hhi s who + c * W s who
  have hc0 : 0 ≤ c := div_nonneg (by positivity) hδ.le
  have hcδ : c * δ = |B| + 1 := by
    dsimp only [c]
    field_simp
  have hcontAdd : ∀ s (mu : PMF G.JointAct) who,
      expect mu (fun a =>
          expect (G.transition s a) (fun s' => Hhi' s' who)) =
        expect mu (fun a =>
          expect (G.transition s a) (fun s' => Hhi s' who)) +
          c * expect mu (fun a =>
            expect (G.transition s a) (fun s' => W s' who)) := by
    intro s mu who
    dsimp only [Hhi']
    simp_rw [expect_add, expect_const_mul]
  have hpure : ∀ s who (d : G.Act who),
      G.mixedStageEU s
            (Function.update (x s) who (PMF.pure d)) who +
          expect (pmfPi (Function.update (x s) who (PMF.pure d)))
            (fun a => expect (G.transition s a) (fun s' => Hhi' s' who)) ≤
        W s who + Hhi' s who := by
    intro s who d
    let contW := expect
      (pmfPi (Function.update (x s) who (PMF.pure d)))
      (fun a => expect (G.transition s a) (fun s' => W s' who))
    rw [hcontAdd]
    change G.mixedStageEU s
          (Function.update (x s) who (PMF.pure d)) who +
        (expect (pmfPi (Function.update (x s) who (PMF.pure d)))
            (fun a => expect (G.transition s a) (fun s' => Hhi s' who)) +
          c * contW) ≤ W s who + (Hhi s who + c * W s who)
    by_cases hstrict : contW < W s who
    · have hgap' := hgap s who d hstrict
      have hbaseUpper : base ⟨(s, who), d⟩ ≤ |B| :=
        (le_abs_self _).trans ((hB ⟨(s, who), d⟩).trans (le_abs_self B))
      have hcLoss : c * (contW - W s who) ≤ c * (-δ) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        dsimp only [contW] at hgap' ⊢
        linarith
      dsimp only [base] at hbaseUpper
      linarith
    · have heq : contW = W s who := by
        apply le_antisymm
        · exact hexcessive s who d
        · exact le_of_not_gt hstrict
      have hn := hneutral s who d (by simpa only [contW] using heq)
      rw [heq]
      linarith
  have hmixedExcessive : ∀ s who (dev : PMF (G.Act who)),
      expect (pmfPi (Function.update (x s) who dev)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who := by
    intro s who dev
    exact G.mixedDeviationContinuation_le_of_pure_bound
      x W s who (W s who) (hexcessive s who) dev
  have honProfileUpper' : ∀ s who,
      G.mixedStageEU s (x s) who +
          expect (pmfPi (x s)) (fun a =>
            expect (G.transition s a) (fun s' => Hhi' s' who)) ≤
        W s who + Hhi' s who := by
    intro s who
    rw [hcontAdd]
    rw [← hharmonic s who]
    dsimp only [Hhi']
    linarith [honProfileUpper s who]
  have hmixed : ∀ s who (dev : PMF (G.Act who)),
      G.mixedStageEU s (Function.update (x s) who dev) who +
          expect (pmfPi (Function.update (x s) who dev)) (fun a =>
            expect (G.transition s a) (fun s' => Hhi' s' who)) ≤
        W s who + Hhi' s who := by
    intro s who dev
    calc
      G.mixedStageEU s (Function.update (x s) who dev) who +
            expect (pmfPi (Function.update (x s) who dev)) (fun a =>
              expect (G.transition s a) (fun s' => Hhi' s' who)) =
          expect dev (fun d =>
            G.mixedStageEU s
                  (Function.update (x s) who (PMF.pure d)) who +
              expect (pmfPi (Function.update (x s) who (PMF.pure d)))
                (fun a => expect (G.transition s a)
                  (fun s' => Hhi' s' who))) := by
            unfold mixedStageEU
            rw [pmfPi_update_bind]
            rw [expect_bind, expect_bind, expect_add]
      _ ≤ expect dev (fun _ => W s who + Hhi' s who) :=
        expect_mono dev _ _ (hpure s who)
      _ = W s who + Hhi' s who := expect_const dev _
  exact
    G.isUniformEquilibriumPayoff_of_stationaryAverageRewardSeparateBias
      s₀ x W Hlo Hhi' hharmonic hmixedExcessive
      honProfileLower honProfileUpper' hmixed

/-- An on-profile bias equation for `B` and a nonnegative baseline drift for
`C` turn `B - C` into an upper bias.  A deviation inequality written directly
for that corrected bias therefore completes a separate-bias certificate. -/
theorem isUniformEquilibriumPayoff_of_stationaryAverageRewardBiasCorrection
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (s₀ : G.State)
    (x : G.StationaryMixedProfile)
    (W B C : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (dev : PMF (G.Act who)),
      expect (pmfPi (Function.update (x s) who dev)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (honProfile : ∀ s who,
      W s who + B s who = G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => B s' who)))
    (hbaselineDrift : ∀ s who,
      C s who ≤ expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => C s' who)))
    (hcorrectedDeviation : ∀ s who (dev : PMF (G.Act who)),
      G.mixedStageEU s (Function.update (x s) who dev) who +
          expect (pmfPi (Function.update (x s) who dev)) (fun a =>
            expect (G.transition s a) (fun s' => B s' who - C s' who)) ≤
        W s who + (B s who - C s who)) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_stationaryAverageRewardSeparateBias
    s₀ x W B (fun s who => B s who - C s who)
    hharmonic hexcessive
  · intro s who
    exact (honProfile s who).le
  · intro s who
    simp_rw [expect_sub]
    linarith [honProfile s who, hbaselineDrift s who]
  · exact hcorrectedDeviation

/-- The correction theorem needs to be checked only on target-neutral pure
deviations.  Strict target losses are absorbed by adding a multiple of `W` to
the corrected upper bias. -/
theorem
    isUniformEquilibriumPayoff_of_stationaryAverageRewardBiasCorrection_on_neutral
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (s₀ : G.State)
    (x : G.StationaryMixedProfile)
    (W B C : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (honProfile : ∀ s who,
      W s who + B s who = G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => B s' who)))
    (hbaselineDrift : ∀ s who,
      C s who ≤ expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => C s' who)))
    (hcorrectedNeutral : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) = W s who →
        G.mixedStageEU s
              (Function.update (x s) who (PMF.pure d)) who +
            expect (pmfPi (Function.update (x s) who (PMF.pure d)))
              (fun a => expect (G.transition s a)
                (fun s' => B s' who - C s' who)) ≤
          W s who + (B s who - C s who)) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply
    G.isUniformEquilibriumPayoff_of_stationaryAverageRewardSeparateBias_on_neutral
      s₀ x W B (fun s who => B s who - C s who)
      hharmonic hexcessive
  · intro s who
    exact (honProfile s who).le
  · intro s who
    simp_rw [expect_sub]
    linarith [honProfile s who, hbaselineDrift s who]
  · exact hcorrectedNeutral

end StochasticGame
end GameTheory
