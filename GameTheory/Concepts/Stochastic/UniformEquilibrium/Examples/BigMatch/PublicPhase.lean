/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Examples.BigMatch.Uniform
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.PhaseCertificate

/-!
# The Big Match as a public-phase certificate

This file is an acceptance test for the public-phase compiler.  The
Blackwell--Ferguson strategy is presented as a public controller whose phase
is the current state together with the observed net Right excess.  Its local
charge is the familiar stopping-probability cost minus one half of the
excess increment.  The two pathwise summation bounds from
`BigMatchUniform` give this charge a uniform vanishing Cesàro average.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace StochasticGame
namespace BigMatch

open Math.Probability Math.PMFProduct

/-- The fair continuation value of the maximizer at a Big Match state. -/
def fairMaxValue (s : State) : ℝ :=
  oneIndicator s + (1 / 2) * liveIndicator s

/-- `fairMaxValue`, read from the current state of a history. -/
def fairMaxHistoryPotential : game.HistoryPotential :=
  fun _ h => fairMaxValue h.2

/-- Against the fair minimizer, the maximizer's conditional stage payoff is
the fair continuation value at every history. -/
theorem stageEUAt_profileUniformMinimizer_eq_fairMaxValue
    (dev : game.BehaviorStrategy false) {t : ℕ} (h : game.Hist t) :
    game.stageEUAt (profileUniformMinimizer dev) h false = fairMaxValue h.2 := by
  unfold stageEUAt
  rw [stageActionDist_profileUniformMinimizer]
  have hthis := expect_stagePayoff_maximizer h.2
    (fun who => if who then uniformMinimizerStrategy t h else dev t h)
  simp only [Bool.false_eq_true, if_false, reduceIte] at hthis
  rw [uniformMinimizerStrategy_apply_true_toReal] at hthis
  rw [hthis]
  unfold fairMaxValue
  ring

/-- One step against the fair minimizer preserves `fairMaxValue`, regardless
of the maximizer's current mixed action. -/
theorem expect_next_fairMaxValue_uniformMinimizer
    (d : PMF Bool) (s : State) :
    expect (pmfPi (fun who => if who then
        coinPMF (1 / 2) (by norm_num) (by norm_num) else d))
      (fun a => expect (game.transition s a) fairMaxValue) =
        fairMaxValue s := by
  let m : Player → PMF Bool :=
    fun who => if who then coinPMF (1 / 2) (by norm_num) (by norm_num) else d
  have hone := expect_next_oneIndicator s m
  have hlive := expect_next_liveIndicator s m
  have hmtrue : (m true true).toReal = 1 / 2 := by
    simp only [m, if_true]
    exact coinPMF_apply_true_toReal (1 / 2) (by norm_num) (by norm_num)
  change expect (pmfPi m)
      (fun a => expect (game.transition s a) fairMaxValue) = fairMaxValue s
  have hsplit :
      expect (pmfPi m) (fun a => expect (game.transition s a) fairMaxValue) =
        expect (pmfPi m) (fun a =>
          expect (game.transition s a) oneIndicator) +
        (1 / 2) * expect (pmfPi m) (fun a =>
          expect (game.transition s a) liveIndicator) := by
    unfold fairMaxValue
    simp_rw [expect_add, expect_const_mul]
  rw [hsplit, hone, hlive, hmtrue]
  unfold fairMaxValue
  ring

/-- The fair state value is harmonic after every public history against the
fair minimizer. -/
theorem historyContinuationEU_fairMax_profileUniformMinimizer
    (dev : game.BehaviorStrategy false) {t : ℕ} (h : game.Hist t) :
    game.historyContinuationEU (profileUniformMinimizer dev)
        fairMaxHistoryPotential h = fairMaxValue h.2 := by
  unfold historyContinuationEU fairMaxHistoryPotential
  rw [stageActionDist_profileUniformMinimizer]
  simpa only [uniformMinimizerStrategy] using
    expect_next_fairMaxValue_uniformMinimizer (dev t h) h.2

/-- Negating a history potential negates its one-step continuation value. -/
theorem historyContinuationEU_neg (σ : game.BehaviorProfile)
    (V : game.HistoryPotential) {t : ℕ} (h : game.Hist t) :
    game.historyContinuationEU σ (fun t h => -V t h) h =
      -game.historyContinuationEU σ V h := by
  unfold historyContinuationEU
  simp_rw [expect_neg]

/-- The Blackwell--Ferguson pointwise submartingale step in
`historyContinuationEU` form. -/
theorem bfXPotential_le_historyContinuationEU (N : ℕ)
    (dev : game.BehaviorStrategy true) {t : ℕ} (h : game.Hist t) :
    bfXPotential N t h ≤
      game.historyContinuationEU (bfDevProfile N dev) (bfXPotential N) h := by
  unfold historyContinuationEU bfXPotential
  have hstep : ∀ a : game.JointAct,
      expect (game.transition h.2 a)
          (fun s' => bfX N ((Fin.snoc h.1 (h.2, a), s') :
            game.Hist (t + 1))) =
        bfX N ((Fin.snoc h.1 (h.2, a), nextState h.2 a) :
          game.Hist (t + 1)) := by
    intro a
    rw [transition_eq_pure, expect_pure]
  simp_rw [hstep]
  exact bfX_le_expect_step N dev h

/-- The compact public controller state used by Blackwell--Ferguson play. -/
abbrev BFPublicPhase := State × ℤ

/-- Blackwell--Ferguson play as a public-phase profile. -/
def bfPublicPhaseProfile (N : ℕ) : game.PublicPhaseProfile where
  Phase := BFPublicPhase
  phase := fun _ h => (h.2, netRightExcess h)
  play := fun p who =>
    if who then coinPMF (1 / 2) (by norm_num) (by norm_num)
    else coinPMF (bfStopProb N p.2)
      (bfStopProb_nonneg N p.2) (bfStopProb_le_one N p.2)

/-- The public-phase profile induces the usual equilibrium-path profile. -/
theorem bfPublicPhaseProfile_behaviorProfile (N : ℕ) :
    (bfPublicPhaseProfile N).behaviorProfile =
      profileUniformMinimizer (blackwellFergusonStrategy N) := by
  funext who t h
  cases who <;> rfl

/-- Fair value as a scalar on the compact public phase. -/
def fairMaxPhaseValue : BFPublicPhase → ℝ :=
  fun p => fairMaxValue p.1

/-- The Blackwell--Ferguson potential as a scalar on the compact phase. -/
def bfPhaseValue (N : ℕ) : BFPublicPhase → ℝ :=
  fun p =>
    (if p.1 = .one then 1 else 0) +
      (if p.1 = .live then bfPotential (bfDenom N p.2) else 0)

@[simp] theorem bfPublicPhaseProfile_fair_historyPotential (N : ℕ) :
    (bfPublicPhaseProfile N).historyPotential fairMaxPhaseValue =
      fairMaxHistoryPotential := rfl

@[simp] theorem bfPublicPhaseProfile_bf_historyPotential (N : ℕ) :
    (bfPublicPhaseProfile N).historyPotential (bfPhaseValue N) =
      bfXPotential N := rfl

/-- The equilibrium payoff, indexed by the Bool player convention. -/
def fairPayoff : Payoff Player :=
  fun who => if who then -(1 / 2) else 1 / 2

/-- The on-path phase potential for either player. -/
def fairPhasePayoff (who : Player) : BFPublicPhase → ℝ :=
  fun p => if who then -fairMaxPhaseValue p else fairMaxPhaseValue p

/-- The deviation potential.  The maximizer retains the fair state value;
the minimizer uses the negative Blackwell--Ferguson potential. -/
def bfDeviationPhasePayoff (N : ℕ) (who : Player) : BFPublicPhase → ℝ :=
  fun p => if who then -bfPhaseValue N p else fairMaxPhaseValue p

/-- The local Blackwell--Ferguson charge.  Only a minimizer deviation incurs
a charge; it is stopping mass minus one half of the conditional excess
increment. -/
def bfDeviationCharge (N : ℕ) :
    ∀ who, game.BehaviorStrategy who → game.HistoryPotential
  | false, _ => fun _ _ => 0
  | true, dev => fun t h =>
      liveIndicator h.2 * bfStopProb N (netRightExcess h) -
        (1 / 2) * (liveIndicator h.2 * (2 * (dev t h true).toReal - 1))

/-- The on-path phase payoff is harmonic under public-phase play. -/
theorem fairPhasePayoff_harmonic (N : ℕ) (who : Player)
    {t : ℕ} (h : game.Hist t) :
    (bfPublicPhaseProfile N).historyPotential (fairPhasePayoff who) t h =
      game.historyContinuationEU (bfPublicPhaseProfile N).behaviorProfile
        ((bfPublicPhaseProfile N).historyPotential (fairPhasePayoff who)) h := by
  rw [bfPublicPhaseProfile_behaviorProfile]
  cases who
  · change fairMaxValue h.2 =
      game.historyContinuationEU
        (profileUniformMinimizer (blackwellFergusonStrategy N))
        fairMaxHistoryPotential h
    rw [historyContinuationEU_fairMax_profileUniformMinimizer]
  · change -fairMaxValue h.2 =
      game.historyContinuationEU
        (profileUniformMinimizer (blackwellFergusonStrategy N))
        (fun t h => -fairMaxHistoryPotential t h) h
    rw [historyContinuationEU_neg,
      historyContinuationEU_fairMax_profileUniformMinimizer]

/-- The on-path phase payoff equals the conditional stage payoff. -/
theorem stageEUAt_bfPublicPhaseProfile_eq_fairPhasePayoff
    (N : ℕ) (who : Player) {t : ℕ} (h : game.Hist t) :
    game.stageEUAt (bfPublicPhaseProfile N).behaviorProfile h who =
      (bfPublicPhaseProfile N).historyPotential (fairPhasePayoff who) t h := by
  rw [bfPublicPhaseProfile_behaviorProfile]
  cases who
  · exact stageEUAt_profileUniformMinimizer_eq_fairMaxValue
      (blackwellFergusonStrategy N) h
  · rw [game_isZeroSumBoolGame.stageEUAt_true_eq_neg_false,
      stageEUAt_profileUniformMinimizer_eq_fairMaxValue]
    rfl

/-- The deviation phase payoff is superharmonic after every unilateral
behavior deviation. -/
theorem bfDeviationPhasePayoff_superharmonic (N : ℕ) (who : Player)
    (dev : game.BehaviorStrategy who) {t : ℕ} (h : game.Hist t) :
    game.historyContinuationEU
        (Function.update (bfPublicPhaseProfile N).behaviorProfile who dev)
        ((bfPublicPhaseProfile N).historyPotential
          (bfDeviationPhasePayoff N who)) h ≤
      (bfPublicPhaseProfile N).historyPotential
        (bfDeviationPhasePayoff N who) t h := by
  rw [bfPublicPhaseProfile_behaviorProfile]
  cases who
  · rw [update_profileUniformMinimizer_false]
    change game.historyContinuationEU (profileUniformMinimizer dev)
        fairMaxHistoryPotential h ≤ fairMaxValue h.2
    rw [historyContinuationEU_fairMax_profileUniformMinimizer]
  · rw [update_profileUniformMinimizer_true]
    change game.historyContinuationEU (bfDevProfile N dev)
        (fun t h => -bfXPotential N t h) h ≤ -bfXPotential N t h
    rw [historyContinuationEU_neg]
    linarith [bfXPotential_le_historyContinuationEU N dev h]

/-- The deviation phase payoff and local charge dominate the conditional
stage payoff after every unilateral behavior deviation. -/
theorem stageEUAt_deviation_le_bfDeviationPhasePayoff_add_charge
    (N : ℕ) (who : Player) (dev : game.BehaviorStrategy who)
    {t : ℕ} (h : game.Hist t) :
    game.stageEUAt
        (Function.update (bfPublicPhaseProfile N).behaviorProfile who dev) h who ≤
      (bfPublicPhaseProfile N).historyPotential
          (bfDeviationPhasePayoff N who) t h +
        bfDeviationCharge N who dev t h := by
  rw [bfPublicPhaseProfile_behaviorProfile]
  cases who
  · rw [update_profileUniformMinimizer_false,
      stageEUAt_profileUniformMinimizer_eq_fairMaxValue]
    change fairMaxValue h.2 ≤ fairMaxValue h.2 + 0
    linarith
  · rw [update_profileUniformMinimizer_true,
      game_isZeroSumBoolGame.stageEUAt_true_eq_neg_false]
    have hbf := stageEUAt_bfDevProfile_ge N dev h
    change -game.stageEUAt (bfDevProfile N dev) h false ≤
      -bfX N h +
        (liveIndicator h.2 * bfStopProb N (netRightExcess h) -
          (1 / 2) *
            (liveIndicator h.2 * (2 * (dev t h true).toReal - 1)))
    linarith

/-- The expected local charge is the difference of the two aggregate terms
already controlled in the Blackwell--Ferguson proof. -/
theorem expectedHistoryValue_bfDeviationCharge_true
    (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    game.expectedHistoryValue (bfDevProfile N dev) .live
        (bfDeviationCharge N true dev) t =
      bfLivePExpect N dev t - (1 / 2) * bfLiveDeltaExpect N dev t := by
  rw [bfLiveDeltaExpect_eq]
  unfold expectedHistoryValue bfDeviationCharge bfLivePExpect
  rw [expect_sub, expect_const_mul]

/-- The total expected local deviation charge has a horizon-independent
bound, uniformly over the deviating minimizer. -/
theorem sum_expectedHistoryValue_bfDeviationCharge_true_le
    (N : ℕ) (dev : game.BehaviorStrategy true) (T : ℕ) :
    (∑ t ∈ Finset.range T,
      game.expectedHistoryValue (bfDevProfile N dev) .live
        (bfDeviationCharge N true dev) t) ≤
      1 + ((N : ℝ) + 1) / 2 := by
  simp_rw [expectedHistoryValue_bfDeviationCharge_true]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [sum_bfLiveDeltaExpect_ge N dev T,
    sum_bfLivePExpect_le_one N dev T]

/-- Closed form of the initial Blackwell--Ferguson potential. -/
theorem bfPotential_succ_eq_half_sub (N : ℕ) :
    bfPotential (N + 1) =
      1 / 2 - 1 / (2 * ((N : ℝ) + 1)) := by
  unfold bfPotential
  push_cast
  have hN0 : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The Blackwell--Ferguson public controller, phase potentials, and local
charge form a public-phase punishment system at every positive error
level. -/
theorem isPublicPhasePunishmentSystemAt_fairPayoff
    (δ : ℝ) (hδ : 0 < δ) :
    game.IsPublicPhasePunishmentSystemAt .live fairPayoff δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hN' : (1 : ℝ) < (N : ℝ) * δ := by
    rw [div_lt_iff₀ hδ] at hN
    exact hN
  have hclose : 1 / (2 * ((N : ℝ) + 1)) ≤ δ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((N : ℝ) + 1))]
    nlinarith [hN', hδ]
  let B : ℝ := 1 + ((N : ℝ) + 1) / 2
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt (B / δ)
  have haverage : ∀ T : ℕ, max T₀ 2 ≤ T →
      (T : ℝ)⁻¹ * B ≤ δ := by
    intro T hT
    have hTposNat : 0 < T := lt_of_lt_of_le (by omega) hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hTposNat
    have hT₀T : T₀ ≤ T := le_trans (le_max_left T₀ 2) hT
    have hT₀Treal : (T₀ : ℝ) ≤ T := by exact_mod_cast hT₀T
    have hBT₀ : B < (T₀ : ℝ) * δ := by
      rw [div_lt_iff₀ hδ] at hT₀
      exact hT₀
    have hBT : B ≤ (T : ℝ) * δ := by
      exact le_trans hBT₀.le (mul_le_mul_of_nonneg_right hT₀Treal hδ.le)
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hTpos).2 (by nlinarith [hBT])
  have hphase0 :
      (bfPublicPhaseProfile N).phase 0 (game.emptyHist State.live) =
        (State.live, 0) := by
    apply Prod.ext
    · rfl
    · exact netRightExcess_zero (game.emptyHist State.live)
  refine ⟨bfPublicPhaseProfile N, ⟨{
    horizon := max T₀ 2
    lowerPotential := fairPhasePayoff
    upperPotential := fairPhasePayoff
    deviationPotential := bfDeviationPhasePayoff N
    lowerCharge := fun _ _ _ => 0
    upperCharge := fun _ _ _ => 0
    deviationCharge := bfDeviationCharge N
    horizon_ge_two := le_max_right T₀ 2
    lower_initial := ?_
    upper_initial := ?_
    deviation_initial := ?_
    lower_subharmonic := ?_
    lower_stage := ?_
    upper_superharmonic := ?_
    upper_stage := ?_
    deviation_superharmonic := ?_
    deviation_stage := ?_
    lower_charge_cesaro := ?_
    upper_charge_cesaro := ?_
    deviation_charge_cesaro := ?_
  }⟩⟩
  · intro who
    rw [hphase0]
    cases who <;>
      norm_num [fairPhasePayoff, fairPayoff, fairMaxPhaseValue, fairMaxValue,
        oneIndicator, liveIndicator] <;> exact hδ.le
  · intro who
    rw [hphase0]
    cases who <;>
      norm_num [fairPhasePayoff, fairPayoff, fairMaxPhaseValue, fairMaxValue,
        oneIndicator, liveIndicator] <;> exact hδ.le
  · intro who
    rw [hphase0]
    cases who
    · norm_num [bfDeviationPhasePayoff, fairPayoff, fairMaxPhaseValue,
        fairMaxValue, oneIndicator, liveIndicator]
      exact hδ.le
    · have hD0 : bfDenom N 0 = N + 1 := by
        unfold bfDenom
        omega
      simp only [bfDeviationPhasePayoff, fairPayoff, if_true]
      simp only [bfPhaseValue, reduceIte]
      rw [if_neg (by decide : State.live ≠ State.one), zero_add]
      rw [hD0, bfPotential_succ_eq_half_sub]
      have heq :
          -(1 / 2 - 1 / (2 * ((N : ℝ) + 1))) - (-(1 / 2)) =
            1 / (2 * ((N : ℝ) + 1)) := by ring
      rw [heq, abs_of_nonneg (by positivity)]
      exact hclose
  · intro who t h
    exact (fairPhasePayoff_harmonic N who h).le
  · intro who t h
    rw [← stageEUAt_bfPublicPhaseProfile_eq_fairPhasePayoff N who h]
    simp
  · intro who t h
    exact (fairPhasePayoff_harmonic N who h).ge
  · intro who t h
    rw [stageEUAt_bfPublicPhaseProfile_eq_fairPhasePayoff N who h]
    simp
  · exact bfDeviationPhasePayoff_superharmonic N
  · exact stageEUAt_deviation_le_bfDeviationPhasePayoff_add_charge N
  · intro who T hT
    simpa [expectedHistoryValue] using hδ.le
  · intro who T hT
    simpa [expectedHistoryValue] using hδ.le
  · intro who dev T hT
    cases who
    · simpa [bfDeviationCharge, expectedHistoryValue] using hδ.le
    · rw [bfPublicPhaseProfile_behaviorProfile,
        update_profileUniformMinimizer_true]
      have hsum :=
        sum_expectedHistoryValue_bfDeviationCharge_true_le N dev T
      exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
        (haverage T hT)

/-- The public-phase compiler produces the full adaptive potential
certificate for the Big Match. -/
theorem isAdaptivePotentialCertificateAt_fairPayoff_via_publicPhase
    (δ : ℝ) (hδ : 0 < δ) :
    game.IsAdaptivePotentialCertificateAt .live fairPayoff δ :=
  game.isAdaptivePotentialCertificateAt_of_isPublicPhasePunishmentSystemAt
    .live fairPayoff δ (isPublicPhasePunishmentSystemAt_fairPayoff δ hδ)

/-- The Big Match's fair payoff has an adaptive potential equilibrium
certificate obtained entirely from the public-phase controller. -/
theorem isAdaptivePotentialEquilibriumCertificate_fairPayoff_via_publicPhase :
    game.IsAdaptivePotentialEquilibriumCertificate .live fairPayoff :=
  isAdaptivePotentialCertificateAt_fairPayoff_via_publicPhase

/-- Acceptance-test capstone: the generic public-phase compiler and generic
adaptive verifier recover the Big Match uniform equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_fairPayoff_via_publicPhase :
    game.IsUniformEquilibriumPayoff .live fairPayoff :=
  game.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
    .live fairPayoff
    isAdaptivePotentialEquilibriumCertificate_fairPayoff_via_publicPhase

end BigMatch
end StochasticGame
end GameTheory
