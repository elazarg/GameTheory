/-
# Multiplicative-weights self-play

This opt-in analytic consumer assembles the game-independent finite
multiplicative-weights bound with Core's finite independent-self-play bridge.
`GameTheoryMath.OnlineLearning` owns the exponential-potential algebra and
`GameTheory.Probability.OnlineLearning` is the sole adapter that turns its
normalized vectors into canonical `FinDist` laws.  No second regret or CCE
predicate is introduced here.
-/

import GameTheory.Core.Learning
import GameTheory.Core.FictitiousPlay
import GameTheory.Analysis.FiniteLaw
import GameTheory.Probability.OnlineLearning
import GameTheoryMath.OnlineLearning

noncomputable section

namespace GameTheory

open Probability
open GameTheoryMath
open Filter

universe uι us uo

variable {ι : Type uι} [DecidableEq ι] [Fintype ι]

namespace UtilityGame

variable (G : UtilityGame.{uι, us, uo} ι)
variable [∀ i, Fintype (G.form.sig.Strategy i)] [∀ i, Nonempty (G.form.sig.Strategy i)]
variable (eta : ℝ) (lo : ι → ℝ) (width : ℝ)

/-- Cumulative normalized-gain score of independent multiplicative-weights
self-play.  The recurrence is structural: the round profile is read only from
the preceding score. -/
noncomputable def mwScore (G : UtilityGame.{uι, us, uo} ι)
    [∀ i, Fintype (G.form.sig.Strategy i)] [∀ i, Nonempty (G.form.sig.Strategy i)]
    (eta : ℝ) (lo : ι → ℝ) (width : ℝ) : ℕ → ∀ i, G.form.sig.Strategy i → ℝ
  | 0 => fun _ _ => 0
  | t + 1 => fun i action =>
      mwScore G eta lo width t i action +
        G.normGain lo width
          (fun j => Probability.OnlineLearning.exponentialWeights eta
            (mwScore G eta lo width t j)) i action

/-- The independent profile played at a round: each player applies the
canonical finite-law exponential-weights adapter to their score. -/
noncomputable def mwProfile (G : UtilityGame.{uι, us, uo} ι)
    [∀ i, Fintype (G.form.sig.Strategy i)] [∀ i, Nonempty (G.form.sig.Strategy i)]
    (eta : ℝ) (lo : ι → ℝ) (width : ℝ) (t : ℕ) : Profile G.form.sig.mixed :=
  fun i => Probability.OnlineLearning.exponentialWeights eta
    (mwScore G eta lo width t i)

/-- The structural score is the game-independent cumulative gain of the
trajectory it induces. -/
theorem mwScore_eq_cumGain (t : ℕ) (who : ι) (action : G.form.sig.Strategy who) :
    mwScore G eta lo width t who action =
      OnlineLearning.cumGain
        (fun round => G.normGain lo width
          (mwProfile G eta lo width round) who) t action := by
  induction t with
  | zero => simp [mwScore, OnlineLearning.cumGain]
  | succ t ih =>
    rw [OnlineLearning.cumGain_succ, ← ih]
    rfl

/-- The round law is exactly the canonical finite-law multiplicative-weights
law on the normalized-gain sequence. -/
theorem mwProfile_eq_multiplicativeWeights (t : ℕ) (who : ι) :
    mwProfile G eta lo width t who =
      Probability.OnlineLearning.multiplicativeWeights eta
        (fun round => G.normGain lo width
          (mwProfile G eta lo width round) who) t := by
  rw [mwProfile, Probability.OnlineLearning.multiplicativeWeights_eq_exponentialWeights]
  congr 1
  funext action
  exact mwScore_eq_cumGain G eta lo width t who action

/-- **Finite multiplicative-weights self-play yields an approximate CCE.**
The result is an explicit finite-horizon bound, not a limit assertion. -/
theorem mwSelfPlay_timeAverage_isεCoarseCorrelatedEq {L : ℝ} (heta : 0 < eta)
    (hwidth : 0 < width)
    (hband : ∀ who outcome, G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (hL : ∀ who, Real.log (Fintype.card (G.form.sig.Strategy who)) ≤ L)
    (T : ℕ) [NeZero T] :
    G.IsεCoarseCorrelatedEq
      (width * (L / eta + (Real.exp eta - 1 - eta) / eta * T) / T)
      (G.timeAverage fun round : Fin T =>
        FinDist.pi (mwProfile G eta lo width (round : ℕ))) := by
  apply G.selfPlay_timeAverage_isεCoarseCorrelatedEq
  intro who action
  let gain : ℕ → G.form.sig.Strategy who → ℝ :=
    fun round => G.normGain lo width
      (mwProfile G eta lo width round) who
  have halgorithm : (∑ round ∈ Finset.range T,
      (mwProfile G eta lo width round who).expect
        (gain round)) =
      OnlineLearning.algorithmGain eta gain T := by
    rw [OnlineLearning.algorithmGain]
    apply Finset.sum_congr rfl
    intro round _
    rw [mwProfile_eq_multiplicativeWeights G eta lo width,
      Probability.OnlineLearning.expect_multiplicativeWeights]
  have hscale :
      (∑ round : Fin T,
        (expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update (mwProfile G eta lo width (round : ℕ)) who
                (FinDist.pure action))) -
          expectedUtility G.utility who
            (G.form.mixed.play (mwProfile G eta lo width (round : ℕ))))) =
      width * (OnlineLearning.cumGain gain T action -
        OnlineLearning.algorithmGain eta gain T) := by
    rw [Fin.sum_univ_eq_sum_range (fun round =>
      expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update (mwProfile G eta lo width round) who
              (FinDist.pure action))) -
        expectedUtility G.utility who
          (G.form.mixed.play (mwProfile G eta lo width round))) T]
    rw [Finset.sum_congr rfl (fun round _ =>
      G.expectedUtility_deviation_eq_width_mul_normGain hwidth
        (mwProfile G eta lo width round) who action)]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, halgorithm]
    rfl
  rw [hscale]
  have hbound : OnlineLearning.cumGain gain T action - OnlineLearning.algorithmGain eta gain T ≤
      L / eta + (Real.exp eta - 1 - eta) / eta * T := by
    calc
      OnlineLearning.cumGain gain T action - OnlineLearning.algorithmGain eta gain T ≤
          OnlineLearning.externalRegret eta gain T :=
        OnlineLearning.fixedActionRegret_le_externalRegret eta gain T action
      _ ≤ Real.log (Fintype.card (G.form.sig.Strategy who)) / eta +
          (Real.exp eta - 1 - eta) / eta * T :=
        OnlineLearning.externalRegret_le heta
          (fun round candidate =>
            G.normGain_mem_Icc hwidth hband
              (mwProfile G eta lo width round) who candidate) T
      _ ≤ L / eta + (Real.exp eta - 1 - eta) / eta * T := by
        have hfirst : Real.log (Fintype.card (G.form.sig.Strategy who)) / eta ≤ L / eta :=
          (div_le_div_iff_of_pos_right heta).2 (hL who)
        linarith
  exact mul_le_mul_of_nonneg_left hbound hwidth.le

/-- The finite MW trajectory exhibits a canonical approximate CCE at every
positive horizon. -/
theorem exists_mwSelfPlay_isεCoarseCorrelatedEq {L : ℝ} (heta : 0 < eta)
    (hwidth : 0 < width)
    (hband : ∀ who outcome, G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (hL : ∀ who, Real.log (Fintype.card (G.form.sig.Strategy who)) ≤ L)
    (T : ℕ) [NeZero T] :
    ∃ law : FinDist (Profile G.form.sig),
      G.IsεCoarseCorrelatedEq
        (width * (L / eta + (Real.exp eta - 1 - eta) / eta * T) / T) law := by
  exact ⟨_, mwSelfPlay_timeAverage_isεCoarseCorrelatedEq G eta lo width
    heta hwidth hband hL T⟩

/-- **Arbitrarily accurate finite MW self-play.** For any positive tolerance,
a concrete rate and finite horizon yield a canonical approximate CCE.  The
proof uses only a finite-horizon exponential remainder estimate. -/
theorem mwSelfPlay_exists_isεCoarseCorrelatedEq_of_pos {L : ℝ}
    (hwidth : 0 < width)
    (hband : ∀ who outcome, G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (hL : ∀ who, Real.log (Fintype.card (G.form.sig.Strategy who)) ≤ L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ law : FinDist (Profile G.form.sig), G.IsεCoarseCorrelatedEq epsilon law := by
  have htwiceWidth : (0 : ℝ) < 2 * width := by linarith
  set eta₀ : ℝ := min 1 (epsilon / (2 * width)) with heta₀
  have heta₀pos : 0 < eta₀ := lt_min one_pos (by positivity)
  have heta₀one : eta₀ ≤ 1 := min_le_left _ _
  have heta₀epsilon : eta₀ ≤ epsilon / (2 * width) := min_le_right _ _
  have heta₀epsilon' : eta₀ * (2 * width) ≤ epsilon :=
    (le_div_iff₀ htwiceWidth).1 heta₀epsilon
  obtain ⟨T', hT'⟩ := exists_nat_ge (2 * width * L / (eta₀ * epsilon))
  haveI : NeZero (T' + 1) := ⟨Nat.succ_ne_zero _⟩
  have hTpos : (0 : ℝ) < ((T' + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos T'
  refine ⟨G.timeAverage (fun round : Fin (T' + 1) =>
    FinDist.pi (mwProfile G eta₀ lo width (round : ℕ))), ?_⟩
  have hMW := mwSelfPlay_timeAverage_isεCoarseCorrelatedEq G eta₀ lo width heta₀pos hwidth
    hband hL (T' + 1)
  rw [G.isεCoarseCorrelatedEq_iff_externalRegret_le] at hMW ⊢
  intro who action
  apply le_trans (hMW who action)
  have hremainder : (Real.exp eta₀ - 1 - eta₀) / eta₀ ≤ eta₀ := by
    rw [div_le_iff₀ heta₀pos]
    have hsq := OnlineLearning.exp_sub_one_sub_self_le_sq heta₀pos.le heta₀one
    rw [pow_two] at hsq
    linarith
  have hTlarge : 2 * width * L ≤ ((T' + 1 : ℕ) : ℝ) * (eta₀ * epsilon) := by
    have h : 2 * width * L / (eta₀ * epsilon) ≤ ((T' + 1 : ℕ) : ℝ) :=
      le_trans hT' (by exact_mod_cast Nat.le_succ T')
    rwa [div_le_iff₀ (by positivity)] at h
  have hfirst : width * L / (eta₀ * ((T' + 1 : ℕ) : ℝ)) ≤ epsilon / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hTlarge]
  have hsecond : width * eta₀ ≤ epsilon / 2 := by
    nlinarith [heta₀epsilon']
  have hsplit :
      width * (L / eta₀ + (Real.exp eta₀ - 1 - eta₀) / eta₀ * ((T' + 1 : ℕ) : ℝ)) /
          ((T' + 1 : ℕ) : ℝ) =
        width * L / (eta₀ * ((T' + 1 : ℕ) : ℝ)) +
          width * ((Real.exp eta₀ - 1 - eta₀) / eta₀) := by
    have heta₀ne : eta₀ ≠ 0 := heta₀pos.ne'
    have hTne : ((T' + 1 : ℕ) : ℝ) ≠ 0 := hTpos.ne'
    field_simp
  rw [hsplit]
  have hscaledRemainder : width * ((Real.exp eta₀ - 1 - eta₀) / eta₀) ≤
      width * eta₀ :=
    mul_le_mul_of_nonneg_left hremainder hwidth.le
  linarith [hfirst, hsecond, hscaledRemainder]

end UtilityGame

/-! ## Fictitious-play limits -/

namespace UtilityGame

variable {G : UtilityGame.{uι, us, uo} ι}
variable [∀ i, Fintype (G.form.sig.Strategy i)]

/-- Expected utility in the finite mixed extension is continuous under
coordinatewise pointwise convergence of canonical finite laws. -/
theorem expectedUtility_mixed_tendsto
    {sequence : ℕ → Profile G.form.sig.mixed} {target : Profile G.form.sig.mixed}
    (hconverges : ∀ i, Analysis.FinDistConvergesPointwise
      (fun n => sequence n i) (target i)) (who : ι) :
    Tendsto
      (fun n => expectedUtility G.utility who (G.form.mixed.play (sequence n)))
      atTop
      (nhds (expectedUtility G.utility who (G.form.mixed.play target))) := by
  have hproduct := Analysis.FinDistConvergesPointwise.pi hconverges
  have hexpect := hproduct.expect
    (fun profile => expectedUtility G.utility who (G.form.play profile))
  simpa only [GameForm.mixed_play, expectedUtility_bind] using hexpect

/-- Fixing one player's pure action preserves convergence of the expected
utility generated by the remaining convergent empirical marginals. -/
theorem expectedUtility_update_pure_tendsto
    {sequence : ℕ → Profile G.form.sig.mixed} {target : Profile G.form.sig.mixed}
    (hconverges : ∀ i, Analysis.FinDistConvergesPointwise
      (fun n => sequence n i) (target i)) (who : ι)
    (action : G.form.sig.Strategy who) :
    Tendsto
      (fun n => expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update (sequence n) who (FinDist.pure action))))
      atTop
      (nhds (expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update target who (FinDist.pure action))))) := by
  apply expectedUtility_mixed_tendsto
  intro other
  by_cases hother : other = who
  · subst hother
    simp only [Profile.update_same]
    exact Analysis.finDistConvergesPointwise_const _
  · simp only [Profile.update_of_ne _ _ hother]
    exact hconverges other

omit [DecidableEq ι] [Fintype ι] [∀ i, Fintype (G.form.sig.Strategy i)] in
/-- If an empirical marginal converges to a law that gives an action positive
mass, that action occurs in infinitely many positive-index rounds. -/
theorem frequently_play_eq_of_empiricalMarginal_converges
    (history : ℕ → Profile G.form.sig) (who : ι)
    (action : G.form.sig.Strategy who) (target : FinDist (G.form.sig.Strategy who))
    (hconverges : Analysis.FinDistConvergesPointwise
      (fun t => G.empiricalMarginal history who (t + 1)) target)
    (haction : action ∈ target.support) :
    ∃ᶠ t in atTop, history (t + 1) who = action := by
  classical
  have hpositive : 0 < target.prob action := FinDist.prob_pos_iff.mpr haction
  by_contra hnot
  rw [not_frequently] at hnot
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnot
  have hbound : ∀ t : ℕ,
      (G.empiricalMarginal history who (t + 1)).prob action ≤
        ((N : ℝ) + 1) / ((t + 1 : ℕ) : ℝ) := by
    intro t
    have hcard :
        (Finset.univ.filter fun k : Fin (t + 1) => history k who = action).card ≤ N + 1 := by
      have hsub :
          (Finset.univ.filter fun k : Fin (t + 1) => history k who = action) ⊆
            (Finset.univ.filter fun k : Fin (t + 1) => k.val < N + 1) := by
        intro k hk
        rw [Finset.mem_filter] at hk ⊢
        refine ⟨hk.1, ?_⟩
        by_contra hge
        have hge' : N + 1 ≤ k.val := not_lt.1 hge
        have hk1 : N ≤ k.val - 1 := by omega
        have hne := hN _ hk1
        rw [Nat.sub_add_cancel (by omega)] at hne
        exact hne hk.2
      refine (Finset.card_le_card hsub).trans ?_
      have hinjected :
          (Finset.univ.filter fun k : Fin (t + 1) => k.val < N + 1).card ≤
            (Finset.range (N + 1)).card :=
        Finset.card_le_card_of_injOn (fun k => k.val)
          (fun k hk => Finset.mem_range.2 (Finset.mem_filter.1 hk).2)
          (fun _ _ _ _ h => Fin.val_injective h)
      simpa using hinjected
    rw [G.empiricalMarginal_prob]
    gcongr
    exact_mod_cast hcard
  have hzero : Tendsto
      (fun t : ℕ => ((N : ℝ) + 1) / ((t + 1 : ℕ) : ℝ))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ((N : ℝ) + 1)).comp
      (tendsto_add_atTop_nat 1)
  have hle : target.prob action ≤ 0 :=
    le_of_tendsto_of_tendsto (hconverges action) hzero
      (Eventually.of_forall hbound)
  linarith

/-- **Every pointwise limit of fictitious-play empirical beliefs is a mixed
Nash equilibrium.** Positive limiting mass forces an action to occur
infinitely often; the roundwise best-response inequalities then pass to the
limit by finite-law continuity. -/
theorem IsFictitiousPlay.limit_isNash
    {history : ℕ → Profile G.form.sig} (hplay : G.IsFictitiousPlay history)
    {target : Profile G.form.sig.mixed}
    (hconverges : ∀ i, Analysis.FinDistConvergesPointwise
      (fun t => G.empiricalBelief history (t + 1) i) (target i)) :
    IsNash G.form.mixed (euPreference G.utility) target := by
  have hbest : ∀ (who : ι) (action : G.form.sig.Strategy who),
      action ∈ (target who).support → ∀ alternative : G.form.sig.Strategy who,
        expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update target who (FinDist.pure alternative))) ≤
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update target who (FinDist.pure action))) := by
    intro who action haction alternative
    have hcoordinate : Analysis.FinDistConvergesPointwise
        (fun t => G.empiricalMarginal history who (t + 1)) (target who) := by
      simpa only [empiricalBelief] using hconverges who
    have hfrequent : ∃ᶠ t in atTop, history (t + 1) who = action :=
      G.frequently_play_eq_of_empiricalMarginal_converges
        history who action (target who) hcoordinate haction
    have hactionTendsto := expectedUtility_update_pure_tendsto
      (G := G) hconverges who action
    have halternativeTendsto := expectedUtility_update_pure_tendsto
      (G := G) hconverges who alternative
    by_contra hnot
    rw [not_le] at hnot
    have hdifference := hactionTendsto.sub halternativeTendsto
    have hnegative :
        expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update target who (FinDist.pure action))) -
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update target who (FinDist.pure alternative))) < 0 := by
      linarith
    have heventuallyNegative :=
      hdifference.eventually (eventually_lt_nhds hnegative)
    have hfrequentlyNonnegative : ∃ᶠ t in atTop,
        0 ≤ expectedUtility G.utility who
              (G.form.mixed.play
                (Profile.update (G.empiricalBelief history (t + 1)) who
                  (FinDist.pure action))) -
            expectedUtility G.utility who
              (G.form.mixed.play
                (Profile.update (G.empiricalBelief history (t + 1)) who
                  (FinDist.pure alternative))) := by
      refine hfrequent.mono fun t ht => ?_
      have hround :=
        (UtilityGame.IsFictitiousPlay.isBestResponse (G := G) hplay t who)
          (FinDist.pure alternative)
      rw [euPreference_apply, ht] at hround
      linarith
    obtain ⟨t, hnonnegative, hnegativeAt⟩ :=
      (hfrequentlyNonnegative.and_eventually heventuallyNegative).exists
    linarith
  rw [isNash_mixed_iff]
  intro who alternative
  calc
    expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update target who (FinDist.pure alternative))) =
        (target who).expect (fun _ =>
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update target who (FinDist.pure alternative)))) :=
      (FinDist.expect_const ..).symm
    _ ≤ (target who).expect (fun action =>
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update target who (FinDist.pure action)))) :=
      FinDist.expect_mono fun action haction =>
        hbest who action haction alternative
    _ = expectedUtility G.utility who (G.form.mixed.play target) :=
      (expectedUtility_mixed_eq_expect G.form G.utility target who).symm

end UtilityGame

end GameTheory
