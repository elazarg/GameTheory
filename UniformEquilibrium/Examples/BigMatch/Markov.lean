/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.Examples.BigMatch.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The scalar stopping calculation behind the Big Match

Let `p t` be the maximizer's probability of stopping at live stage `t`.
The probability that the game is still live before stage `t` is
`prod k < t, (1 - p k)`.

The minimizer's cutoff response plays the safe-right column before a cutoff
`N` and the safe-left column afterwards.  Before `N`, a stop is absorbed at
payoff zero and a continuation pays one.  After `N`, continuation pays zero
and a stop is absorbed at payoff one.  The expected stage payoff is therefore
the live probability at the next stage before the cutoff, and the probability
of a winning stop since the cutoff afterwards.

The main result `exists_cutoff_eventually_average_lt_of_summable` proves that
when the stopping hazards are summable, one cutoff response makes every
sufficiently long average smaller than any prescribed positive epsilon.  The
complementary all-right calculation is recorded by
`tendsto_allRightAverage_zero`: whenever the live probability tends to zero,
the all-right response has average payoff tending to zero.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace BigMatch
namespace MarkovScalar

open Filter

/-- Probability of remaining live before stage `t`. -/
def liveProbability (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∏ k ∈ Finset.range t, (1 - p k)

@[simp] theorem liveProbability_zero (p : ℕ → ℝ) :
    liveProbability p 0 = 1 := by
  simp [liveProbability]

theorem liveProbability_succ (p : ℕ → ℝ) (t : ℕ) :
    liveProbability p (t + 1) = liveProbability p t * (1 - p t) := by
  simp [liveProbability, Finset.prod_range_succ]

theorem liveProbability_nonneg (p : ℕ → ℝ)
    (_hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) (t : ℕ) :
    0 ≤ liveProbability p t := by
  unfold liveProbability
  apply Finset.prod_nonneg
  intro k hk
  exact sub_nonneg.mpr (hp1 k)

theorem liveProbability_le_one (p : ℕ → ℝ)
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) (t : ℕ) :
    liveProbability p t ≤ 1 := by
  unfold liveProbability
  apply Finset.prod_le_one
  · intro k hk
    exact sub_nonneg.mpr (hp1 k)
  · intro k hk
    linarith [hp0 k]

/-- Probability lost from the live state at stage `t`. -/
theorem liveProbability_sub_succ (p : ℕ → ℝ) (t : ℕ) :
    liveProbability p t - liveProbability p (t + 1) =
      liveProbability p t * p t := by
  rw [liveProbability_succ]
  ring

/-- The stopped mass between two dates is the corresponding drop in live
probability. -/
theorem sum_liveProbability_mul_eq_sub (p : ℕ → ℝ)
    {N M : ℕ} (hNM : N ≤ M) :
    ∑ k ∈ Finset.Ico N M, liveProbability p k * p k =
      liveProbability p N - liveProbability p M := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      rw [Finset.sum_Ico_succ_top hNM, ih, liveProbability_succ]
      ring

/-- Expected stage payoff against the cutoff response: safe-right before
`N`, safe-left from `N` onwards. -/
def cutoffStagePayoff (p : ℕ → ℝ) (N t : ℕ) : ℝ :=
  if t < N then liveProbability p (t + 1)
  else liveProbability p N - liveProbability p (t + 1)

/-- Expected finite-horizon average against the cutoff response. -/
def cutoffAverage (p : ℕ → ℝ) (N T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, cutoffStagePayoff p N t

theorem cutoffStagePayoff_nonneg (p : ℕ → ℝ)
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (N t : ℕ) : 0 ≤ cutoffStagePayoff p N t := by
  unfold cutoffStagePayoff
  split_ifs with ht
  · exact liveProbability_nonneg p hp0 hp1 (t + 1)
  · rw [← sum_liveProbability_mul_eq_sub p
      (show N ≤ t + 1 by omega)]
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (liveProbability_nonneg p hp0 hp1 k) (hp0 k)

theorem cutoffStagePayoff_le_one (p : ℕ → ℝ)
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (N t : ℕ) : cutoffStagePayoff p N t ≤ 1 := by
  unfold cutoffStagePayoff
  split_ifs with ht
  · exact liveProbability_le_one p hp0 hp1 (t + 1)
  · have hnonneg := liveProbability_nonneg p hp0 hp1 (t + 1)
    have hle := liveProbability_le_one p hp0 hp1 N
    linarith

/-- After the cutoff, expected payoff is bounded by the remaining sum of
stopping hazards. -/
theorem cutoffStagePayoff_le_tail (p : ℕ → ℝ)
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (hsum : Summable p) {N t : ℕ} (hNt : N ≤ t) :
    cutoffStagePayoff p N t ≤ ∑' k : ℕ, p (k + N) := by
  rw [cutoffStagePayoff, if_neg (not_lt.mpr hNt),
    ← sum_liveProbability_mul_eq_sub p
      (show N ≤ t + 1 by omega)]
  calc
    ∑ k ∈ Finset.Ico N (t + 1), liveProbability p k * p k ≤
        ∑ k ∈ Finset.Ico N (t + 1), p k := by
      apply Finset.sum_le_sum
      intro k hk
      have hS0 := liveProbability_nonneg p hp0 hp1 k
      have hS1 := liveProbability_le_one p hp0 hp1 k
      nlinarith [hp0 k]
    _ = ∑ k ∈ Finset.range (t + 1 - N), p (k + N) := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      rw [add_comm]
    _ ≤ ∑' k : ℕ, p (k + N) := by
      have htail : Summable (fun k : ℕ => p (k + N)) :=
        (summable_nat_add_iff N).2 hsum
      exact htail.sum_le_tsum _ (fun k hk => hp0 (k + N))

/-- The cutoff average is bounded by the transient prefix divided by the
horizon, plus the total hazard remaining after the cutoff. -/
theorem cutoffAverage_le_prefix_add_tail (p : ℕ → ℝ)
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (hsum : Summable p) {N T : ℕ} (hNT : N ≤ T) (hT : 0 < T) :
    cutoffAverage p N T ≤
      (N : ℝ) / T + ∑' k : ℕ, p (k + N) := by
  let tail : ℝ := ∑' k : ℕ, p (k + N)
  have htail0 : 0 ≤ tail := tsum_nonneg fun k => hp0 (k + N)
  have hprefix :
      ∑ t ∈ Finset.range N, cutoffStagePayoff p N t ≤ N := by
    calc
      ∑ t ∈ Finset.range N, cutoffStagePayoff p N t ≤
          ∑ _t ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        exact cutoffStagePayoff_le_one p hp0 hp1 N t
      _ = N := by simp
  have hlate :
      ∑ t ∈ Finset.Ico N T, cutoffStagePayoff p N t ≤
        (T - N : ℕ) * tail := by
    calc
      ∑ t ∈ Finset.Ico N T, cutoffStagePayoff p N t ≤
          ∑ _t ∈ Finset.Ico N T, tail := by
        apply Finset.sum_le_sum
        intro t ht
        exact cutoffStagePayoff_le_tail p hp0 hp1 hsum
          (Finset.mem_Ico.mp ht).1
      _ = (T - N : ℕ) * tail := by
        simp [Nat.card_Ico, hNT]
  have hsumBound :
      ∑ t ∈ Finset.range T, cutoffStagePayoff p N t ≤
        N + (T - N : ℕ) * tail := by
    rw [← Finset.sum_range_add_sum_Ico _ hNT]
    exact add_le_add hprefix hlate
  rw [cutoffAverage]
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  calc
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        cutoffStagePayoff p N t ≤
        (T : ℝ)⁻¹ * (N + (T - N : ℕ) * tail) := by
      exact mul_le_mul_of_nonneg_left hsumBound (inv_nonneg.mpr hTreal.le)
    _ ≤ (N : ℝ) / T + tail := by
      rw [div_eq_mul_inv]
      have hsub : ((T - N : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.sub_le T N
      calc
        (T : ℝ)⁻¹ * (N + (T - N : ℕ) * tail) =
            (N : ℝ) * (T : ℝ)⁻¹ +
              ((T - N : ℕ) : ℝ) * (T : ℝ)⁻¹ * tail := by ring
        _ ≤ (N : ℝ) * (T : ℝ)⁻¹ + 1 * tail := by
          gcongr
          exact (div_le_one hTreal).2 hsub
        _ = (N : ℝ) * (T : ℝ)⁻¹ + tail := by ring

/-- Summable stopping hazards are defeated by one cutoff response: for every
positive epsilon, all sufficiently long expected averages are below epsilon.
-/
theorem exists_cutoff_eventually_average_lt_of_summable
    (p : ℕ → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (hsum : Summable p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ᶠ T in atTop, cutoffAverage p N T < ε := by
  have htail : Tendsto (fun N : ℕ => ∑' k : ℕ, p (k + N))
      atTop (nhds 0) := tendsto_sum_nat_add p
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htail) (ε / 2) (by linarith)
  refine ⟨N, ?_⟩
  have hprefix : Tendsto (fun T : ℕ => (N : ℝ) / (T : ℝ))
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp hprefix) (ε / 2) (by linarith)
  filter_upwards [eventually_ge_atTop (max (max N T₀) 1)] with T hT
  have hNT : N ≤ T := le_trans (le_max_left N T₀)
    (le_trans (le_max_left (max N T₀) 1) hT)
  have hT₀T : T₀ ≤ T := le_trans (le_max_right N T₀)
    (le_trans (le_max_left (max N T₀) 1) hT)
  have hTpos : 0 < T := lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right (max N T₀) 1) hT)
  have hbound := cutoffAverage_le_prefix_add_tail p hp0 hp1 hsum hNT hTpos
  have hprefixSmall := hT₀ T hT₀T
  have htail0 : 0 ≤ ∑' k : ℕ, p (k + N) :=
    tsum_nonneg fun k => hp0 (k + N)
  have hprefix0 : 0 ≤ (N : ℝ) / (T : ℝ) := by positivity
  have htailSmall := hN N le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg htail0] at htailSmall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hprefix0] at hprefixSmall
  linarith

/-- Expected stage payoff against the always-right response. -/
def allRightStagePayoff (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  liveProbability p (t + 1)

/-- Expected average against the always-right response. -/
def allRightAverage (p : ℕ → ℝ) (T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, allRightStagePayoff p t

/-- If stopping eventually occurs with probability one, always playing right
makes the expected averages converge to zero. -/
theorem tendsto_allRightAverage_zero (p : ℕ → ℝ)
    (hlive : Tendsto (liveProbability p) atTop (nhds 0)) :
    Tendsto (allRightAverage p) atTop (nhds 0) := by
  have hstage : Tendsto (allRightStagePayoff p) atTop (nhds 0) := by
    exact hlive.comp (tendsto_add_atTop_nat 1)
  unfold allRightAverage
  exact hstage.cesaro

/-- Every sequence of stopping probabilities has the branch needed by the
Big-Match response.  If the decreasing live probabilities have positive
limit `L`, then `L * p t` is bounded by the live-mass loss at stage `t`.
Telescoping makes the partial sums of `p` bounded, hence summable.  If the
limit is not positive, it is zero. -/
theorem summable_or_tendsto_liveProbability_zero
    (p : ℕ → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) :
    Summable p ∨ Tendsto (liveProbability p) atTop (nhds 0) := by
  let S : ℕ → ℝ := liveProbability p
  have hS0 : ∀ t, 0 ≤ S t := fun t =>
    liveProbability_nonneg p hp0 hp1 t
  have hanti : Antitone S := antitone_nat_of_succ_le fun t => by
    change liveProbability p (t + 1) ≤ liveProbability p t
    rw [liveProbability_succ]
    have hmul : 0 ≤ liveProbability p t * p t :=
      mul_nonneg (liveProbability_nonneg p hp0 hp1 t) (hp0 t)
    nlinarith
  have hbdd : BddBelow (Set.range S) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hS0 t
  let L : ℝ := sInf (Set.range S)
  have hlim : Tendsto S atTop (nhds L) :=
    by simpa only [L, sInf_range] using tendsto_atTop_ciInf hanti hbdd
  have hL0 : 0 ≤ L := by
    apply le_csInf (Set.range_nonempty S)
    rintro _ ⟨t, rfl⟩
    exact hS0 t
  by_cases hL : L = 0
  · right
    simpa only [S, hL] using hlim
  · left
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
    apply summable_of_sum_range_le hp0 (c := 1 / L)
    intro n
    have hmul : L * ∑ k ∈ Finset.range n, p k ≤ 1 := by
      calc
        L * ∑ k ∈ Finset.range n, p k =
            ∑ k ∈ Finset.range n, L * p k := by rw [Finset.mul_sum]
        _ ≤ ∑ k ∈ Finset.range n, S k * p k := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right
            (csInf_le hbdd ⟨k, rfl⟩) (hp0 k)
        _ = S 0 - S n := by
          simpa only [Nat.Ico_zero_eq_range, S] using
            sum_liveProbability_mul_eq_sub p (Nat.zero_le n)
        _ ≤ 1 := by
          have := hS0 n
          simp only [S, liveProbability_zero]
          linarith
    exact (le_div_iff₀ hLpos).2 (by simpa [mul_comm] using hmul)

/-- The complete scalar dichotomy used in Big-Match arguments.  Either a
summable-hazard cutoff or the all-right response defeats the time-indexed
stopping rule. -/
theorem exists_response_eventually_average_lt
    (p : ℕ → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (hbranch : Summable p ∨ Tendsto (liveProbability p) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    (∃ N : ℕ, ∀ᶠ T in atTop, cutoffAverage p N T < ε) ∨
      ∀ᶠ T in atTop, allRightAverage p T < ε := by
  rcases hbranch with hsum | hlive
  · exact Or.inl (exists_cutoff_eventually_average_lt_of_summable
      p hp0 hp1 hsum hε)
  · right
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp (tendsto_allRightAverage_zero p hlive)) ε hε
    filter_upwards [eventually_ge_atTop N] with T hT
    have hdist := hN T hT
    have hnonneg : 0 ≤ allRightAverage p T := by
      unfold allRightAverage allRightStagePayoff
      apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_nonneg
      intro t ht
      exact liveProbability_nonneg p hp0 hp1 (t + 1)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hdist
    exact hdist

/-- Unconditional time-indexed Big-Match response theorem.  For any sequence
of live-state stopping probabilities and any positive epsilon, one fixed
opponent schedule—a cutoff response or always-right—keeps every sufficiently
long expected average below epsilon. -/
theorem exists_response_eventually_average_lt_unconditional
    (p : ℕ → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    (∃ N : ℕ, ∀ᶠ T in atTop, cutoffAverage p N T < ε) ∨
      ∀ᶠ T in atTop, allRightAverage p T < ε := by
  exact exists_response_eventually_average_lt p hp0 hp1
    (summable_or_tendsto_liveProbability_zero p hp0 hp1) hε

end MarkovScalar

/-! ## Realization by behavior-strategy deviations -/

/-- A pure calendar-time strategy for the minimizer. -/
def minimizerSchedule (d : ℕ → Bool) : game.BehaviorStrategy true :=
  fun t _h => PMF.pure (d t)

/-- Replace the minimizer component of a time/state mixed profile by a pure
calendar-time schedule. -/
def replaceMinimizer (m : TimeStateMixedProfile) (d : ℕ → Bool) :
    TimeStateMixedProfile :=
  fun t s who => match who with
    | false => m t s false
    | true => PMF.pure (d t)

@[simp] theorem replaceMinimizer_false
    (m : TimeStateMixedProfile) (d : ℕ → Bool) (t : ℕ) (s : State) :
    replaceMinimizer m d t s false = m t s false := rfl

@[simp] theorem replaceMinimizer_true
    (m : TimeStateMixedProfile) (d : ℕ → Bool) (t : ℕ) (s : State) :
    replaceMinimizer m d t s true = PMF.pure (d t) := rfl

theorem update_timeStateBehaviorProfile_minimizerSchedule
    (m : TimeStateMixedProfile) (d : ℕ → Bool) :
    Function.update (timeStateBehaviorProfile m) true (minimizerSchedule d) =
      timeStateBehaviorProfile (replaceMinimizer m d) := by
  funext who t h
  cases who <;>
    simp [timeStateBehaviorProfile, minimizerSchedule, replaceMinimizer]

/-- The minimizer always chooses Right. -/
def allRightMinimizer : game.BehaviorStrategy true :=
  minimizerSchedule fun _ => true

/-- The minimizer chooses Right before `N` and Left from `N` onwards. -/
def cutoffMinimizer (N : ℕ) : game.BehaviorStrategy true :=
  minimizerSchedule fun t => if t < N then true else false

def allRightProfile (m : TimeStateMixedProfile) : TimeStateMixedProfile :=
  replaceMinimizer m fun _ => true

def cutoffProfile (m : TimeStateMixedProfile) (N : ℕ) :
    TimeStateMixedProfile :=
  replaceMinimizer m fun t => if t < N then true else false

@[simp] theorem stopProbability_replaceMinimizer
    (m : TimeStateMixedProfile) (d : ℕ → Bool) (t : ℕ) :
    stopProbability (replaceMinimizer m d) t = stopProbability m t := rfl

@[simp] theorem rightProbability_replaceMinimizer
    (m : TimeStateMixedProfile) (d : ℕ → Bool) (t : ℕ) :
    rightProbability (replaceMinimizer m d) t = if d t then 1 else 0 := by
  cases hd : d t <;>
    simp [rightProbability, replaceMinimizer, hd]

@[simp] theorem stopProbability_allRightProfile
    (m : TimeStateMixedProfile) (t : ℕ) :
    stopProbability (allRightProfile m) t = stopProbability m t := by
  simp [allRightProfile]

@[simp] theorem rightProbability_allRightProfile
    (m : TimeStateMixedProfile) (t : ℕ) :
    rightProbability (allRightProfile m) t = 1 := by
  simp [allRightProfile]

@[simp] theorem stopProbability_cutoffProfile
    (m : TimeStateMixedProfile) (N t : ℕ) :
    stopProbability (cutoffProfile m N) t = stopProbability m t := by
  simp [cutoffProfile]

@[simp] theorem rightProbability_cutoffProfile
    (m : TimeStateMixedProfile) (N t : ℕ) :
    rightProbability (cutoffProfile m N) t = if t < N then 1 else 0 := by
  simp [cutoffProfile]

theorem stateLiveProbability_replaceMinimizer
    (m : TimeStateMixedProfile) (d : ℕ → Bool) (t : ℕ) :
    stateLiveProbability (replaceMinimizer m d) t =
      MarkovScalar.liveProbability (stopProbability m) t := by
  rw [stateLiveProbability_eq_prod]
  simp only [stopProbability_replaceMinimizer]
  rfl

theorem stateLiveProbability_allRightProfile
    (m : TimeStateMixedProfile) (t : ℕ) :
    stateLiveProbability (allRightProfile m) t =
      MarkovScalar.liveProbability (stopProbability m) t :=
  stateLiveProbability_replaceMinimizer m (fun _ => true) t

theorem stateLiveProbability_cutoffProfile
    (m : TimeStateMixedProfile) (N t : ℕ) :
    stateLiveProbability (cutoffProfile m N) t =
      MarkovScalar.liveProbability (stopProbability m) t :=
  stateLiveProbability_replaceMinimizer m
    (fun t => if t < N then true else false) t

@[simp] theorem stateOneProbability_allRightProfile
    (m : TimeStateMixedProfile) (t : ℕ) :
    stateOneProbability (allRightProfile m) t = 0 := by
  induction t with
  | zero => simp [allRightProfile]
  | succ t ih =>
      rw [stateOneProbability_succ, ih]
      simp

theorem stateOneProbability_cutoffProfile_eq_zero_of_le
    (m : TimeStateMixedProfile) (N t : ℕ) (ht : t ≤ N) :
    stateOneProbability (cutoffProfile m N) t = 0 := by
  induction t with
  | zero => simp [cutoffProfile]
  | succ t ih =>
      have htN : t ≤ N := by omega
      have hlt : t < N := by omega
      rw [stateOneProbability_succ, ih htN]
      simp [hlt]

theorem stateOneProbability_cutoffProfile_eq_sub_of_le
    (m : TimeStateMixedProfile) (N t : ℕ) (hNt : N ≤ t) :
    stateOneProbability (cutoffProfile m N) t =
      MarkovScalar.liveProbability (stopProbability m) N -
        MarkovScalar.liveProbability (stopProbability m) t := by
  induction t, hNt using Nat.le_induction with
  | base =>
      rw [stateOneProbability_cutoffProfile_eq_zero_of_le m N N le_rfl]
      ring
  | succ t hNt ih =>
      rw [stateOneProbability_succ, ih,
        rightProbability_cutoffProfile, if_neg (not_lt.mpr hNt),
        stopProbability_cutoffProfile,
        stateLiveProbability_cutoffProfile,
        MarkovScalar.liveProbability_succ]
      ring

theorem expectedStagePayoff_allRightProfile
    (m : TimeStateMixedProfile) (t : ℕ) :
    game.expectedStagePayoff (timeStateBehaviorProfile (allRightProfile m))
        .live t false =
      MarkovScalar.allRightStagePayoff (stopProbability m) t := by
  rw [expectedStagePayoff_maximizer,
    stateOneProbability_allRightProfile,
    stateLiveProbability_allRightProfile]
  simp [liveStageReward, MarkovScalar.allRightStagePayoff,
    MarkovScalar.liveProbability_succ]
  ring

theorem expectedStagePayoff_cutoffProfile
    (m : TimeStateMixedProfile) (N t : ℕ) :
    game.expectedStagePayoff (timeStateBehaviorProfile (cutoffProfile m N))
        .live t false =
      MarkovScalar.cutoffStagePayoff (stopProbability m) N t := by
  rw [expectedStagePayoff_maximizer,
    stateLiveProbability_cutoffProfile]
  unfold liveStageReward MarkovScalar.cutoffStagePayoff
  by_cases ht : t < N
  · rw [if_pos ht,
      stateOneProbability_cutoffProfile_eq_zero_of_le m N t (by omega),
      rightProbability_cutoffProfile, if_pos ht,
      stopProbability_cutoffProfile,
      MarkovScalar.liveProbability_succ]
    ring
  · have hNt : N ≤ t := not_lt.mp ht
    rw [if_neg ht,
      stateOneProbability_cutoffProfile_eq_sub_of_le m N t hNt,
      rightProbability_cutoffProfile, if_neg ht,
      stopProbability_cutoffProfile,
      MarkovScalar.liveProbability_succ]
    ring

/-- The actual finite-horizon payoff of the always-right minimizer deviation
is exactly the scalar all-right average. -/
theorem finiteAveragePayoff_update_allRightMinimizer
    (m : TimeStateMixedProfile) (T : ℕ) :
    game.finiteAveragePayoff .live T
        (Function.update (timeStateBehaviorProfile m) true allRightMinimizer)
        false =
      MarkovScalar.allRightAverage (stopProbability m) T := by
  rw [allRightMinimizer, update_timeStateBehaviorProfile_minimizerSchedule,
    game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  unfold MarkovScalar.allRightAverage
  apply congrArg ((T : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro t ht
  exact expectedStagePayoff_allRightProfile m t

/-- The actual finite-horizon payoff of the cutoff minimizer deviation is
exactly the scalar cutoff average. -/
theorem finiteAveragePayoff_update_cutoffMinimizer
    (m : TimeStateMixedProfile) (N T : ℕ) :
    game.finiteAveragePayoff .live T
        (Function.update (timeStateBehaviorProfile m) true (cutoffMinimizer N))
        false =
      MarkovScalar.cutoffAverage (stopProbability m) N T := by
  rw [cutoffMinimizer, update_timeStateBehaviorProfile_minimizerSchedule,
    game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  unfold MarkovScalar.cutoffAverage
  apply congrArg ((T : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro t ht
  exact expectedStagePayoff_cutoffProfile m N t

end BigMatch
end StochasticGame
end GameTheory
