/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.BigMatchMarkov
import GameTheory.Concepts.Stochastic.AdaptiveCertificate
import Math.SequenceVariation

/-!
# The Big Match: the positive (Blackwell–Ferguson) side of the uniform value

`BigMatchNoMarkov.lean` shows that no calendar-time × state Markov profile can
witness the classical Big Match uniform value `(1/2, -1/2)`: the maximizer's
`ε`-optimal response has to be genuinely history-dependent.  This file
constructs such a history-dependent witness, following Blackwell–Ferguson
(1968), and proves the Big Match's uniform equilibrium payoff exists at the
live state: **`exists_uniformEquilibriumPayoff_live`**, the capstone theorem,
is sorry-free.

## The maximizer's history-dependent strategy

At every live stage, define the *net excess* `k` of the minimizer's past
Right plays over Left plays (`netRightExcess`).  The Blackwell–Ferguson
strategy with parameter `N` stops with probability `1 / D ^ 2`, where
`D = max (k + N + 1) 1` (`bfDenom`) is the excess shifted by `N` and clamped
to stay at least `1`.  This is `blackwellFergusonStrategy`.

## The minimizer's stationary strategy and the easy direction

The minimizer's uniform stationary strategy `uniformMinimizerStrategy` plays
Left/Right with probability `1/2` after every history.  Against it, *every*
maximizer strategy earns finite-average payoff *exactly* `1/2`, at every
positive horizon (`finiteAveragePayoff_eq_half_of_uniformMinimizer`): the
off-diagonal reward is symmetric, and a uniform minimizer keeps the
probabilities of ever absorbing at `.one` versus `.zero` exactly equal at
every stage, so the two absorption events cancel in expectation.  This is the
content of `expectedStateValue_oneIndicator_eq_zeroIndicator` and its
corollary `expectedStagePayoff_eq_half_of_uniformMinimizer`.  Together these
give the *deviation cap* for the maximizer's half of a prospective uniform
equilibrium at `(1/2, -1/2)`, and (after inverting via zero-sumness) they are
also exactly what the minimizer would need from *its* opponent to cap the
maximizer from below at `1/2 - δ`: that lower bound is the hard direction.

## The hard (Blackwell–Ferguson) estimate, in three stages

* **Stage 3a–3b** (deterministic minimizer schedules): `blackwellFergusonStrategy
  N` earns at least `1/2 - O(1/N)` against every fixed calendar schedule
  `d : ℕ → Bool`.  Stage 3a (`histDist_eq_bfSeqProfile`) collapses the
  history-dependent excess to the deterministic `bfExcess d t` along every
  reachable branch, reusing `BigMatch.lean`'s `TimeStateMixedProfile` API;
  Stage 3b tracks the exact-identity potential `bfPotential D := (D - 1)/(2D)`
  against the excess denominator (`bfM_le_succ` through `bfFiniteAverage_ge`,
  culminating in `bfSeq_eventually_ge_half`).
* **Stage 3c** (arbitrary minimizer deviations, `bf_dev_eventually_ge_half`):
  lifts Stage 3b from schedules to *every* minimizer behavior strategy `dev`,
  via a *history-level* submartingale `bfX`/`bfXExpect` (Piece 2,
  `bfXExpect_le_succ`/`bfXExpect_ge_bfPotential`, the direct history-level
  analogue of `bfM_le_succ`), a per-stage payoff bound against the mixed
  minimizer action (Piece 3, `stageEUAt_bfDevProfile_ge`/
  `expectedStagePayoff_bfDevProfile_ge`), and two summation bounds over the
  horizon (Piece 4: `sum_bfLiveDeltaExpect_ge`, a *pathwise* support-level
  induction on the raw stage record reusing
  `netRightExcess_ge_of_live_of_mem_support`; `sum_bfLivePExpect_le_one`, a
  telescoping identity on the live-mass process).
* **Stage 4** (`exists_uniformEquilibriumPayoff_live`): assembles Stage 2's
  exact on-path/maximizer-deviation caps and Stage 3c's minimizer-deviation
  cap (via the zero-sum identity `finiteAveragePayoff_minimizer`) through
  `isUniformEquilibriumPayoff_of_deviation_caps`.

Two earlier obstructions are worth recording for context (both are genuine
mathematical facts about this problem, not proof-search failures, and neither
blocks the route actually taken above): no *pointwise*, everywhere-sure
Bellman telescope can support a strictly positive rate across the `.zero`
self-loop, and no *bounded, history-independent* potential against a flat
target `v` can either (`.zero`-absorbed mass never shrinks in Cesàro average).
Stage 3c's per-stage bound instead carries its own floor `bfPotential (N+1)`
rather than a flat target, sidestepping both obstructions. An *aggregate*
(expectation-level, non-pathwise) Abel-summation route for Piece 4(i) was
also tried and fails, since liveness and the excess step are correlated
across the different histories present at a fixed stage; Piece 4(i)'s
*pathwise* per-history argument (mask by the prefix's own liveness, telescope
via `netRightExcess_snoc`, expectations only at the end) avoids this
entirely and needs no `restrictHist`/Abel summation at all — only a direct
structural induction on the horizon, mirroring
`netRightExcess_ge_of_live_of_mem_support`'s own proof.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace StochasticGame
namespace BigMatch

open Math.Probability Math.PMFProduct

/-! ## A biased coin as a `PMF Bool` -/

/-- The `PMF Bool` that returns `true` with probability `p` and `false` with
probability `1 - p`. -/
def coinPMF (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, if_false, Bool.false_eq_true]
      rw [← ENNReal.ofReal_add hp0 (by linarith)]
      norm_num)

@[simp] theorem coinPMF_apply_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    coinPMF p hp0 hp1 true = ENNReal.ofReal p := by
  simp [coinPMF, PMF.ofFintype_apply]

@[simp] theorem coinPMF_apply_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    coinPMF p hp0 hp1 false = ENNReal.ofReal (1 - p) := by
  simp [coinPMF, PMF.ofFintype_apply]

theorem coinPMF_apply_true_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coinPMF p hp0 hp1 true).toReal = p := by
  rw [coinPMF_apply_true, ENNReal.toReal_ofReal hp0]

theorem coinPMF_apply_false_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coinPMF p hp0 hp1 false).toReal = 1 - p := by
  rw [coinPMF_apply_false, ENNReal.toReal_ofReal (by linarith)]

/-! ## Stage 1: the Blackwell–Ferguson maximizer strategy and the minimizer's
uniform stationary strategy -/

/-- The minimizer's action recorded at past stage `j` of a history at `t`. -/
def minimizerActionAt {t : ℕ} (h : game.Hist t) (j : Fin t) : Bool :=
  (h.1 j).2 true

/-- Net excess of the minimizer's past Right plays over Left plays, read off
a history: `+1` for every past Right, `-1` for every past Left, summed over
all recorded past stages. -/
def netRightExcess {t : ℕ} (h : game.Hist t) : ℤ :=
  ∑ j : Fin t, if minimizerActionAt h j then (1 : ℤ) else -1

@[simp] theorem netRightExcess_zero (h : game.Hist 0) : netRightExcess h = 0 := by
  simp [netRightExcess]

/-- The Blackwell–Ferguson denominator at parameter `N`: the excess `k`
shifted by `N` and clamped to stay at least `1`. -/
def bfDenom (N : ℕ) (k : ℤ) : ℕ :=
  max (k + (N : ℤ) + 1).toNat 1

theorem one_le_bfDenom (N : ℕ) (k : ℤ) : 1 ≤ bfDenom N k :=
  le_max_right _ _

theorem bfDenom_pos (N : ℕ) (k : ℤ) : 0 < bfDenom N k :=
  lt_of_lt_of_le one_pos (one_le_bfDenom N k)

/-- The Blackwell–Ferguson stopping probability at parameter `N` and excess
`k`: `1 / D ^ 2`, where `D` is the clamped denominator `bfDenom N k`. -/
def bfStopProb (N : ℕ) (k : ℤ) : ℝ :=
  1 / (bfDenom N k : ℝ) ^ 2

theorem bfStopProb_nonneg (N : ℕ) (k : ℤ) : 0 ≤ bfStopProb N k := by
  unfold bfStopProb
  positivity

theorem bfStopProb_le_one (N : ℕ) (k : ℤ) : bfStopProb N k ≤ 1 := by
  unfold bfStopProb
  have hD : (1 : ℝ) ≤ (bfDenom N k : ℝ) := by
    exact_mod_cast one_le_bfDenom N k
  rw [div_le_one (by positivity)]
  nlinarith

/-- The Blackwell–Ferguson maximizer strategy with parameter `N`: at every
history, stop with probability `bfStopProb N k`, where `k` is the net excess
of the minimizer's past Right plays over Left plays. -/
def blackwellFergusonStrategy (N : ℕ) : game.BehaviorStrategy false :=
  fun _ h => coinPMF (bfStopProb N (netRightExcess h))
    (bfStopProb_nonneg N _) (bfStopProb_le_one N _)

/-- The minimizer's uniform stationary strategy: Left and Right each with
probability `1/2`, after every history. -/
def uniformMinimizerStrategy : game.BehaviorStrategy true :=
  fun _ _ => coinPMF (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem uniformMinimizerStrategy_apply_true_toReal (t : ℕ) (h : game.Hist t) :
    ((uniformMinimizerStrategy t h) true).toReal = 1 / 2 :=
  coinPMF_apply_true_toReal (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem uniformMinimizerStrategy_apply_false_toReal (t : ℕ) (h : game.Hist t) :
    ((uniformMinimizerStrategy t h) false).toReal = 1 / 2 := by
  rw [uniformMinimizerStrategy, coinPMF_apply_false_toReal]
  norm_num

/-! ## Stage 2: the minimizer's uniform strategy caps the maximizer at `1/2`
exactly -/

/-- Play the maximizer strategy `dev` against the minimizer's uniform
stationary strategy. -/
def profileUniformMinimizer (dev : game.BehaviorStrategy false) : game.BehaviorProfile :=
  fun who t h => if who then uniformMinimizerStrategy t h else dev t h

@[simp] theorem profileUniformMinimizer_false (dev : game.BehaviorStrategy false) :
    profileUniformMinimizer dev false = dev := rfl

@[simp] theorem profileUniformMinimizer_true (dev : game.BehaviorStrategy false) :
    profileUniformMinimizer dev true = uniformMinimizerStrategy := rfl

theorem stageActionDist_profileUniformMinimizer (dev : game.BehaviorStrategy false)
    {t : ℕ} (h : game.Hist t) :
    game.stageActionDist (profileUniformMinimizer dev) h =
      pmfPi (fun who => if who then uniformMinimizerStrategy t h else dev t h) := rfl

/-- Against the minimizer's uniform stationary strategy, the probabilities of
ever absorbing at `.one` and of ever absorbing at `.zero` stay exactly equal
at every stage, for *every* maximizer strategy: the off-diagonal reward is
symmetric under a fair-coin minimizer, so a stop is equally likely to land at
either absorbing state regardless of how the maximizer's stopping
probabilities depend on history. -/
theorem expectedStateValue_oneIndicator_eq_zeroIndicator
    (dev : game.BehaviorStrategy false) (t : ℕ) :
    game.expectedStateValue (profileUniformMinimizer dev) .live t oneIndicator =
      game.expectedStateValue (profileUniformMinimizer dev) .live t zeroIndicator := by
  induction t with
  | zero => simp [oneIndicator, zeroIndicator]
  | succ t ih =>
      rw [game.expectedStateValue_succ, game.expectedStateValue_succ]
      have hstep : ∀ h : game.Hist t,
          expect (game.stageActionDist (profileUniformMinimizer dev) h)
              (fun a => expect (game.transition h.2 a) oneIndicator) =
            oneIndicator h.2 + (dev t h true).toReal * (1 / 2) * liveIndicator h.2 ∧
          expect (game.stageActionDist (profileUniformMinimizer dev) h)
              (fun a => expect (game.transition h.2 a) zeroIndicator) =
            zeroIndicator h.2 + (dev t h true).toReal * (1 / 2) * liveIndicator h.2 := by
        intro h
        rw [stageActionDist_profileUniformMinimizer]
        have h1 := expect_next_oneIndicator h.2
          (fun who => if who then uniformMinimizerStrategy t h else dev t h)
        have h2 := expect_next_zeroIndicator h.2
          (fun who => if who then uniformMinimizerStrategy t h else dev t h)
        simp only [Bool.false_eq_true, if_false, reduceIte] at h1 h2
        rw [uniformMinimizerStrategy_apply_true_toReal] at h1 h2
        refine ⟨by rw [h1]; ring, by rw [h2]⟩
      have honeSum :
          expect (game.histDist (profileUniformMinimizer dev) .live t)
              (fun h => expect (game.stageActionDist (profileUniformMinimizer dev) h)
                (fun a => expect (game.transition h.2 a) oneIndicator)) =
            expect (game.histDist (profileUniformMinimizer dev) .live t)
                (fun h => oneIndicator h.2) +
              expect (game.histDist (profileUniformMinimizer dev) .live t)
                (fun h => (dev t h true).toReal * (1 / 2) * liveIndicator h.2) := by
        rw [← expect_add]
        exact Math.ProbabilityMassFunction.expect_congr_on_support _ _ _ fun h _ => (hstep h).1
      have hzeroSum :
          expect (game.histDist (profileUniformMinimizer dev) .live t)
              (fun h => expect (game.stageActionDist (profileUniformMinimizer dev) h)
                (fun a => expect (game.transition h.2 a) zeroIndicator)) =
            expect (game.histDist (profileUniformMinimizer dev) .live t)
                (fun h => zeroIndicator h.2) +
              expect (game.histDist (profileUniformMinimizer dev) .live t)
                (fun h => (dev t h true).toReal * (1 / 2) * liveIndicator h.2) := by
        rw [← expect_add]
        exact Math.ProbabilityMassFunction.expect_congr_on_support _ _ _ fun h _ => (hstep h).2
      rw [honeSum, hzeroSum]
      unfold expectedStateValue at ih
      rw [ih]

/-- The three state indicators' expectations always sum to `1`, for any
behavior profile and initial state. -/
theorem expectedStateValue_liveIndicator_add_zeroIndicator_add_oneIndicator
    (σ : game.BehaviorProfile) (s₀ : game.State) (t : ℕ) :
    game.expectedStateValue σ s₀ t liveIndicator +
        game.expectedStateValue σ s₀ t zeroIndicator +
        game.expectedStateValue σ s₀ t oneIndicator = 1 := by
  unfold expectedStateValue
  rw [← expect_add, ← expect_add]
  simp [indicators_sum]

/-- Against the minimizer's uniform stationary strategy, every maximizer
strategy has expected stage payoff *exactly* `1/2`, at every stage: the
`.one`/`.zero` absorption events cancel
(`expectedStateValue_oneIndicator_eq_zeroIndicator`), leaving only the
constant `1/2` reward earned while still live. -/
theorem expectedStagePayoff_eq_half_of_uniformMinimizer
    (dev : game.BehaviorStrategy false) (t : ℕ) :
    game.expectedStagePayoff (profileUniformMinimizer dev) .live t false = 1 / 2 := by
  have hstep : ∀ h : game.Hist t,
      game.stageEUAt (profileUniformMinimizer dev) h false =
        oneIndicator h.2 + (1 / 2) * liveIndicator h.2 := by
    intro h
    unfold stageEUAt
    rw [stageActionDist_profileUniformMinimizer]
    have hthis := expect_stagePayoff_maximizer h.2
      (fun who => if who then uniformMinimizerStrategy t h else dev t h)
    simp only [Bool.false_eq_true, if_false, reduceIte] at hthis
    rw [uniformMinimizerStrategy_apply_true_toReal] at hthis
    rw [hthis]; ring
  unfold expectedStagePayoff
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _ fun h _ => hstep h,
    expect_add, expect_const_mul]
  have hone := expectedStateValue_oneIndicator_eq_zeroIndicator dev t
  have hsum := expectedStateValue_liveIndicator_add_zeroIndicator_add_oneIndicator
    (profileUniformMinimizer dev) .live t
  unfold expectedStateValue at hone hsum
  rw [← hone] at hsum
  linarith

/-- **Stage 2, easy direction.** Against the minimizer's uniform stationary
strategy, every maximizer strategy has finite-average payoff *exactly* `1/2`
at every positive horizon: the off-diagonal reward table is symmetric under a
fair-coin minimizer, so no history-dependent maximizer strategy — in
particular neither `blackwellFergusonStrategy N` nor any deviation from it —
can do better (or worse) than `1/2` against it. This gives the maximizer's
deviation cap for a prospective uniform equilibrium at `(1/2, -1/2)`. -/
theorem finiteAveragePayoff_eq_half_of_uniformMinimizer
    (dev : game.BehaviorStrategy false) {T : ℕ} (hT : 0 < T) :
    game.finiteAveragePayoff .live T (profileUniformMinimizer dev) false = 1 / 2 := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rw [Finset.sum_congr rfl fun t _ => expectedStagePayoff_eq_half_of_uniformMinimizer dev t,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  field_simp

/-- Replacing the maximizer's component of any uniform-minimizer profile by
`dev` gives back `profileUniformMinimizer dev`: the shape needed to read
`finiteAveragePayoff_eq_half_of_uniformMinimizer` as the maximizer's
deviation cap in `isUniformEquilibriumPayoff_of_deviation_caps`'s sense. -/
theorem update_profileUniformMinimizer_false
    (baseDev dev : game.BehaviorStrategy false) :
    Function.update (profileUniformMinimizer baseDev) false dev =
      profileUniformMinimizer dev := by
  funext who t h
  cases who
  · simp [profileUniformMinimizer]
  · simp [profileUniformMinimizer]

/-! ## Stage 3a: collapsing a deterministic minimizer schedule to a
`TimeStateMixedProfile`

Against `blackwellFergusonStrategy N`, the live histories at any stage carry
no maximizer-side information: on any live branch the maximizer's own past
actions have all been `false` (continue), since a single `true` (stop) would
have left `.live` for good.  So when the minimizer plays a *fixed calendar
schedule* `d : ℕ → Bool` (`BigMatchMarkov.minimizerSchedule d`), the combined
profile's induced play is *exactly* the play of the simple, state/time-only
`TimeStateMixedProfile` `bfSeqProfile N d`: the excess `netRightExcess h`
appearing in `blackwellFergusonStrategy`'s stopping probability collapses,
along every reachable history, to the deterministic `bfExcess d t`.  This
lets every downstream computation reuse `BigMatch.lean`'s already-proved
`TimeStateMixedProfile` machinery (`stateLiveProbability_eq_prod`,
`finiteAveragePayoff_maximizer`, etc.) instead of re-deriving it. -/

/-- Deterministic net excess of a schedule `d`: the calendar-time analogue of
`netRightExcess`. -/
def bfExcess (d : ℕ → Bool) (t : ℕ) : ℤ :=
  ∑ j : Fin t, if d j then (1 : ℤ) else -1

@[simp] theorem bfExcess_zero (d : ℕ → Bool) : bfExcess d 0 = 0 := by
  simp [bfExcess]

theorem bfExcess_succ (d : ℕ → Bool) (t : ℕ) :
    bfExcess d (t + 1) = bfExcess d t + (if d t then 1 else -1) := by
  unfold bfExcess
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rfl

/-- The Blackwell–Ferguson maximizer against the fixed schedule `d`, as a
`TimeStateMixedProfile` (state-independent, since the excess along a
`d`-consistent history never depends on the current state). -/
def bfSeqProfile (N : ℕ) (d : ℕ → Bool) : TimeStateMixedProfile :=
  fun t _s who =>
    if who then PMF.pure (d t) else
      coinPMF (bfStopProb N (bfExcess d t))
        (bfStopProb_nonneg N _) (bfStopProb_le_one N _)

/-- The full profile: `blackwellFergusonStrategy N` for the maximizer,
`minimizerSchedule d` for the minimizer. -/
def bfSeqFullProfile (N : ℕ) (d : ℕ → Bool) : game.BehaviorProfile :=
  Function.update (fun _ => blackwellFergusonStrategy N) true (minimizerSchedule d)

@[simp] theorem bfSeqFullProfile_false (N : ℕ) (d : ℕ → Bool) :
    bfSeqFullProfile N d false = blackwellFergusonStrategy N := rfl

@[simp] theorem bfSeqFullProfile_true (N : ℕ) (d : ℕ → Bool) :
    bfSeqFullProfile N d true = minimizerSchedule d := rfl

/-- On every history reached under `bfSeqFullProfile N d`, the minimizer's
recorded past actions agree exactly with the schedule `d`. -/
theorem minimizerActionAt_eq_of_mem_support_bfSeqFullProfile (N : ℕ) (d : ℕ → Bool) :
    ∀ (t : ℕ) (h : game.Hist t),
      h ∈ (game.histDist (bfSeqFullProfile N d) .live t).support →
      ∀ j : Fin t, minimizerActionAt h j = d j := by
  intro t
  induction t with
  | zero => intro h _ j; exact absurd j.isLt (by omega)
  | succ t ih =>
    intro h' hh' j
    rw [game.mem_support_histDist_succ] at hh'
    obtain ⟨h, hh, a, ha, s', hs', rfl⟩ := hh'
    have hat : a true = d t := by
      have h0 : (game.stageActionDist (bfSeqFullProfile N d) h) a ≠ 0 := by
        rwa [PMF.mem_support_iff] at ha
      rw [stageActionDist, pmfPi_apply] at h0
      have h0' := Finset.prod_ne_zero_iff.mp h0 true (Finset.mem_univ true)
      rw [bfSeqFullProfile_true, minimizerSchedule] at h0'
      have hmem : a true ∈ (PMF.pure (d t)).support := by
        rwa [PMF.mem_support_iff]
      rwa [PMF.support_pure, Set.mem_singleton_iff] at hmem
    induction j using Fin.lastCases with
    | last => simpa [minimizerActionAt] using hat
    | cast j' => simpa [minimizerActionAt] using ih h hh j'

/-- Consequently the excess itself collapses along every reachable history. -/
theorem netRightExcess_eq_of_mem_support_bfSeqFullProfile (N : ℕ) (d : ℕ → Bool) (t : ℕ)
    (h : game.Hist t) (hh : h ∈ (game.histDist (bfSeqFullProfile N d) .live t).support) :
    netRightExcess h = bfExcess d t := by
  unfold netRightExcess bfExcess
  exact Finset.sum_congr rfl fun j _ => by
    rw [minimizerActionAt_eq_of_mem_support_bfSeqFullProfile N d t h hh j]

/-- Along every reachable history, `bfSeqFullProfile` and the collapsed
`TimeStateMixedProfile` `bfSeqProfile` choose the same stage mixed action. -/
theorem stageActionDist_eq_of_mem_support_bfSeqFullProfile (N : ℕ) (d : ℕ → Bool) (t : ℕ)
    (h : game.Hist t) (hh : h ∈ (game.histDist (bfSeqFullProfile N d) .live t).support) :
    game.stageActionDist (bfSeqFullProfile N d) h =
      game.stageActionDist (timeStateBehaviorProfile (bfSeqProfile N d)) h := by
  rw [stageActionDist_timeStateBehaviorProfile]
  change pmfPi (fun i => bfSeqFullProfile N d i t h) = pmfPi (bfSeqProfile N d t h.2)
  congr 1
  funext who
  cases who
  · change blackwellFergusonStrategy N t h = bfSeqProfile N d t h.2 false
    unfold blackwellFergusonStrategy bfSeqProfile
    simp only [Bool.false_eq_true, if_false]
    congr 2
    exact netRightExcess_eq_of_mem_support_bfSeqFullProfile N d t h hh
  · change minimizerSchedule d t h = bfSeqProfile N d t h.2 true
    unfold minimizerSchedule bfSeqProfile
    simp

/-- **Stage 3a, the observation-collapse lemma.**  Against
`blackwellFergusonStrategy N`, playing the fixed calendar schedule `d`
induces exactly the same distribution over histories as the collapsed
`TimeStateMixedProfile` `bfSeqProfile N d` — every downstream computation
(`finiteAveragePayoff`, `expectedStagePayoff`, `stateLiveProbability`, …) can
therefore reuse `BigMatch.lean`'s already-proved `TimeStateMixedProfile`
machinery verbatim. -/
theorem histDist_eq_bfSeqProfile (N : ℕ) (d : ℕ → Bool) :
    ∀ T : ℕ, game.histDist (bfSeqFullProfile N d) .live T =
      game.histDist (timeStateBehaviorProfile (bfSeqProfile N d)) .live T := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [game.histDist_succ, game.histDist_succ, ih]
    apply Math.ProbabilityMassFunction.bind_congr_on_support
    intro h hh
    have hh' : h ∈ (game.histDist (bfSeqFullProfile N d) .live T).support := by
      rw [ih]; exact hh
    rw [stageActionDist_eq_of_mem_support_bfSeqFullProfile N d T h hh']

/-- Finite-average payoffs collapse the same way. -/
theorem finiteAveragePayoff_eq_bfSeqProfile (N : ℕ) (d : ℕ → Bool) (T : ℕ) (who : Player) :
    game.finiteAveragePayoff .live T (bfSeqFullProfile N d) who =
      game.finiteAveragePayoff .live T (timeStateBehaviorProfile (bfSeqProfile N d)) who := by
  unfold finiteAveragePayoff
  rw [histDist_eq_bfSeqProfile N d T]

/-! ## Stage 3b: the deterministic-sequence estimate (exact-identity route)

The Blackwell–Ferguson potential `bfPotential D := (D - 1) / (2 D)` and the
excess-denominator recursion `bfDenom` support an *exact* telescoping
identity (no per-step slack) away from the `D = 1` boundary, so the
quantity `bfM := stateOneProbability + stateLiveProbability * bfPotential`
is monotone nondecreasing along every schedule — a pure real-algebra fact,
verified below stage by stage. -/

/-- The Blackwell–Ferguson potential: `φ(1) = 0`, `φ D ∈ [0, 1/2)` for `D ≥ 1`,
`φ D → 1/2` as `D → ∞`. -/
def bfPotential (D : ℕ) : ℝ := ((D : ℝ) - 1) / (2 * D)

@[simp] theorem bfPotential_one : bfPotential 1 = 0 := by norm_num [bfPotential]

theorem bfPotential_nonneg {D : ℕ} (hD : 1 ≤ D) : 0 ≤ bfPotential D := by
  unfold bfPotential
  have : (1:ℝ) ≤ D := by exact_mod_cast hD
  positivity

theorem bfPotential_lt_half {D : ℕ} (hD : 1 ≤ D) : bfPotential D < 1 / 2 := by
  unfold bfPotential
  have hD' : (1:ℝ) ≤ D := by exact_mod_cast hD
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- Off the clamp boundary, a Right step advances the denominator by one. -/
theorem bfDenom_succ_of_right (N : ℕ) (k : ℤ) (hk : 2 ≤ bfDenom N k) :
    bfDenom N (k + 1) = bfDenom N k + 1 := by
  unfold bfDenom at *
  omega

/-- Off the clamp boundary, a Left step retreats the denominator by one. -/
theorem bfDenom_succ_of_left (N : ℕ) (k : ℤ) (hk : 2 ≤ bfDenom N k) :
    bfDenom N (k - 1) = bfDenom N k - 1 := by
  unfold bfDenom at *
  omega

@[simp] theorem stopProbability_bfSeqProfile (N : ℕ) (d : ℕ → Bool) (t : ℕ) :
    stopProbability (bfSeqProfile N d) t = bfStopProb N (bfExcess d t) := by
  unfold stopProbability bfSeqProfile
  simp only [Bool.false_eq_true, if_false]
  exact coinPMF_apply_true_toReal _ _ _

@[simp] theorem rightProbability_bfSeqProfile (N : ℕ) (d : ℕ → Bool) (t : ℕ) :
    rightProbability (bfSeqProfile N d) t = if d t then 1 else 0 := by
  unfold rightProbability bfSeqProfile
  simp only [if_true]
  cases d t <;> simp [PMF.pure_apply]

/-- The Blackwell–Ferguson potential process:
`M t := stateOneProbability t + stateLiveProbability t * φ (D t)`, where
`D t` is the excess denominator at stage `t`. -/
def bfM (N : ℕ) (d : ℕ → Bool) (t : ℕ) : ℝ :=
  stateOneProbability (bfSeqProfile N d) t +
    stateLiveProbability (bfSeqProfile N d) t * bfPotential (bfDenom N (bfExcess d t))

/-- Exact identity behind the Right step of Lemma 1: holds for every `D ≥ 1`,
including `D = 1` (where both sides vanish). -/
theorem bfPotential_right_id (D : ℕ) :
    (1 - 1 / (D : ℝ) ^ 2) * bfPotential (D + 1) = bfPotential D := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · simp [hD, bfPotential]
  · unfold bfPotential
    have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hD0 : (D : ℝ) ≠ 0 := by linarith
    push_cast
    field_simp
    ring

/-- Exact identity behind the Left step of Lemma 1: holds for every `D ≥ 2`. -/
theorem bfPotential_left_id {D : ℕ} (hD : 2 ≤ D) :
    1 / (D : ℝ) ^ 2 + (1 - 1 / (D : ℝ) ^ 2) * bfPotential (D - 1) = bfPotential D := by
  unfold bfPotential
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hcast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
    have h1 : 1 ≤ D := by omega
    rw [Nat.cast_sub h1]
    norm_num
  rw [hcast]
  have hD0 : (D : ℝ) ≠ 0 := by linarith
  have hD1 : (D : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem stateLiveProbability_nonneg (m : TimeStateMixedProfile) (t : ℕ) :
    0 ≤ stateLiveProbability m t := by
  unfold stateLiveProbability expectedStateValue
  exact expect_nonneg _ _ fun h => by cases h.2 <;> simp [liveIndicator]

theorem stateOneProbability_nonneg (m : TimeStateMixedProfile) (t : ℕ) :
    0 ≤ stateOneProbability m t := by
  unfold stateOneProbability expectedStateValue
  exact expect_nonneg _ _ fun h => by cases h.2 <;> simp [oneIndicator]

/-- **Lemma 1, the algebraic heart of Stage 3b.**  The potential process
`bfM` is monotone nondecreasing along every schedule. -/
theorem bfM_le_succ (N : ℕ) (d : ℕ → Bool) (t : ℕ) : bfM N d t ≤ bfM N d (t + 1) := by
  unfold bfM
  rw [stateOneProbability_succ, stateLiveProbability_succ,
    stopProbability_bfSeqProfile, rightProbability_bfSeqProfile, bfExcess_succ]
  have hS : 0 ≤ stateLiveProbability (bfSeqProfile N d) t :=
    stateLiveProbability_nonneg _ t
  set S := stateLiveProbability (bfSeqProfile N d) t with hSdef
  set O := stateOneProbability (bfSeqProfile N d) t with hOdef
  set k := bfExcess d t with hkdef
  have hDpos : 1 ≤ bfDenom N k := one_le_bfDenom N k
  rcases eq_or_lt_of_le hDpos with hD1 | hD2
  · have hp1 : bfStopProb N k = 1 := by
      unfold bfStopProb
      rw [← hD1]
      norm_num
    rcases hdt : d t
    · simp only [Bool.false_eq_true, if_false]
      rw [hp1]
      have : bfPotential (bfDenom N k) = 0 := by rw [← hD1]; exact bfPotential_one
      rw [this]
      nlinarith
    · simp only [if_true]
      rw [hp1]
      have : bfPotential (bfDenom N k) = 0 := by rw [← hD1]; exact bfPotential_one
      rw [this]
      nlinarith
  · rcases hdt : d t
    · have hDenom' : bfDenom N (k + -1) = bfDenom N k - 1 := by
        have : k + (-1 : ℤ) = k - 1 := by ring
        rw [this]; exact bfDenom_succ_of_left N k hD2
      simp only [Bool.false_eq_true, if_false]
      rw [hDenom']
      unfold bfStopProb
      have hid := bfPotential_left_id (D := bfDenom N k) hD2
      nlinarith [hid]
    · have hDenom' : bfDenom N (k + 1) = bfDenom N k + 1 :=
        bfDenom_succ_of_right N k hD2
      simp only [if_true]
      rw [hDenom']
      unfold bfStopProb
      have hid := bfPotential_right_id (bfDenom N k)
      nlinarith [hid]

/-- Corollary: the potential process never drops below its initial value. -/
theorem bfM_zero_le (N : ℕ) (d : ℕ → Bool) (t : ℕ) : bfM N d 0 ≤ bfM N d t := by
  induction t with
  | zero => exact le_refl _
  | succ t ih => exact ih.trans (bfM_le_succ N d t)

theorem bfM_zero_eq (N : ℕ) (d : ℕ → Bool) : bfM N d 0 = bfPotential (N + 1) := by
  unfold bfM
  rw [stateOneProbability_zero, stateLiveProbability_zero, bfExcess_zero]
  have hD0 : bfDenom N 0 = N + 1 := by unfold bfDenom; omega
  rw [hD0]
  ring

/-- **Corollary of Lemma 1.** The potential's `1/2 - 1/(2(N+1))` floor holds
at every stage, for every schedule. -/
theorem bfM_ge_half_sub (N : ℕ) (d : ℕ → Bool) (t : ℕ) :
    1 / 2 - 1 / (2 * ((N : ℝ) + 1)) ≤ bfM N d t := by
  have h1 := bfM_zero_le N d t
  rw [bfM_zero_eq] at h1
  have h2 : bfPotential (N + 1) = 1 / 2 - 1 / (2 * ((N : ℝ) + 1)) := by
    unfold bfPotential
    push_cast
    have hN0 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  linarith [h1, h2.symm.le, h2.le]

/-- **Lemma 2, the stage-payoff formula.**  From Stage 3a's bridge plus
`BigMatch.lean`'s `expectedStagePayoff_maximizer`. -/
theorem bfStagePayoff_eq (N : ℕ) (d : ℕ → Bool) (t : ℕ) :
    game.expectedStagePayoff (timeStateBehaviorProfile (bfSeqProfile N d)) .live t false =
      stateOneProbability (bfSeqProfile N d) t +
        stateLiveProbability (bfSeqProfile N d) t *
          (if d t then 1 - bfStopProb N (bfExcess d t) else bfStopProb N (bfExcess d t)) := by
  rw [expectedStagePayoff_maximizer]
  congr 1
  unfold liveStageReward
  simp only [stopProbability_bfSeqProfile, rightProbability_bfSeqProfile]
  cases d t <;> simp <;> ring

/-- **Lemma 3, the per-stage lower bound.** -/
theorem bfStagePayoff_ge (N : ℕ) (d : ℕ → Bool) (t : ℕ) :
    bfM N d 0 +
        (1 / 2) * stateLiveProbability (bfSeqProfile N d) t * (if d t then (1 : ℝ) else -1) -
        stateLiveProbability (bfSeqProfile N d) t * bfStopProb N (bfExcess d t) ≤
      game.expectedStagePayoff (timeStateBehaviorProfile (bfSeqProfile N d)) .live t false := by
  rw [bfStagePayoff_eq]
  set S := stateLiveProbability (bfSeqProfile N d) t with hSdef
  set O := stateOneProbability (bfSeqProfile N d) t with hOdef
  set p := bfStopProb N (bfExcess d t) with hpdef
  have hS : 0 ≤ S := stateLiveProbability_nonneg _ t
  have hp : 0 ≤ p := bfStopProb_nonneg N _
  have hDpos : 1 ≤ bfDenom N (bfExcess d t) := one_le_bfDenom N _
  have hphalf : bfPotential (bfDenom N (bfExcess d t)) < 1 / 2 := bfPotential_lt_half hDpos
  have hMt : bfM N d 0 ≤ O + S * bfPotential (bfDenom N (bfExcess d t)) := bfM_zero_le N d t
  have hOS : bfM N d 0 ≤ O + S / 2 := by nlinarith [hMt, hphalf, hS]
  split_ifs with hdt <;> nlinarith [hOS, hS, hp]

/-- Whenever the live mass is still positive at stage `t`, the excess is
bounded below by `-N`: once the excess drops to `-N`, the denominator
clamps to `1`, forcing certain absorption at the *next* stage. -/
theorem bfExcess_ge_of_stateLiveProbability_pos (N : ℕ) (d : ℕ → Bool) :
    ∀ t, 0 < stateLiveProbability (bfSeqProfile N d) t → -(N : ℤ) ≤ bfExcess d t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro hpos
    rw [stateLiveProbability_succ, stopProbability_bfSeqProfile] at hpos
    have hSt : 0 < stateLiveProbability (bfSeqProfile N d) t := by
      rcases (stateLiveProbability_nonneg (bfSeqProfile N d) t).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hpos; simp at hpos
    have hp1 : bfStopProb N (bfExcess d t) < 1 := by
      by_contra h
      push Not at h
      have hp1' : bfStopProb N (bfExcess d t) = 1 :=
        le_antisymm (bfStopProb_le_one N _) h
      rw [hp1'] at hpos
      simp at hpos
    have hD2 : 2 ≤ bfDenom N (bfExcess d t) := by
      by_contra h
      push Not at h
      have hD1 : bfDenom N (bfExcess d t) = 1 := by
        have := one_le_bfDenom N (bfExcess d t); omega
      have hp1' : bfStopProb N (bfExcess d t) = 1 := by
        unfold bfStopProb; rw [hD1]; norm_num
      linarith [hp1, hp1']
    have hk_ge : -(N : ℤ) + 1 ≤ bfExcess d t := by
      unfold bfDenom at hD2
      omega
    rw [bfExcess_succ]
    rcases hdt : d t <;> omega

/-- **Lemma 5, total absorption.** The absorbed mass never exceeds the
initial live mass `1`. -/
theorem bfTotalAbsorb_le (N : ℕ) (d : ℕ → Bool) (T : ℕ) :
    ∑ t ∈ Finset.range T,
        stateLiveProbability (bfSeqProfile N d) t * bfStopProb N (bfExcess d t) ≤ 1 := by
  have key : ∀ T, ∑ t ∈ Finset.range T,
      stateLiveProbability (bfSeqProfile N d) t * bfStopProb N (bfExcess d t) =
        1 - stateLiveProbability (bfSeqProfile N d) T := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, ih, ← stopProbability_bfSeqProfile,
        stateLiveProbability_succ]
      ring
  rw [key T]
  have := stateLiveProbability_nonneg (bfSeqProfile N d) T
  linarith

theorem stateLiveProbability_le_one (m : TimeStateMixedProfile) (t : ℕ) :
    stateLiveProbability m t ≤ 1 := by
  unfold stateLiveProbability expectedStateValue
  have h1 : expect (game.histDist (timeStateBehaviorProfile m) .live t) (fun _ => (1 : ℝ)) = 1 :=
    expect_const _ _
  rw [← h1]
  exact expect_mono _ _ _ fun h => by cases h.2 <;> simp [liveIndicator]

/-- The live mass is nonincreasing. -/
theorem bfLive_antitone (N : ℕ) (d : ℕ → Bool) (t : ℕ) :
    stateLiveProbability (bfSeqProfile N d) (t + 1) ≤
      stateLiveProbability (bfSeqProfile N d) t := by
  rw [stateLiveProbability_succ, stopProbability_bfSeqProfile]
  have hp := bfStopProb_nonneg N (bfExcess d t)
  have hS := stateLiveProbability_nonneg (bfSeqProfile N d) t
  nlinarith

/-- The `±1`-step sum matches the excess: the discrete integral of `δ`. -/
theorem sum_range_bfDelta_eq (d : ℕ → Bool) (n : ℕ) :
    ∑ i ∈ Finset.range n, (if d i then (1 : ℝ) else -1) = (bfExcess d n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, bfExcess_succ]
    push_cast
    split_ifs <;> ring

/-- **Lemma 4, the Abel-summation bound.** The negative drift of `S t * δ t`
is bounded uniformly in the horizon, by summation by parts against the
excess bound `bfExcess_ge_of_stateLiveProbability_pos`. -/
theorem bfAbel_bound (N : ℕ) (d : ℕ → Bool) (T : ℕ) :
    -(2 * ((N : ℝ) + 1)) ≤ ∑ t ∈ Finset.range T,
      stateLiveProbability (bfSeqProfile N d) t * (if d t then (1 : ℝ) else -1) := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    simp only [Finset.range_zero, Finset.sum_empty]
    have : (0:ℝ) ≤ 2 * ((N:ℝ) + 1) := by positivity
    linarith
  set S : ℕ → ℝ := fun t => stateLiveProbability (bfSeqProfile N d) t with hSdef
  set k : ℕ → ℝ := fun t => (bfExcess d t : ℝ) with hkdef
  have hbp := Finset.sum_range_by_parts S (fun t => (if d t then (1 : ℝ) else -1)) T
  simp only [smul_eq_mul] at hbp
  have hG : ∀ n, (∑ i ∈ Finset.range n, (if d i then (1 : ℝ) else -1)) = k n := fun n =>
    sum_range_bfDelta_eq d n
  simp_rw [hG] at hbp
  rw [hbp]
  have hbound1 : -((N : ℝ) + 1) ≤ S (T - 1) * k T := by
    rcases eq_or_lt_of_le (stateLiveProbability_nonneg (bfSeqProfile N d) (T - 1))
      with hS0 | hS0
    · have hz : S (T - 1) = 0 := hS0.symm
      rw [hz]
      have hN0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      nlinarith
    · have hki : -(N : ℤ) ≤ bfExcess d (T - 1) :=
        bfExcess_ge_of_stateLiveProbability_pos N d (T - 1) hS0
      have hki1 : -(N : ℤ) - 1 ≤ bfExcess d T := by
        have hTeq : T = (T - 1) + 1 := by omega
        rw [hTeq, bfExcess_succ]
        split_ifs <;> omega
      have hkT : (-(N : ℝ) - 1) ≤ k T := by
        change (-(N : ℝ) - 1) ≤ (bfExcess d T : ℝ); exact_mod_cast hki1
      have hSle1 : S (T - 1) ≤ 1 := stateLiveProbability_le_one _ _
      have hSnn : 0 ≤ S (T - 1) := hS0.le
      nlinarith [hkT, hSle1, hSnn]
  have hbound2 : (∑ i ∈ Finset.range (T - 1), (S (i + 1) - S i) * k (i + 1)) ≤ (N : ℝ) + 1 := by
    have hterm : ∀ i ∈ Finset.range (T - 1),
        (S (i + 1) - S i) * k (i + 1) ≤ (S i - S (i + 1)) * ((N : ℝ) + 1) := by
      intro i _
      have hci : 0 ≤ S i - S (i + 1) := by
        have hanti : S (i + 1) ≤ S i := bfLive_antitone N d i
        linarith
      rcases eq_or_lt_of_le (stateLiveProbability_nonneg (bfSeqProfile N d) i) with hS0 | hS0
      · have hSi : S i = 0 := hS0.symm
        have hSi1 : S (i + 1) = 0 := by
          have hanti : S (i + 1) ≤ S i := bfLive_antitone N d i
          have hnn : (0 : ℝ) ≤ S (i + 1) := stateLiveProbability_nonneg _ _
          linarith
        rw [hSi, hSi1]
        norm_num
      · have hki : -(N : ℤ) ≤ bfExcess d i :=
          bfExcess_ge_of_stateLiveProbability_pos N d i hS0
        have hki1 : -(N : ℤ) - 1 ≤ bfExcess d (i + 1) := by
          rw [bfExcess_succ]; split_ifs <;> omega
        have hkv : (-(N : ℝ) - 1) ≤ k (i + 1) := by
          change (-(N : ℝ) - 1) ≤ (bfExcess d (i + 1) : ℝ); exact_mod_cast hki1
        nlinarith [hci, hkv]
    calc ∑ i ∈ Finset.range (T - 1), (S (i + 1) - S i) * k (i + 1)
        ≤ ∑ i ∈ Finset.range (T - 1), (S i - S (i + 1)) * ((N : ℝ) + 1) :=
          Finset.sum_le_sum hterm
      _ = ((N : ℝ) + 1) * ∑ i ∈ Finset.range (T - 1), (S i - S (i + 1)) := by
          rw [Finset.mul_sum]; congr 1; funext i; ring
      _ = ((N : ℝ) + 1) * (S 0 - S (T - 1)) := by
        rw [Math.sum_range_sub_succ]
      _ ≤ (N : ℝ) + 1 := by
          have h1 : S 0 = 1 := stateLiveProbability_zero _
          have h2 : 0 ≤ S (T - 1) := stateLiveProbability_nonneg _ _
          nlinarith [h1, h2]
  linarith [hbound1, hbound2]

/-- **Assembly, part 1.** Summing Lemma 3 over the horizon and applying
Lemmas 4 and 5. -/
theorem bfFiniteAverage_ge (N : ℕ) (d : ℕ → Bool) (T : ℕ) (hT : 0 < T) :
    bfM N d 0 - (((N : ℝ) + 1) + 1) / T ≤
      game.finiteAveragePayoff .live T (timeStateBehaviorProfile (bfSeqProfile N d)) false := by
  have hsum_le : ∑ t ∈ Finset.range T,
      (bfM N d 0 +
          (1 / 2) * stateLiveProbability (bfSeqProfile N d) t * (if d t then (1 : ℝ) else -1) -
          stateLiveProbability (bfSeqProfile N d) t * bfStopProb N (bfExcess d t)) ≤
      ∑ t ∈ Finset.range T,
        game.expectedStagePayoff (timeStateBehaviorProfile (bfSeqProfile N d)) .live t false :=
    Finset.sum_le_sum fun t _ => bfStagePayoff_ge N d t
  have hstep : ∀ t, (bfM N d 0 +
      (1 / 2) * stateLiveProbability (bfSeqProfile N d) t * (if d t then (1 : ℝ) else -1) -
      stateLiveProbability (bfSeqProfile N d) t * bfStopProb N (bfExcess d t)) =
      bfM N d 0 +
        (1 / 2) * (stateLiveProbability (bfSeqProfile N d) t * (if d t then (1 : ℝ) else -1)) -
        stateLiveProbability (bfSeqProfile N d) t * bfStopProb N (bfExcess d t) := fun t => by ring
  simp_rw [hstep] at hsum_le
  have hlhs_eq : ∑ t ∈ Finset.range T,
      (bfM N d 0 +
          (1 / 2) * (stateLiveProbability (bfSeqProfile N d) t *
            (if d t then (1 : ℝ) else -1)) -
          stateLiveProbability (bfSeqProfile N d) t * bfStopProb N (bfExcess d t)) =
      (T : ℝ) * bfM N d 0 +
        (1 / 2) * (∑ t ∈ Finset.range T,
          stateLiveProbability (bfSeqProfile N d) t * (if d t then (1 : ℝ) else -1)) -
        ∑ t ∈ Finset.range T,
          stateLiveProbability (bfSeqProfile N d) t * bfStopProb N (bfExcess d t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Finset.mul_sum]
  rw [hlhs_eq] at hsum_le
  have h4 := bfAbel_bound N d T
  have h5 := bfTotalAbsorb_le N d T
  have hsum_ge : (T : ℝ) * bfM N d 0 - (((N : ℝ) + 1) + 1) ≤
      ∑ t ∈ Finset.range T,
        game.expectedStagePayoff (timeStateBehaviorProfile (bfSeqProfile N d)) .live t false := by
    linarith [hsum_le, h4, h5]
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hTinv : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum_ge hTinv
  have hrw : (T : ℝ)⁻¹ * ((T : ℝ) * bfM N d 0 - (((N : ℝ) + 1) + 1)) =
      bfM N d 0 - (((N : ℝ) + 1) + 1) / T := by
    field_simp
  rw [hrw] at hmul
  exact hmul

/-- **Stage 3b, the deterministic-sequence estimate.**  For every `ε > 0`
there is a Blackwell–Ferguson parameter `N` and a horizon `T₀` past which the
finite-average payoff against *every* deterministic minimizer schedule `d`
is within `ε` of `1/2`, from below. -/
theorem bfSeq_eventually_ge_half (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ T₀ : ℕ, ∀ d : ℕ → Bool, ∀ T, T₀ ≤ T →
      1 / 2 - ε ≤ game.finiteAveragePayoff .live T
        (timeStateBehaviorProfile (bfSeqProfile N d)) false := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hN' : (1 : ℝ) < (N : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hN; exact hN
  have hNε : 1 / (2 * ((N : ℝ) + 1)) ≤ ε / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hN', hε]
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt (2 * (((N : ℝ) + 1) + 1) / ε)
  refine ⟨N, max T₀ 1, fun d T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right T₀ 1) hT)
  have hTge : (T₀ : ℝ) ≤ T := by
    have : T₀ ≤ T := le_trans (le_max_left T₀ 1) hT
    exact_mod_cast this
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT0
  have h1 := bfFiniteAverage_ge N d T hT0
  have h2 := bfM_ge_half_sub N d 0
  have hT₀' : 2 * (((N : ℝ) + 1) + 1) < (T₀ : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hT₀; exact hT₀
  have htail : (((N : ℝ) + 1) + 1) / T ≤ ε / 2 := by
    rw [div_le_iff₀ hTreal]
    have hstep1 : (((N : ℝ) + 1) + 1) * 2 < (T₀ : ℝ) * ε := by linarith [hT₀']
    have hstep2 : (T₀ : ℝ) * ε ≤ (T : ℝ) * ε := by
      apply mul_le_mul_of_nonneg_right hTge hε.le
    nlinarith [hstep1, hstep2]
  linarith [h1, h2, hNε, htail]

/-! ## Stage 3c: toward general minimizer deviations

`bfDevProfile N dev` pairs `blackwellFergusonStrategy N` for the maximizer
with an *arbitrary* minimizer behavior strategy `dev` (as opposed to a fixed
calendar schedule `minimizerSchedule d`).  The excess bound
`bfExcess_ge_of_stateLiveProbability_pos` generalizes to this setting
essentially verbatim, since it only uses that `blackwellFergusonStrategy`'s
own stopping probability is forced to `1` once the excess denominator
clamps to `1` (a fact about the maximizer's own coin, independent of what
the minimizer does). -/

/-- The joint profile: `blackwellFergusonStrategy N` for the maximizer, an
*arbitrary* behavior strategy `dev` for the minimizer. -/
def bfDevProfile (N : ℕ) (dev : game.BehaviorStrategy true) : game.BehaviorProfile :=
  Function.update (fun _ => blackwellFergusonStrategy N) true dev

@[simp] theorem bfDevProfile_false (N : ℕ) (dev : game.BehaviorStrategy true) :
    bfDevProfile N dev false = blackwellFergusonStrategy N := rfl

@[simp] theorem bfDevProfile_true (N : ℕ) (dev : game.BehaviorStrategy true) :
    bfDevProfile N dev true = dev := rfl

theorem stageActionDist_bfDevProfile (N : ℕ) (dev : game.BehaviorStrategy true)
    {t : ℕ} (h : game.Hist t) :
    game.stageActionDist (bfDevProfile N dev) h =
      pmfPi (fun i => if i then dev t h else blackwellFergusonStrategy N t h) := by
  unfold stageActionDist bfDevProfile
  congr 1
  funext i
  cases i <;> simp

/-- Extending a history by one stage extends the net excess by the sign of
the minimizer's action at the new stage: the general (non-schedule) analogue
of `bfExcess_succ`. -/
theorem netRightExcess_snoc {t : ℕ} (h : game.Hist t) (a : game.JointAct) (s' : game.State) :
    netRightExcess ((Fin.snoc h.1 (h.2, a), s') : game.Hist (t + 1)) =
      netRightExcess h + (if a true then (1 : ℤ) else -1) := by
  unfold netRightExcess minimizerActionAt
  rw [Fin.sum_univ_castSucc]
  simp

/-- **Generalization of `bfExcess_ge_of_stateLiveProbability_pos` to
arbitrary minimizer deviations.**  Whenever a history is *live* and reachable
under `blackwellFergusonStrategy N` paired with *any* minimizer behavior
strategy `dev`, its net excess is bounded below by `-N`: once the excess
denominator clamps to `1`, the maximizer's own coin is forced to stop with
probability `1`, so every reachable continuation absorbs — a fact that
depends only on the maximizer's own strategy, hence is independent of
`dev`. -/
theorem netRightExcess_ge_of_live_of_mem_support (N : ℕ) (dev : game.BehaviorStrategy true) :
    ∀ (t : ℕ) (h : game.Hist t),
      h ∈ (game.histDist (bfDevProfile N dev) .live t).support → h.2 = .live →
      -(N : ℤ) ≤ netRightExcess h := by
  intro t
  induction t with
  | zero => intro h _ _; simp
  | succ t ih =>
    intro h' hh' hlive
    rw [game.mem_support_histDist_succ] at hh'
    obtain ⟨h, hh, a, ha, s', hs', rfl⟩ := hh'
    have hs'eq : s' = nextState h.2 a := by
      rw [transition_eq_pure, PMF.support_pure, Set.mem_singleton_iff] at hs'
      exact hs'
    have hns : nextState h.2 a = .live := hs'eq ▸ hlive
    have hcase : h.2 = .live ∧ a false = false := by
      unfold nextState at hns
      rcases hs2 : h.2 with _ | _ | _
      · refine ⟨rfl, ?_⟩
        rcases hfa : a false with _ | _
        · rfl
        · exfalso
          rw [hs2, hfa] at hns
          rcases hta : a true with _ | _ <;> rw [hta] at hns <;> simp at hns
      · rw [hs2] at hns; simp at hns
      · rw [hs2] at hns; simp at hns
    obtain ⟨hh2, hfa⟩ := hcase
    have hht : h ∈ (game.histDist (bfDevProfile N dev) .live t).support := hh
    have hk_prev : -(N : ℤ) ≤ netRightExcess h := ih h hht hh2
    rw [PMF.mem_support_iff, stageActionDist_bfDevProfile] at ha
    rw [pmfPi_apply] at ha
    have ha' := Finset.prod_ne_zero_iff.mp ha false (Finset.mem_univ false)
    simp only [Bool.false_eq_true, if_false, hfa] at ha'
    unfold blackwellFergusonStrategy at ha'
    rw [coinPMF_apply_false] at ha'
    have hp1 : bfStopProb N (netRightExcess h) < 1 := by
      by_contra hcon
      push Not at hcon
      have : bfStopProb N (netRightExcess h) = 1 :=
        le_antisymm (bfStopProb_le_one N _) hcon
      rw [this] at ha'
      simp at ha'
    have hD2 : 2 ≤ bfDenom N (netRightExcess h) := by
      by_contra hcon
      push Not at hcon
      have hD1 : bfDenom N (netRightExcess h) = 1 := by
        have := one_le_bfDenom N (netRightExcess h); omega
      have hp1' : bfStopProb N (netRightExcess h) = 1 := by
        unfold bfStopProb; rw [hD1]; norm_num
      linarith [hp1, hp1']
    have hk_ge : -(N : ℤ) + 1 ≤ netRightExcess h := by
      unfold bfDenom at hD2
      omega
    rw [netRightExcess_snoc]
    rcases (a true) <;> omega

/-! ## Piece 1 (Stage 3c): prefix restriction of histories

*Migration candidate: `Basic.lean`.*  This is a general fact about
`StochasticGame.Hist`/`histDist`, not specific to the Big Match; it is kept
here (rather than in `Basic.lean`) to avoid rebuilding the whole library. -/

/-- Restrict a history at horizon `T` to its first `t ≤ T` stages: drop the
tail, keeping the record of the first `t` stages and the state that was
current at decision epoch `t` (read off the `t`-th recorded stage if
`t < T`, or the final current state if `t = T`). -/
def restrictHist (G : StochasticGame ι) {t T : ℕ} (htT : t ≤ T) (h : G.Hist T) :
    G.Hist t :=
  (fun j => h.1 (Fin.castLE htT j), if hlt : t < T then (h.1 ⟨t, hlt⟩).1 else h.2)

/-- Restricting to the full horizon is the identity. -/
@[simp] theorem restrictHist_self (G : StochasticGame ι) {t : ℕ} (h : G.Hist t) :
    restrictHist G (le_refl t) h = h := by
  unfold restrictHist
  simp

/-- Restricting a one-step extension of a `T`-history back to a prefix
`t ≤ T` recovers exactly the restriction of the original `T`-history: the
newly appended stage is invisible to any earlier-time restriction. -/
theorem restrictHist_snoc (G : StochasticGame ι) {t T : ℕ} (htT : t ≤ T)
    (h : G.Hist T) (a : G.JointAct) (s' : G.State) :
    restrictHist G (Nat.le_succ_of_le htT)
        ((Fin.snoc h.1 (h.2, a), s') : G.Hist (T + 1)) =
      restrictHist G htT h := by
  have hrec : (fun j : Fin t =>
        (Fin.snoc h.1 (h.2, a) : Fin (T + 1) → G.State × G.JointAct)
          (Fin.castLE (Nat.le_succ_of_le htT) j))
      = (fun j : Fin t => h.1 (Fin.castLE htT j)) := by
    funext j
    have hcast : Fin.castLE (Nat.le_succ_of_le htT) j = Fin.castSucc (Fin.castLE htT j) :=
      Fin.ext rfl
    rw [hcast, Fin.snoc_castSucc]
  rcases lt_or_eq_of_le htT with hlt | heq
  · have hlt1 : t < T + 1 := hlt.trans (Nat.lt_succ_self T)
    have hidx : (⟨t, hlt1⟩ : Fin (T + 1)) = Fin.castSucc ⟨t, hlt⟩ := Fin.ext rfl
    have hst : ((Fin.snoc h.1 (h.2, a) : Fin (T + 1) → G.State × G.JointAct)
        ⟨t, hlt1⟩).1 = (h.1 ⟨t, hlt⟩).1 := by
      rw [hidx, Fin.snoc_castSucc]
    unfold restrictHist
    rw [dif_pos hlt1, dif_pos hlt]
    exact Prod.ext hrec hst
  · have hnlt : ¬ t < T := by omega
    have hlt1 : t < T + 1 := by omega
    have hidx : (⟨t, hlt1⟩ : Fin (T + 1)) = Fin.last T := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    have hst : ((Fin.snoc h.1 (h.2, a) : Fin (T + 1) → G.State × G.JointAct)
        ⟨t, hlt1⟩).1 = h.2 := by
      rw [hidx, Fin.snoc_last]
    unfold restrictHist
    rw [dif_pos hlt1, dif_neg hnlt]
    exact Prod.ext hrec hst

/-- **Piece 1, the marginal-consistency identity.**  Prefix restriction is
compatible with `histDist` across horizons: the distribution over `t`-stage
histories is exactly the `t`-restriction of the distribution over
`T`-stage histories, for any `t ≤ T`.  Proved by induction on `T`, using
`restrictHist_snoc` to see that the one-step extension collapses under
`PMF.bind_const` once mapped through the restriction. -/
theorem histDist_map_restrictHist (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) :
    ∀ {t T : ℕ} (htT : t ≤ T),
      (G.histDist σ s₀ T).map (restrictHist G htT) = G.histDist σ s₀ t := by
  have key : ∀ T : ℕ, ∀ t : ℕ, ∀ htT : t ≤ T,
      (G.histDist σ s₀ T).map (restrictHist G htT) = G.histDist σ s₀ t := by
    intro T
    induction T with
    | zero =>
      intro t htT
      have ht0 : t = 0 := Nat.le_zero.mp htT
      subst ht0
      rw [G.histDist_zero, PMF.pure_map, restrictHist_self]
    | succ T ih =>
      intro t htT
      rcases eq_or_lt_of_le htT with heq | hlt
      · have ht : t = T + 1 := heq
        subst ht
        have hid : restrictHist G htT = id := funext fun h => restrictHist_self G h
        rw [hid, PMF.map_id]
      · have htT' : t ≤ T := Nat.lt_succ_iff.mp hlt
        rw [G.histDist_succ, PMF.map_bind]
        have hstep : ∀ h : G.Hist T,
            ((G.stageActionDist σ h).bind fun a =>
                (G.transition h.2 a).bind fun s' =>
                  PMF.pure ((Fin.snoc h.1 (h.2, a), s') : G.Hist (T + 1))).map
              (restrictHist G htT) = PMF.pure (restrictHist G htT' h) := by
          intro h
          rw [PMF.map_bind]
          have hinner : ∀ a : G.JointAct,
              ((G.transition h.2 a).bind fun s' =>
                  PMF.pure ((Fin.snoc h.1 (h.2, a), s') : G.Hist (T + 1))).map
                (restrictHist G htT) = PMF.pure (restrictHist G htT' h) := by
            intro a
            rw [PMF.map_bind]
            have hinner2 : ∀ s' : G.State,
                ((PMF.pure ((Fin.snoc h.1 (h.2, a), s') : G.Hist (T + 1))).map
                    (restrictHist G htT)) = PMF.pure (restrictHist G htT' h) := by
              intro s'
              rw [PMF.pure_map]
              congr 1
              exact restrictHist_snoc G htT' h a s'
            simp only [hinner2]
            exact PMF.bind_const _ _
          simp only [hinner]
          exact PMF.bind_const _ _
        simp only [hstep]
        change (G.histDist σ s₀ T).map (restrictHist G htT') = G.histDist σ s₀ t
        exact ih t htT'
  intro t T htT
  exact key T t htT

/-! ## Piece 2 (Stage 3c): the history-level submartingale

`bfX N h` is the history-level analogue of `bfM`'s summand
`oneIndicator h.2 + liveIndicator h.2 * bfPotential (bfDenom N (excess))`, read
off a single history rather than aggregated over a `TimeStateMixedProfile`.
Its expectation under `histDist (bfDevProfile N dev)` is monotone
nondecreasing in `t`, for *every* minimizer deviation `dev` — the direct
history-level generalization of `bfM_le_succ`. -/

/-- The history-level Blackwell–Ferguson potential: `1` at `.one`, the excess
potential `bfPotential (bfDenom N (netRightExcess h))` while `.live`, and `0`
at `.zero`. -/
def bfX (N : ℕ) {t : ℕ} (h : game.Hist t) : ℝ :=
  (if h.2 = .one then 1 else 0) +
    (if h.2 = .live then bfPotential (bfDenom N (netRightExcess h)) else 0)

theorem bfX_one {t : ℕ} (N : ℕ) {h : game.Hist t} (hs : h.2 = .one) :
    bfX N h = 1 := by simp [bfX, hs]

theorem bfX_zero {t : ℕ} (N : ℕ) {h : game.Hist t} (hs : h.2 = .zero) :
    bfX N h = 0 := by simp [bfX, hs]

theorem bfX_live {t : ℕ} (N : ℕ) {h : game.Hist t} (hs : h.2 = .live) :
    bfX N h = bfPotential (bfDenom N (netRightExcess h)) := by simp [bfX, hs]

theorem bfX_nonneg (N : ℕ) {t : ℕ} (h : game.Hist t) : 0 ≤ bfX N h := by
  rcases hs : h.2 with _ | _ | _
  · rw [bfX_live N hs]; exact bfPotential_nonneg (one_le_bfDenom N _)
  · rw [bfX_zero N hs]
  · rw [bfX_one N hs]; norm_num

/-- Closed form for `expect` against a `PMF Bool` built by `coinPMF`. -/
theorem expect_coinPMF (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (coinPMF p hp0 hp1) f = p * f true + (1 - p) * f false := by
  rw [expect_eq_sum, Fintype.sum_bool, coinPMF_apply_true_toReal,
    coinPMF_apply_false_toReal]

/-- The scalar one-step inequality behind Piece 2: the real-algebra content of
`bfM_le_succ`, generalized from a pure minimizer action (`if d t then … else
…`) to a mixed one (`q ∈ [0, 1]`).  Off the clamp boundary (`bfDenom N k ≥ 2`)
this is an *exact* identity, `q` times `bfPotential_right_id` plus `1 - q`
times `bfPotential_left_id`; at the clamp boundary (`bfDenom N k = 1`) the
stopping probability is forced to `1` and the inequality reduces to
`0 ≤ 1 - q`. -/
theorem bfPotential_step_ge (N : ℕ) (k : ℤ) (q : ℝ) (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    bfPotential (bfDenom N k) ≤
      bfStopProb N k * (1 - q) +
        (1 - bfStopProb N k) *
          (q * bfPotential (bfDenom N (k + 1)) + (1 - q) * bfPotential (bfDenom N (k - 1))) := by
  rcases eq_or_lt_of_le (one_le_bfDenom N k) with hD1 | hD2
  · have hp1 : bfStopProb N k = 1 := by unfold bfStopProb; rw [← hD1]; norm_num
    have hpot0 : bfPotential (bfDenom N k) = 0 := by rw [← hD1]; exact bfPotential_one
    rw [hp1, hpot0]
    nlinarith [hq1]
  · have hDenomR : bfDenom N (k + 1) = bfDenom N k + 1 := bfDenom_succ_of_right N k hD2
    have hDenomL : bfDenom N (k - 1) = bfDenom N k - 1 := bfDenom_succ_of_left N k hD2
    rw [hDenomR, hDenomL]
    have hidR := bfPotential_right_id (bfDenom N k)
    have hidL := bfPotential_left_id (D := bfDenom N k) hD2
    have heq : bfPotential (bfDenom N k) =
        bfStopProb N k * (1 - q) + (1 - bfStopProb N k) *
          (q * bfPotential (bfDenom N k + 1) + (1 - q) * bfPotential (bfDenom N k - 1)) := by
      unfold bfStopProb
      linear_combination (-q) * hidR - (1 - q) * hidL
    linarith [heq]

/-- **Piece 2, the pointwise one-step inequality.**  At every history `h`
(live or absorbed), `bfX N h` is dominated by the expected value of `bfX N`
at the deterministic one-step extension by the joint action drawn from
`bfDevProfile N dev` — for *every* minimizer deviation `dev`.  At absorbed
states the inequality is an equality (self-loop, `bfX` constant); at live
states it reduces to `bfPotential_step_ge` at `q := (dev t h true).toReal`,
via `expect_pmfPi_bool`'s Fubini expansion of the joint (maximizer,
minimizer) coin. -/
theorem bfX_le_expect_step (N : ℕ) (dev : game.BehaviorStrategy true) {t : ℕ}
    (h : game.Hist t) :
    bfX N h ≤ expect (game.stageActionDist (bfDevProfile N dev) h)
      (fun a => bfX N ((Fin.snoc h.1 (h.2, a), nextState h.2 a) : game.Hist (t + 1))) := by
  rcases hs : h.2 with _ | _ | _
  · -- h.2 = .live (the ambient goal already has `h.2` rewritten to `State.live` by `rcases`)
    rw [stageActionDist_bfDevProfile, expect_pmfPi_bool]
    simp only [Bool.false_eq_true, if_false, if_true]
    unfold blackwellFergusonStrategy
    rw [expect_coinPMF, bfX_live N hs]
    have hGtrue : expect (dev t h)
        (fun b => bfX N ((Fin.snoc h.1 (State.live, fun who => if who then b else true),
            nextState State.live (fun who => if who then b else true)) : game.Hist (t + 1))) =
        1 - (dev t h true).toReal := by
      have hfun : (fun b => bfX N ((Fin.snoc h.1 (State.live, fun who => if who then b else true),
          nextState State.live (fun who => if who then b else true)) : game.Hist (t + 1))) =
          fun b : Bool => if b then (0 : ℝ) else 1 := by
        funext b
        rcases b with _ | _
        · have hns : nextState State.live (fun who => if who then false else true) = State.one :=
            rfl
          rw [hns]; exact bfX_one N rfl
        · have hns : nextState State.live (fun who => if who then true else true) = State.zero :=
            rfl
          rw [hns]; exact bfX_zero N rfl
      rw [hfun, expect_eq_sum, Fintype.sum_bool]
      simp only [Bool.false_eq_true, if_true, if_false]
      rw [pmfBool_false_toReal (dev t h)]; ring
    have hGfalse : expect (dev t h)
        (fun b => bfX N ((Fin.snoc h.1 (State.live, fun who => if who then b else false),
            nextState State.live (fun who => if who then b else false)) : game.Hist (t + 1))) =
        (dev t h true).toReal * bfPotential (bfDenom N (netRightExcess h + 1)) +
          (1 - (dev t h true).toReal) * bfPotential (bfDenom N (netRightExcess h - 1)) := by
      have hfun : (fun b => bfX N ((Fin.snoc h.1 (State.live, fun who => if who then b else false),
          nextState State.live (fun who => if who then b else false)) : game.Hist (t + 1))) =
          fun b : Bool => bfPotential (bfDenom N (netRightExcess h + (if b then 1 else -1))) := by
        funext b
        have hns : nextState State.live (fun who => if who then b else false) = State.live := by
          cases b <;> rfl
        have hlive : ((Fin.snoc h.1 (State.live, fun who => if who then b else false),
            nextState State.live (fun who => if who then b else false)) : game.Hist (t + 1)).2 =
            State.live := hns
        have hexc : netRightExcess ((Fin.snoc h.1 (State.live, fun who => if who then b else false),
            nextState State.live (fun who => if who then b else false)) : game.Hist (t + 1)) =
            netRightExcess h + (if b then (1 : ℤ) else -1) := by
          have h0 := netRightExcess_snoc h (fun who => if who then b else false)
            (nextState State.live (fun who => if who then b else false))
          rw [hs] at h0
          rw [h0]
          cases b <;> rfl
        rw [bfX_live N hlive, hexc]
      rw [hfun, expect_eq_sum, Fintype.sum_bool]
      have hkeyF : netRightExcess h + (if (false : Bool) then (1 : ℤ) else -1) =
          netRightExcess h - 1 := by
        simp only [Bool.false_eq_true, if_false]; omega
      have hkeyT : netRightExcess h + (if (true : Bool) then (1 : ℤ) else -1) =
          netRightExcess h + 1 := by
        simp only [if_true]
      rw [hkeyF, hkeyT]
      rw [pmfBool_false_toReal (dev t h)]
    rw [hGtrue, hGfalse]
    exact bfPotential_step_ge N (netRightExcess h) (dev t h true).toReal
      ENNReal.toReal_nonneg (ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _))
  · -- h.2 = .zero (the ambient goal already has `h.2` rewritten to `State.zero`)
    have heq0 : (fun a => bfX N ((Fin.snoc h.1 (State.zero, a), nextState State.zero a) :
        game.Hist (t + 1))) = fun _ => (0 : ℝ) := by
      funext a
      exact bfX_zero N rfl
    rw [bfX_zero N hs, heq0, expect_const]
  · -- h.2 = .one (the ambient goal already has `h.2` rewritten to `State.one`)
    have heq1 : (fun a => bfX N ((Fin.snoc h.1 (State.one, a), nextState State.one a) :
        game.Hist (t + 1))) = fun _ => (1 : ℝ) := by
      funext a
      exact bfX_one N rfl
    rw [bfX_one N hs, heq1, expect_const]

/-- **Piece 2, the history-level submartingale.**  The expectation of `bfX N`
under `histDist (bfDevProfile N dev)` at decision epoch `t`. -/
def bfXExpect (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) : ℝ :=
  expect (game.histDist (bfDevProfile N dev) .live t) (bfX N)

/-- **Piece 2, the monotonicity theorem.**  `bfXExpect` is monotone
nondecreasing in `t`, for *every* minimizer deviation `dev`: unfold `histDist`
one step via its recursive `bind`, collapse the deterministic `transition`
step by `expect_pure`, and apply `bfX_le_expect_step` pointwise via
`expect_mono` (no restriction to the support is needed, since `game.Hist t`
is finite). -/
theorem bfXExpect_le_succ (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    bfXExpect N dev t ≤ bfXExpect N dev (t + 1) := by
  unfold bfXExpect
  rw [game.histDist_succ, expect_bind]
  apply expect_mono
  intro h
  rw [expect_bind]
  have hstep : ∀ a : game.JointAct,
      expect ((game.transition h.2 a).bind fun s' =>
          PMF.pure ((Fin.snoc h.1 (h.2, a), s') : game.Hist (t + 1))) (bfX N) =
        bfX N ((Fin.snoc h.1 (h.2, a), nextState h.2 a) : game.Hist (t + 1)) := by
    intro a
    rw [expect_bind, transition_eq_pure, expect_pure, expect_pure]
  simp_rw [hstep]
  exact bfX_le_expect_step N dev h

theorem bfXExpect_monotone (N : ℕ) (dev : game.BehaviorStrategy true) :
    Monotone (bfXExpect N dev) :=
  monotone_nat_of_le_succ (bfXExpect_le_succ N dev)

theorem bfXExpect_zero (N : ℕ) (dev : game.BehaviorStrategy true) :
    bfXExpect N dev 0 = bfPotential (N + 1) := by
  unfold bfXExpect
  rw [game.histDist_zero, expect_pure, bfX_live N (rfl : (game.emptyHist State.live).2 = .live),
    netRightExcess_zero]
  have hD0 : bfDenom N 0 = N + 1 := by unfold bfDenom; omega
  rw [hD0]

/-- **Corollary of Piece 2.**  `bfXExpect` never drops below its initial
value `bfPotential (N + 1) = 1/2 - 1/(2(N+1))` — the history-level analogue
of `bfM_ge_half_sub`, but now valid against *every* minimizer deviation
`dev`, not just deterministic schedules. -/
theorem bfXExpect_ge_bfPotential (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    bfPotential (N + 1) ≤ bfXExpect N dev t := by
  rw [← bfXExpect_zero N dev]
  exact bfXExpect_monotone N dev (Nat.zero_le t)

/-! ## Piece 3 (Stage 3c): the per-stage payoff bound

`stageEUAt_bfDevProfile_ge` is the history-level, mixed-action generalization
of Stage 3b's `bfStagePayoff_ge`: at a live history, the maximizer's own coin
(`blackwellFergusonStrategy`) and the minimizer's mixed action `dev t h`
combine into an expected stage reward `p*(1-q) + (1-p)*q` (the off-diagonal
Big Match reward), which dominates `bfX N h + (q - 1/2) - p` since `bfX N h =
φ(D) < 1/2` and `p, q ≥ 0` absorb the rest — the same "drop the nonnegative
correction terms" step as `bfStagePayoff_ge`, now against a mixed `q` instead
of a pure `d t`. -/

/-- Marginalizing `bfDevProfile`'s joint action distribution over the
minimizer's own component recovers `dev`'s own mixed action exactly: the
maximizer's independent coin integrates away. -/
theorem expect_stageActionDist_bfDevProfile_minimizer (N : ℕ) (dev : game.BehaviorStrategy true)
    {t : ℕ} (h : game.Hist t) (f : Bool → ℝ) :
    expect (game.stageActionDist (bfDevProfile N dev) h) (fun a => f (a true)) =
      expect (dev t h) f := by
  rw [stageActionDist_bfDevProfile, expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  exact expect_const _ _

/-- **Piece 3, the pointwise stage-reward bound.** -/
theorem stageEUAt_bfDevProfile_ge (N : ℕ) (dev : game.BehaviorStrategy true) {t : ℕ}
    (h : game.Hist t) :
    bfX N h + (1 / 2) * (liveIndicator h.2 * (2 * (dev t h true).toReal - 1)) -
        liveIndicator h.2 * bfStopProb N (netRightExcess h) ≤
      game.stageEUAt (bfDevProfile N dev) h false := by
  unfold stageEUAt
  rw [stageActionDist_bfDevProfile]
  have heq := expect_stagePayoff_maximizer h.2
    (fun i => if i then dev t h else blackwellFergusonStrategy N t h)
  simp only [Bool.false_eq_true, if_false, if_true] at heq
  rw [heq]
  unfold blackwellFergusonStrategy
  rw [coinPMF_apply_true_toReal]
  set p := bfStopProb N (netRightExcess h) with hpdef
  set q := (dev t h true).toReal with hqdef
  have hp0 : 0 ≤ p := bfStopProb_nonneg N _
  have hp1 : p ≤ 1 := bfStopProb_le_one N _
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q ≤ 1 := ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  rcases hs : h.2 with _ | _ | _
  · rw [bfX_live N hs]
    have hphi : bfPotential (bfDenom N (netRightExcess h)) < 1 / 2 :=
      bfPotential_lt_half (one_le_bfDenom N _)
    simp only [liveIndicator, oneIndicator]
    nlinarith [hp0, hp1, hq0, hq1, hphi]
  · rw [bfX_zero N hs]; simp [liveIndicator, oneIndicator]
  · rw [bfX_one N hs]; simp [liveIndicator, oneIndicator]

/-- The realized ±1 minimizer action recorded at stage `t`, read off the
last stage of a `(t + 1)`-history, weighted by liveness of the prefix at
epoch `t`: the history-level, realized-action analogue of the `q := (dev t h
true).toReal`-based conditional mean used in `stageEUAt_bfDevProfile_ge`. -/
def bfLiveDeltaExpect (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) : ℝ :=
  expect (game.histDist (bfDevProfile N dev) .live (t + 1))
    (fun h => if (h.1 ⟨t, Nat.lt_succ_self t⟩).1 = State.live then
      (if (h.1 ⟨t, Nat.lt_succ_self t⟩).2 true then (1 : ℝ) else -1) else 0)

/-- The stopping probability at a live history, weighted by liveness, in
expectation at stage `t`. -/
def bfLivePExpect (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) : ℝ :=
  expect (game.histDist (bfDevProfile N dev) .live t)
    (fun h => liveIndicator h.2 * bfStopProb N (netRightExcess h))

/-- **Bridge lemma.**  `bfLiveDeltaExpect` (a `(t + 1)`-level expectation of
the *realized* minimizer action) equals the `t`-level expectation of its
*conditional mean* `2 * (dev t h true).toReal - 1`: unfold `histDist_succ`
one step (as in `bfXExpect_le_succ`), observe the newly appended stage's
prefix state and recorded action are exactly `h.2` and `a`, and marginalize
the transition (irrelevant to a stage-`t` quantity) and the maximizer's own
coin (`expect_stageActionDist_bfDevProfile_minimizer`) away. -/
theorem bfLiveDeltaExpect_eq (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    bfLiveDeltaExpect N dev t =
      expect (game.histDist (bfDevProfile N dev) .live t)
        (fun h => liveIndicator h.2 * (2 * (dev t h true).toReal - 1)) := by
  unfold bfLiveDeltaExpect
  rw [game.histDist_succ, expect_bind]
  have hstep : ∀ h : game.Hist t,
      expect ((game.stageActionDist (bfDevProfile N dev) h).bind fun a =>
          (game.transition h.2 a).bind fun s' =>
            PMF.pure ((Fin.snoc h.1 (h.2, a), s') : game.Hist (t + 1)))
        (fun h' => if (h'.1 ⟨t, Nat.lt_succ_self t⟩).1 = State.live then
            (if (h'.1 ⟨t, Nat.lt_succ_self t⟩).2 true then (1 : ℝ) else -1) else 0) =
      liveIndicator h.2 * (2 * (dev t h true).toReal - 1) := by
    intro h
    rw [expect_bind]
    have hinner : ∀ a : game.JointAct,
        expect ((game.transition h.2 a).bind fun s' =>
            PMF.pure ((Fin.snoc h.1 (h.2, a), s') : game.Hist (t + 1)))
          (fun h' => if (h'.1 ⟨t, Nat.lt_succ_self t⟩).1 = State.live then
              (if (h'.1 ⟨t, Nat.lt_succ_self t⟩).2 true then (1 : ℝ) else -1) else 0) =
        (if h.2 = State.live then (if a true then (1 : ℝ) else -1) else 0) := by
      intro a
      rw [expect_bind]
      have hlast : (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1)) = Fin.last t := Fin.ext rfl
      have hidx2 : ((Fin.snoc h.1 (h.2, a) : Fin (t + 1) → game.State × game.JointAct)
          ⟨t, Nat.lt_succ_self t⟩) = (h.2, a) := by rw [hlast, Fin.snoc_last]
      simp only [expect_pure, hidx2]
      exact expect_const _ _
    simp only [hinner]
    rcases hs : h.2 with _ | _ | _
    · simp only [reduceIte]
      rw [expect_stageActionDist_bfDevProfile_minimizer N dev h
        (fun b => if b then (1 : ℝ) else -1), expect_eq_sum, Fintype.sum_bool,
        pmfBool_false_toReal (dev t h)]
      simp only [liveIndicator, Bool.false_eq_true, if_false, if_true]
      ring
    · simp [liveIndicator]
    · simp [liveIndicator]
  simp_rw [hstep]

/-- **Piece 3, the per-stage payoff bound, un-substituted.**  The direct,
pre-floor-substitution form: bounds the stage payoff below by *that same
epoch's* `bfXExpect`, not yet replaced by the constant floor
`bfPotential (N + 1)`.  This is exactly the per-stage hypothesis consumed by
`AdaptiveCertificate.lean`'s "submartingale floor" mechanism
(`finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le`); see
`finiteAveragePayoff_bfDevProfile_ge_via_certificate` below.  Substituting
Piece 2's floor `bfXExpect_ge_bfPotential` recovers
`expectedStagePayoff_bfDevProfile_ge`. -/
theorem expectedStagePayoff_bfDevProfile_ge_of_bfXExpect (N : ℕ)
    (dev : game.BehaviorStrategy true) (t : ℕ) :
    bfXExpect N dev t + (1 / 2) * bfLiveDeltaExpect N dev t - bfLivePExpect N dev t ≤
      game.expectedStagePayoff (bfDevProfile N dev) .live t false := by
  have hpt : expect (game.histDist (bfDevProfile N dev) .live t)
      (fun h => bfX N h + (1 / 2) * (liveIndicator h.2 * (2 * (dev t h true).toReal - 1)) -
        liveIndicator h.2 * bfStopProb N (netRightExcess h)) ≤
      game.expectedStagePayoff (bfDevProfile N dev) .live t false := by
    unfold expectedStagePayoff
    exact expect_mono _ _ _ fun h => stageEUAt_bfDevProfile_ge N dev h
  have hsplit : expect (game.histDist (bfDevProfile N dev) .live t)
      (fun h => bfX N h + (1 / 2) * (liveIndicator h.2 * (2 * (dev t h true).toReal - 1)) -
        liveIndicator h.2 * bfStopProb N (netRightExcess h)) =
      bfXExpect N dev t + (1 / 2) * bfLiveDeltaExpect N dev t - bfLivePExpect N dev t := by
    rw [bfLiveDeltaExpect_eq]
    unfold bfXExpect bfLivePExpect
    rw [expect_sub, expect_add, expect_const_mul]
  rw [hsplit] at hpt
  exact hpt

/-- **Piece 3, the per-stage payoff bound.**  Substitutes Piece 2's floor
`bfXExpect_ge_bfPotential` into `expectedStagePayoff_bfDevProfile_ge_of_bfXExpect`. -/
theorem expectedStagePayoff_bfDevProfile_ge (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    bfPotential (N + 1) + (1 / 2) * bfLiveDeltaExpect N dev t - bfLivePExpect N dev t ≤
      game.expectedStagePayoff (bfDevProfile N dev) .live t false := by
  have hfloor := bfXExpect_ge_bfPotential N dev t
  linarith [expectedStagePayoff_bfDevProfile_ge_of_bfXExpect N dev t, hfloor]

/-! ## Piece 4 (Stage 3c): the two summation bounds

Two bounds needed to sum Piece 3's per-stage inequality over a horizon:
`sum_bfLiveDeltaExpect_ge` (part (i)) and `sum_bfLivePExpect_le_one` (part
(ii)). Both avoid `restrictHist` entirely: (i) is proved by a *pathwise*
support-level induction on the raw stage record (`bfDeltaSum`), reusing
`netRightExcess_ge_of_live_of_mem_support`, and then lifted to the
expectation level by the *same* one-step `histDist_succ` unfolding used for
`bfLiveDeltaExpect_eq`; (ii) is proved by recognizing `bfLivePExpect` as the
one-step drop in live probability, telescoping via
`Math.sum_range_sub_succ`. -/

/-! ### Part (i): the signed-excess sum -/

/-- The raw, unconditional analogue of `netRightExcess`, masked by liveness of
each past stage's *own* prefix state: the pathwise integrand behind
`bfLiveDeltaExpect`, defined directly on a history's stage record (no
reference to `histDist` or `dev`). -/
def bfDeltaSum {n : ℕ} (h : game.Hist n) : ℤ :=
  ∑ j : Fin n, if (h.1 j).1 = State.live then (if (h.1 j).2 true then (1 : ℤ) else -1) else 0

@[simp] theorem bfDeltaSum_zero (h : game.Hist 0) : bfDeltaSum h = 0 := by simp [bfDeltaSum]

/-- One-step extension identity for `bfDeltaSum`, exactly analogous to
`netRightExcess_snoc`: the new term is masked by the *previous* current state
`h.2` (the prefix state at the newly appended stage), independent of `s'`. -/
theorem bfDeltaSum_snoc {t : ℕ} (h : game.Hist t) (a : game.JointAct) (s' : game.State) :
    bfDeltaSum ((Fin.snoc h.1 (h.2, a), s') : game.Hist (t + 1)) =
      bfDeltaSum h + (if h.2 = State.live then (if a true then (1 : ℤ) else -1) else 0) := by
  unfold bfDeltaSum
  rw [Fin.sum_univ_castSucc]
  simp

/-- **Piece 4(i), the pathwise support-level bound.**  Simultaneously: at a
live history, the liveness mask is vacuous (`bfDeltaSum` agrees with
`netRightExcess`), and in general `bfDeltaSum` never drops below `-(N + 1)` —
either the newest term is masked to `0` (already absorbed), or the history is
live and `netRightExcess_ge_of_live_of_mem_support` bounds it, dropping by at
most `1` from the new term. Proved by induction on the horizon, mirroring
`netRightExcess_ge_of_live_of_mem_support`'s own induction. -/
theorem bfDeltaSum_facts (N : ℕ) (dev : game.BehaviorStrategy true) :
    ∀ (n : ℕ) (h : game.Hist n),
      h ∈ (game.histDist (bfDevProfile N dev) .live n).support →
      (h.2 = State.live → bfDeltaSum h = netRightExcess h) ∧ -((N : ℤ) + 1) ≤ bfDeltaSum h := by
  intro n
  induction n with
  | zero =>
    intro h _
    refine ⟨fun _ => by simp [netRightExcess], ?_⟩
    simp only [bfDeltaSum_zero]
    omega
  | succ n ih =>
    intro h' hh'
    rw [game.mem_support_histDist_succ] at hh'
    obtain ⟨h, hh, a, ha, s', hs', rfl⟩ := hh'
    have hs'eq : s' = nextState h.2 a := by
      rw [transition_eq_pure, PMF.support_pure, Set.mem_singleton_iff] at hs'
      exact hs'
    subst hs'eq
    rw [bfDeltaSum_snoc]
    obtain ⟨iheq, ihge⟩ := ih h hh
    rcases hlive : h.2 with _ | _ | _
    · have hne := netRightExcess_snoc h a (nextState h.2 a)
      rw [hlive] at hne
      rw [iheq hlive]
      have hzero : (if State.live = State.live then
          (if a true then (1 : ℤ) else -1) else 0) =
          (if a true then (1 : ℤ) else -1) := by simp
      rw [hzero]
      have hexc := netRightExcess_ge_of_live_of_mem_support N dev n h hh hlive
      refine ⟨fun _ => hne.symm, ?_⟩
      rcases (a true) <;> omega
    · have hzero : (if State.zero = State.live then
          (if a true then (1 : ℤ) else -1) else 0) = 0 := by simp
      rw [hzero]
      refine ⟨fun hc => ?_, by omega⟩
      exfalso
      have hc2 : State.zero = State.live := hc
      exact absurd hc2 (by decide)
    · have hzero : (if State.one = State.live then
          (if a true then (1 : ℤ) else -1) else 0) = 0 := by simp
      rw [hzero]
      refine ⟨fun hc => ?_, by omega⟩
      exfalso
      have hc2 : State.one = State.live := hc
      exact absurd hc2 (by decide)

/-- The expected value of `bfDeltaSum` at horizon `T`: the pathwise sum,
integrated. -/
def bfPartialDeltaSum (N : ℕ) (dev : game.BehaviorStrategy true) (T : ℕ) : ℝ :=
  expect (game.histDist (bfDevProfile N dev) .live T) (fun h => (bfDeltaSum h : ℝ))

theorem bfPartialDeltaSum_ge (N : ℕ) (dev : game.BehaviorStrategy true) (T : ℕ) :
    -((N : ℝ) + 1) ≤ bfPartialDeltaSum N dev T := by
  unfold bfPartialDeltaSum
  have hb : ∀ h : game.Hist T, h ∈ (game.histDist (bfDevProfile N dev) .live T).support →
      -((N : ℝ) + 1) ≤ (bfDeltaSum h : ℝ) := by
    intro h hh
    have := (bfDeltaSum_facts N dev T h hh).2
    exact_mod_cast this
  exact Math.ProbabilityMassFunction.le_expect_of_le_on_support _ _ hb

/-- One-step recursion for `bfPartialDeltaSum`: exactly the same `histDist_succ`
unfolding as `bfLiveDeltaExpect_eq`'s proof, so it reuses that lemma directly
(in reverse) once the raw `bfDeltaSum_snoc` identity replaces `netRightExcess_snoc`. -/
theorem bfPartialDeltaSum_succ_eq (N : ℕ) (dev : game.BehaviorStrategy true) (T : ℕ) :
    bfPartialDeltaSum N dev (T + 1) = bfPartialDeltaSum N dev T + bfLiveDeltaExpect N dev T := by
  unfold bfPartialDeltaSum
  rw [game.histDist_succ, expect_bind, bfLiveDeltaExpect_eq]
  have hstep : ∀ h : game.Hist T,
      expect ((game.stageActionDist (bfDevProfile N dev) h).bind fun a =>
          (game.transition h.2 a).bind fun s' =>
            PMF.pure ((Fin.snoc h.1 (h.2, a), s') : game.Hist (T + 1)))
        (fun h' => (bfDeltaSum h' : ℝ)) =
      (bfDeltaSum h : ℝ) + liveIndicator h.2 * (2 * (dev T h true).toReal - 1) := by
    intro h
    rw [expect_bind]
    have hinner : ∀ a : game.JointAct,
        expect ((game.transition h.2 a).bind fun s' =>
            PMF.pure ((Fin.snoc h.1 (h.2, a), s') : game.Hist (T + 1)))
          (fun h' => (bfDeltaSum h' : ℝ)) =
        (bfDeltaSum h : ℝ) +
          (if h.2 = State.live then (if a true then (1 : ℝ) else -1) else 0) := by
      intro a
      rw [expect_bind]
      have hstep2 : ∀ s' : game.State,
          (bfDeltaSum ((Fin.snoc h.1 (h.2, a), s') : game.Hist (T + 1)) : ℝ) =
            (bfDeltaSum h : ℝ) +
              (if h.2 = State.live then (if a true then (1 : ℝ) else -1) else 0) := by
        intro s'
        rw [bfDeltaSum_snoc]
        rcases h.2 with _ | _ | _ <;> rcases (a true) <;> push_cast <;> ring
      simp_rw [expect_pure, hstep2]
      exact expect_const _ _
    simp_rw [hinner]
    rw [expect_add, expect_const]
    congr 1
    rcases h.2 with _ | _ | _
    · simp only [reduceIte]
      rw [expect_stageActionDist_bfDevProfile_minimizer N dev h
        (fun b => if b then (1 : ℝ) else -1), expect_eq_sum, Fintype.sum_bool,
        pmfBool_false_toReal (dev T h)]
      simp only [liveIndicator, Bool.false_eq_true, if_false, if_true]
      ring
    · simp [liveIndicator]
    · simp [liveIndicator]
  simp_rw [hstep]
  rw [expect_add]

theorem bfPartialDeltaSum_eq_sum (N : ℕ) (dev : game.BehaviorStrategy true) (T : ℕ) :
    bfPartialDeltaSum N dev T = ∑ t ∈ Finset.range T, bfLiveDeltaExpect N dev t := by
  induction T with
  | zero => simp [bfPartialDeltaSum]
  | succ T ih => rw [bfPartialDeltaSum_succ_eq, ih, Finset.sum_range_succ]

/-- **Piece 4(i).** -/
theorem sum_bfLiveDeltaExpect_ge (N : ℕ) (dev : game.BehaviorStrategy true) (T : ℕ) :
    -((N : ℝ) + 1) ≤ ∑ t ∈ Finset.range T, bfLiveDeltaExpect N dev t := by
  rw [← bfPartialDeltaSum_eq_sum]
  exact bfPartialDeltaSum_ge N dev T

/-! ### Part (ii): the absorbed-mass sum -/

/-- The probability of still being live at decision epoch `t`: definitionally
`game.expectedStateValue (bfDevProfile N dev) .live t liveIndicator`, letting
`bfPLive_succ_eq` reuse `Discounted.lean`'s `expectedStateValue_succ` and
`BigMatch.lean`'s `expect_next_liveIndicator` directly. -/
def bfPLive (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) : ℝ :=
  expect (game.histDist (bfDevProfile N dev) .live t) (fun h => liveIndicator h.2)

theorem bfPLive_eq_expectedStateValue (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    bfPLive N dev t = game.expectedStateValue (bfDevProfile N dev) .live t liveIndicator := rfl

@[simp] theorem bfPLive_zero (N : ℕ) (dev : game.BehaviorStrategy true) :
    bfPLive N dev 0 = 1 := by
  rw [bfPLive_eq_expectedStateValue, game.expectedStateValue_zero]
  rfl

theorem bfPLive_nonneg (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    0 ≤ bfPLive N dev t :=
  expect_nonneg _ _ fun h => by rcases h.2 with _ | _ | _ <;> simp [liveIndicator]

/-- One-step recursion: live mass drops by exactly `bfLivePExpect`. -/
theorem bfPLive_succ_eq (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    bfPLive N dev (t + 1) = bfPLive N dev t - bfLivePExpect N dev t := by
  rw [bfPLive_eq_expectedStateValue N dev (t + 1), game.expectedStateValue_succ]
  unfold bfPLive bfLivePExpect
  have hstep : ∀ h : game.Hist t,
      expect (game.stageActionDist (bfDevProfile N dev) h)
          (fun a => expect (game.transition h.2 a) liveIndicator) =
        liveIndicator h.2 - liveIndicator h.2 * bfStopProb N (netRightExcess h) := by
    intro h
    rw [stageActionDist_bfDevProfile]
    have heq := expect_next_liveIndicator h.2
      (fun i => if i then dev t h else blackwellFergusonStrategy N t h)
    simp only [Bool.false_eq_true, if_false] at heq
    rw [heq]
    unfold blackwellFergusonStrategy
    rw [coinPMF_apply_true_toReal]
    ring
  simp_rw [hstep]
  rw [expect_sub]

theorem bfLivePExpect_eq_sub (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    bfLivePExpect N dev t = bfPLive N dev t - bfPLive N dev (t + 1) := by
  have := bfPLive_succ_eq N dev t
  linarith

/-- **Piece 4(ii).** -/
theorem sum_bfLivePExpect_le_one (N : ℕ) (dev : game.BehaviorStrategy true) (T : ℕ) :
    ∑ t ∈ Finset.range T, bfLivePExpect N dev t ≤ 1 := by
  have hsum : ∑ t ∈ Finset.range T, bfLivePExpect N dev t = bfPLive N dev 0 - bfPLive N dev T := by
    simp_rw [bfLivePExpect_eq_sub]
    exact Math.sum_range_sub_succ (bfPLive N dev) T
  rw [hsum, bfPLive_zero]
  have := bfPLive_nonneg N dev T
  linarith

/-! ## Stage 3c assembly: lifting Stage 3b from schedules to general deviations

Combines Pieces 2–4 into the general-`dev` analogue of `bfFiniteAverage_ge` /
`bfSeq_eventually_ge_half`. -/

/-- **Assembly, general-`dev` analogue of `bfFiniteAverage_ge`.**  Sum Piece
3's per-stage bound over the horizon and apply Piece 4's two summation
bounds. -/
theorem finiteAveragePayoff_bfDevProfile_ge (N : ℕ) (dev : game.BehaviorStrategy true)
    (T : ℕ) (hT : 0 < T) :
    bfPotential (N + 1) - (((N : ℝ) + 1) / 2 + 1) / T ≤
      game.finiteAveragePayoff .live T (bfDevProfile N dev) false := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hsum_le : ∑ t ∈ Finset.range T,
      (bfPotential (N + 1) + (1 / 2) * bfLiveDeltaExpect N dev t - bfLivePExpect N dev t) ≤
      ∑ t ∈ Finset.range T, game.expectedStagePayoff (bfDevProfile N dev) .live t false :=
    Finset.sum_le_sum fun t _ => expectedStagePayoff_bfDevProfile_ge N dev t
  have hlhs_eq : ∑ t ∈ Finset.range T,
      (bfPotential (N + 1) + (1 / 2) * bfLiveDeltaExpect N dev t - bfLivePExpect N dev t) =
      (T : ℝ) * bfPotential (N + 1) +
        (1 / 2) * (∑ t ∈ Finset.range T, bfLiveDeltaExpect N dev t) -
        ∑ t ∈ Finset.range T, bfLivePExpect N dev t := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Finset.mul_sum]
  rw [hlhs_eq] at hsum_le
  have h4i := sum_bfLiveDeltaExpect_ge N dev T
  have h4ii := sum_bfLivePExpect_le_one N dev T
  have hsum_ge : (T : ℝ) * bfPotential (N + 1) - (((N : ℝ) + 1) / 2 + 1) ≤
      ∑ t ∈ Finset.range T, game.expectedStagePayoff (bfDevProfile N dev) .live t false := by
    linarith [hsum_le, h4i, h4ii]
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hTinv : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum_ge hTinv
  have hrw : (T : ℝ)⁻¹ * ((T : ℝ) * bfPotential (N + 1) - (((N : ℝ) + 1) / 2 + 1)) =
      bfPotential (N + 1) - (((N : ℝ) + 1) / 2 + 1) / T := by
    field_simp
  rw [hrw] at hmul
  exact hmul

/-- **Stage 3c, the target of this stage.**  For every `ε > 0` there is a
Blackwell–Ferguson parameter `N` and a horizon `T₀` past which the
finite-average payoff against *every* minimizer behavior-strategy deviation
`dev` (not just deterministic schedules, as in Stage 3b) is within `ε` of
`1/2`, from below. -/
theorem bf_dev_eventually_ge_half (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ T₀ : ℕ, ∀ (dev : game.BehaviorStrategy true) (T : ℕ), T₀ ≤ T →
      1 / 2 - ε ≤ game.finiteAveragePayoff .live T (bfDevProfile N dev) false := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hN' : (1 : ℝ) < (N : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hN; exact hN
  have hNε : 1 / (2 * ((N : ℝ) + 1)) ≤ ε / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hN', hε]
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt (2 * ((((N : ℝ) + 1) / 2 + 1)) / ε)
  refine ⟨N, max T₀ 1, fun dev T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right T₀ 1) hT)
  have hTge : (T₀ : ℝ) ≤ T := by
    have : T₀ ≤ T := le_trans (le_max_left T₀ 1) hT
    exact_mod_cast this
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT0
  have h1 := finiteAveragePayoff_bfDevProfile_ge N dev T hT0
  have h2 : bfPotential (N + 1) = 1 / 2 - 1 / (2 * ((N : ℝ) + 1)) := by
    unfold bfPotential
    push_cast
    have hN0 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hT₀' : 2 * ((((N : ℝ) + 1) / 2 + 1)) < (T₀ : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hT₀; exact hT₀
  have htail : ((((N : ℝ) + 1) / 2 + 1)) / T ≤ ε / 2 := by
    rw [div_le_iff₀ hTreal]
    have hstep1 : ((((N : ℝ) + 1) / 2 + 1)) * 2 < (T₀ : ℝ) * ε := by linarith [hT₀']
    have hstep2 : (T₀ : ℝ) * ε ≤ (T : ℝ) * ε := mul_le_mul_of_nonneg_right hTge hε.le
    nlinarith [hstep1, hstep2]
  linarith [h1, h2, hNε, htail]

/-! ## Stage 3c, re-derived via the "V2" adaptive potential certificate

`bfXExpect N dev` (as `bfXPotential N`, a `HistoryPotential` constant in
`t`) and its already-proved facts —
`bfXExpect_le_succ` (the submartingale step) and
`expectedStagePayoff_bfDevProfile_ge_of_bfXExpect` (the per-stage bound) —
are *exactly* the data
`AdaptiveCertificate.lean`'s `finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le`
("V2") consumes: no bound on `bfX` at any history but the initial one is
used anywhere below, matching the module docstring's obstruction that no
*bounded, history-independent* (V1-style) potential can witness this bound.
This reproves `finiteAveragePayoff_bfDevProfile_ge` /
`bf_dev_eventually_ge_half` through the general verification machinery
instead of by hand-telescoping Piece 2 and Piece 3 together, demonstrating
that the "V2" interface captures the proof that actually works here. -/

/-- `bfX N`, read as a `HistoryPotential` (constant in the calendar-time
argument, as `bfX` itself already is independent of it). -/
def bfXPotential (N : ℕ) : game.HistoryPotential := fun _ h => bfX N h

/-- `expectedHistoryValue` against `bfXPotential` is exactly `bfXExpect`. -/
theorem expectedHistoryValue_bfXPotential (N : ℕ) (dev : game.BehaviorStrategy true) (t : ℕ) :
    game.expectedHistoryValue (bfDevProfile N dev) .live (bfXPotential N) t =
      bfXExpect N dev t := rfl

/-- **Stage 3c's bound, re-derived via the V2 certificate's core lemma.**
Instantiates `finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le`
with `φ := bfXPotential N`, submartingale step `bfXExpect_le_succ`, per-stage
bound `expectedStagePayoff_bfDevProfile_ge_of_bfXExpect`, and budget
`e t := bfLivePExpect N dev t - (1 / 2) * bfLiveDeltaExpect N dev t`, then
bounds the accumulated budget by Piece 4's two summation bounds
(`sum_bfLiveDeltaExpect_ge`, `sum_bfLivePExpect_le_one`) exactly as
`finiteAveragePayoff_bfDevProfile_ge` does. Same statement as
`finiteAveragePayoff_bfDevProfile_ge`, proved by a genuinely different
route. -/
theorem finiteAveragePayoff_bfDevProfile_ge_via_certificate (N : ℕ)
    (dev : game.BehaviorStrategy true) (T : ℕ) (hT : 0 < T) :
    bfPotential (N + 1) - (((N : ℝ) + 1) / 2 + 1) / T ≤
      game.finiteAveragePayoff .live T (bfDevProfile N dev) false := by
  have hmono : ∀ t, game.expectedHistoryValue (bfDevProfile N dev) .live (bfXPotential N) t ≤
      game.expectedHistoryValue (bfDevProfile N dev) .live (bfXPotential N) (t + 1) := by
    intro t
    rw [expectedHistoryValue_bfXPotential, expectedHistoryValue_bfXPotential]
    exact bfXExpect_le_succ N dev t
  have hbellman : ∀ t, game.expectedHistoryValue (bfDevProfile N dev) .live (bfXPotential N) t ≤
      game.expectedStagePayoff (bfDevProfile N dev) .live t false +
        (bfLivePExpect N dev t - (1 / 2) * bfLiveDeltaExpect N dev t) := by
    intro t
    rw [expectedHistoryValue_bfXPotential]
    have := expectedStagePayoff_bfDevProfile_ge_of_bfXExpect N dev t
    linarith
  have hkey := game.finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le
    (bfDevProfile N dev) .live false (bfXPotential N)
    (fun t => bfLivePExpect N dev t - (1 / 2) * bfLiveDeltaExpect N dev t) hmono hbellman hT
  rw [expectedHistoryValue_bfXPotential, bfXExpect_zero] at hkey
  have h4i := sum_bfLiveDeltaExpect_ge N dev T
  have h4ii := sum_bfLivePExpect_le_one N dev T
  have hsum_le : (∑ t ∈ Finset.range T,
      (bfLivePExpect N dev t - (1 / 2) * bfLiveDeltaExpect N dev t)) ≤ 1 + ((N : ℝ) + 1) / 2 := by
    rw [Finset.sum_sub_distrib]
    have hmul : ∑ t ∈ Finset.range T, (1 / 2 : ℝ) * bfLiveDeltaExpect N dev t =
        (1 / 2) * ∑ t ∈ Finset.range T, bfLiveDeltaExpect N dev t := by
      rw [Finset.mul_sum]
    rw [hmul]
    linarith [h4i, h4ii]
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hTinv : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
  have hmul2 := mul_le_mul_of_nonneg_left hsum_le hTinv
  have hrw : (T : ℝ)⁻¹ * (1 + ((N : ℝ) + 1) / 2) = (((N : ℝ) + 1) / 2 + 1) / T := by
    field_simp; ring
  rw [hrw] at hmul2
  linarith [hkey, hmul2]

/-- **Stage 3c, the target of this stage, re-derived via the V2 certificate.**
Same statement as `bf_dev_eventually_ge_half`, via
`finiteAveragePayoff_bfDevProfile_ge_via_certificate` in place of
`finiteAveragePayoff_bfDevProfile_ge`; the surrounding `ε`-bookkeeping is
identical. -/
theorem bf_dev_eventually_ge_half_via_certificate (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ T₀ : ℕ, ∀ (dev : game.BehaviorStrategy true) (T : ℕ), T₀ ≤ T →
      1 / 2 - ε ≤ game.finiteAveragePayoff .live T (bfDevProfile N dev) false := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hN' : (1 : ℝ) < (N : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hN; exact hN
  have hNε : 1 / (2 * ((N : ℝ) + 1)) ≤ ε / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hN', hε]
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt (2 * ((((N : ℝ) + 1) / 2 + 1)) / ε)
  refine ⟨N, max T₀ 1, fun dev T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right T₀ 1) hT)
  have hTge : (T₀ : ℝ) ≤ T := by
    have : T₀ ≤ T := le_trans (le_max_left T₀ 1) hT
    exact_mod_cast this
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT0
  have h1 := finiteAveragePayoff_bfDevProfile_ge_via_certificate N dev T hT0
  have h2 : bfPotential (N + 1) = 1 / 2 - 1 / (2 * ((N : ℝ) + 1)) := by
    unfold bfPotential
    push_cast
    have hN0 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hT₀' : 2 * ((((N : ℝ) + 1) / 2 + 1)) < (T₀ : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hT₀; exact hT₀
  have htail : ((((N : ℝ) + 1) / 2 + 1)) / T ≤ ε / 2 := by
    rw [div_le_iff₀ hTreal]
    have hstep1 : ((((N : ℝ) + 1) / 2 + 1)) * 2 < (T₀ : ℝ) * ε := by linarith [hT₀']
    have hstep2 : (T₀ : ℝ) * ε ≤ (T : ℝ) * ε := mul_le_mul_of_nonneg_right hTge hε.le
    nlinarith [hstep1, hstep2]
  linarith [h1, h2, hNε, htail]

/-! ## Stage 4: the equilibrium payoff assembly

The final assembly, via `isUniformEquilibriumPayoff_of_deviation_caps`. On
path, `(blackwellFergusonStrategy N, uniformMinimizerStrategy)`
earns exactly `(1/2, -1/2)` at every horizon (Stage 2, no `δ`-slack needed);
the maximizer's deviation cap is likewise exact (Stage 2); the minimizer's
deviation cap is Stage 3c plus the zero-sum identity
`finiteAveragePayoff_minimizer`. -/

/-- Updating the minimizer's component of `profileUniformMinimizer
(blackwellFergusonStrategy N)` recovers `bfDevProfile N dev`: the shape
needed to read Stage 3c as the minimizer's deviation cap. -/
theorem update_profileUniformMinimizer_true (N : ℕ) (dev : game.BehaviorStrategy true) :
    Function.update (profileUniformMinimizer (blackwellFergusonStrategy N)) true dev =
      bfDevProfile N dev := by
  funext who t h
  cases who
  · simp [profileUniformMinimizer, bfDevProfile]
  · simp [bfDevProfile]

/-- **Capstone.** The Big Match has a uniform equilibrium payoff `(1/2,
-1/2)` from the live state, witnessed by the history-dependent
Blackwell–Ferguson strategy: the positive direction of the Big Match's
uniform value, complementing `BigMatchNoMarkov.lean`'s proof that no
calendar-time × state Markov profile can witness it. -/
theorem exists_uniformEquilibriumPayoff_live :
    ∃ v : Payoff Player, game.IsUniformEquilibriumPayoff .live v := by
  refine ⟨fun who => if who then -(1 / 2 : ℝ) else (1 / 2 : ℝ), ?_⟩
  apply isUniformEquilibriumPayoff_of_deviation_caps
  intro δ hδ
  obtain ⟨N, T₀, hT₀⟩ := bf_dev_eventually_ge_half δ hδ
  refine ⟨profileUniformMinimizer (blackwellFergusonStrategy N), max T₀ 1, fun T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right T₀ 1) hT)
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left T₀ 1) hT
  have hmaxpath : game.finiteAveragePayoff .live T
      (profileUniformMinimizer (blackwellFergusonStrategy N)) false = 1 / 2 :=
    finiteAveragePayoff_eq_half_of_uniformMinimizer (blackwellFergusonStrategy N) hT0
  have hminpath : game.finiteAveragePayoff .live T
      (profileUniformMinimizer (blackwellFergusonStrategy N)) true = -(1 / 2) := by
    rw [finiteAveragePayoff_minimizer .live T
      (profileUniformMinimizer (blackwellFergusonStrategy N)), hmaxpath]
  refine ⟨?_, ?_⟩
  · intro who
    cases who
    · simp [hmaxpath]; linarith
    · simp [hminpath]; linarith
  · intro who dev
    cases who
    · rw [update_profileUniformMinimizer_false]
      rw [finiteAveragePayoff_eq_half_of_uniformMinimizer dev hT0]
      norm_num
      linarith
    · rw [update_profileUniformMinimizer_true]
      rw [finiteAveragePayoff_minimizer .live T (bfDevProfile N dev)]
      have := hT₀ dev T hTT₀
      norm_num
      linarith

/-! ## Stage 5: the capstone, re-derived through the zero-sum wrapper

The Big Match is `IsZeroSumBoolGame` at every state and joint action
(`payoff_minimizer`); the maximizer's Blackwell–Ferguson strategy is a
one-sided guarantee securing `1/2` (Stage 3c,
`bf_dev_eventually_ge_half_via_certificate`, exactly); the minimizer's
uniform stationary strategy is a one-sided guarantee securing `-1/2`
(Stage 2, `finiteAveragePayoff_eq_half_of_uniformMinimizer`, an *exact*
equality against every maximizer completion — no submartingale needed).
Feeding both into
`AdaptiveCertificate.lean`'s `isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_oneSidedGuarantees`
reproves the capstone, factoring it as "construct two one-sided
certificates + invoke the generic wrapper". -/

/-- The Big Match is zero-sum in `AdaptiveCertificate.lean`'s `Bool`-indexed
sense, at every state and joint action: `payoff_minimizer`, repackaged. -/
theorem game_isZeroSumBoolGame : game.IsZeroSumBoolGame := fun s a => payoff_minimizer s a

/-- Overriding the minimizer's component of *any* profile by
`blackwellFergusonStrategy N` recovers `bfDevProfile N` applied to that
profile's own minimizer component: the shape needed to read Stage 3c as a
one-sided guarantee (`IsOneSidedGuaranteeCertificateAt`'s `opp`-quantified
form) rather than just a deviation cap from one fixed base profile. -/
theorem update_false_blackwellFergusonStrategy (N : ℕ) (opp : game.BehaviorProfile) :
    Function.update opp false (blackwellFergusonStrategy N) = bfDevProfile N (opp true) := by
  funext who t h
  cases who
  · simp [bfDevProfile]
  · simp [bfDevProfile]

/-- **The maximizer's one-sided guarantee**: `blackwellFergusonStrategy N`
(for a suitable `N`, depending on the error level, exactly as in Stage 3c)
secures `1/2` against *every* completion of the minimizer's play — the
`IsOneSidedGuaranteeCertificate` repackaging of
`bf_dev_eventually_ge_half_via_certificate`. -/
theorem isOneSidedGuaranteeCertificate_blackwellFerguson :
    game.IsOneSidedGuaranteeCertificate .live false (1 / 2) := by
  intro ε hε
  obtain ⟨N, T₀, hT₀⟩ := bf_dev_eventually_ge_half_via_certificate ε hε
  refine ⟨blackwellFergusonStrategy N, max T₀ 2, le_max_right _ _, fun opp T hT => ?_⟩
  have hT0 : T₀ ≤ T := le_trans (le_max_left _ _) hT
  rw [update_false_blackwellFergusonStrategy]
  exact hT₀ (opp true) T hT0

/-- Overriding the maximizer's component of *any* profile by
`uniformMinimizerStrategy` recovers `profileUniformMinimizer` applied to
that profile's own maximizer component: the `opp`-quantified analogue of
`update_profileUniformMinimizer_false`/`update_profileUniformMinimizer_true`. -/
theorem update_true_uniformMinimizerStrategy (opp : game.BehaviorProfile) :
    Function.update opp true uniformMinimizerStrategy = profileUniformMinimizer (opp false) := by
  funext who t h
  cases who
  · simp [profileUniformMinimizer]
  · simp [profileUniformMinimizer]

/-- **The minimizer's one-sided guarantee**: `uniformMinimizerStrategy`
secures `-1/2` *exactly* against every completion of the maximizer's play —
an `IsOneSidedGuaranteeCertificate` needing no error at all, since Stage 2's
`finiteAveragePayoff_eq_half_of_uniformMinimizer` is an equality. -/
theorem isOneSidedGuaranteeCertificate_uniformMinimizer :
    game.IsOneSidedGuaranteeCertificate .live true (-(1 / 2)) := by
  intro δ hδ
  refine ⟨uniformMinimizerStrategy, 2, le_refl 2, fun opp T hT => ?_⟩
  have hT0 : 0 < T := by omega
  rw [update_true_uniformMinimizerStrategy]
  rw [finiteAveragePayoff_minimizer .live T (profileUniformMinimizer (opp false)),
    finiteAveragePayoff_eq_half_of_uniformMinimizer (opp false) hT0]
  linarith

/-- **Capstone, re-derived through the zero-sum wrapper.** Same conclusion
as `exists_uniformEquilibriumPayoff_live` (up to the cosmetic difference
between `fun who => if who then -(1/2) else 1/2` and the wrapper's
`fun who => match who with | false => 1/2 | true => -(1/2)`, equal payoff
vectors), obtained by constructing the two one-sided guarantees above and
invoking `isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_oneSidedGuarantees`
— the capstone factors as "construct two one-sided certificates + invoke
the generic wrapper". -/
theorem exists_uniformEquilibriumPayoff_live_via_wrapper :
    ∃ v : Payoff Player, game.IsUniformEquilibriumPayoff .live v :=
  ⟨_, isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_oneSidedGuarantees game
    game_isZeroSumBoolGame .live (1 / 2)
    isOneSidedGuaranteeCertificate_blackwellFerguson
    isOneSidedGuaranteeCertificate_uniformMinimizer⟩

/-! ## Superseded route-analysis notes (kept out of the module docstring)

Earlier passes on this file explored, and abandoned, two other routes before
landing on the one summarized in the module docstring above: (route (a)) a
mixture-over-deterministic-schedules identity built from scratch against a
`liveHistOf`/`wPMF` construction, matching Kuhn's theorem but requiring a
nontrivial disintegration argument to formalize directly; and (route (b), in
an early form) an *aggregate* Abel-summation attempt for what became Piece
4(i), which does not work for the reason recorded in the module docstring
(liveness and the excess step are correlated across histories at a fixed
stage). Both were superseded by the pathwise argument that Piece 4(i) above
actually uses. `GameTheory.Languages.Kuhn.BehavioralToMixedCore` (route (c))
was also inspected as a possible shortcut and set aside: instantiating it
for this game's history-dependent stopping rule would require re-encoding
`game.Hist t` as `List`-based traces, at least as much bridging work as the
direct route. None of this is needed to understand the (complete, sorry-free)
proof above; it is kept only as a historical note against re-exploration.
-/

end BigMatch
end StochasticGame
end GameTheory
