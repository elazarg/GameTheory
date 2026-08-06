/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.MultiOwnerFaceCirculationOrbit
import GameTheory.Concepts.Stochastic.QuittingHazardRowBridge
import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPathCompiler
import GameTheory.Concepts.Stochastic.QuittingNashBellmanSpine
import GameTheory.Concepts.Stochastic.QuittingInfinitePathCompiler
import Math.Topology.CompactFinitePrefixRelation

/-!
# From multi-owner face circulations to chronological quitting paths

This file closes the interface gap between the forward real-hazard orbit
constructed in `MultiOwnerFaceCirculationOrbit.lean` and the chronological
PMF-root paths consumed by `QuittingSupportWitnessPathCompiler.lean`.

The first theorem strengthens the producer's quantifiers.  One discretisation
is chosen for each positive tolerance, independently of a requested quit-mass
target; every target is then reached by a prefix of that same orbit.  It also
exposes the uniform one-stage absorption lower bound already proved inside the
old prefix estimate.

The elementary dictionary lemmas below convert real hazard rows to Boolean
PMF roots without losing either the Bellman recursion or the support-local
one-stage inequalities.  The remainder of the file uses reversed finite
prefixes and compactness to obtain one infinite chronological path.
-/

noncomputable section

namespace GameTheory

open Finset Filter StochasticGame Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## A single orbit, uniform in every prefix target -/

/-- **Uniform-prefix strengthening of `exists_multiCirculation_orbit`.**
For a fixed positive tolerance, the phase length, survival factors and owner
words are chosen once.  The resulting one orbit reaches every finite quit-mass
target.  The theorem additionally exposes the pointwise positive absorption
lower bound `(1-a)/N`, which is what survives compact reversal. -/
theorem exists_multiCirculation_orbit_uniform_prefix [Nonempty ι]
    {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (β : ZMod L → ℝ) (word : ZMod L → ℕ → ι),
      0 < N ∧
      (∀ l, 0 ≤ β l) ∧
      (∀ l, β l ≤ 1) ∧
      (∀ l, β l ^ N = C.ratio l) ∧
      (∀ n j, multiActual C word β N (n + 1) j =
        oneStageNext r (multiRow word β N n) (multiActual C word β N n) j) ∧
      (∀ n, IsSupportPerfectRow r (multiRow word β N n)
        (multiActual C word β N n) ε) ∧
      (∀ n j, floor j - ε ≤ multiActual C word β N n j) ∧
      (∀ n, (1 - a) / (N : ℝ) ≤
        1 - continueMass (multiRow word β N n)) ∧
      ∀ Q : ℝ, ∃ T : ℕ,
        Q ≤ ∑ n ∈ Finset.range T,
          (1 - continueMass (multiRow word β N n)) := by
  have hs1 : 1 ≤ s :=
    le_trans (Finset.card_pos.mpr
      (mixSupport_nonempty _ (C.mixWeight_nonneg 0) (C.mixWeight_sum 0))) (hs 0)
  have hs1' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  set B : ℝ := 2 * M * ((s : ℝ) - 1) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; nlinarith
  have ha0 : (0 : ℝ) < 1 - a := by linarith
  set D : ℝ := 2 * M + B * (3 - a) / (1 - a) + 1 with hDdef
  have hD0 : 0 < D := by
    have hfrac : 0 ≤ B * (3 - a) / (1 - a) :=
      div_nonneg (mul_nonneg hB0 (by linarith)) ha0.le
    rw [hDdef]
    linarith
  set H : ℝ := ε / D with hHdef
  have hH0 : 0 < H := by rw [hHdef]; exact div_pos hε hD0
  have hHD : H * D = ε := by rw [hHdef]; field_simp
  set K : ℝ := 2 * H * B / (1 - a) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (by nlinarith [hH0.le]) ha0.le
  have hne : (Finset.univ : Finset (ZMod L)).Nonempty :=
    ⟨0, Finset.mem_univ 0⟩
  set amin : ℝ := Finset.univ.inf' hne C.ratio with hamindef
  have hamin_le : ∀ l, amin ≤ C.ratio l :=
    fun l => Finset.inf'_le _ (Finset.mem_univ l)
  have hamin0 : 0 < amin := by
    rw [hamindef, Finset.lt_inf'_iff]
    exact fun l _ => C.ratio_pos l
  have hamin1 : amin < 1 :=
    lt_of_le_of_lt (hamin_le 0) (C.ratio_lt_one 0)
  obtain ⟨N, b, hN, hb0, hb1, hbN, hbH⟩ :=
    exists_pow_eq_and_one_sub_le amin hamin0 hamin1 H hH0
  have hN0 : N ≠ 0 := hN.ne'
  set β : ZMod L → ℝ :=
    fun l => C.ratio l ^ ((N : ℝ)⁻¹) with hβdef
  have hβ0 : ∀ l, 0 ≤ β l :=
    fun l => Real.rpow_nonneg (C.ratio_pos l).le _
  have hβN : ∀ l, β l ^ N = C.ratio l :=
    fun l => Real.rpow_inv_natCast_pow (C.ratio_pos l).le hN0
  have hβlt : ∀ l, β l < 1 :=
    fun l => Real.rpow_lt_one (C.ratio_pos l).le
      (C.ratio_lt_one l) (by positivity)
  have hβ1 : ∀ l, β l ≤ 1 := fun l => (hβlt l).le
  have hbβ : ∀ l, b ≤ β l := by
    intro l
    refine le_of_pow_le_pow_left₀ hN0 (hβ0 l) ?_
    rw [hbN, hβN]
    exact hamin_le l
  have hH : ∀ l, 1 - β l ≤ H :=
    fun l => by linarith [hbβ l, hbH]
  set word : ZMod L → ℕ → ι :=
    fun l => balancedWord (C.mixWeight l) with hworddef
  have hword : ∀ l t, 0 < C.mixWeight l (word l t) :=
    fun l t => balancedWord_mem_support _
      (C.mixWeight_nonneg l) (C.mixWeight_sum l) t
  have hdrift : ∀ l T j,
      |wordDrift r (C.mixWeight l) (word l) T j| ≤ B := by
    intro l T j
    refine le_trans (abs_wordDrift_balancedWord_le r (C.mixWeight l)
      M hM0 hM (C.mixWeight_nonneg l) (C.mixWeight_sum l) T j) ?_
    have hcard : ((mixSupport (C.mixWeight l)).card : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs l
    rw [hBdef]
    nlinarith
  have hK : ∀ l,
      C.ratio l * K + (1 - β l) * B * (2 - C.ratio l) ≤ K := by
    intro l
    have h1 :
        (1 - β l) * B * (2 - C.ratio l) ≤ H * B * 2 := by
      have h2 : (0 : ℝ) ≤ 2 - C.ratio l := by
        linarith [C.ratio_lt_one l]
      nlinarith [hH l, C.ratio_pos l,
        mul_nonneg (by linarith [hβ1 l] : (0 : ℝ) ≤ 1 - β l) hB0]
    have h3 : (1 - a) * K = 2 * H * B := by
      rw [hKdef]
      field_simp
    nlinarith [ha l]
  have hεbound : K + H * B + 2 * M * H ≤ ε := by
    have hsum : K + H * B + 2 * M * H = H * (D - 1) := by
      rw [hKdef, hDdef]
      field_simp
      ring
    rw [hsum]
    nlinarith [hHD]
  have hquitLower : ∀ n,
      (1 - a) / (N : ℝ) ≤
        1 - continueMass (multiRow word β N n) := by
    intro n
    rw [quitMass_multiRow]
    have hbern := sub_le_nsmul_one_sub_of_pow_eq
      (C.ratio (chainPhase L N n))
      (β (chainPhase L N n)) N
      (hβ0 _) (hβN _)
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [div_le_iff₀ hNpos]
    nlinarith [ha (chainPhase L N n)]
  refine ⟨N, β, word, hN, hβ0, hβ1, hβN,
    fun n j => rfl, ?_, ?_, hquitLower, ?_⟩
  · exact fun n => isSupportPerfectRow_multi C word β N hN
      hβ0 hβ1 hβN hword M B K H hM0 hM hB0 hdrift hK hH
      ε hεbound n
  · exact fun n j => multiActual_ge_floor_sub C word β N hN
      hβ0 hβ1 hβN M B K H hM0 hB0 hdrift hK hH
      ε hεbound n j
  · intro Q
    exact exists_prefix_quitMass_multi_ge C word β N hN hβ0 hβN
      a ha ha1 Q

/-! ## Exact real-hazard/PMF-root dictionary -/

/-- Turning a real hazard row into PMF roots preserves the one-stage successor
exactly. -/
theorem quittingRootSuccessorPayoff_rootOfHazard_eq_oneStageNext
    (r : Finset ι → ι → ℝ) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (tail : Payoff ι) :
    quittingRootSuccessorPayoff (rewardOfWeight r) tail
        (rootOfHazard x hx0 hx1) =
      oneStageNext r x tail := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue]
  simp only [rootOfHazard, quittingHazardCoin_true_toReal,
    quittingHazardCoin_false_toReal, hazardOfRoot_rootOfHazard,
    sigmaValue_weightOfReward_rewardOfWeight,
    gammaValue_weightOfReward_rewardOfWeight]
  rfl

/-- Turning a support-perfect real row into PMF roots preserves the
support-local endpoint inequalities exactly. -/
theorem isQuittingRootSupportApproxNash_rootOfHazard_of_isSupportPerfectRow
    (r : Finset ι → ι → ℝ) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (tail : Payoff ι) (ε : ℝ)
    (hrow : IsSupportPerfectRow r x tail ε) :
    IsQuittingRootSupportApproxNash (rewardOfWeight r) tail ε
      (rootOfHazard x hx0 hx1) := by
  intro who
  have hgain :
      quittingRootEndpointDifference (rewardOfWeight r) tail
          (rootOfHazard x hx0 hx1) who =
        gainValue r x who (tail who) := by
    rw [quittingRootEndpointDifference_eq_gainValue,
      hazardOfRoot_rootOfHazard,
      gainValue_weightOfReward_rewardOfWeight]
  constructor
  · intro hpositive
    rw [hgain]
    apply (hrow who).1
    simpa [rootOfHazard] using hpositive
  · intro hpositive
    rw [hgain]
    apply (hrow who).2
    have : 0 < 1 - x who := by
      simpa [rootOfHazard] using hpositive
    linarith

/-- The PMF all-continue probability of a converted root is the real row's
continuation product. -/
theorem quittingStationaryContinueMass_rootOfHazard
    (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    quittingStationaryContinueMass (rootOfHazard x hx0 hx1) =
      continueMass x := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [rootOfHazard, continueMass]

/-- Therefore PMF absorption mass and real-row quit mass agree exactly. -/
theorem quittingRootAbsorptionMass_rootOfHazard
    (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    quittingRootAbsorptionMass (rootOfHazard x hx0 hx1) =
      1 - continueMass x := by
  unfold quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_rootOfHazard]

/-! ## A uniform value bound for the forward orbit -/

/-- The forward singleton-hazard recursion stays in the convex hull of the
initial value and the bounded terminal rows. -/
theorem abs_multiActual_le_reward_add_vertex
    {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r floor L)
    (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N : ℕ)
    (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (n : ℕ) (j : ι) :
    |multiActual C word β N n j| ≤
      M + ∑ k, |C.vertex 0 k| := by
  induction n with
  | zero =>
      have hsingle : |C.vertex 0 j| ≤ ∑ k, |C.vertex 0 k| :=
        Finset.single_le_sum (fun k _ => abs_nonneg (C.vertex 0 k))
          (Finset.mem_univ j)
      simpa [multiActual] using hsingle.trans
        (le_add_of_nonneg_left hM0)
  | succ n ih =>
      rw [multiActual_succ_apply]
      have hb0 := hβ0 (chainPhase L N n)
      have hb1 := hβ1 (chainPhase L N n)
      have hrest0 : 0 ≤ 1 - β (chainPhase L N n) := by linarith
      calc
        |β (chainPhase L N n) * multiActual C word β N n j +
            (1 - β (chainPhase L N n)) *
              r {word (chainPhase L N n) (chainStep L N n)} j| ≤
            |β (chainPhase L N n) * multiActual C word β N n j| +
              |(1 - β (chainPhase L N n)) *
                r {word (chainPhase L N n) (chainStep L N n)} j| :=
          abs_add _ _
        _ = β (chainPhase L N n) * |multiActual C word β N n j| +
              (1 - β (chainPhase L N n)) *
                |r {word (chainPhase L N n) (chainStep L N n)} j| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg hrest0]
        _ ≤ β (chainPhase L N n) *
                (M + ∑ k, |C.vertex 0 k|) +
              (1 - β (chainPhase L N n)) * M := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left ih hb0)
            (mul_le_mul_of_nonneg_left
              (hM {word (chainPhase L N n) (chainStep L N n)} j) hrest0)
        _ ≤ β (chainPhase L N n) *
                (M + ∑ k, |C.vertex 0 k|) +
              (1 - β (chainPhase L N n)) *
                (M + ∑ k, |C.vertex 0 k|) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right
                (Finset.sum_nonneg fun k _ => abs_nonneg (C.vertex 0 k)))
              hrest0)
        _ = M + ∑ k, |C.vertex 0 k| := by ring

end GameTheory
