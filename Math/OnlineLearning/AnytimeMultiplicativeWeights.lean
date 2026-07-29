/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.MultiplicativeWeights

/-!
# Anytime multiplicative weights

A deterministic restarted schedule for signed multiplicative weights. Epoch `k` has length
`(k + 1)²` and learning rate `1 / (k + 1)`. The update rule is independent of the evaluation
horizon. Its regret through any prefix of epoch `K` is quadratic in `K`, while the elapsed time
at the start of that epoch is cubic in `K`.
-/

namespace Math.OnlineLearning

open Filter Topology
open Math.Probability

/-- Epoch `k` contains `(k + 1)²` rounds. -/
def anytimeEpochLength (k : ℕ) : ℕ := (k + 1) ^ 2

/-- Epoch `k` uses learning rate `1 / (k + 1)`. -/
noncomputable def anytimeEpochRate (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ)⁻¹

theorem anytimeEpochRate_pos (k : ℕ) : 0 < anytimeEpochRate k := by
  rw [anytimeEpochRate]
  exact inv_pos.mpr (by positivity)

theorem anytimeEpochRate_le_one (k : ℕ) : anytimeEpochRate k ≤ 1 := by
  simp only [anytimeEpochRate]
  apply inv_le_one_of_one_le₀
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)

theorem anytimeEpoch_regretTerm_eq (L : ℝ) (k : ℕ) :
    2 * (L / anytimeEpochRate k + anytimeEpochRate k * anytimeEpochLength k) =
      2 * (L + 1) * (k + 1) := by
  have hn : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  simp only [anytimeEpochRate, anytimeEpochLength]
  push_cast
  field_simp

theorem sum_range_cast_add_one (K : ℕ) :
    (∑ k ∈ Finset.range K, ((k : ℝ) + 1)) =
      (K : ℝ) * ((K : ℝ) + 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem sum_anytimeEpoch_regretTerm_eq (L : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K,
        2 * (L / anytimeEpochRate k + anytimeEpochRate k * anytimeEpochLength k)) =
      (L + 1) * K * (K + 1) := by
  simp_rw [anytimeEpoch_regretTerm_eq]
  rw [← Finset.mul_sum, sum_range_cast_add_one]
  ring

theorem anytimeEpoch_prefixRegretTerm_le (L : ℝ) (K T : ℕ)
    (hT : T ≤ anytimeEpochLength K) :
    2 * (L / anytimeEpochRate K + anytimeEpochRate K * T) ≤
      2 * (L + 1) * (K + 1) := by
  change T ≤ (K + 1) ^ 2 at hT
  have hn : 0 < (((K + 1 : ℕ) : ℝ)) := by positivity
  have hTreal : (T : ℝ) ≤ (((K + 1 : ℕ) : ℝ)) ^ 2 := by
    exact_mod_cast hT
  have hcurrent :
      (((K + 1 : ℕ) : ℝ))⁻¹ * (T : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    rw [inv_mul_le_iff₀ hn]
    nlinarith
  rw [anytimeEpochRate, div_inv_eq_mul]
  norm_num [Nat.cast_add, Nat.cast_one] at hcurrent ⊢
  linarith

/-- Elapsed time at the start of epoch `K`, as the sum-of-squares polynomial. -/
theorem anytimeEpochStart_cast (K : ℕ) :
    (epochStart anytimeEpochLength K : ℝ) =
      (K : ℝ) * ((K : ℝ) + 1) * (2 * (K : ℝ) + 1) / 6 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [epochStart_succ]
      push_cast
      rw [ih]
      simp only [anytimeEpochLength]
      push_cast
      ring

/-- Per-round upper envelope obtained by dividing the quadratic regret bound by the cubic elapsed
    time at an epoch boundary. -/
noncomputable def anytimeRegretEnvelope (C : ℝ) (K : ℕ) : ℝ :=
  6 * C * (K + 2) / (K * (2 * K + 1))

theorem anytimeRegretEnvelope_le (C : ℝ) (hC : 0 ≤ C) (K : ℕ) :
    anytimeRegretEnvelope C K ≤ 18 * C / (K + 1) := by
  cases K with
  | zero => simpa [anytimeRegretEnvelope] using hC
  | succ K =>
      have hden1 :
          (0 : ℝ) < (K + 1 : ℕ) * (2 * (K + 1 : ℕ) + 1) := by positivity
      have hden2 : (0 : ℝ) < ((K + 1 : ℕ) + 1) := by positivity
      simp only [anytimeRegretEnvelope]
      rw [div_le_div_iff₀ hden1 hden2]
      push_cast
      have hpoly :
          6 * ((K : ℝ) + 1 + 2) * ((K : ℝ) + 1 + 1) ≤
            18 * ((K : ℝ) + 1) * (2 * ((K : ℝ) + 1) + 1) := by
        nlinarith [sq_nonneg (K : ℝ)]
      nlinarith [mul_le_mul_of_nonneg_left hpoly hC]

theorem tendsto_anytimeRegretEnvelope (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (anytimeRegretEnvelope C) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro K
    exact div_nonneg (by positivity) (by positivity)
  · exact anytimeRegretEnvelope_le C hC
  · have h :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (18 * C)
    simpa [div_eq_mul_inv] using h

/-- Epoch starts are monotone. -/
theorem monotone_anytimeEpochStart : Monotone (epochStart anytimeEpochLength) := by
  intro k l hkl
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  change (∑ j ∈ Finset.range k, anytimeEpochLength j) ≤
    ∑ j ∈ Finset.range (k + d), anytimeEpochLength j
  rw [Finset.sum_range_add]
  omega

theorem le_anytimeEpochStart (K : ℕ) : K ≤ epochStart anytimeEpochLength K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [epochStart_succ]
      have hlength : 1 ≤ anytimeEpochLength K := by
        unfold anytimeEpochLength
        exact Nat.one_le_pow 2 (K + 1) (Nat.succ_pos K)
      omega

theorem exists_lt_anytimeEpochStart_succ (t : ℕ) :
    ∃ K, t < epochStart anytimeEpochLength (K + 1) := by
  refine ⟨t, ?_⟩
  have hstart := le_anytimeEpochStart (t + 1)
  omega

/-- Epoch containing absolute time `t`. -/
def anytimeEpochIndex (t : ℕ) : ℕ := Nat.find (exists_lt_anytimeEpochStart_succ t)

/-- Local time within the epoch containing absolute time `t`. -/
def anytimeEpochOffset (t : ℕ) : ℕ :=
  t - epochStart anytimeEpochLength (anytimeEpochIndex t)

theorem lt_anytimeEpochStart_index_succ (t : ℕ) :
    t < epochStart anytimeEpochLength (anytimeEpochIndex t + 1) := by
  exact Nat.find_spec (exists_lt_anytimeEpochStart_succ t)

theorem anytimeEpochStart_index_le (t : ℕ) :
    epochStart anytimeEpochLength (anytimeEpochIndex t) ≤ t := by
  by_cases hzero : anytimeEpochIndex t = 0
  · simp [hzero]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hklt : k < anytimeEpochIndex t := by omega
    have hnot : ¬t < epochStart anytimeEpochLength (k + 1) := by
      exact Nat.find_min (exists_lt_anytimeEpochStart_succ t)
        (by simpa [anytimeEpochIndex] using hklt)
    have hnot' : ¬t < epochStart anytimeEpochLength (anytimeEpochIndex t) := by
      simpa [hk, Nat.succ_eq_add_one] using hnot
    omega

theorem anytimeEpochStart_add_offset (t : ℕ) :
    epochStart anytimeEpochLength (anytimeEpochIndex t) + anytimeEpochOffset t = t := by
  rw [anytimeEpochOffset, Nat.add_sub_of_le (anytimeEpochStart_index_le t)]

theorem anytimeEpochOffset_le (t : ℕ) :
    anytimeEpochOffset t ≤ anytimeEpochLength (anytimeEpochIndex t) := by
  have hlt := lt_anytimeEpochStart_index_succ t
  rw [epochStart_succ] at hlt
  rw [anytimeEpochOffset]
  omega

theorem anytimeEpochOffset_lt (t : ℕ) :
    anytimeEpochOffset t < anytimeEpochLength (anytimeEpochIndex t) := by
  have hlt := lt_anytimeEpochStart_index_succ t
  have hle := anytimeEpochStart_index_le t
  rw [epochStart_succ] at hlt
  rw [anytimeEpochOffset]
  omega

theorem anytimeEpochIndex_ge_of_start_le {K t : ℕ}
    (h : epochStart anytimeEpochLength K ≤ t) : K ≤ anytimeEpochIndex t := by
  by_contra hnot
  have hsucc : anytimeEpochIndex t + 1 ≤ K := by omega
  have hmono := monotone_anytimeEpochStart hsucc
  have hlt := lt_anytimeEpochStart_index_succ t
  omega

theorem anytimeEpochIndex_eq {K t : ℕ}
    (hleft : epochStart anytimeEpochLength K ≤ t)
    (hright : t < epochStart anytimeEpochLength (K + 1)) :
    anytimeEpochIndex t = K := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (exists_lt_anytimeEpochStart_succ t) hright
  · exact anytimeEpochIndex_ge_of_start_le hleft

variable {A : Type*} [Fintype A] [Nonempty A]

/-- Regret at the end of `K` complete anytime epochs. -/
theorem anytimeRestartedSigned_fixedActionRegret_le
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (K : ℕ) (a : A) :
    cumGain g (epochStart anytimeEpochLength K) a
        - restartedSignedAlgGain anytimeEpochRate anytimeEpochLength g K
      ≤ (Real.log (Fintype.card A) + 1) * K * (K + 1) := by
  calc
    cumGain g (epochStart anytimeEpochLength K) a
          - restartedSignedAlgGain anytimeEpochRate anytimeEpochLength g K
      ≤ ∑ k ∈ Finset.range K,
          2 * (Real.log (Fintype.card A) / anytimeEpochRate k
            + anytimeEpochRate k * anytimeEpochLength k) :=
        restartedSigned_fixedActionRegret_le anytimeEpochRate anytimeEpochLength
          anytimeEpochRate_pos anytimeEpochRate_le_one hg K a
    _ = (Real.log (Fintype.card A) + 1) * K * (K + 1) :=
      sum_anytimeEpoch_regretTerm_eq _ K

/-- Regret through every prefix `T` of epoch `K`. The bound is quadratic in `K`, uniformly over
    the active prefix. -/
theorem anytimeRestartedSigned_fixedActionRegretPrefix_le
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (K T : ℕ) (hT : T ≤ anytimeEpochLength K) (a : A) :
    cumGain g (epochStart anytimeEpochLength K + T) a
        - restartedSignedAlgGainPrefix anytimeEpochRate anytimeEpochLength g K T
      ≤ (Real.log (Fintype.card A) + 1) * (K + 1) * (K + 2) := by
  calc
    cumGain g (epochStart anytimeEpochLength K + T) a
          - restartedSignedAlgGainPrefix anytimeEpochRate anytimeEpochLength g K T
      ≤ (∑ k ∈ Finset.range K,
          2 * (Real.log (Fintype.card A) / anytimeEpochRate k
            + anytimeEpochRate k * anytimeEpochLength k))
          + 2 * (Real.log (Fintype.card A) / anytimeEpochRate K
            + anytimeEpochRate K * T) :=
        restartedSigned_fixedActionRegretPrefix_le anytimeEpochRate anytimeEpochLength
          anytimeEpochRate_pos anytimeEpochRate_le_one hg K T a
    _ ≤ (Real.log (Fintype.card A) + 1) * K * (K + 1)
          + 2 * (Real.log (Fintype.card A) + 1) * (K + 1) := by
        rw [sum_anytimeEpoch_regretTerm_eq]
        linarith [anytimeEpoch_prefixRegretTerm_le
          (Real.log (Fintype.card A)) K T hT]
    _ = (Real.log (Fintype.card A) + 1) * (K + 1) * (K + 2) := by
      ring

/-- The per-round fixed-action regret through every prefix of epoch `K` is bounded by an explicit
    envelope tending to zero. -/
theorem anytimeRestartedSigned_fixedActionRegretPrefix_div_le
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (K T : ℕ) (hK : 1 ≤ K) (hT : T ≤ anytimeEpochLength K) (a : A) :
    (cumGain g (epochStart anytimeEpochLength K + T) a
        - restartedSignedAlgGainPrefix anytimeEpochRate anytimeEpochLength g K T) /
        (epochStart anytimeEpochLength K + T)
      ≤ anytimeRegretEnvelope (Real.log (Fintype.card A) + 1) K := by
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hcard : (1 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast Fintype.card_pos
  have hC : 0 ≤ Real.log (Fintype.card A) + 1 :=
    add_nonneg (Real.log_nonneg hcard) zero_le_one
  have hstartpos : 0 < (epochStart anytimeEpochLength K : ℝ) := by
    rw [anytimeEpochStart_cast]
    positivity
  have hdenpos : 0 < (epochStart anytimeEpochLength K + T : ℝ) := by
    positivity
  have hden : (epochStart anytimeEpochLength K : ℝ) ≤
      (epochStart anytimeEpochLength K : ℝ) + T :=
    le_add_of_nonneg_right (Nat.cast_nonneg T)
  have hreg := anytimeRestartedSigned_fixedActionRegretPrefix_le hg K T hT a
  have hdiv := (div_le_div_iff_of_pos_right hdenpos).2 hreg
  calc
    (cumGain g (epochStart anytimeEpochLength K + T) a
          - restartedSignedAlgGainPrefix anytimeEpochRate anytimeEpochLength g K T) /
        (epochStart anytimeEpochLength K + T)
      ≤ ((Real.log (Fintype.card A) + 1) * (K + 1) * (K + 2)) /
          (epochStart anytimeEpochLength K + T) := hdiv
    _ ≤ ((Real.log (Fintype.card A) + 1) * (K + 1) * (K + 2)) /
          epochStart anytimeEpochLength K := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)
      · exact hstartpos
      · exact hden
    _ = anytimeRegretEnvelope (Real.log (Fintype.card A) + 1) K := by
      rw [anytimeEpochStart_cast]
      simp only [anytimeRegretEnvelope]
      field_simp

/-- Uniform no-regret statement for the horizon-independent schedule: for every positive
    tolerance, all sufficiently late epochs and all prefixes of their active epoch have
    per-round regret below that tolerance, simultaneously for every fixed action. -/
theorem eventually_anytimeRestartedSigned_fixedActionRegretPrefix_div_lt
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K in atTop, ∀ T ≤ anytimeEpochLength K, ∀ a : A,
      (cumGain g (epochStart anytimeEpochLength K + T) a
          - restartedSignedAlgGainPrefix anytimeEpochRate anytimeEpochLength g K T) /
          (epochStart anytimeEpochLength K + T) < ε := by
  have hcard : (1 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast Fintype.card_pos
  have hC : 0 ≤ Real.log (Fintype.card A) + 1 :=
    add_nonneg (Real.log_nonneg hcard) zero_le_one
  have hlimit :=
    tendsto_anytimeRegretEnvelope (Real.log (Fintype.card A) + 1) hC
  filter_upwards [(tendsto_order.1 hlimit).2 ε hε, eventually_ge_atTop 1]
    with K henv hK
  intro T hT a
  exact lt_of_le_of_lt
    (anytimeRestartedSigned_fixedActionRegretPrefix_div_le hg K T hK hT a)
    henv

/-- Total signed gain of the fixed anytime learner through the absolute horizon `T`. -/
noncomputable def anytimeSignedAlgGain (g : ℕ → A → ℝ) (T : ℕ) : ℝ :=
  restartedSignedAlgGainPrefix anytimeEpochRate anytimeEpochLength g
    (anytimeEpochIndex T) (anytimeEpochOffset T)

/-- Distribution played by the fixed anytime learner at absolute round `t`. -/
noncomputable def anytimeSignedMWDist (g : ℕ → A → ℝ) (t : ℕ) : PMF A :=
  signedMWDistFrom (anytimeEpochRate (anytimeEpochIndex t)) g
    (epochStart anytimeEpochLength (anytimeEpochIndex t)) (anytimeEpochOffset t)

theorem anytimeSignedMWDist_congr_of_forall_lt
    (g h : ℕ → A → ℝ) (t : ℕ) (heq : ∀ s < t, g s = h s) :
    anytimeSignedMWDist g t = anytimeSignedMWDist h t := by
  unfold anytimeSignedMWDist
  apply signedMWDistFrom_congr_of_forall_lt
  intro s hs
  apply heq
  have htime := anytimeEpochStart_add_offset t
  omega

theorem anytimeSignedAlgGain_succ (g : ℕ → A → ℝ) (T : ℕ) :
    anytimeSignedAlgGain g (T + 1) =
      anytimeSignedAlgGain g T + expect (anytimeSignedMWDist g T) (g T) := by
  let K := anytimeEpochIndex T
  let r := anytimeEpochOffset T
  have htime : epochStart anytimeEpochLength K + r = T := by
    simpa [K, r] using anytimeEpochStart_add_offset T
  have hrlt : r < anytimeEpochLength K := by
    simpa [K, r] using anytimeEpochOffset_lt T
  by_cases hwithin : r + 1 < anytimeEpochLength K
  · have hleft : epochStart anytimeEpochLength K ≤ T + 1 := by omega
    have hright : T + 1 < epochStart anytimeEpochLength (K + 1) := by
      rw [epochStart_succ]
      omega
    have hindex : anytimeEpochIndex (T + 1) = K :=
      anytimeEpochIndex_eq hleft hright
    have hoffset : anytimeEpochOffset (T + 1) = r + 1 := by
      rw [anytimeEpochOffset, hindex]
      omega
    simp only [anytimeSignedAlgGain]
    unfold anytimeSignedMWDist
    rw [hindex, hoffset]
    change restartedSignedAlgGain anytimeEpochRate anytimeEpochLength g K +
        signedAlgGainFrom (anytimeEpochRate K) g
          (epochStart anytimeEpochLength K) (r + 1) =
      (restartedSignedAlgGain anytimeEpochRate anytimeEpochLength g K +
        signedAlgGainFrom (anytimeEpochRate K) g
          (epochStart anytimeEpochLength K) r) +
      expect (signedMWDistFrom (anytimeEpochRate K) g
        (epochStart anytimeEpochLength K) r) (g T)
    rw [signedAlgGainFrom_succ, ← htime]
    ring
  · have hboundary : r + 1 = anytimeEpochLength K := by omega
    have hnext : T + 1 = epochStart anytimeEpochLength (K + 1) := by
      rw [epochStart_succ]
      omega
    have hpos : 0 < anytimeEpochLength (K + 1) := by
      unfold anytimeEpochLength
      positivity
    have hright : T + 1 < epochStart anytimeEpochLength ((K + 1) + 1) := by
      calc
        T + 1 = epochStart anytimeEpochLength (K + 1) := hnext
        _ < epochStart anytimeEpochLength (K + 1) + anytimeEpochLength (K + 1) :=
          Nat.lt_add_of_pos_right hpos
        _ = epochStart anytimeEpochLength ((K + 1) + 1) :=
          (epochStart_succ anytimeEpochLength (K + 1)).symm
    have hindex : anytimeEpochIndex (T + 1) = K + 1 :=
      anytimeEpochIndex_eq (by omega) hright
    have hoffset : anytimeEpochOffset (T + 1) = 0 := by
      rw [anytimeEpochOffset, hindex, hnext, Nat.sub_self]
    simp only [anytimeSignedAlgGain]
    unfold anytimeSignedMWDist
    rw [hindex, hoffset]
    change restartedSignedAlgGain anytimeEpochRate anytimeEpochLength g (K + 1) +
        signedAlgGainFrom (anytimeEpochRate (K + 1)) g
          (epochStart anytimeEpochLength (K + 1)) 0 =
      (restartedSignedAlgGain anytimeEpochRate anytimeEpochLength g K +
        signedAlgGainFrom (anytimeEpochRate K) g
          (epochStart anytimeEpochLength K) r) +
      expect (signedMWDistFrom (anytimeEpochRate K) g
        (epochStart anytimeEpochLength K) r) (g T)
    rw [restartedSignedAlgGain_succ, signedAlgGainFrom_zero, add_zero]
    rw [← hboundary, signedAlgGainFrom_succ, htime]
    ring

@[simp] theorem anytimeSignedAlgGain_zero (g : ℕ → A → ℝ) :
    anytimeSignedAlgGain g 0 = 0 := by
  have hindex : anytimeEpochIndex 0 = 0 := by
    apply anytimeEpochIndex_eq
    · simp
    · norm_num [epochStart, anytimeEpochLength]
  simp [anytimeSignedAlgGain, restartedSignedAlgGainPrefix, hindex,
    anytimeEpochOffset, restartedSignedAlgGain]

/-- Operational identity: the epoch-aggregated gain is exactly the sum of the expected gains of
    the absolute per-round distributions played by the anytime learner. -/
theorem anytimeSignedAlgGain_eq_sum (g : ℕ → A → ℝ) (T : ℕ) :
    anytimeSignedAlgGain g T =
      ∑ t ∈ Finset.range T, expect (anytimeSignedMWDist g t) (g t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [anytimeSignedAlgGain_succ, Finset.sum_range_succ, ih]

/-- The absolute-horizon regret bound, obtained by locating `T` in its deterministic epoch. -/
theorem anytimeSigned_fixedActionRegret_div_le
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (T : ℕ) (hT : 1 ≤ T) (a : A) :
    (cumGain g T a - anytimeSignedAlgGain g T) / T
      ≤ anytimeRegretEnvelope (Real.log (Fintype.card A) + 1) (anytimeEpochIndex T) := by
  have hstart : epochStart anytimeEpochLength 1 ≤ T := by
    simpa [epochStart, anytimeEpochLength] using hT
  have hindex : 1 ≤ anytimeEpochIndex T :=
    anytimeEpochIndex_ge_of_start_le hstart
  have hbound := anytimeRestartedSigned_fixedActionRegretPrefix_div_le hg
    (anytimeEpochIndex T) (anytimeEpochOffset T) hindex (anytimeEpochOffset_le T) a
  have htime :
      (epochStart anytimeEpochLength (anytimeEpochIndex T) : ℝ)
          + anytimeEpochOffset T = T := by
    exact_mod_cast anytimeEpochStart_add_offset T
  rw [anytimeEpochStart_add_offset T, htime] at hbound
  simpa [anytimeSignedAlgGain] using hbound

/-- Absolute-time no regret: one fixed restarted learner has vanishing positive fixed-action
    regret at every sufficiently large horizon. -/
theorem eventually_anytimeSigned_fixedActionRegret_div_lt
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ a : A,
      (cumGain g T a - anytimeSignedAlgGain g T) / T < ε := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1
    (eventually_anytimeRestartedSigned_fixedActionRegretPrefix_div_lt hg hε)
  refine eventually_atTop.2 ⟨epochStart anytimeEpochLength K₀, ?_⟩
  intro T hT a
  have hindex : K₀ ≤ anytimeEpochIndex T :=
    anytimeEpochIndex_ge_of_start_le hT
  have hbound := hK₀ (anytimeEpochIndex T) hindex
    (anytimeEpochOffset T) (anytimeEpochOffset_le T) a
  have htime :
      (epochStart anytimeEpochLength (anytimeEpochIndex T) : ℝ)
          + anytimeEpochOffset T = T := by
    exact_mod_cast anytimeEpochStart_add_offset T
  rw [anytimeEpochStart_add_offset T, htime] at hbound
  simpa [anytimeSignedAlgGain] using hbound

end Math.OnlineLearning
