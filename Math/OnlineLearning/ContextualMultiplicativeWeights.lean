/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.MultiplicativeWeights
import Mathlib.Analysis.Real.Sqrt

/-!
# Context-local multiplicative weights

This module runs one independent horizon-free multiplicative-weights learner
for every public context.  A context is revealed before prediction, and only
the learner attached to that context advances.  Consequently the pathwise
regret depends on context visitation counts, not on context switches.

The local calendar has epoch length `4 ^ k` and learning rate `2⁻ᵏ`.
The existing restartable signed-gain bound then gives square-root regret in
local time without knowing the evaluation horizon.
-/

namespace Math.OnlineLearning

open Math.Probability

noncomputable section

/-- Epoch `k` of the geometric local learner has `4 ^ k` rounds. -/
def contextualEpochLength (k : ℕ) : ℕ := 4 ^ k

/-- Epoch `k` of the geometric local learner uses rate `2⁻ᵏ`. -/
def contextualEpochRate (k : ℕ) : ℝ := (((2 ^ k : ℕ) : ℝ))⁻¹

theorem contextualEpochRate_pos (k : ℕ) :
    0 < contextualEpochRate k := by
  rw [contextualEpochRate]
  positivity

theorem contextualEpochRate_le_one (k : ℕ) :
    contextualEpochRate k ≤ 1 := by
  rw [contextualEpochRate]
  apply inv_le_one_of_one_le₀
  exact_mod_cast Nat.one_le_two_pow

theorem contextualEpochLength_pos (k : ℕ) :
    0 < contextualEpochLength k := by
  rw [contextualEpochLength]
  positivity

theorem contextualEpoch_regretTerm_eq (L : ℝ) (k : ℕ) :
    2 *
        (L / contextualEpochRate k +
          contextualEpochRate k * contextualEpochLength k) =
      2 * (L + 1) * (2 : ℝ) ^ k := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  simp only [contextualEpochRate, contextualEpochLength]
  push_cast
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
    ← pow_mul, mul_comm 2 k, pow_mul]
  field_simp

theorem sum_contextualEpoch_regretTerm_eq (L : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K,
        2 *
          (L / contextualEpochRate k +
            contextualEpochRate k * contextualEpochLength k)) =
      2 * (L + 1) * ((2 : ℝ) ^ K - 1) := by
  simp_rw [contextualEpoch_regretTerm_eq]
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

theorem contextualEpoch_prefixRegretTerm_le
    (L : ℝ) (K T : ℕ)
    (hT : T ≤ contextualEpochLength K) :
    2 *
        (L / contextualEpochRate K +
          contextualEpochRate K * T) ≤
      2 * (L + 1) * (2 : ℝ) ^ K := by
  have hrate := contextualEpochRate_pos K
  have hcast : (T : ℝ) ≤ contextualEpochLength K := by
    exact_mod_cast hT
  calc
    2 *
          (L / contextualEpochRate K +
            contextualEpochRate K * T) ≤
        2 *
          (L / contextualEpochRate K +
            contextualEpochRate K * contextualEpochLength K) := by
      gcongr
    _ = 2 * (L + 1) * (2 : ℝ) ^ K :=
      contextualEpoch_regretTerm_eq L K

/-- The elapsed local time at the beginning of geometric epoch `K`. -/
theorem contextualEpochStart_cast (K : ℕ) :
    (epochStart contextualEpochLength K : ℝ) =
      ((4 : ℝ) ^ K - 1) / 3 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [epochStart_succ]
      push_cast
      rw [ih]
      simp only [contextualEpochLength]
      push_cast
      rw [pow_succ]
      ring

theorem monotone_contextualEpochStart :
    Monotone (epochStart contextualEpochLength) := by
  intro k l hkl
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  change (∑ j ∈ Finset.range k, contextualEpochLength j) ≤
    ∑ j ∈ Finset.range (k + d), contextualEpochLength j
  rw [Finset.sum_range_add]
  omega

theorem le_contextualEpochStart (K : ℕ) :
    K ≤ epochStart contextualEpochLength K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [epochStart_succ]
      have hlength : 1 ≤ contextualEpochLength K :=
        contextualEpochLength_pos K
      omega

theorem exists_lt_contextualEpochStart_succ (t : ℕ) :
    ∃ K, t < epochStart contextualEpochLength (K + 1) := by
  refine ⟨t, ?_⟩
  have hstart := le_contextualEpochStart (t + 1)
  omega

/-- Geometric epoch containing local time `t`. -/
def contextualEpochIndex (t : ℕ) : ℕ :=
  Nat.find (exists_lt_contextualEpochStart_succ t)

/-- Offset of local time `t` inside its geometric epoch. -/
def contextualEpochOffset (t : ℕ) : ℕ :=
  t - epochStart contextualEpochLength (contextualEpochIndex t)

theorem lt_contextualEpochStart_index_succ (t : ℕ) :
    t <
      epochStart contextualEpochLength
        (contextualEpochIndex t + 1) := by
  exact Nat.find_spec (exists_lt_contextualEpochStart_succ t)

theorem contextualEpochStart_index_le (t : ℕ) :
    epochStart contextualEpochLength (contextualEpochIndex t) ≤ t := by
  by_cases hzero : contextualEpochIndex t = 0
  · simp [hzero]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hklt : k < contextualEpochIndex t := by omega
    have hnot :
        ¬t < epochStart contextualEpochLength (k + 1) := by
      exact Nat.find_min (exists_lt_contextualEpochStart_succ t)
        (by simpa [contextualEpochIndex] using hklt)
    have hnot' :
        ¬t <
          epochStart contextualEpochLength
            (contextualEpochIndex t) := by
      simpa [hk, Nat.succ_eq_add_one] using hnot
    omega

theorem contextualEpochStart_add_offset (t : ℕ) :
    epochStart contextualEpochLength (contextualEpochIndex t) +
        contextualEpochOffset t =
      t := by
  rw [contextualEpochOffset,
    Nat.add_sub_of_le (contextualEpochStart_index_le t)]

theorem contextualEpochOffset_le (t : ℕ) :
    contextualEpochOffset t ≤
      contextualEpochLength (contextualEpochIndex t) := by
  have hlt := lt_contextualEpochStart_index_succ t
  rw [epochStart_succ] at hlt
  rw [contextualEpochOffset]
  omega

theorem contextualEpochOffset_lt (t : ℕ) :
    contextualEpochOffset t <
      contextualEpochLength (contextualEpochIndex t) := by
  have hlt := lt_contextualEpochStart_index_succ t
  have hle := contextualEpochStart_index_le t
  rw [epochStart_succ] at hlt
  rw [contextualEpochOffset]
  omega

theorem contextualEpochIndex_ge_of_start_le {K t : ℕ}
    (h : epochStart contextualEpochLength K ≤ t) :
    K ≤ contextualEpochIndex t := by
  by_contra hnot
  have hsucc : contextualEpochIndex t + 1 ≤ K := by omega
  have hmono := monotone_contextualEpochStart hsucc
  have hlt := lt_contextualEpochStart_index_succ t
  omega

theorem contextualEpochIndex_eq {K t : ℕ}
    (hleft : epochStart contextualEpochLength K ≤ t)
    (hright :
      t < epochStart contextualEpochLength (K + 1)) :
    contextualEpochIndex t = K := by
  apply Nat.le_antisymm
  · exact Nat.find_min'
      (exists_lt_contextualEpochStart_succ t) hright
  · exact contextualEpochIndex_ge_of_start_le hleft

variable {A : Type*} [Fintype A] [Nonempty A]

/-- Total gain of the horizon-free geometric learner through local time `T`. -/
def contextualLocalAlgGain
    (g : ℕ → A → ℝ) (T : ℕ) : ℝ :=
  restartedSignedAlgGainPrefix
    contextualEpochRate contextualEpochLength g
    (contextualEpochIndex T) (contextualEpochOffset T)

/-- Distribution played by the geometric learner at local time `t`. -/
def contextualLocalMWDist
    (g : ℕ → A → ℝ) (t : ℕ) : PMF A :=
  signedMWDistFrom
    (contextualEpochRate (contextualEpochIndex t)) g
    (epochStart contextualEpochLength (contextualEpochIndex t))
    (contextualEpochOffset t)

theorem contextualLocalMWDist_congr_of_forall_lt
    (g h : ℕ → A → ℝ) (t : ℕ)
    (heq : ∀ s < t, g s = h s) :
    contextualLocalMWDist g t =
      contextualLocalMWDist h t := by
  unfold contextualLocalMWDist
  apply signedMWDistFrom_congr_of_forall_lt
  intro s hs
  apply heq
  have htime := contextualEpochStart_add_offset t
  omega

theorem contextualLocalAlgGain_succ
    (g : ℕ → A → ℝ) (T : ℕ) :
    contextualLocalAlgGain g (T + 1) =
      contextualLocalAlgGain g T +
        expect (contextualLocalMWDist g T) (g T) := by
  let K := contextualEpochIndex T
  let r := contextualEpochOffset T
  have htime :
      epochStart contextualEpochLength K + r = T := by
    simpa [K, r] using contextualEpochStart_add_offset T
  have hrle : r < contextualEpochLength K := by
    simpa [K, r] using contextualEpochOffset_lt T
  by_cases hwithin : r + 1 < contextualEpochLength K
  · have hleft :
        epochStart contextualEpochLength K ≤ T + 1 := by
      omega
    have hright :
        T + 1 <
          epochStart contextualEpochLength (K + 1) := by
      rw [epochStart_succ]
      omega
    have hindex : contextualEpochIndex (T + 1) = K :=
      contextualEpochIndex_eq hleft hright
    have hoffset :
        contextualEpochOffset (T + 1) = r + 1 := by
      rw [contextualEpochOffset, hindex]
      omega
    simp only [contextualLocalAlgGain]
    unfold contextualLocalMWDist
    rw [hindex, hoffset]
    change
      restartedSignedAlgGain
            contextualEpochRate contextualEpochLength g K +
          signedAlgGainFrom
            (contextualEpochRate K) g
            (epochStart contextualEpochLength K) (r + 1) =
        (restartedSignedAlgGain
              contextualEpochRate contextualEpochLength g K +
            signedAlgGainFrom
              (contextualEpochRate K) g
              (epochStart contextualEpochLength K) r) +
          expect
            (signedMWDistFrom
              (contextualEpochRate K) g
              (epochStart contextualEpochLength K) r)
            (g T)
    rw [signedAlgGainFrom_succ, ← htime]
    ring
  · have hboundary :
        r + 1 = contextualEpochLength K := by omega
    have hnext :
        T + 1 =
          epochStart contextualEpochLength (K + 1) := by
      rw [epochStart_succ]
      omega
    have hpos :
        0 < contextualEpochLength (K + 1) :=
      contextualEpochLength_pos (K + 1)
    have hright :
        T + 1 <
          epochStart contextualEpochLength ((K + 1) + 1) := by
      calc
        T + 1 =
            epochStart contextualEpochLength (K + 1) := hnext
        _ <
            epochStart contextualEpochLength (K + 1) +
              contextualEpochLength (K + 1) :=
          Nat.lt_add_of_pos_right hpos
        _ =
            epochStart contextualEpochLength ((K + 1) + 1) :=
          (epochStart_succ contextualEpochLength (K + 1)).symm
    have hindex :
        contextualEpochIndex (T + 1) = K + 1 :=
      contextualEpochIndex_eq (by omega) hright
    have hoffset :
        contextualEpochOffset (T + 1) = 0 := by
      rw [contextualEpochOffset, hindex, hnext, Nat.sub_self]
    simp only [contextualLocalAlgGain]
    unfold contextualLocalMWDist
    rw [hindex, hoffset]
    change
      restartedSignedAlgGain
            contextualEpochRate contextualEpochLength g (K + 1) +
          signedAlgGainFrom
            (contextualEpochRate (K + 1)) g
            (epochStart contextualEpochLength (K + 1)) 0 =
        (restartedSignedAlgGain
              contextualEpochRate contextualEpochLength g K +
            signedAlgGainFrom
              (contextualEpochRate K) g
              (epochStart contextualEpochLength K) r) +
          expect
            (signedMWDistFrom
              (contextualEpochRate K) g
              (epochStart contextualEpochLength K) r)
            (g T)
    rw [restartedSignedAlgGain_succ, signedAlgGainFrom_zero, add_zero]
    rw [← hboundary, signedAlgGainFrom_succ, htime]
    ring

@[simp]
theorem contextualLocalAlgGain_zero (g : ℕ → A → ℝ) :
    contextualLocalAlgGain g 0 = 0 := by
  have hindex : contextualEpochIndex 0 = 0 := by
    apply contextualEpochIndex_eq
    · simp
    · norm_num [epochStart, contextualEpochLength]
  simp [contextualLocalAlgGain, restartedSignedAlgGainPrefix,
    hindex, contextualEpochOffset, restartedSignedAlgGain]

theorem contextualLocalAlgGain_eq_sum
    (g : ℕ → A → ℝ) (T : ℕ) :
    contextualLocalAlgGain g T =
      ∑ t ∈ Finset.range T,
        expect (contextualLocalMWDist g t) (g t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [contextualLocalAlgGain_succ,
        Finset.sum_range_succ, ih]

private theorem contextual_log_card_add_one_nonneg :
    0 ≤ Real.log (Fintype.card A) + 1 := by
  have hcard : (1 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast Fintype.card_pos
  exact add_nonneg (Real.log_nonneg hcard) zero_le_one

/-- Local fixed-action regret in terms of the active geometric epoch. -/
theorem contextualLocal_fixedActionRegret_le_index
    {g : ℕ → A → ℝ}
    (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (T : ℕ) (a : A) :
    cumGain g T a - contextualLocalAlgGain g T ≤
      4 * (Real.log (Fintype.card A) + 1) *
        (2 : ℝ) ^ contextualEpochIndex T := by
  let K := contextualEpochIndex T
  let r := contextualEpochOffset T
  have hbound :=
    restartedSigned_fixedActionRegretPrefix_le
      contextualEpochRate contextualEpochLength
      contextualEpochRate_pos contextualEpochRate_le_one
      hg K r a
  have htime :
      epochStart contextualEpochLength K + r = T := by
    simpa [K, r] using contextualEpochStart_add_offset T
  have hprefix :=
    contextualEpoch_prefixRegretTerm_le
      (Real.log (Fintype.card A)) K r
      (by simpa [K, r] using contextualEpochOffset_le T)
  rw [sum_contextualEpoch_regretTerm_eq] at hbound
  rw [htime] at hbound
  change
    cumGain g T a - contextualLocalAlgGain g T ≤ _ at hbound
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ K := by
    exact one_le_pow₀ (by norm_num)
  have hC := contextual_log_card_add_one_nonneg (A := A)
  calc
    cumGain g T a - contextualLocalAlgGain g T ≤
        2 * (Real.log (Fintype.card A) + 1) *
              ((2 : ℝ) ^ K - 1) +
            2 * (Real.log (Fintype.card A) + 1) *
              (2 : ℝ) ^ K := by
      exact hbound.trans (add_le_add (le_refl _) hprefix)
    _ ≤
        4 * (Real.log (Fintype.card A) + 1) *
          (2 : ℝ) ^ K := by
      nlinarith

theorem contextualEpochIndex_pow_le (T : ℕ) :
    ((2 : ℝ) ^ contextualEpochIndex T) ^ 2 ≤
      3 * T + 1 := by
  have hstart := contextualEpochStart_index_le T
  have hstartReal :
      (epochStart contextualEpochLength
          (contextualEpochIndex T) : ℝ) ≤ T := by
    exact_mod_cast hstart
  rw [contextualEpochStart_cast] at hstartReal
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
    ← pow_mul, mul_comm 2 (contextualEpochIndex T),
    pow_mul] at hstartReal
  linarith

theorem contextualEpochIndex_pow_le_sqrt (T : ℕ) :
    (2 : ℝ) ^ contextualEpochIndex T ≤
      Real.sqrt (3 * T + 1) := by
  exact Real.le_sqrt_of_sq_le
    (contextualEpochIndex_pow_le T)

/-- The geometric learner has square-root fixed-action regret at every
local horizon, with zero regret at the empty horizon. -/
theorem contextualLocal_fixedActionRegret_le_sqrt
    {g : ℕ → A → ℝ}
    (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (T : ℕ) (a : A) :
    cumGain g T a - contextualLocalAlgGain g T ≤
      8 * (Real.log (Fintype.card A) + 1) *
        Real.sqrt T := by
  cases T with
  | zero => simp
  | succ T =>
      have hbase :=
        contextualLocal_fixedActionRegret_le_index
          hg (T + 1) a
      have hindex :=
        contextualEpochIndex_pow_le_sqrt (T + 1)
      have hindex' :
          (2 : ℝ) ^ contextualEpochIndex (T + 1) ≤
            Real.sqrt (3 * (T + 1 : ℝ) + 1) := by
        norm_num [Nat.cast_add, Nat.cast_one] at hindex ⊢
        exact hindex
      have harg :
          Real.sqrt (3 * (T + 1 : ℝ) + 1) ≤
            2 * Real.sqrt (T + 1) := by
        apply (Real.sqrt_le_iff).2
        constructor
        · positivity
        · rw [mul_pow, Real.sq_sqrt (by positivity)]
          norm_num
          nlinarith
      have harg' :
          Real.sqrt (3 * (T + 1 : ℕ) + 1) ≤
            2 * Real.sqrt (T + 1 : ℕ) := by
        norm_num [Nat.cast_add, Nat.cast_one] at harg ⊢
        exact harg
      have hC := contextual_log_card_add_one_nonneg (A := A)
      calc
        cumGain g (T + 1) a -
              contextualLocalAlgGain g (T + 1) ≤
            4 * (Real.log (Fintype.card A) + 1) *
              (2 : ℝ) ^ contextualEpochIndex (T + 1) :=
          hbase
        _ ≤
            4 * (Real.log (Fintype.card A) + 1) *
              Real.sqrt (3 * (T + 1 : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_left hindex'
            (mul_nonneg (by norm_num) hC)
        _ ≤
            8 * (Real.log (Fintype.card A) + 1) *
              Real.sqrt (T + 1 : ℕ) := by
          calc
            4 * (Real.log (Fintype.card A) + 1) *
                  Real.sqrt (3 * (T + 1 : ℝ) + 1) ≤
                4 * (Real.log (Fintype.card A) + 1) *
                  (2 * Real.sqrt (T + 1 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left harg
                (mul_nonneg (by norm_num) hC)
            _ =
                8 * (Real.log (Fintype.card A) + 1) *
                  Real.sqrt (T + 1 : ℕ) := by
              norm_num [Nat.cast_add, Nat.cast_one]
              ring

section Contexts

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Number of occurrences of context `q` before global time `T`. -/
def contextVisitCount
    (context : ℕ → Q) (q : Q) (T : ℕ) : ℕ :=
  ((Finset.range T).filter fun t => context t = q).card

omit [Fintype Q] in
@[simp]
theorem contextVisitCount_zero
    (context : ℕ → Q) (q : Q) :
    contextVisitCount context q 0 = 0 := by
  simp [contextVisitCount]

omit [Fintype Q] in
theorem contextVisitCount_succ
    (context : ℕ → Q) (q : Q) (T : ℕ) :
    contextVisitCount context q (T + 1) =
      contextVisitCount context q T +
        if context T = q then 1 else 0 := by
  simp only [contextVisitCount, Finset.range_add_one,
    Finset.filter_insert]
  by_cases hq : context T = q <;> simp [hq]

theorem sum_contextVisitCount
    (context : ℕ → Q) (T : ℕ) :
    ∑ q, contextVisitCount context q T = T := by
  induction T with
  | zero => simp
  | succ T ih =>
      simp_rw [contextVisitCount_succ]
      rw [Finset.sum_add_distrib, ih]
      simp

/-- The local round of the learner selected by the context at global time
`t`.  It counts only earlier occurrences of the revealed context. -/
def contextLocalRound (context : ℕ → Q) (t : ℕ) : ℕ :=
  contextVisitCount context (context t) t

/-- The distribution played after the current context is revealed.  The
gain stream is indexed by context and local visit number. -/
def contextualMWDist
    (context : ℕ → Q) (g : Q → ℕ → A → ℝ)
    (t : ℕ) : PMF A :=
  contextualLocalMWDist
    (g (context t)) (contextLocalRound context t)

omit [Fintype Q] in
/-- Prediction at time `t` depends only on the revealed context and the
earlier gains observed on visits to that same context. -/
theorem contextualMWDist_congr_of_local_past
    (context : ℕ → Q) (g h : Q → ℕ → A → ℝ)
    (t : ℕ)
    (heq :
      ∀ n < contextLocalRound context t,
        g (context t) n = h (context t) n) :
    contextualMWDist context g t =
      contextualMWDist context h t := by
  exact contextualLocalMWDist_congr_of_forall_lt
    (g (context t)) (h (context t))
    (contextLocalRound context t) heq

/-- Gain of a fixed contextual policy through horizon `T`. -/
def contextualPolicyGain
    (context : ℕ → Q) (g : Q → ℕ → A → ℝ)
    (T : ℕ) (policy : Q → A) : ℝ :=
  ∑ q, cumGain (g q) (contextVisitCount context q T) (policy q)

/-- Gain of all context-local learners through horizon `T`. -/
def contextualAlgGain
    (context : ℕ → Q) (g : Q → ℕ → A → ℝ)
    (T : ℕ) : ℝ :=
  ∑ q,
    contextualLocalAlgGain
      (g q) (contextVisitCount context q T)

omit [Fintype A] [Nonempty A] in
theorem contextualPolicyGain_eq_sum
    (context : ℕ → Q) (g : Q → ℕ → A → ℝ)
    (T : ℕ) (policy : Q → A) :
    contextualPolicyGain context g T policy =
      ∑ t ∈ Finset.range T,
        g (context t) (contextLocalRound context t)
          (policy (context t)) := by
  induction T with
  | zero => simp [contextualPolicyGain]
  | succ T ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [contextualPolicyGain, contextVisitCount_succ]
      calc
        (∑ q,
            cumGain (g q)
              (contextVisitCount context q T +
                if context T = q then 1 else 0)
              (policy q)) =
            ∑ q,
              (cumGain (g q)
                  (contextVisitCount context q T) (policy q) +
                if context T = q then
                  g q (contextVisitCount context q T) (policy q)
                else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases hq : context T = q
          · simp [hq, cumGain_succ]
          · simp [hq]
        _ =
            (∑ q,
              cumGain (g q)
                (contextVisitCount context q T) (policy q)) +
              g (context T) (contextLocalRound context T)
                (policy (context T)) := by
          rw [Finset.sum_add_distrib]
          simp [contextLocalRound]

theorem contextualAlgGain_eq_sum
    (context : ℕ → Q) (g : Q → ℕ → A → ℝ)
    (T : ℕ) :
    contextualAlgGain context g T =
      ∑ t ∈ Finset.range T,
        expect (contextualMWDist context g t)
          (g (context t) (contextLocalRound context t)) := by
  induction T with
  | zero => simp [contextualAlgGain]
  | succ T ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [contextualAlgGain, contextVisitCount_succ]
      calc
        (∑ q,
            contextualLocalAlgGain (g q)
              (contextVisitCount context q T +
                if context T = q then 1 else 0)) =
            ∑ q,
              (contextualLocalAlgGain (g q)
                  (contextVisitCount context q T) +
                if context T = q then
                  expect
                    (contextualLocalMWDist
                      (g q) (contextVisitCount context q T))
                    (g q (contextVisitCount context q T))
                else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases hq : context T = q
          · simp [hq, contextualLocalAlgGain_succ]
          · simp [hq]
        _ =
            (∑ q,
              contextualLocalAlgGain
                (g q) (contextVisitCount context q T)) +
              expect (contextualMWDist context g T)
                (g (context T) (contextLocalRound context T)) := by
          rw [Finset.sum_add_distrib]
          simp [contextualMWDist, contextLocalRound]

/-- Pathwise regret against every fixed context-to-action policy.  The
bound depends only on visitation counts and has no context-switch term. -/
theorem contextual_fixedPolicyRegret_le_visits
    (context : ℕ → Q) {g : Q → ℕ → A → ℝ}
    (hg : ∀ q t a, g q t a ∈ Set.Icc (-1 : ℝ) 1)
    (T : ℕ) (policy : Q → A) :
    contextualPolicyGain context g T policy -
        contextualAlgGain context g T ≤
      8 * (Real.log (Fintype.card A) + 1) *
        ∑ q, Real.sqrt (contextVisitCount context q T) := by
  rw [contextualPolicyGain, contextualAlgGain,
    ← Finset.sum_sub_distrib]
  calc
    (∑ q,
        (cumGain (g q) (contextVisitCount context q T)
            (policy q) -
          contextualLocalAlgGain
            (g q) (contextVisitCount context q T))) ≤
        ∑ q,
          8 * (Real.log (Fintype.card A) + 1) *
            Real.sqrt (contextVisitCount context q T) := by
      apply Finset.sum_le_sum
      intro q _
      exact contextualLocal_fixedActionRegret_le_sqrt
        (hg q) (contextVisitCount context q T) (policy q)
    _ =
        8 * (Real.log (Fintype.card A) + 1) *
          ∑ q, Real.sqrt (contextVisitCount context q T) := by
      rw [Finset.mul_sum]

theorem sum_sqrt_contextVisitCount_le
    (context : ℕ → Q) (T : ℕ) :
    (∑ q, Real.sqrt (contextVisitCount context q T)) ≤
      Real.sqrt (Fintype.card Q * T) := by
  have h :=
    Real.sum_sqrt_mul_sqrt_le
      (Finset.univ : Finset Q)
      (f := fun q => (contextVisitCount context q T : ℝ))
      (g := fun _q => (1 : ℝ))
      (fun _ => by positivity)
      (fun _ => by positivity)
  have hcount :
      (∑ q, (contextVisitCount context q T : ℝ)) = T := by
    rw [← Nat.cast_sum, sum_contextVisitCount]
  rw [hcount] at h
  calc
    (∑ q, Real.sqrt (contextVisitCount context q T)) ≤
        Real.sqrt T * Real.sqrt (Fintype.card Q) := by
      simpa only [Real.sqrt_one, mul_one, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, one_mul] using h
    _ = Real.sqrt (Fintype.card Q * T) := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ T)]
      congr 1
      ring

/-- Deterministic cardinality-only corollary of the visitation-count bound. -/
theorem contextual_fixedPolicyRegret_le_card
    (context : ℕ → Q) {g : Q → ℕ → A → ℝ}
    (hg : ∀ q t a, g q t a ∈ Set.Icc (-1 : ℝ) 1)
    (T : ℕ) (policy : Q → A) :
    contextualPolicyGain context g T policy -
        contextualAlgGain context g T ≤
      8 * (Real.log (Fintype.card A) + 1) *
        Real.sqrt (Fintype.card Q * T) := by
  exact
    (contextual_fixedPolicyRegret_le_visits
      context hg T policy).trans
      (mul_le_mul_of_nonneg_left
        (sum_sqrt_contextVisitCount_le context T)
        (by positivity))

end Contexts

end

end Math.OnlineLearning
