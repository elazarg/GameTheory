/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.SuffixHistory

/-!
# Fixed-prefix public-history accounting

This file identifies the root history law after a deterministic public prefix
length with the average of the conditional suffix laws at that prefix.  It
then aggregates conditional suffix charge bounds over the realized prefix
law.

The prefix length is deterministic.  A random stopping prefix needs a
separate stopped-history type or a finite disjoint union of history lengths;
that seam is deliberately not hidden by casts here.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- The root law at a sum of two deterministic horizons is the prefix law
followed by the conditional full-history suffix law from the realized
prefix. -/
theorem histDist_add_eq_bind_histDistAfter
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State)
    (prefixLength suffixLength : ℕ) :
    G.histDist profile initial (prefixLength + suffixLength) =
      (G.histDist profile initial prefixLength).bind fun base =>
        G.histDistAfter profile base suffixLength := by
  induction suffixLength with
  | zero =>
      simp only [Nat.add_zero, G.histDistAfter_zero, PMF.bind_pure]
  | succ suffixLength ih =>
      change
        G.histDist profile initial ((prefixLength + suffixLength) + 1) =
          (G.histDist profile initial prefixLength).bind fun base =>
            G.histDistAfter profile base (suffixLength + 1)
      rw [G.histDist_succ, ih, PMF.bind_bind]
      apply congrArg (PMF.bind (G.histDist profile initial prefixLength))
      funext base
      exact (G.histDistAfter_succ profile base suffixLength).symm

/-- A root expectation after a fixed prefix is the prefix-law average of
the corresponding conditional suffix expectation. -/
theorem expectedHistoryValue_add_eq_expect_afterHistory
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State)
    (potential : G.HistoryPotential) (prefixLength suffixLength : ℕ) :
    G.expectedHistoryValue profile initial potential
        (prefixLength + suffixLength) =
      expect (G.histDist profile initial prefixLength) fun base =>
        G.expectedHistoryValue (G.afterHistoryProfile profile base)
          base.2 (G.afterHistoryPotential potential base) suffixLength := by
  unfold expectedHistoryValue
  rw [G.histDist_add_eq_bind_histDistAfter, expect_bind]
  apply congrArg (expect (G.histDist profile initial prefixLength))
  funext base
  exact (G.expectedHistoryValue_afterHistory profile potential base
    suffixLength).symm

/-- Conditional normalized suffix-charge bounds aggregate exactly over the
root prefix law.

Only reachable prefixes need satisfy the conditional bound. -/
theorem normalized_suffix_charge_le_expect
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State)
    (charge : G.HistoryPotential) (prefixLength horizon : ℕ)
    (error : G.Hist prefixLength → ℝ)
    (hbound : ∀ base,
      base ∈ (G.histDist profile initial prefixLength).support →
        (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          G.expectedHistoryValue (G.afterHistoryProfile profile base)
            base.2 (G.afterHistoryPotential charge base) time ≤
          error base) :
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        G.expectedHistoryValue profile initial charge
          (prefixLength + time) ≤
      expect (G.histDist profile initial prefixLength) error := by
  let prefixLaw := G.histDist profile initial prefixLength
  let localCharge : ℕ → G.Hist prefixLength → ℝ :=
    fun time base =>
      G.expectedHistoryValue (G.afterHistoryProfile profile base)
        base.2 (G.afterHistoryPotential charge base) time
  have hdecompose : ∀ time,
      G.expectedHistoryValue profile initial charge
          (prefixLength + time) =
        expect prefixLaw (localCharge time) := by
    intro time
    exact G.expectedHistoryValue_add_eq_expect_afterHistory
      profile initial charge prefixLength time
  have hsum :
      ∑ time ∈ Finset.range horizon,
          expect prefixLaw (localCharge time) =
        expect prefixLaw fun base =>
          ∑ time ∈ Finset.range horizon, localCharge time base := by
    classical
    letI : Fintype (G.Hist prefixLength) :=
      Fintype.ofFinite (G.Hist prefixLength)
    simp only [expect_eq_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro base _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun time _ => hdecompose time, hsum]
  rw [← expect_const_mul]
  classical
  let aggregate : G.Hist prefixLength → ℝ :=
    fun base =>
      (horizon : ℝ)⁻¹ *
        ∑ time ∈ Finset.range horizon, localCharge time base
  have hcongr :
      expect prefixLaw aggregate =
        expect prefixLaw fun base =>
          if base ∈ prefixLaw.support then aggregate base else error base :=
    Math.ProbabilityMassFunction.expect_congr_on_support
      prefixLaw _ _ fun base hbase => by simp [hbase]
  rw [hcongr]
  apply expect_mono
  intro base
  by_cases hbase : base ∈ prefixLaw.support
  · simpa [aggregate, localCharge, prefixLaw, hbase] using
      hbound base hbase
  · simp [hbase]

/-- A uniform conditional suffix-charge bound remains uniform after
averaging over the root prefix law. -/
theorem normalized_suffix_charge_le
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State)
    (charge : G.HistoryPotential) (prefixLength horizon : ℕ)
    (error : ℝ)
    (hbound : ∀ base,
      base ∈ (G.histDist profile initial prefixLength).support →
        (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          G.expectedHistoryValue (G.afterHistoryProfile profile base)
            base.2 (G.afterHistoryPotential charge base) time ≤ error) :
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        G.expectedHistoryValue profile initial charge
          (prefixLength + time) ≤ error := by
  have h := G.normalized_suffix_charge_le_expect profile initial charge
    prefixLength horizon (fun _ => error) hbound
  simpa using h

/-- A deterministic prefix contributes only its own finite charge, while the
remaining suffix charge is the prefix-law average of the conditional suffix
bounds. -/
theorem fixed_prefix_charge_sum_le
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State)
    (charge : G.HistoryPotential) (prefixLength horizon : ℕ)
    (prefixBound : ℝ) (error : G.Hist prefixLength → ℝ)
    (hhorizon : 0 < horizon)
    (hprefix : ∀ time, time < prefixLength →
      G.expectedHistoryValue profile initial charge time ≤ prefixBound)
    (hsuffix : ∀ base,
      base ∈ (G.histDist profile initial prefixLength).support →
        (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          G.expectedHistoryValue (G.afterHistoryProfile profile base)
            base.2 (G.afterHistoryPotential charge base) time ≤
          error base) :
    ∑ time ∈ Finset.range (prefixLength + horizon),
        G.expectedHistoryValue profile initial charge time ≤
      (prefixLength : ℝ) * prefixBound +
        (horizon : ℝ) *
          expect (G.histDist profile initial prefixLength) error := by
  let prefixLaw := G.histDist profile initial prefixLength
  have hprefixSum :
      ∑ time ∈ Finset.range prefixLength,
          G.expectedHistoryValue profile initial charge time ≤
        (prefixLength : ℝ) * prefixBound := by
    calc
      ∑ time ∈ Finset.range prefixLength,
          G.expectedHistoryValue profile initial charge time ≤
          ∑ _time ∈ Finset.range prefixLength, prefixBound := by
            apply Finset.sum_le_sum
            intro time htime
            exact hprefix time (Finset.mem_range.mp htime)
      _ = (prefixLength : ℝ) * prefixBound := by simp
  have hsuffixNormalized :=
    G.normalized_suffix_charge_le_expect profile initial charge
      prefixLength horizon error hsuffix
  have hhorizonReal : (0 : ℝ) < horizon := by exact_mod_cast hhorizon
  have hsuffixSum :
      ∑ time ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial charge
            (prefixLength + time) ≤
        (horizon : ℝ) * expect prefixLaw error := by
    calc
      ∑ time ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial charge
            (prefixLength + time) =
          (horizon : ℝ) *
            ((horizon : ℝ)⁻¹ *
              ∑ time ∈ Finset.range horizon,
                G.expectedHistoryValue profile initial charge
                  (prefixLength + time)) := by
            field_simp
      _ ≤ (horizon : ℝ) * expect prefixLaw error :=
        mul_le_mul_of_nonneg_left hsuffixNormalized
          (le_of_lt hhorizonReal)
  rw [Finset.sum_range_add]
  exact add_le_add hprefixSum hsuffixSum

/-- With a nonnegative uniform suffix error, a fixed prefix costs at most its
length times the prefix bound divided by the full horizon.  This is the
explicit `O(prefixLength / totalHorizon)` splice loss. -/
theorem normalized_fixed_prefix_charge_le
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State)
    (charge : G.HistoryPotential) (prefixLength horizon : ℕ)
    (prefixBound error : ℝ) (hhorizon : 0 < horizon)
    (herror : 0 ≤ error)
    (hprefix : ∀ time, time < prefixLength →
      G.expectedHistoryValue profile initial charge time ≤ prefixBound)
    (hsuffix : ∀ base,
      base ∈ (G.histDist profile initial prefixLength).support →
        (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          G.expectedHistoryValue (G.afterHistoryProfile profile base)
            base.2 (G.afterHistoryPotential charge base) time ≤ error) :
    ((prefixLength + horizon : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range (prefixLength + horizon),
          G.expectedHistoryValue profile initial charge time ≤
      error +
        ((prefixLength + horizon : ℕ) : ℝ)⁻¹ *
          (prefixLength : ℝ) * prefixBound := by
  have hsum := G.fixed_prefix_charge_sum_le profile initial charge
    prefixLength horizon prefixBound (fun _ => error) hhorizon hprefix
    hsuffix
  have hsum' :
      ∑ time ∈ Finset.range (prefixLength + horizon),
          G.expectedHistoryValue profile initial charge time ≤
        (prefixLength : ℝ) * prefixBound +
          (horizon : ℝ) * error := by
    simpa using hsum
  let total : ℝ := prefixLength + horizon
  have htotal : 0 < total := by
    dsimp [total]
    positivity
  have hnormalize := mul_le_mul_of_nonneg_left hsum'
    (inv_nonneg.mpr (le_of_lt htotal))
  have hsuffixWeight :
      total⁻¹ * (horizon : ℝ) ≤ 1 := by
    calc
      total⁻¹ * (horizon : ℝ) ≤
          total⁻¹ * total := by
            apply mul_le_mul_of_nonneg_left
            · dsimp [total]
              exact le_add_of_nonneg_left (Nat.cast_nonneg prefixLength)
            · exact inv_nonneg.mpr (le_of_lt htotal)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt htotal)
  have hweightedError :
      total⁻¹ * ((horizon : ℝ) * error) ≤ error := by
    rw [← mul_assoc]
    simpa using mul_le_mul_of_nonneg_right hsuffixWeight herror
  rw [Nat.cast_add]
  change
    total⁻¹ *
        ∑ time ∈ Finset.range (prefixLength + horizon),
          G.expectedHistoryValue profile initial charge time ≤
      error + total⁻¹ * (prefixLength : ℝ) * prefixBound
  calc
    total⁻¹ *
        ∑ time ∈ Finset.range (prefixLength + horizon),
          G.expectedHistoryValue profile initial charge time ≤
        total⁻¹ *
          ((prefixLength : ℝ) * prefixBound +
            (horizon : ℝ) * error) := hnormalize
    _ =
        total⁻¹ * ((prefixLength : ℝ) * prefixBound) +
          total⁻¹ * ((horizon : ℝ) * error) := by ring
    _ ≤ total⁻¹ * ((prefixLength : ℝ) * prefixBound) + error :=
      add_le_add (le_refl _) hweightedError
    _ = error + total⁻¹ * (prefixLength : ℝ) * prefixBound := by
      ring

/-- Join a scalar prefix charge to a scalar suffix charge at a fixed
deterministic time. -/
def fixedPrefixScalarCharge (prefixLength : ℕ)
    (prefixCharge suffixCharge : ℕ → ℝ) : ℕ → ℝ :=
  fun time =>
    if time < prefixLength then
      prefixCharge time
    else
      suffixCharge (time - prefixLength)

/-- The charge of a deterministic prefix/suffix splice splits exactly into
the prefix sum and the rebased suffix sum. -/
theorem sum_fixedPrefixScalarCharge
    (prefixLength suffixLength : ℕ)
    (prefixCharge suffixCharge : ℕ → ℝ) :
    ∑ time ∈ Finset.range (prefixLength + suffixLength),
        fixedPrefixScalarCharge prefixLength prefixCharge suffixCharge time =
      (∑ time ∈ Finset.range prefixLength, prefixCharge time) +
        ∑ time ∈ Finset.range suffixLength, suffixCharge time := by
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro time htime
    simp only [Finset.mem_range] at htime
    simp [fixedPrefixScalarCharge, htime]
  · apply Finset.sum_congr rfl
    intro time _
    have hnot :
        ¬prefixLength + time < prefixLength :=
      not_lt_of_ge (Nat.le_add_right prefixLength time)
    simp [fixedPrefixScalarCharge, hnot]

/-- A fixed scalar prefix cost and a uniform suffix Cesàro budget combine
without losing more than the allocated prefix error.

The parent threshold only has to dominate the accounting horizon, while the
suffix length must already dominate the child's threshold. -/
theorem normalized_fixedPrefixScalarCharge_le
    (prefixLength suffixLength accountingHorizon : ℕ)
    (prefixCharge suffixCharge : ℕ → ℝ)
    (prefixError childError : ℝ)
    (hsuffixLength : 0 < suffixLength)
    (haccounting :
      accountingHorizon ≤ prefixLength + suffixLength)
    (hprefixError : 0 ≤ prefixError)
    (hchildError : 0 ≤ childError)
    (hprefix :
      ∑ time ∈ Finset.range prefixLength, prefixCharge time ≤
        (accountingHorizon : ℝ) * prefixError)
    (hsuffix :
      (suffixLength : ℝ)⁻¹ *
          ∑ time ∈ Finset.range suffixLength, suffixCharge time ≤
        childError) :
    ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range (prefixLength + suffixLength),
          fixedPrefixScalarCharge prefixLength
            prefixCharge suffixCharge time ≤
      prefixError + childError := by
  have hsuffixReal : (0 : ℝ) < suffixLength := by
    exact_mod_cast hsuffixLength
  have htotalNat : 0 < prefixLength + suffixLength :=
    Nat.zero_lt_of_lt (lt_of_lt_of_le hsuffixLength
      (Nat.le_add_left suffixLength prefixLength))
  have htotalReal :
      (0 : ℝ) < ((prefixLength + suffixLength : ℕ) : ℝ) := by
    exact_mod_cast htotalNat
  have haccountingReal :
      (accountingHorizon : ℝ) ≤
        ((prefixLength + suffixLength : ℕ) : ℝ) := by
    exact_mod_cast haccounting
  have hsuffixLeTotal :
      (suffixLength : ℝ) ≤
        ((prefixLength + suffixLength : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left suffixLength prefixLength
  have hprefixTotal :
      ∑ time ∈ Finset.range prefixLength, prefixCharge time ≤
        ((prefixLength + suffixLength : ℕ) : ℝ) * prefixError := by
    exact hprefix.trans
      (mul_le_mul_of_nonneg_right haccountingReal hprefixError)
  have hsuffixSum :
      ∑ time ∈ Finset.range suffixLength, suffixCharge time ≤
        (suffixLength : ℝ) * childError := by
    calc
      ∑ time ∈ Finset.range suffixLength, suffixCharge time =
          (suffixLength : ℝ) *
            ((suffixLength : ℝ)⁻¹ *
              ∑ time ∈ Finset.range suffixLength,
                suffixCharge time) := by
            field_simp
      _ ≤ (suffixLength : ℝ) * childError :=
        mul_le_mul_of_nonneg_left hsuffix hsuffixReal.le
  have hsuffixTotal :
      ∑ time ∈ Finset.range suffixLength, suffixCharge time ≤
        ((prefixLength + suffixLength : ℕ) : ℝ) * childError := by
    exact hsuffixSum.trans
      (mul_le_mul_of_nonneg_right hsuffixLeTotal hchildError)
  rw [sum_fixedPrefixScalarCharge]
  have hsum :
      (∑ time ∈ Finset.range prefixLength, prefixCharge time) +
          ∑ time ∈ Finset.range suffixLength, suffixCharge time ≤
        ((prefixLength + suffixLength : ℕ) : ℝ) *
          (prefixError + childError) := by
    calc
      (∑ time ∈ Finset.range prefixLength, prefixCharge time) +
          ∑ time ∈ Finset.range suffixLength, suffixCharge time ≤
          ((prefixLength + suffixLength : ℕ) : ℝ) * prefixError +
            ((prefixLength + suffixLength : ℕ) : ℝ) * childError :=
        add_le_add hprefixTotal hsuffixTotal
      _ = ((prefixLength + suffixLength : ℕ) : ℝ) *
          (prefixError + childError) := by ring
  calc
    ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ((∑ time ∈ Finset.range prefixLength, prefixCharge time) +
          ∑ time ∈ Finset.range suffixLength, suffixCharge time) ≤
      ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        (((prefixLength + suffixLength : ℕ) : ℝ) *
          (prefixError + childError)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr htotalReal.le)
    _ = prefixError + childError := by
      field_simp

end StochasticGame
end GameTheory
