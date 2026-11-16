module

/-
# Small lotteries and a possibility preference

A geometric law on the naturals with infinite support, a fair coin, and a
preference on Boolean lotteries that compares only whether `true` is possible.
The preference inspects supports directly, so it has no expected-utility
representation; the geometric law separates binary from countable mixtures.
-/

public import GameTheory.Core.Utility
public import GameTheory.Math.Probability.Mixture
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

namespace GameTheory.Examples.Lotteries

open GameTheory.Math.Probability
open scoped ENNReal

/-- Probability `2^-(n+1)` at `n`. -/
def halving : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal ((1 : ℝ) / 2 / 2 ^ n), by
    have hsum : HasSum (fun n : ℕ => (1 : ℝ) / 2 / 2 ^ n) 1 := by
      simpa only [one_div] using hasSum_geometric_two' (1 : ℝ)
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable,
      hsum.tsum_eq, ENNReal.ofReal_one]⟩

/-- Only the possibility of outcome `true` matters. This preference compares
support membership directly and contains no utility or expectation operation. -/
def supportPreference : WeakPreference Unit Bool :=
  fun _ preferred alternative => true ∈ preferred.support ∨ true ∉ alternative.support

/-- A fair lottery still makes `true` possible. -/
def supportFairLaw : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)

theorem true_mem_supportFairLaw : true ∈ supportFairLaw.support :=
  mem_support_mix_left (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by simp)

end GameTheory.Examples.Lotteries
