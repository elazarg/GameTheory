/-
# Tightness boundary controls for PMFs

The Dirac sequence on `Nat` loses all pointwise mass at each fixed atom. Its
mass therefore cannot converge pointwise along any subsequence to a PMF.
-/

import GameTheory.Math.Probability.Convergence
import GameTheory.Math.Probability.Compactness
import Mathlib.Probability.Distributions.Geometric

noncomputable section

namespace GameTheory.Tests.PMFTightness

open Filter GameTheory.Math.Probability

private theorem exists_nat_not_mem_finset (s : Finset ℕ) :
    ∃ n, n ∉ s := by
  classical
  by_cases hs : s.Nonempty
  · refine ⟨s.max' hs + 1, ?_⟩
    intro hmem
    have hle := s.le_max' (s.max' hs + 1) hmem
    omega
  · exact ⟨0, fun hmem => hs ⟨0, hmem⟩⟩

/-- The sequence of point masses escaping to larger natural numbers. -/
def diracNatSequence (n : ℕ) : PMF ℕ := PMF.pure n

/-- Every fixed atom's mass in the escaping Dirac sequence tends to zero. -/
theorem diracNat_mass_tendsto_zero (value : ℕ) :
    Tendsto (fun n => diracNatSequence n value) atTop (nhds 0) := by
  apply (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (nhds 0)).congr'
  filter_upwards [eventually_gt_atTop value] with n hn
  simp [diracNatSequence, PMF.pure_apply, Nat.ne_of_lt hn]

/-- The escaping Dirac sequence has no pointwise-convergent subsequence with a
PMF limit. -/
theorem diracNat_no_pointwise_convergent_subsequence
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq) (target : PMF ℕ)
    (hconverges : PMFConvergesPointwise
      (fun n => diracNatSequence (subseq n)) target) : False := by
  have hzero : ∀ value, target value = 0 := by
    intro value
    exact tendsto_nhds_unique (hconverges value)
      ((diracNat_mass_tendsto_zero value).comp hsubseq.tendsto_atTop)
  have htotal : (∑' value : ℕ, target value) = 0 :=
    ENNReal.tsum_eq_zero.mpr hzero
  have hmass := target.tsum_coe
  rw [htotal] at hmass
  norm_num at hmass

/-- Escaping point masses cannot capture almost all mass in one finite set. -/
theorem diracNat_not_uniformlyTight :
    ¬ UniformlyTight diracNatSequence := by
  intro htight
  obtain ⟨s, hs⟩ := htight (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_not_mem_finset s
  have hsum : ∑ a ∈ s, (diracNatSequence n a).toReal = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have han : a ≠ n := by
      intro heq
      subst a
      exact hn ha
    simp [diracNatSequence, PMF.pure_apply, han]
  have := hs n
  rw [hsum] at this
  norm_num at this

/-- Each coordinate uses an infinite-support law on the uncountable real
carrier, shifted by its coordinate index. -/
def halfParameter : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by constructor <;> norm_num⟩

def halfGeometric : PMF ℕ :=
  (ProbabilityTheory.geometricMeasure halfParameter).toPMF

theorem halfGeometric_support : halfGeometric.support = Set.univ := by
  have hp0 : halfParameter ≠ 0 := by
    intro h
    have hh := congrArg Subtype.val h
    norm_num [halfParameter] at hh
  have hp1 : halfParameter ≠ 1 := by
    intro h
    have hh := congrArg Subtype.val h
    norm_num [halfParameter] at hh
  ext n
  simp only [PMF.mem_support_iff, Set.mem_univ, iff_true]
  rw [halfGeometric, MeasureTheory.Measure.toPMF_apply,
    ProbabilityTheory.geometricMeasure_singleton hp0]
  exact (ENNReal.ofReal_pos.mpr
    (ProbabilityTheory.geometricMeasure_pos hp0 hp1 n)).ne'

def realGeometric (i : ℕ) : PMF ℝ :=
  PMF.map (fun n : ℕ => (n : ℝ) + i)
    halfGeometric

theorem realGeometric_support_infinite (i : ℕ) :
    (realGeometric i).support.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℝ) + i) := by
    intro a b hab
    exact Nat.cast_injective (add_right_cancel hab)
  have hsupport : (realGeometric i).support =
      Set.range (fun n : ℕ => (n : ℝ) + i) := by
    simp [realGeometric, PMF.support_map, halfGeometric_support]
  rw [hsupport]
  exact Set.infinite_range_of_injective hinj

/-- A countable family of coordinatewise oscillating infinite-support laws on `ℝ` has one
common pointwise-convergent PMF subsequence, with no countability assumption
on the ambient outcome carrier. -/
theorem alternating_realGeometric_common_subsequence :
    ∃ (target : ℕ → PMF ℝ) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        ∀ i, PMFConvergesPointwise
          (fun n => if Nat.testBit (subseq n) i = true then realGeometric i
            else realGeometric (i + 1)) (target i) := by
  classical
  exact exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight
    (fun n i => if Nat.testBit n i = true then realGeometric i
      else realGeometric (i + 1))
    (fun i => (uniformlyTight_const (realGeometric i)).ite
      (uniformlyTight_const (realGeometric (i + 1)))
      (fun n => Nat.testBit n i = true))

end GameTheory.Tests.PMFTightness
