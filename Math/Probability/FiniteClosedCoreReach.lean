/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.FiniteKernelRegeneration
import Math.Probability.HittingTimePotential

/-!
# Finite closed-core reachability and transient occupation

For a finite Markov kernel, suppose a set `core` is support-closed and every
state has a positive-probability support path to some (source-dependent)
state of `core`.  Finiteness upgrades those paths to one common horizon and
one positive lower bound on the probability of having entered `core`.

The hitting-time potential API then gives an exact Poisson equation for the
off-core indicator.  Consequently total expected off-core occupation is
uniformly bounded, and the indicator has zero harmonic component in every
mean-ergodic Poisson decomposition.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Math.ProbabilityMassFunction

variable {S : Type*}

/-- Closedness makes one-step off-core probability no larger than the
off-core indicator at the source. -/
theorem expect_transientCharge_kernel_le
    [Finite S]
    {kernel : S → PMF S} {core : Set S}
    (hclosed : IsClosedCore kernel core) (source : S) :
    expect (kernel source) (transientCharge core) ≤
      transientCharge core source := by
  by_cases hsource : source ∈ core
  · rw [transientCharge_of_mem hsource]
    exact le_of_eq
      (expect_eq_zero_of_mem_coreVanishing hclosed
        (transientCharge_mem_coreVanishing core) hsource)
  · rw [transientCharge_of_not_mem hsource]
    simpa using
      expect_mono (kernel source) (transientCharge core)
        (fun _ => 1) (transientCharge_le_one core)

/-- The probability of remaining outside a closed core is nonincreasing in
the iteration horizon. -/
theorem expect_iter_succ_transientCharge_le
    [Finite S]
    {kernel : S → PMF S} {core : Set S}
    (hclosed : IsClosedCore kernel core)
    (steps : ℕ) (source : S) :
    expect (Math.PMFIter.iter kernel (steps + 1) source)
        (transientCharge core) ≤
      expect (Math.PMFIter.iter kernel steps source)
        (transientCharge core) := by
  rw [Math.PMFIter.iter_succ', expect_bind]
  exact expect_mono
    (Math.PMFIter.iter kernel steps source)
    (fun state => expect (kernel state) (transientCharge core))
    (transientCharge core)
    (expect_transientCharge_kernel_le hclosed)

/-- Padding an iteration can only lower off-core probability. -/
theorem expect_iter_add_transientCharge_le
    [Finite S]
    {kernel : S → PMF S} {core : Set S}
    (hclosed : IsClosedCore kernel core)
    (steps extra : ℕ) (source : S) :
    expect (Math.PMFIter.iter kernel (steps + extra) source)
        (transientCharge core) ≤
      expect (Math.PMFIter.iter kernel steps source)
        (transientCharge core) := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ]
      exact
        (expect_iter_succ_transientCharge_le
          hclosed (steps + extra) source).trans ih

/-- A point mass already lying in the core lowers off-core probability by
at least that coordinate. -/
theorem expect_transientCharge_le_one_sub_apply_toReal
    [Finite S]
    (distribution : PMF S) {core : Set S} {target : S}
    (htarget : target ∈ core) :
    expect distribution (transientCharge core) ≤
      1 - (distribution target).toReal := by
  letI : Fintype S := Fintype.ofFinite S
  have hcomplement_nonneg : ∀ state,
      0 ≤ 1 - transientCharge core state := by
    intro state
    linarith [transientCharge_le_one core state]
  have hcoreMass_ge :
      (distribution target).toReal ≤
        expect distribution
          (fun state => 1 - transientCharge core state) := by
    rw [expect_eq_sum]
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset S))
      (f := fun state =>
        (distribution state).toReal *
          (1 - transientCharge core state))
      (fun state _ =>
        mul_nonneg ENNReal.toReal_nonneg
          (hcomplement_nonneg state))
      (Finset.mem_univ target)
    simpa [transientCharge_of_mem htarget] using hsingle
  have hsplit :
      expect distribution (transientCharge core) +
          expect distribution
            (fun state => 1 - transientCharge core state) = 1 := by
    rw [← expect_add]
    simp
  linarith

/-- Support reachability of a closed core compiles to one common positive
finite-horizon entry margin.  The reached core state may depend on the
source. -/
theorem exists_uniformCoreReach_of_closed_of_reachable
    [Finite S] [Nonempty S]
    (kernel : S → PMF S) (core : Set S)
    (hclosed : IsClosedCore kernel core)
    (hreachable : ∀ source,
      ∃ target, target ∈ core ∧
        PMFReachable kernel source target) :
    ∃ (horizon : ℕ) (minorization : ℝ),
      0 < minorization ∧ minorization ≤ 1 ∧
        HasUniformCoreReach kernel core horizon minorization := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  have hexists : ∀ source,
      ∃ (target : S) (steps : ℕ),
        target ∈ core ∧
          Math.PMFIter.iter kernel steps source target ≠ 0 := by
    intro source
    obtain ⟨target, htarget, hpath⟩ := hreachable source
    obtain ⟨steps, hsteps⟩ :=
      exists_iter_support_of_pmfReachable kernel hpath
    exact ⟨target, steps, htarget, hsteps⟩
  choose targetOf stepsOf htargetOf hmassOf using hexists
  let mass : S → ℝ := fun source =>
    (Math.PMFIter.iter kernel (stepsOf source)
      source (targetOf source)).toReal
  have hmass_pos : ∀ source, 0 < mass source := by
    intro source
    exact ENNReal.toReal_pos (hmassOf source)
      (PMF.apply_ne_top
        (Math.PMFIter.iter kernel (stepsOf source) source)
        (targetOf source))
  let masses : Finset ℝ := Finset.univ.image mass
  have hmasses_nonempty : masses.Nonempty := by
    let source : S := Classical.choice inferInstance
    exact ⟨mass source,
      Finset.mem_image.mpr
        ⟨source, Finset.mem_univ source, rfl⟩⟩
  let minorization : ℝ := masses.min' hmasses_nonempty
  have hminorization_pos : 0 < minorization := by
    have hmember : minorization ∈ masses :=
      Finset.min'_mem masses hmasses_nonempty
    obtain ⟨source, -, hsource⟩ := Finset.mem_image.mp hmember
    rw [← hsource]
    exact hmass_pos source
  have hminorization_le : ∀ source,
      minorization ≤ mass source := by
    intro source
    apply Finset.min'_le masses
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_univ source, rfl⟩
  have hmass_le_one : ∀ source, mass source ≤ 1 := by
    intro source
    have hle := PMF.coe_le_one
      (Math.PMFIter.iter kernel (stepsOf source) source)
      (targetOf source)
    exact
      ((ENNReal.toReal_le_toReal
        (PMF.apply_ne_top _ _) (by norm_num)).mpr hle).trans_eq
        (by simp)
  have hminorization_le_one : minorization ≤ 1 :=
    (hminorization_le (Classical.choice inferInstance)).trans
      (hmass_le_one (Classical.choice inferInstance))
  let horizon : ℕ := ∑ source, stepsOf source
  have hsteps_le : ∀ source, stepsOf source ≤ horizon := by
    intro source
    exact Finset.single_le_sum
      (fun other _ => Nat.zero_le (stepsOf other))
      (Finset.mem_univ source)
  refine ⟨horizon, minorization, hminorization_pos,
    hminorization_le_one, ?_⟩
  intro source
  have hselected :
      expect
          (Math.PMFIter.iter kernel (stepsOf source) source)
          (transientCharge core) ≤
        1 - mass source := by
    exact expect_transientCharge_le_one_sub_apply_toReal
      (Math.PMFIter.iter kernel (stepsOf source) source)
      (htargetOf source)
  have hpad := expect_iter_add_transientCharge_le
    hclosed (stepsOf source) (horizon - stepsOf source) source
  rw [Nat.add_sub_of_le (hsteps_le source)] at hpad
  exact hpad.trans (hselected.trans (sub_le_sub_left
    (hminorization_le source) 1))

/-- A closed-core transience package: uniform entry, an exact nonnegative
hitting-time potential, and its quantitative norm bound. -/
structure ClosedCoreTransienceCertificate
    [Fintype S]
    (kernel : S → PMF S) (core : Set S) where
  horizon : ℕ
  minorization : ℝ
  minorization_pos : 0 < minorization
  minorization_le_one : minorization ≤ 1
  uniform_reach :
    HasUniformCoreReach kernel core horizon minorization
  potential : S → ℝ
  potential_nonneg : ∀ state, 0 ≤ potential state
  potential_eq_zero_on_core :
    ∀ {state}, state ∈ core → potential state = 0
  poisson : ∀ state,
    potential state - expect (kernel state) potential =
      transientCharge core state
  potential_norm_le :
    ‖potential‖ ≤ (horizon : ℝ) / minorization

/-- Compile closed support reachability into the full quantitative
transience certificate. -/
theorem exists_closedCoreTransienceCertificate
    [Fintype S] [Nonempty S]
    (kernel : S → PMF S) (core : Set S)
    (hclosed : IsClosedCore kernel core)
    (hreachable : ∀ source,
      ∃ target, target ∈ core ∧
        PMFReachable kernel source target) :
    Nonempty (ClosedCoreTransienceCertificate kernel core) := by
  obtain ⟨horizon, minorization, hpos, hone, hreach⟩ :=
    exists_uniformCoreReach_of_closed_of_reachable
      kernel core hclosed hreachable
  obtain ⟨potential, hnonneg, hzero, hpoisson, hnorm⟩ :=
    exists_nonnegative_poissonPotential_of_uniformCoreReach
      hclosed hpos hone hreach
  exact ⟨{
    horizon := horizon
    minorization := minorization
    minorization_pos := hpos
    minorization_le_one := hone
    uniform_reach := hreach
    potential := potential
    potential_nonneg := hnonneg
    potential_eq_zero_on_core := fun {_} hstate => hzero hstate
    poisson := hpoisson
    potential_norm_le := hnorm
  }⟩

namespace ClosedCoreTransienceCertificate

variable [Fintype S]
  {kernel : S → PMF S} {core : Set S}

/-- The expected total number of off-core visits through any finite horizon
is bounded uniformly in the initial state and horizon. -/
theorem total_transientOccupation_le
    (certificate : ClosedCoreTransienceCertificate kernel core)
    (steps : ℕ) (source : S) :
    (∑ time ∈ Finset.range steps,
      expect (Math.PMFIter.iter kernel time source)
        (transientCharge core)) ≤
      (certificate.horizon : ℝ) / certificate.minorization := by
  have hdecomp := poissonPotential_eq_sum_expect_add_expect_iter
    certificate.poisson steps source
  have htail_nonneg :
      0 ≤ expect (Math.PMFIter.iter kernel steps source)
        certificate.potential := by
    simpa using expect_mono
      (Math.PMFIter.iter kernel steps source)
      (fun _ => 0) certificate.potential
      certificate.potential_nonneg
  have hsum_le_potential :
      (∑ time ∈ Finset.range steps,
        expect (Math.PMFIter.iter kernel time source)
          (transientCharge core)) ≤
        certificate.potential source := by
    linarith
  have hpoint_le_norm :
      certificate.potential source ≤ ‖certificate.potential‖ := by
    calc
      certificate.potential source ≤
          |certificate.potential source| := le_abs_self _
      _ ≤ ‖certificate.potential‖ := by
        simpa [Real.norm_eq_abs] using
          norm_le_pi_norm certificate.potential source
  exact hsum_le_potential.trans
    (hpoint_le_norm.trans certificate.potential_norm_le)

/-- The off-core indicator has zero harmonic component in any
harmonic-plus-Poisson decomposition. -/
theorem harmonicComponent_transientCharge_eq_zero
    (certificate : ClosedCoreTransienceCertificate kernel core)
    (harmonic poissonPotential : S → ℝ)
    (hharmonic : ∀ state,
      expect (kernel state) harmonic = harmonic state)
    (hdecomp : ∀ state,
      transientCharge core state = harmonic state +
        (expect (kernel state) poissonPotential -
          poissonPotential state)) :
    harmonic = 0 := by
  apply Math.MeanErgodic.harmonic_eq_of_add_poisson_eq
    kernel (transientCharge core)
      harmonic poissonPotential 0 (-certificate.potential)
      hharmonic hdecomp
  · intro state
    change expect (kernel state) (fun _ => (0 : ℝ)) = 0
    exact expect_const (kernel state) (0 : ℝ)
  · intro state
    have hneg :
        expect (kernel state) (-certificate.potential) =
          -(expect (kernel state) certificate.potential) := by
      change
        expect (kernel state)
            (fun next => -certificate.potential next) = _
      simpa using
        expect_const_mul (kernel state) (-1 : ℝ)
          certificate.potential
    simp only [Pi.zero_apply, zero_add, Pi.neg_apply, hneg]
    linarith [certificate.poisson state]

end ClosedCoreTransienceCertificate

end Probability
end Math
