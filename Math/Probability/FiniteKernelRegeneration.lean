/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.PMFIter
import Math.Probability.ReachableClosedClass

/-!
# Bounded-step regeneration for finite kernels

If a fixed target is support-reachable from every state of a finite Markov
kernel, choose one witness length for every source.  Finiteness gives a
uniform bound on those lengths and a strictly positive lower bound on the
corresponding finite-step transition masses.

The witness time may depend on the source.  A common exact time requires an
additional aperiodicity or holding assumption; support communication alone
does not provide it.  This file concerns one fixed kernel and makes no
claim about a power-law lower bound for a parameterized family.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S : Type*}

/-- Support reachability is equivalent to positive mass at some finite
kernel iterate in the direction needed here. -/
theorem exists_iter_support_of_pmfReachable
    (kernel : S → PMF S) {source target : S}
    (hreach : PMFReachable kernel source target) :
    ∃ steps,
      Math.PMFIter.iter kernel steps source target ≠ 0 := by
  induction hreach with
  | refl =>
      refine ⟨0, ?_⟩
      simp [Math.PMFIter.iter_zero]
  | @tail middle target hprefix hstep ih =>
      obtain ⟨steps, hsteps⟩ := ih
      refine ⟨steps + 1, ?_⟩
      rw [Math.PMFIter.iter_succ']
      change
        target ∈
          ((Math.PMFIter.iter
            kernel steps source).bind kernel).support
      rw [PMF.mem_support_bind_iff]
      exact ⟨middle, hsteps, hstep⟩

/-- Uniform bounded-step minorization at one fixed target.  For every
source, `stepCount source` is at most `horizon`, and the corresponding
iterate assigns at least `minorization` mass to `target`. -/
structure FiniteKernelRegeneration
    [Fintype S]
    (kernel : S → PMF S) (target : S) where
  horizon : ℕ
  stepCount : S → ℕ
  stepCount_le_horizon : ∀ source, stepCount source ≤ horizon
  minorization : ℝ
  minorization_pos : 0 < minorization
  target_mass_ge :
    ∀ source,
      minorization ≤
        (Math.PMFIter.iter
          kernel (stepCount source) source target).toReal

namespace FiniteKernelRegeneration

variable [Fintype S] {kernel : S → PMF S} {target : S}

/-- Each source has a witness time within the common horizon at which the
target mass is bounded below by the common minorization constant. -/
theorem exists_step_le_horizon
    (R : FiniteKernelRegeneration kernel target)
    (source : S) :
    ∃ steps ≤ R.horizon,
      R.minorization ≤
        (Math.PMFIter.iter kernel steps source target).toReal :=
  ⟨R.stepCount source, R.stepCount_le_horizon source,
    R.target_mass_ge source⟩

/-- In particular, every selected bounded-step target mass is positive. -/
theorem target_mass_pos
    (R : FiniteKernelRegeneration kernel target)
    (source : S) :
    0 <
      (Math.PMFIter.iter
        kernel (R.stepCount source) source target).toReal :=
  R.minorization_pos.trans_le (R.target_mass_ge source)

end FiniteKernelRegeneration

/-- Finite support reachability from every source produces a bounded-step
regeneration package with a strictly positive fixed-kernel constant. -/
theorem exists_finiteKernelRegeneration
    [Fintype S]
    (kernel : S → PMF S) (target : S)
    (hreach : ∀ source, PMFReachable kernel source target) :
    Nonempty (FiniteKernelRegeneration kernel target) := by
  classical
  have hexists :
      ∀ source,
        ∃ steps,
          Math.PMFIter.iter
            kernel steps source target ≠ 0 :=
    fun source =>
      exists_iter_support_of_pmfReachable
        kernel (hreach source)
  let stepCount : S → ℕ :=
    fun source => Nat.find (hexists source)
  have hstepSupport :
      ∀ source,
        Math.PMFIter.iter
          kernel (stepCount source) source target ≠ 0 :=
    fun source => Nat.find_spec (hexists source)
  let mass : S → ℝ :=
    fun source =>
      (Math.PMFIter.iter
        kernel (stepCount source) source target).toReal
  have hmassPos : ∀ source, 0 < mass source := by
    intro source
    exact ENNReal.toReal_pos (hstepSupport source)
      (PMF.apply_ne_top
        (Math.PMFIter.iter
          kernel (stepCount source) source) target)
  let masses : Finset ℝ :=
    Finset.univ.image mass
  have hmassesNonempty : masses.Nonempty := by
    exact
      ⟨mass target,
        Finset.mem_image.mpr
          ⟨target, Finset.mem_univ target, rfl⟩⟩
  let minorization : ℝ :=
    masses.min' hmassesNonempty
  have hminorizationPos : 0 < minorization := by
    have hmember :
        minorization ∈ masses :=
      Finset.min'_mem masses hmassesNonempty
    obtain ⟨source, -, hsource⟩ :=
      Finset.mem_image.mp hmember
    rw [← hsource]
    exact hmassPos source
  let horizon : ℕ :=
    ∑ source, stepCount source
  have hstepLe :
      ∀ source, stepCount source ≤ horizon := by
    intro source
    exact Finset.single_le_sum
      (fun other _ => Nat.zero_le (stepCount other))
      (Finset.mem_univ source)
  have hminorizationLe :
      ∀ source, minorization ≤ mass source := by
    intro source
    apply Finset.min'_le masses
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_univ source, rfl⟩
  exact ⟨{
    horizon := horizon
    stepCount := stepCount
    stepCount_le_horizon := hstepLe
    minorization := minorization
    minorization_pos := hminorizationPos
    target_mass_ge := hminorizationLe
  }⟩

/-- Make a target absorbing. Iteration of this kernel records whether the
original chain has hit the target by the given horizon. -/
noncomputable def stoppedAt
    (kernel : S → PMF S) (target : S) : S → PMF S := by
  classical
  exact fun state =>
    if state = target then PMF.pure target else kernel state

@[simp]
theorem stoppedAt_target
    (kernel : S → PMF S) (target : S) :
    stoppedAt kernel target target = PMF.pure target := by
  classical
  simp [stoppedAt]

/-- A support path to the target remains available after making the target
absorbing. -/
theorem pmfReachable_stoppedAt
    (kernel : S → PMF S) {source target : S}
    (hreach : PMFReachable kernel source target) :
    PMFReachable (stoppedAt kernel target) source target := by
  classical
  induction hreach using
      Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head source middle hstep _ ih =>
      by_cases hsource : source = target
      · subst source
        exact Relation.ReflTransGen.refl
      · apply ih.head
        simpa [PMFSupportStep, stoppedAt, hsource] using hstep

/-- Once the target is absorbing, its transition mass is nondecreasing with
the iteration horizon. -/
theorem iter_stoppedAt_target_toReal_le_add
    [Finite S]
    (kernel : S → PMF S) (target source : S)
    (steps extra : ℕ) :
    (Math.PMFIter.iter
        (stoppedAt kernel target) steps source target).toReal ≤
      (Math.PMFIter.iter
        (stoppedAt kernel target)
        (steps + extra) source target).toReal := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  rw [Math.PMFIter.iter_add,
    Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
  have hterm :
      (Math.PMFIter.iter
          (stoppedAt kernel target) steps source target).toReal *
          (Math.PMFIter.iter
            (stoppedAt kernel target) extra target target).toReal ≤
        ∑ state,
          (Math.PMFIter.iter
              (stoppedAt kernel target) steps source state).toReal *
            (Math.PMFIter.iter
              (stoppedAt kernel target) extra state target).toReal :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset S))
      (f := fun state =>
        (Math.PMFIter.iter
            (stoppedAt kernel target) steps source state).toReal *
          (Math.PMFIter.iter
            (stoppedAt kernel target) extra state target).toReal)
      (fun state _ =>
        mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (Finset.mem_univ target)
  simpa [Math.PMFIter.iter_of_terminal
    (stoppedAt_target kernel target)] using hterm

/-- A true fixed-horizon hitting minorization, expressed through the kernel
stopped at the target. -/
structure FiniteHittingMinorization
    [Fintype S]
    (kernel : S → PMF S) (target : S) where
  horizon : ℕ
  minorization : ℝ
  minorization_pos : 0 < minorization
  target_mass_ge :
    ∀ source,
      minorization ≤
        (Math.PMFIter.iter
          (stoppedAt kernel target)
          horizon source target).toReal

/-- Finite support reachability produces a common finite horizon and a
strictly positive lower bound on the probability of hitting the target by
that horizon. -/
theorem exists_finiteHittingMinorization
    [Fintype S]
    (kernel : S → PMF S) (target : S)
    (hreach : ∀ source, PMFReachable kernel source target) :
    Nonempty (FiniteHittingMinorization kernel target) := by
  classical
  obtain ⟨regeneration⟩ :=
    exists_finiteKernelRegeneration
      (stoppedAt kernel target) target
      (fun source =>
        pmfReachable_stoppedAt kernel (hreach source))
  refine ⟨{
    horizon := regeneration.horizon
    minorization := regeneration.minorization
    minorization_pos := regeneration.minorization_pos
    target_mass_ge := ?_
  }⟩
  intro source
  have hstep :=
    regeneration.target_mass_ge source
  have hmono :=
    iter_stoppedAt_target_toReal_le_add
      kernel target source
      (regeneration.stepCount source)
      (regeneration.horizon -
        regeneration.stepCount source)
  rw [Nat.add_sub_of_le
    (regeneration.stepCount_le_horizon source)] at hmono
  exact hstep.trans hmono

end Probability
end Math
