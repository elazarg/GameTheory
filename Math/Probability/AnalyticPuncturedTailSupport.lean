/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticKernelRegeneration

/-!
# Tail-reachable support of analytic kernel coordinates

An analytic Bellman curve is a stochastic kernel only on its valid positive
parameter interval.  Its analytic extension need not be PMF-valued away
from that interval.  Accordingly, this file defines punctured support for
raw real coordinates, rather than assuming a globally PMF-valued analytic
kernel.

After the coordinate support stabilizes, the relevant state space need not
be the set reachable from the original game entry: a finite prefix may
already have moved the actual law elsewhere.  The correct fixed tail space
is the forward punctured-support closure of the support of the actual law at
the chosen tail start.

The main result says that an exact time-inhomogeneous `PMF.bind` recurrence
whose tail kernels use only stabilized coordinate edges has every later
marginal supported in this same fixed subtype.  No communicating-class,
stationary-law, charge, or game-theoretic claim is made.
-/

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S : Type*}

/-- A raw analytic coordinate is retained when it is not the zero right
germ.  Unlike `analyticPuncturedSupport`, this definition does not require
the analytic extension to be PMF-valued away from the valid interval. -/
def analyticPuncturedCoordinateSupport
    (coordinate : ℝ → S → S → ℝ)
    (source destination : S) : Prop :=
  ¬∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
    coordinate t source destination = 0

/-- The raw-coordinate definition specializes exactly to the existing
punctured support of a PMF-valued analytic kernel. -/
theorem analyticPuncturedCoordinateSupport_toReal_iff
    (kernel : ℝ → S → PMF S)
    (source destination : S) :
    analyticPuncturedCoordinateSupport
        (fun t state next =>
          (kernel t state next).toReal)
        source destination ↔
      analyticPuncturedSupport kernel source destination := by
  rfl

/-- Finite analytic coordinates which are eventually nonnegative have one
fixed strict-positive support on a sufficiently small punctured interval.
-/
theorem eventually_coordinate_pos_iff_puncturedSupport
    [Finite S]
    (coordinate : ℝ → S → S → ℝ)
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => coordinate t source destination) 0)
    (hnonneg :
      ∀ source destination,
        ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
          0 ≤ coordinate t source destination) :
    ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
      ∀ source destination,
        0 < coordinate t source destination ↔
          analyticPuncturedCoordinateSupport
            coordinate source destination := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  have coordinateAlternative :
      ∀ source destination,
        (∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
          coordinate t source destination = 0) ∨
        (∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
          0 < coordinate t source destination) := by
    intro source destination
    exact
      analyticAt_eventually_eq_zero_or_pos_of_eventually_nonneg
        (hanalytic source destination)
        (hnonneg source destination)
  apply Filter.eventually_all.mpr
  intro source
  apply Filter.eventually_all.mpr
  intro destination
  rcases coordinateAlternative source destination with hzero | hpos
  · have missing :
        ¬analyticPuncturedCoordinateSupport
          coordinate source destination := by
      exact fun edge => edge hzero
    filter_upwards [hzero] with t ht
    constructor
    · exact fun positive => (ne_of_gt positive ht).elim
    · exact fun edge => (missing edge).elim
  · have edge :
        analyticPuncturedCoordinateSupport
          coordinate source destination := by
      intro hzero
      obtain ⟨t, positive, zero⟩ := (hpos.and hzero).exists
      exact (ne_of_gt positive) zero
    filter_upwards [hpos] with t positive
    exact ⟨fun _ => edge, fun _ => positive⟩

/-- Forward punctured-coordinate reachability from the support of an actual
probability law.  It is a `Set`, so its definition does not install a
spurious global `Fintype` or decidability requirement. -/
def analyticPuncturedTailSupport
    (coordinate : ℝ → S → S → ℝ)
    (initialLaw : PMF S) : Set S :=
  {destination |
    ∃ source,
      initialLaw source ≠ 0 ∧
        Relation.ReflTransGen
          (analyticPuncturedCoordinateSupport coordinate)
          source destination}

theorem mem_analyticPuncturedTailSupport_iff
    (coordinate : ℝ → S → S → ℝ)
    (initialLaw : PMF S) (destination : S) :
    destination ∈
        analyticPuncturedTailSupport coordinate initialLaw ↔
      ∃ source,
        initialLaw source ≠ 0 ∧
          Relation.ReflTransGen
            (analyticPuncturedCoordinateSupport coordinate)
            source destination := by
  rfl

/-- The starting law is supported in its own punctured forward closure. -/
theorem mem_analyticPuncturedTailSupport_of_initial_ne_zero
    (coordinate : ℝ → S → S → ℝ)
    (initialLaw : PMF S) {source : S}
    (source_mem : initialLaw source ≠ 0) :
    source ∈ analyticPuncturedTailSupport coordinate initialLaw :=
  ⟨source, source_mem, Relation.ReflTransGen.refl⟩

/-- The punctured forward closure of a probability law is nonempty. -/
theorem analyticPuncturedTailSupport_nonempty
    [Finite S]
    (coordinate : ℝ → S → S → ℝ)
    (initialLaw : PMF S) :
    (analyticPuncturedTailSupport
      coordinate initialLaw).Nonempty := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  obtain ⟨source, source_mem⟩ := initialLaw.support_nonempty
  refine
    ⟨source,
      mem_analyticPuncturedTailSupport_of_initial_ne_zero
        coordinate initialLaw ?_⟩
  simpa only [PMF.mem_support_iff] using source_mem

/-- The tail support is closed under every punctured-coordinate edge. -/
theorem analyticPuncturedTailSupport_closed
    (coordinate : ℝ → S → S → ℝ)
    (initialLaw : PMF S)
    {source destination : S}
    (source_mem :
      source ∈ analyticPuncturedTailSupport coordinate initialLaw)
    (step :
      analyticPuncturedCoordinateSupport
        coordinate source destination) :
    destination ∈
      analyticPuncturedTailSupport coordinate initialLaw := by
  obtain ⟨entry, entry_mem, reachable⟩ := source_mem
  exact ⟨entry, entry_mem, reachable.tail step⟩

/-- The fixed subtype carrying the tail-reachable state space.  It is finite
whenever the ambient state space is finite. -/
abbrev AnalyticPuncturedTailState
    (coordinate : ℝ → S → S → ℝ)
    (initialLaw : PMF S) :=
  analyticPuncturedTailSupport coordinate initialLaw

/-- A calendar uses one raw analytic punctured support after `start` when
every positive-probability transition after that time is a retained raw
coordinate edge. -/
structure UsesAnalyticPuncturedSupportAfter
    (coordinate : ℝ → S → S → ℝ)
    (calendarKernel : ℕ → S → PMF S)
    (start : ℕ) : Prop where
  support_step :
    ∀ ⦃stage⦄, start ≤ stage →
      ∀ ⦃source destination⦄,
        PMFSupportStep (calendarKernel stage) source destination →
          analyticPuncturedCoordinateSupport
            coordinate source destination

/-- Exact recurrence plus tail support stabilization keeps every later law
inside the punctured forward closure of the actual law at `start`.

The `offset` formulation makes the finite prefix explicit: no assertion is
made about the laws before `start`. -/
theorem ne_zero_law_add_imp_mem_analyticPuncturedTailSupport
    [Finite S]
    (coordinate : ℝ → S → S → ℝ)
    (calendarKernel : ℕ → S → PMF S)
    (law : ℕ → PMF S)
    (start : ℕ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind (calendarKernel stage))
    (tail :
      UsesAnalyticPuncturedSupportAfter
        coordinate calendarKernel start) :
    ∀ offset state,
      law (start + offset) state ≠ 0 →
        state ∈
          analyticPuncturedTailSupport
            coordinate (law start) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  intro offset
  induction offset with
  | zero =>
      intro state state_mem
      exact
        mem_analyticPuncturedTailSupport_of_initial_ne_zero
          coordinate (law start) (by simpa using state_mem)
  | succ offset inductionHypothesis =>
      intro destination destination_mem
      have destination_support :
          destination ∈
            (law (start + Nat.succ offset)).support := by
        simpa only [PMF.mem_support_iff] using destination_mem
      rw [Nat.add_succ, law_step,
        PMF.mem_support_bind_iff] at destination_support
      obtain ⟨source, source_mem, step⟩ := destination_support
      apply
        analyticPuncturedTailSupport_closed
          coordinate (law start)
      · apply inductionHypothesis
        simpa only [PMF.mem_support_iff] using source_mem
      · exact tail.support_step (by omega) step

/-- Calendar-time form of the preceding theorem. -/
theorem ne_zero_law_imp_mem_analyticPuncturedTailSupport_of_start_le
    [Finite S]
    (coordinate : ℝ → S → S → ℝ)
    (calendarKernel : ℕ → S → PMF S)
    (law : ℕ → PMF S)
    (start : ℕ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind (calendarKernel stage))
    (tail :
      UsesAnalyticPuncturedSupportAfter
        coordinate calendarKernel start)
    {stage : ℕ} (start_le : start ≤ stage)
    {state : S} (state_mem : law stage state ≠ 0) :
    state ∈
      analyticPuncturedTailSupport
        coordinate (law start) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le start_le
  exact
    ne_zero_law_add_imp_mem_analyticPuncturedTailSupport
      coordinate calendarKernel law start
      law_step tail offset state state_mem

end Probability
end Math
