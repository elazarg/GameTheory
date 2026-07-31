/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AlgebraicSelection
import Math.Probability.FiniteKernelRegeneration

/-!
# Power-law regeneration for analytic finite kernels

A frozen directed support graph with a path from every state to one target
gives a finite family of selected paths.  If the transition coordinates are
analytic, eventually lie in `[0, 1]`, and are eventually positive on every
selected support edge, the product of all selected path weights is a positive
analytic germ.  It therefore has a lower bound `c * t ^ K`.  Since all path
weights are at most one, the same lower bound applies to every selected path.

The first half of this file is deliberately about raw real coordinates.  The
second half is the semantic bridge: when those coordinates are exactly the
point masses of a kernel stopped at the target, a selected path weight is
bounded by the target mass of the corresponding kernel iterate.  Padding with
the absorbing target turns the source-dependent path lengths into one common
hit-by-`H` horizon.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Finset BigOperators Set

variable {S : Type*}

/-- A finite path whose edges lie in a fixed support relation.  This lives in
`Type`, rather than `Prop`, because its length and coordinate product are data
used by the quantitative theorem below. -/
inductive FrozenSupportPath
    (edge : S → S → Prop) : S → S → Type _
  | refl (state : S) : FrozenSupportPath edge state state
  | tail (source middle target : S) :
      FrozenSupportPath edge source middle →
      edge middle target →
      FrozenSupportPath edge source target

namespace FrozenSupportPath

/-- Number of edges in a frozen support path. -/
def length {edge : S → S → Prop} {source target : S} :
    FrozenSupportPath edge source target → ℕ
  | .refl _ => 0
  | .tail _ _ _ initial _ => initial.length + 1

/-- Product of the real transition coordinates along a frozen path. -/
def weight {edge : S → S → Prop} {source target : S}
    (coordinate : ℝ → S → S → ℝ) :
    FrozenSupportPath edge source target → ℝ → ℝ
  | .refl _ => fun _ => 1
  | .tail _ middle target initial _ =>
      fun t => initial.weight coordinate t * coordinate t middle target

/-- Ordinary reflexive-transitive reachability contains a data-bearing
frozen support path. -/
theorem nonempty_of_reflTransGen
    {edge : S → S → Prop} {source target : S}
    (hreach : Relation.ReflTransGen edge source target) :
    Nonempty (FrozenSupportPath edge source target) := by
  induction hreach with
  | refl => exact ⟨.refl _⟩
  | @tail middle target _ hedge ih =>
      exact
        ⟨.tail source middle target
          (Classical.choice ih) hedge⟩

/-- Analytic transition coordinates have analytic finite path products. -/
theorem analyticAt_weight
    {edge : S → S → Prop} {source target : S}
    (coordinate : ℝ → S → S → ℝ)
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => coordinate t source destination) 0)
    (path : FrozenSupportPath edge source target) :
    AnalyticAt ℝ (path.weight coordinate) 0 := by
  induction path with
  | refl =>
      simpa [weight] using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) 0)
  | tail middle target initial hedge ih =>
      change
        AnalyticAt ℝ
          (initial.weight coordinate *
            fun t => coordinate t middle target) 0
      exact ih.mul (hanalytic middle target)

/-- Eventual strict positivity on the frozen edges gives strict positivity
of every selected path product. -/
theorem eventually_weight_pos
    {edge : S → S → Prop} {source target : S}
    (coordinate : ℝ → S → S → ℝ)
    (hedge :
      ∀ {source destination},
        edge source destination →
          ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
            0 < coordinate t source destination)
    (path : FrozenSupportPath edge source target) :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      0 < path.weight coordinate t := by
  induction path with
  | refl => simp [weight]
  | tail middle target initial hedge_initial ih =>
      filter_upwards [ih, hedge hedge_initial] with t hinitial hstep
      simpa [weight] using mul_pos hinitial hstep

/-- If all raw transition coordinates eventually lie in `[0, 1]`, so does
every finite path product. -/
theorem eventually_weight_mem_Icc
    {edge : S → S → Prop} {source target : S}
    (coordinate : ℝ → S → S → ℝ)
    (hunit :
      ∀ source destination,
        ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
          coordinate t source destination ∈ Set.Icc 0 1)
    (path : FrozenSupportPath edge source target) :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      path.weight coordinate t ∈ Set.Icc 0 1 := by
  induction path with
  | refl => simp [weight]
  | tail middle target initial hedge ih =>
      filter_upwards [ih, hunit middle target] with t hinitial hstep
      constructor
      · exact mul_nonneg hinitial.1 hstep.1
      · exact mul_le_one₀ hinitial.2 hstep.1 hstep.2

/-- Freeze the parameter of a path-coordinate family. -/
theorem weight_freeze
    {edge : S → S → Prop} {source target : S}
    (coordinate : ℝ → S → S → ℝ)
    (path : FrozenSupportPath edge source target)
    (t u : ℝ) :
    path.weight coordinate t =
      path.weight
        (fun _ state destination =>
          coordinate t state destination) u := by
  induction path with
  | refl => simp [weight]
  | tail middle target initial hedge ih =>
      simp only [weight]
      rw [ih]

end FrozenSupportPath

/-- The punctured support of an analytic kernel coordinate family.  An edge
is retained precisely when its coordinate is not the zero right germ. -/
def analyticPuncturedSupport
    (kernel : ℝ → S → PMF S) (source destination : S) : Prop :=
  ¬∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
    (kernel t source destination).toReal = 0

/-- A finite analytic stochastic kernel has one fixed support graph on a
sufficiently small punctured interval. -/
theorem eventually_kernel_support_iff_analyticPuncturedSupport
    [Finite S]
    (kernel : ℝ → S → PMF S)
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => (kernel t source destination).toReal) 0) :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ source destination,
      0 < (kernel t source destination).toReal ↔
        analyticPuncturedSupport kernel source destination := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  have coordinateAlternative :
      ∀ source destination,
        (∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
          (kernel t source destination).toReal = 0) ∨
        (∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
          0 < (kernel t source destination).toReal) := by
    intro source destination
    apply analyticAt_eventually_eq_zero_or_pos_of_eventually_nonneg
      (hanalytic source destination)
    exact Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  apply Filter.eventually_all.mpr
  intro source
  apply Filter.eventually_all.mpr
  intro destination
  rcases coordinateAlternative source destination with hzero | hpos
  · have hedge :
        ¬analyticPuncturedSupport kernel source destination := by
      intro edge
      exact edge hzero
    filter_upwards [hzero] with t ht
    constructor
    · intro hpositive
      exact False.elim ((ne_of_gt hpositive) ht)
    · intro edge
      exact False.elim (hedge edge)
  · have hedge :
        analyticPuncturedSupport kernel source destination := by
      intro hzero
      obtain ⟨t, hpositive, htzero⟩ := (hpos.and hzero).exists
      exact (ne_of_gt hpositive) htzero
    filter_upwards [hpos] with t hpositive
    exact ⟨fun _ => hedge, fun _ => hpositive⟩

/-- An edge outside the punctured support is eventually exactly absent. -/
theorem eventually_kernel_coordinate_eq_zero_of_not_puncturedSupport
    (kernel : ℝ → S → PMF S)
    {source destination : S}
    (missing :
      ¬analyticPuncturedSupport kernel source destination) :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      (kernel t source destination).toReal = 0 := by
  simpa only [analyticPuncturedSupport, not_not] using missing

/-- Quantitative data extracted from a frozen support graph and analytic raw
transition coordinates. -/
structure AnalyticPathMinorization
    [Fintype S]
    (edge : S → S → Prop)
    (coordinate : ℝ → S → S → ℝ)
    (target : S) where
  horizon : ℕ
  exponent : ℕ
  constant : ℝ
  constant_pos : 0 < constant
  path : ∀ source, FrozenSupportPath edge source target
  path_length_le : ∀ source, (path source).length ≤ horizon
  eventually_path_weight_ge :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ source,
      constant * t ^ exponent ≤
        (path source).weight coordinate t

/-- Frozen reachability and eventual positivity of analytic transition
coordinates produce one power-law minorization for selected paths from every
source.  This theorem uses only raw real coordinates. -/
theorem exists_analyticPathMinorization
    [Fintype S]
    (edge : S → S → Prop)
    (coordinate : ℝ → S → S → ℝ)
    (target : S)
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => coordinate t source destination) 0)
    (hunit :
      ∀ source destination,
        ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
          coordinate t source destination ∈ Set.Icc 0 1)
    (hedge :
      ∀ {source destination},
        edge source destination →
          ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
            0 < coordinate t source destination)
    (hreach :
      ∀ source,
        Relation.ReflTransGen edge source target) :
    Nonempty (AnalyticPathMinorization edge coordinate target) := by
  classical
  let path : ∀ source,
      FrozenSupportPath edge source target :=
    fun source =>
      Classical.choice
        (FrozenSupportPath.nonempty_of_reflTransGen
          (hreach source))
  let horizon : ℕ := ∑ source, (path source).length
  let total : ℝ → ℝ :=
    fun t => ∏ source, (path source).weight coordinate t
  have htotalAnalytic : AnalyticAt ℝ total 0 := by
    simpa [total] using
      (Finset.univ.analyticAt_fun_prod
        (fun source _ =>
          FrozenSupportPath.analyticAt_weight
            coordinate hanalytic (path source)))
  have htotalPos :
      ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
        0 < total t := by
    filter_upwards
      [Filter.eventually_all.mpr fun source =>
        FrozenSupportPath.eventually_weight_pos
          coordinate hedge (path source)] with t ht
    exact Finset.prod_pos fun source _ => ht source
  obtain ⟨exponent, constant, hconstant, hpower⟩ :=
    analyticAt_eventually_const_mul_pow_le_of_eventually_pos
      htotalAnalytic htotalPos
  have hpathUnit :
      ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ source,
        (path source).weight coordinate t ∈ Set.Icc 0 1 :=
    Filter.eventually_all.mpr fun source =>
      FrozenSupportPath.eventually_weight_mem_Icc
        coordinate hunit (path source)
  refine ⟨{
    horizon := horizon
    exponent := exponent
    constant := constant
    constant_pos := hconstant
    path := path
    path_length_le := ?_
    eventually_path_weight_ge := ?_
  }⟩
  · intro source
    exact Finset.single_le_sum
      (fun other _ => Nat.zero_le (path other).length)
      (Finset.mem_univ source)
  · filter_upwards [hpower, hpathUnit] with t htotalLower hpathBounds
    intro source
    have hsubset :
        ({source} : Finset S) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hproduct :=
      Finset.prod_le_prod_of_subset_of_le_one
        (f := fun state =>
          (path state).weight coordinate t)
        hsubset
        (fun state _ => (hpathBounds state).1)
        (fun state _ _ => (hpathBounds state).2)
    have hcombined := htotalLower.trans hproduct
    simpa [total] using hcombined

/-- A frozen path weight made from exact PMF point masses is bounded by the
mass of its endpoint at the corresponding iterate. -/
theorem FrozenSupportPath.weight_le_iter_toReal
    [Finite S]
    {edge : S → S → Prop} {source target : S}
    (path : FrozenSupportPath edge source target)
    (kernel : S → PMF S)
    (coordinate : S → S → ℝ)
    (hcoordinate :
      ∀ state destination,
        coordinate state destination =
          (kernel state destination).toReal) :
    path.weight (fun _ => coordinate) 0 ≤
      (Math.PMFIter.iter
        kernel path.length source target).toReal := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  induction path with
  | refl =>
      simp [FrozenSupportPath.weight,
        FrozenSupportPath.length]
  | tail middle target initial hedge ih =>
      rw [FrozenSupportPath.weight,
        FrozenSupportPath.length,
        Math.PMFIter.iter_succ',
        Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
      rw [hcoordinate middle target]
      have hmul :
          initial.weight (fun _ => coordinate) 0 *
              (kernel middle target).toReal ≤
            (Math.PMFIter.iter
                kernel initial.length source middle).toReal *
              (kernel middle target).toReal :=
        mul_le_mul_of_nonneg_right ih ENNReal.toReal_nonneg
      exact hmul.trans
        (Finset.single_le_sum
          (f := fun state =>
            (Math.PMFIter.iter
                kernel initial.length source state).toReal *
              (kernel state target).toReal)
          (fun state _ =>
            mul_nonneg ENNReal.toReal_nonneg
              ENNReal.toReal_nonneg)
          (Finset.mem_univ middle))

/-- Semantic bridge from an abstract analytic path minorization to a genuine
uniform hit-by-horizon bound.  The equality hypothesis says exactly that the
raw coordinates are the point masses of the kernel stopped at the target. -/
theorem AnalyticPathMinorization.eventually_le_stopped_iter
    [Fintype S]
    {edge : S → S → Prop}
    {coordinate : ℝ → S → S → ℝ}
    {target : S}
    (minorization :
      AnalyticPathMinorization edge coordinate target)
    (kernel : ℝ → S → PMF S)
    (hcoordinate :
      ∀ t state destination,
        coordinate t state destination =
          (stoppedAt (kernel t) target state destination).toReal) :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ source,
      minorization.constant * t ^ minorization.exponent ≤
        (Math.PMFIter.iter
          (stoppedAt (kernel t) target)
          minorization.horizon source target).toReal := by
  filter_upwards
    [minorization.eventually_path_weight_ge] with t ht
  intro source
  let fixedCoordinate : S → S → ℝ :=
    fun state destination =>
      coordinate t state destination
  have hpath :
      (minorization.path source).weight coordinate t ≤
        (Math.PMFIter.iter
          (stoppedAt (kernel t) target)
          (minorization.path source).length
          source target).toReal := by
    rw [FrozenSupportPath.weight_freeze
      coordinate (minorization.path source) t 0]
    exact
      FrozenSupportPath.weight_le_iter_toReal
        (minorization.path source)
        (stoppedAt (kernel t) target)
        fixedCoordinate
        (fun state destination =>
          hcoordinate t state destination)
  have hpad :=
    iter_stoppedAt_target_toReal_le_add
      (kernel t) target source
      (minorization.path source).length
      (minorization.horizon -
        (minorization.path source).length)
  rw [Nat.add_sub_of_le
    (minorization.path_length_le source)] at hpad
  exact (ht source).trans (hpath.trans hpad)

/-- Main finite analytic-kernel regeneration theorem.  Analyticity is asked
of the actual stopped-kernel point-mass coordinates; the positivity
hypothesis freezes a support graph reaching the target from every source.
The conclusion is a common power-law lower bound on hitting the target by a
common finite horizon. -/
theorem exists_analytic_finiteHittingMinorization
    [Finite S]
    (kernel : ℝ → S → PMF S)
    (target : S)
    (edge : S → S → Prop)
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t =>
            (stoppedAt
              (kernel t) target source destination).toReal) 0)
    (hedge :
      ∀ {source destination},
        edge source destination →
          ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
            0 <
              (stoppedAt
                (kernel t) target source destination).toReal)
    (hreach :
      ∀ source,
        Relation.ReflTransGen edge source target) :
    ∃ horizon exponent constant,
      0 < constant ∧
        ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ source,
          constant * t ^ exponent ≤
            (Math.PMFIter.iter
              (stoppedAt (kernel t) target)
              horizon source target).toReal := by
  letI : Fintype S := Fintype.ofFinite S
  let coordinate : ℝ → S → S → ℝ :=
    fun t source destination =>
      (stoppedAt
        (kernel t) target source destination).toReal
  have hunit :
      ∀ source destination,
        ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
          coordinate t source destination ∈ Set.Icc 0 1 := by
    intro source destination
    filter_upwards [] with t
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle :=
        PMF.coe_le_one
          (stoppedAt (kernel t) target source)
          destination
      exact
        (ENNReal.toReal_le_toReal
          (PMF.apply_ne_top
            (stoppedAt (kernel t) target source)
            destination)
          (by norm_num)).mpr hle |>.trans_eq (by simp)
  obtain ⟨minorization⟩ :=
    exists_analyticPathMinorization
      edge coordinate target hanalytic hunit hedge hreach
  exact
    ⟨minorization.horizon,
      minorization.exponent,
      minorization.constant,
      minorization.constant_pos,
      minorization.eventually_le_stopped_iter
        kernel (fun _ _ _ => rfl)⟩

end Probability
end Math
