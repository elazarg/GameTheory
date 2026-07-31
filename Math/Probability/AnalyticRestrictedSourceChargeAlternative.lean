/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticChargedOccupationFlow
import Math.Probability.PositiveChargedCirculationClass

/-!
# Analytic charge alternatives on a fixed source subtype

Let `R` be a fixed finite family of operational sources in a finite ambient
state space `S`.  An analytic real occupation column
`column : ℝ → R → S → ℝ` and analytic signed charge have the exact
punctured-germ alternative:

* a pole-cleared analytic nonnegative circulation supported on `R` with
  positive total charge; or
* a pole-cleared analytic state potential whose drift pairing dominates the
  charge at every source in `R`.

The real analytic column need not itself come from a `PMF` at every real
parameter.  A separate semantic structure records one valid punctured
parameter where the column is realized by actual transition laws.  It also
records closure of the fixed source family and that every source is
support-reachable from some state in the support of an externally supplied
tail law.  The seed may depend on the source: the forward closure of a law
is generally a union of several rooted reachable sets.

Evaluating an analytic circulation at such a parameter produces a positive
aggregate-charge communicating class.  What is preserved externally is
precise: there is some positive-mass state of the tail law from which the
selected class representative is reachable in the union of the semantic row
supports.  Internally, every selected class state is reachable from the
representative under the induced active kernel.  No positive probability for
an actual time-inhomogeneous path, calendar accounting, or game-theoretic
child is constructed here.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S R : Type*}

/-- The analytic charged-flow alternative with a fixed restricted source
index type `R`.  In the potential branch the inequality is asserted for
every source in `R` by
`AnalyticScaledChargedOccupationPotential.eventual`. -/
theorem
    analyticRestrictedSourcePositiveCirculation_xor_scaledPotential
    [Fintype S] [Fintype R]
    (column : ℝ → R → S → ℝ)
    (charge : ℝ → R → ℝ)
    (hcolumn :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => column t source destination) 0)
    (hcharge :
      ∀ source,
        AnalyticAt ℝ (fun t => charge t source) 0) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation column charge))
      (Nonempty
        (AnalyticScaledChargedOccupationPotential column charge)) :=
  analyticPositiveChargedCirculation_xor_scaledPotential
    column charge hcolumn hcharge

/-- A valid punctured semantic realization of a real occupation column on a
fixed source family generated from the support of a tail law.

`source_closed` states that every positive-probability destination is again
represented by the fixed source family.  `source_reachable_from_law` says
that every represented source lies in the union of the support-reachable
sets rooted at states carrying positive tail-law mass.  The witnessing root
may depend on the source.  This is graph reachability in the union of all
semantic row supports, not a claim about an actual time-inhomogeneous state
law. -/
structure LawSupportedRestrictedSemanticKernelAt
    [Fintype R] [DecidableEq S]
    (column : ℝ → R → S → ℝ)
    (source : R → S)
    (validParameter : ℝ → Prop)
    (tailLaw : PMF S) (parameter : ℝ) where
  valid : validParameter parameter
  kernel : R → PMF S
  realizes :
    ∀ index destination,
      column parameter index destination =
        (kernel index destination).toReal -
          if destination = source index then 1 else 0
  source_closed :
    ∀ index {destination},
      kernel index destination ≠ 0 →
        ∃ nextIndex, source nextIndex = destination
  source_reachable_from_law :
    ∀ index,
      ∃ seed, tailLaw seed ≠ 0 ∧
        AvailableReachable kernel source seed (source index)

/-- A punctured positive-charge class extracted from an analytic
circulation on the fixed source family. -/
structure PuncturedLawSupportedRestrictedPositiveChargedClass
    [Fintype S] [Fintype R] [DecidableEq S]
    (column : ℝ → R → S → ℝ)
    (charge : ℝ → R → ℝ)
    (source : R → S)
    (validParameter : ℝ → Prop)
    (tailLaw : PMF S) where
  parameter : ℝ
  parameter_pos : 0 < parameter
  semantic :
    LawSupportedRestrictedSemanticKernelAt
      column source validParameter tailLaw parameter
  circulation :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn semantic.kernel source)
      (charge parameter)
  positiveClass :
    PositiveChargedCirculationClass
      semantic.kernel source (charge parameter)

namespace PuncturedLawSupportedRestrictedPositiveChargedClass

variable [Fintype S] [Fintype R] [DecidableEq S]
  {column : ℝ → R → S → ℝ}
  {charge : ℝ → R → ℝ}
  {source : R → S}
  {validParameter : ℝ → Prop}
  {tailLaw : PMF S}

/-- Every source in the fixed restricted family is support-reachable from
some positive-mass state of the tail law.  The root is source-dependent. -/
theorem everySource_reachable_from_tailLaw
    (data :
      PuncturedLawSupportedRestrictedPositiveChargedClass
        column charge source validParameter tailLaw)
    (index : R) :
    ∃ seed, tailLaw seed ≠ 0 ∧
      AvailableReachable data.semantic.kernel source seed (source index) :=
  data.semantic.source_reachable_from_law index

/-- The representative is the source of a positive-mass restricted row, so
it is support-reachable from some positive-mass state of the tail law. -/
theorem exists_tailLaw_seed_reaching_representative
    (data :
      PuncturedLawSupportedRestrictedPositiveChargedClass
        column charge source validParameter tailLaw) :
    ∃ seed, tailLaw seed ≠ 0 ∧
      AvailableReachable data.semantic.kernel source seed
        data.positiveClass.representative.1 := by
  obtain ⟨index, source_eq, -⟩ :=
    data.positiveClass.exists_positive_index_at_representative
  obtain ⟨seed, seed_mem, reachable⟩ :=
    data.semantic.source_reachable_from_law index
  rw [source_eq] at reachable
  exact ⟨seed, seed_mem, reachable⟩

/-- The ambient representative is represented by at least one index of the
fixed restricted source family.  For a subtype inclusion this is exactly the
statement that the representative belongs to the restricted state set. -/
theorem exists_restrictedSource_at_representative
    (data :
      PuncturedLawSupportedRestrictedPositiveChargedClass
        column charge source validParameter tailLaw) :
    ∃ index, source index = data.positiveClass.representative.1 := by
  obtain ⟨index, source_eq, -⟩ :=
    data.positiveClass.exists_positive_index_at_representative
  exact ⟨index, source_eq⟩

/-- Every member of the selected class is internally reachable from its
representative under the induced active kernel. -/
theorem classState_reachable_from_representative
    (data :
      PuncturedLawSupportedRestrictedPositiveChargedClass
        column charge source validParameter tailLaw)
    {state :
      occupationActiveStates source data.positiveClass.mass}
    (state_mem : state ∈ data.positiveClass.closedClass.states) :
    PMFReachable
      (occupationActiveKernel
        data.semantic.kernel source
        data.positiveClass.mass data.positiveClass.mass_nonneg
        (actualOccupationBalance_explicit
          data.semantic.kernel source
          data.positiveClass.mass data.positiveClass.balance))
      data.positiveClass.representative state := by
  exact data.positiveClass.reachable_from_representative state_mem

end PuncturedLawSupportedRestrictedPositiveChargedClass

/-- Evaluate a positive analytic restricted-source circulation at a valid
punctured semantic kernel and extract a positive aggregate-charge class.

The hypothesis deliberately states semantic availability only eventually
on the positive punctured germ.  No global analytic map into `PMF` is
required. -/
theorem exists_puncturedLawSupportedRestrictedPositiveChargedClass
    [Fintype S] [Fintype R] [DecidableEq S]
    (column : ℝ → R → S → ℝ)
    (charge : ℝ → R → ℝ)
    (source : R → S)
    (validParameter : ℝ → Prop)
    (tailLaw : PMF S)
    (circulation :
      AnalyticPositiveChargedCirculation column charge)
    (semanticEventually :
      ∀ᶠ parameter in nhdsWithin 0 (Ioi (0 : ℝ)),
        Nonempty
          (LawSupportedRestrictedSemanticKernelAt
            column source validParameter tailLaw parameter)) :
    Nonempty
      (PuncturedLawSupportedRestrictedPositiveChargedClass
        column charge source validParameter tailLaw) := by
  have parameter_pos_eventually :
      ∀ᶠ parameter in nhdsWithin 0 (Ioi (0 : ℝ)),
        0 < parameter := by
    filter_upwards [self_mem_nhdsWithin] with parameter parameter_mem
    exact parameter_mem
  obtain
      ⟨parameter, ⟨semanticNonempty, normalized⟩, parameter_pos⟩ :=
    (semanticEventually.and
      circulation.eventually_hasNormalizedPositiveChargedCirculation).and
        parameter_pos_eventually |>.exists
  obtain ⟨semantic⟩ := semanticNonempty
  have column_eq :
      column parameter =
        actualOccupationColumn semantic.kernel source := by
    funext index destination
    exact semantic.realizes index destination
  rw [column_eq] at normalized
  obtain ⟨positiveClass⟩ :=
    normalized.exists_positiveChargedClass
      semantic.kernel source (charge parameter)
  exact ⟨{
    parameter := parameter
    parameter_pos := parameter_pos
    semantic := semantic
    circulation := normalized
    positiveClass := positiveClass
  }⟩

end Probability
end Math
