/-
# EXP-104: division-free conditional independence

Conditional independence is stated directly with the cross-product identity

`P(x,y,z) * P(z) = P(x,z) * P(y,z)`.

This avoids division and therefore remains meaningful when the evidence atom
has zero mass. The law is an ordinary PMF and the observable carriers are
unrestricted. It introduces neither a Bayesian-network evaluator nor a
positivity convention.
-/

import GameTheory.Math.Probability.Support
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence

open GameTheory.Math.Probability

universe uΩ uX uY uZ

variable {Ω : Type uΩ} {X : Type uX} {Y : Type uY} {Z : Type uZ}

/-- The atom of one observable. -/
def atom (observable : Ω → X) (value : X) : Set Ω :=
  {ω | observable ω = value}

/-- The simultaneous atom of two observables. -/
def pairAtom (first : Ω → X) (second : Ω → Z)
    (firstValue : X) (secondValue : Z) : Set Ω :=
  {ω | first ω = firstValue ∧ second ω = secondValue}

/-- The simultaneous atom of three observables. -/
def tripleAtom (first : Ω → X) (second : Ω → Y) (evidence : Ω → Z)
    (firstValue : X) (secondValue : Y) (evidenceValue : Z) : Set Ω :=
  {ω | first ω = firstValue ∧ second ω = secondValue ∧
    evidence ω = evidenceValue}

/-- Division-free conditional independence for ordinary PMFs.

The equality is required at every triple of values, including evidence values
outside the support. -/
def IsConditionallyIndependent (law : PMF Ω)
    (first : Ω → X) (second : Ω → Y) (evidence : Ω → Z) : Prop :=
  ∀ firstValue secondValue evidenceValue,
    (law.toOuterMeasure (tripleAtom first second evidence
        firstValue secondValue evidenceValue)).toReal *
      (law.toOuterMeasure (atom evidence evidenceValue)).toReal =
    (law.toOuterMeasure
      (pairAtom first evidence firstValue evidenceValue)).toReal *
      (law.toOuterMeasure
        (pairAtom second evidence secondValue evidenceValue)).toReal

/-- Conditional independence is symmetric in the two separated observables. -/
theorem IsConditionallyIndependent.symm
    {law : PMF Ω} {first : Ω → X} {second : Ω → Y}
    {evidence : Ω → Z}
    (h : IsConditionallyIndependent law first second evidence) :
    IsConditionallyIndependent law second first evidence := by
  intro secondValue firstValue evidenceValue
  have hjoint :
      tripleAtom second first evidence secondValue firstValue evidenceValue =
        tripleAtom first second evidence firstValue secondValue evidenceValue := by
    ext ω
    simp only [tripleAtom, Set.mem_ofPred_eq]
    tauto
  rw [hjoint, h firstValue secondValue evidenceValue, mul_comm]

/-- At an impossible evidence value, the cross-product identity holds without
a positivity premise or an arbitrary conditional-law convention. -/
theorem cross_product_at_zero_evidence
    (law : PMF Ω) (first : Ω → X) (second : Ω → Y)
    (evidence : Ω → Z) (firstValue : X) (secondValue : Y)
    (evidenceValue : Z)
    (hzero : (law.toOuterMeasure (atom evidence evidenceValue)).toReal = 0) :
    (law.toOuterMeasure (tripleAtom first second evidence
        firstValue secondValue evidenceValue)).toReal *
      (law.toOuterMeasure (atom evidence evidenceValue)).toReal =
    (law.toOuterMeasure
      (pairAtom first evidence firstValue evidenceValue)).toReal *
    (law.toOuterMeasure
      (pairAtom second evidence secondValue evidenceValue)).toReal := by
  have hevidenceZero :
      law.toOuterMeasure (atom evidence evidenceValue) = 0 := by
    simpa [ENNReal.toReal_eq_zero_iff,
      outerMeasure_ne_top law (atom evidence evidenceValue)] using hzero
  have hfirst :
      (law.toOuterMeasure
        (pairAtom first evidence firstValue evidenceValue)).toReal = 0 :=
    outerMeasure_toReal_eq_zero_of_subset law (by
      intro ω hpair
      exact hpair.2) hevidenceZero
  have hsecond :
      (law.toOuterMeasure
        (pairAtom second evidence secondValue evidenceValue)).toReal = 0 :=
    outerMeasure_toReal_eq_zero_of_subset law (by
      intro ω hpair
      exact hpair.2) hevidenceZero
  rw [hzero, hfirst, hsecond, mul_zero, zero_mul]

private theorem pure_outerMass_eq_indicator (point : Ω) (event : Set Ω) :
    ((PMF.pure point).toOuterMeasure event).toReal =
      event.indicator (fun _ => (1 : ℝ)) point := by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_eq_single point]
  · by_cases hmem : point ∈ event <;>
      simp [Set.indicator, PMF.pure_apply, hmem]
  · intro value hne
    simp [Set.indicator, PMF.pure_apply, hne]

/-- Every deterministic joint law satisfies the division-free criterion. -/
theorem pure_conditionallyIndependent (point : Ω)
    (first : Ω → X) (second : Ω → Y) (evidence : Ω → Z) :
    IsConditionallyIndependent (PMF.pure point) first second evidence := by
  intro firstValue secondValue evidenceValue
  rw [pure_outerMass_eq_indicator, pure_outerMass_eq_indicator,
    pure_outerMass_eq_indicator, pure_outerMass_eq_indicator]
  by_cases hfirst : first point = firstValue <;>
    by_cases hsecond : second point = secondValue <;>
      by_cases hevidence : evidence point = evidenceValue <;>
        simp [tripleAtom, pairAtom, atom, hfirst, hsecond, hevidence]

/-! ## Hostile finite controls -/

def impossibleEvidenceLaw : PMF Unit := PMF.pure ()

def impossibleFirst (_ : Unit) : Bool := false

def impossibleSecond (_ : Unit) : Bool := true

def impossibleEvidence (_ : Unit) : Bool := false

/-- The deterministic control is conditionally independent. -/
theorem impossibleEvidence_conditionallyIndependent :
    IsConditionallyIndependent impossibleEvidenceLaw
      impossibleFirst impossibleSecond impossibleEvidence :=
  pure_conditionallyIndependent () _ _ _

/-- `true` is genuinely a zero-mass evidence atom in the control. -/
theorem impossibleEvidence_true_mass :
    (impossibleEvidenceLaw.toOuterMeasure
      (atom impossibleEvidence true)).toReal = 0 := by
  rw [impossibleEvidenceLaw, pure_outerMass_eq_indicator]
  simp [atom, impossibleEvidence]

/-- The impossible-evidence equation is validated directly, rather than hidden
behind a vacuous positivity assumption. -/
theorem impossibleEvidence_true_cross_product (firstValue secondValue : Bool) :
    (impossibleEvidenceLaw.toOuterMeasure
        (tripleAtom impossibleFirst impossibleSecond impossibleEvidence
          firstValue secondValue true)).toReal *
      (impossibleEvidenceLaw.toOuterMeasure
        (atom impossibleEvidence true)).toReal =
    (impossibleEvidenceLaw.toOuterMeasure
        (pairAtom impossibleFirst impossibleEvidence firstValue true)).toReal *
      (impossibleEvidenceLaw.toOuterMeasure
        (pairAtom impossibleSecond impossibleEvidence secondValue true)).toReal :=
  cross_product_at_zero_evidence _ _ _ _ _ _ _ impossibleEvidence_true_mass

def diagonalLaw : PMF (Fin 2) := PMF.uniformOfFintype (Fin 2)

def diagonalFirst (value : Fin 2) : Fin 2 := value

def diagonalSecond (value : Fin 2) : Fin 2 := value

def trivialEvidence (_ : Fin 2) : Unit := ()

/-- A shared fair bit is a nearby rejection control: the two copies are not
independent given constant evidence. -/
theorem diagonal_not_conditionallyIndependent :
    ¬ IsConditionallyIndependent diagonalLaw
      diagonalFirst diagonalSecond trivialEvidence := by
  intro independent
  have bad := independent (0 : Fin 2) (1 : Fin 2) ()
  have hjoint :
      tripleAtom diagonalFirst diagonalSecond trivialEvidence
        (0 : Fin 2) (1 : Fin 2) () = ∅ := by
    ext value
    fin_cases value <;>
      simp [tripleAtom, diagonalFirst, diagonalSecond, trivialEvidence]
  have hevidence : atom trivialEvidence () = Set.univ := by
    ext value
    simp [atom, trivialEvidence]
  have hfirst :
      pairAtom diagonalFirst trivialEvidence (0 : Fin 2) () =
        ({0} : Set (Fin 2)) := by
    ext value
    fin_cases value <;>
      simp [pairAtom, diagonalFirst, trivialEvidence]
  have hsecond :
      pairAtom diagonalSecond trivialEvidence (1 : Fin 2) () =
        ({1} : Set (Fin 2)) := by
    ext value
    fin_cases value <;>
      simp [pairAtom, diagonalSecond, trivialEvidence]
  rw [hjoint, hevidence, hfirst, hsecond] at bad
  have hempty :
      (diagonalLaw.toOuterMeasure (∅ : Set (Fin 2))).toReal = 0 := by
    simp [diagonalLaw]
  have huniv :
      (diagonalLaw.toOuterMeasure (Set.univ : Set (Fin 2))).toReal = 1 := by
    simp [diagonalLaw]
  have hsingleton (value : Fin 2) :
      (diagonalLaw.toOuterMeasure ({value} : Set (Fin 2))).toReal = 2⁻¹ := by
    rw [PMF.toOuterMeasure_apply, tsum_eq_single value]
    · simp [diagonalLaw]
    · intro candidate hne
      simp [Set.indicator, hne]
  rw [hempty, huniv, hsingleton, hsingleton] at bad
  norm_num at bad

end GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence
