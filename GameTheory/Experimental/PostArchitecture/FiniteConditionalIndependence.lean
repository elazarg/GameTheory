/-
# EXP-104: division-free finite conditional independence

Conditional independence is stated directly with the cross-product identity

`P(x,y,z) * P(z) = P(x,z) * P(y,z)`.

This avoids division and therefore remains meaningful when the evidence atom
has zero mass.  The experiment is deliberately limited to a joint
finite-support law and three observables.  It introduces neither a Bayesian
network evaluator nor a positivity convention.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence

open GameTheory.Math.Probability

universe uΩ uX uY uZ

variable {Ω : Type uΩ} {X : Type uX} {Y : Type uY} {Z : Type uZ}

/-- The atom of one finite-law observable. -/
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

/-- Division-free conditional independence for finite-support laws.

The equality is required at every triple of values, including evidence values
outside the support. -/
def IsConditionallyIndependent (law : FinDist Ω)
    (first : Ω → X) (second : Ω → Y) (evidence : Ω → Z) : Prop :=
  ∀ firstValue secondValue evidenceValue,
    law.probOf (tripleAtom first second evidence
        firstValue secondValue evidenceValue) *
      law.probOf (atom evidence evidenceValue) =
    law.probOf (pairAtom first evidence firstValue evidenceValue) *
      law.probOf (pairAtom second evidence secondValue evidenceValue)

/-- Conditional independence is symmetric in the two separated observables. -/
theorem IsConditionallyIndependent.symm
    {law : FinDist Ω} {first : Ω → X} {second : Ω → Y}
    {evidence : Ω → Z}
    (h : IsConditionallyIndependent law first second evidence) :
    IsConditionallyIndependent law second first evidence := by
  intro secondValue firstValue evidenceValue
  have hjoint :
      tripleAtom second first evidence secondValue firstValue evidenceValue =
        tripleAtom first second evidence firstValue secondValue evidenceValue := by
    ext ω
    simp only [tripleAtom, Set.mem_setOf_eq]
    tauto
  rw [hjoint, h firstValue secondValue evidenceValue, mul_comm]

/-- Event mass is nonnegative. -/
theorem probOf_nonneg (law : FinDist Ω) (event : Set Ω) :
    0 ≤ law.probOf event := by
  unfold FinDist.probOf
  exact ENNReal.toReal_nonneg

/-- Finite-law event mass is monotone. -/
theorem probOf_mono (law : FinDist Ω) {smaller larger : Set Ω}
    (hsubset : smaller ⊆ larger) :
    law.probOf smaller ≤ law.probOf larger := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf,
    ← FinDist.expect_indicator_eq_probOf]
  apply FinDist.expect_mono
  intro ω _
  by_cases hsmall : ω ∈ smaller
  · simp [hsmall, hsubset hsmall]
  · by_cases hlarge : ω ∈ larger <;> simp [hsmall, hlarge]

/-- Every subevent of a zero-mass event also has zero mass. -/
theorem probOf_eq_zero_of_subset (law : FinDist Ω) {smaller larger : Set Ω}
    (hsubset : smaller ⊆ larger) (hzero : law.probOf larger = 0) :
    law.probOf smaller = 0 := by
  apply le_antisymm
  · simpa [hzero] using probOf_mono law hsubset
  · exact probOf_nonneg law smaller

/-- At an impossible evidence value, the cross-product identity holds without
a positivity premise or an arbitrary conditional-law convention. -/
theorem cross_product_at_zero_evidence
    (law : FinDist Ω) (first : Ω → X) (second : Ω → Y)
    (evidence : Ω → Z) (firstValue : X) (secondValue : Y)
    (evidenceValue : Z)
    (hzero : law.probOf (atom evidence evidenceValue) = 0) :
    law.probOf (tripleAtom first second evidence
        firstValue secondValue evidenceValue) *
      law.probOf (atom evidence evidenceValue) =
    law.probOf (pairAtom first evidence firstValue evidenceValue) *
      law.probOf (pairAtom second evidence secondValue evidenceValue) := by
  have hfirst :
      law.probOf (pairAtom first evidence firstValue evidenceValue) = 0 :=
    probOf_eq_zero_of_subset law (by
      intro ω hpair
      exact hpair.2) hzero
  have hsecond :
      law.probOf (pairAtom second evidence secondValue evidenceValue) = 0 :=
    probOf_eq_zero_of_subset law (by
      intro ω hpair
      exact hpair.2) hzero
  rw [hzero, hfirst, hsecond, mul_zero, zero_mul]

private theorem probOf_pure_eq_indicator (point : Ω) (event : Set Ω) :
    (FinDist.pure point).probOf event =
      event.indicator (fun _ => (1 : ℝ)) point := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_pure]
  by_cases hmem : point ∈ event <;> simp [hmem]

/-- Every deterministic joint law satisfies the division-free criterion. -/
theorem pure_conditionallyIndependent (point : Ω)
    (first : Ω → X) (second : Ω → Y) (evidence : Ω → Z) :
    IsConditionallyIndependent (FinDist.pure point) first second evidence := by
  intro firstValue secondValue evidenceValue
  rw [probOf_pure_eq_indicator, probOf_pure_eq_indicator,
    probOf_pure_eq_indicator, probOf_pure_eq_indicator]
  by_cases hfirst : first point = firstValue <;>
    by_cases hsecond : second point = secondValue <;>
      by_cases hevidence : evidence point = evidenceValue <;>
        simp [tripleAtom, pairAtom, atom, hfirst, hsecond, hevidence]

/-! ## Hostile finite controls -/

def impossibleEvidenceLaw : FinDist Unit := FinDist.pure ()

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
    impossibleEvidenceLaw.probOf (atom impossibleEvidence true) = 0 := by
  simp [impossibleEvidenceLaw, probOf_pure_eq_indicator, atom,
    impossibleEvidence]

/-- The impossible-evidence equation is validated directly, rather than hidden
behind a vacuous positivity assumption. -/
theorem impossibleEvidence_true_cross_product (firstValue secondValue : Bool) :
    impossibleEvidenceLaw.probOf
        (tripleAtom impossibleFirst impossibleSecond impossibleEvidence
          firstValue secondValue true) *
      impossibleEvidenceLaw.probOf (atom impossibleEvidence true) =
    impossibleEvidenceLaw.probOf
        (pairAtom impossibleFirst impossibleEvidence firstValue true) *
      impossibleEvidenceLaw.probOf
        (pairAtom impossibleSecond impossibleEvidence secondValue true) :=
  cross_product_at_zero_evidence _ _ _ _ _ _ _ impossibleEvidence_true_mass

def diagonalLaw : FinDist (Fin 2) := FinDist.uniformFin 2

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
  have hempty : diagonalLaw.probOf (∅ : Set (Fin 2)) = 0 := by
    classical
    rw [← FinDist.expect_indicator_eq_probOf]
    simp
  have huniv : diagonalLaw.probOf (Set.univ : Set (Fin 2)) = 1 := by
    classical
    rw [← FinDist.expect_indicator_eq_probOf]
    simp
  have hsingleton (value : Fin 2) :
      diagonalLaw.probOf ({value} : Set (Fin 2)) = 2⁻¹ := by
    have hset : ({value} : Set (Fin 2)) =
        (({value} : Finset (Fin 2)) : Set (Fin 2)) := by
      ext candidate
      simp
    rw [hset, FinDist.probOf_finset_eq_sum]
    simp [diagonalLaw]
  rw [hempty, huniv, hsingleton, hsingleton] at bad
  norm_num at bad

end GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence
