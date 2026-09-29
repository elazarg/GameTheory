/-
# Implications between preservation properties

A solution concept is a family of incentive comparisons indexed by deviating
units, and a concept holds for a utility when every comparison of its family
does. `Implies source target` says that every utility respecting the source
family respects the target family. Within one game it orders concepts: a
refinement implies the concept it refines. Across a compilation it is
preservation of a concept for every utility.

Preservation properties do not inherit the order of the concepts. Preserving
a fine concept implies preserving a coarser one for every target exactly when
the two concepts coincide on the source; the converse implication holds for
every source exactly when they coincide on the target. In each case the
counterpart that separates the two preservation properties when coincidence
fails is the fixed side's own fine family, used as both concepts of the other
side.

Coincidence has a constructive sufficient reason. A fine comparison is
*localized* in a coarse family when some coarse comparison has exactly a
positive multiple of its incentive difference. Every localized comparison is
implied by the coarse family, and a comparison localized only with weight zero
carries no such implication: the weight is the probability with which the
coarse deviation reaches the fine comparison's point.
-/

import GameTheory.Analysis.IncentiveCone

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability
open scoped RealInnerProductSpace

namespace IncentiveComparison

universe u v us us' ut ut'

variable {Outcome : Type u} {ι : Type v}

/-! ## Implication between comparison families -/

section Implies

variable {Source : ι → Type us} {Middle : ι → Type us'} {Target : ι → Type ut}

/-- Transfer a comparison fact along an equality of comparisons. Stated with
`exact`-style unification so that deviations whose types are only
definitionally equal still match. -/
theorem holds_iff_of_eq {first second : IncentiveComparison Outcome} (h : first = second)
    (utility : Outcome → ℝ) : first.Holds utility ↔ second.Holds utility :=
  iff_of_eq (congrArg (fun comparison => comparison.Holds utility) h)

/-- Every utility profile respecting all source comparisons respects all
target comparisons. Within one game this orders concepts; across two games it
is preservation for every utility. -/
def Implies (source : (who : ι) → Source who → IncentiveComparison Outcome)
    (target : (who : ι) → Target who → IncentiveComparison Outcome) : Prop :=
  ∀ utility : Outcome → ι → ℝ,
    (∀ who deviation, (source who deviation).Holds (utility · who)) →
      ∀ who deviation, (target who deviation).Holds (utility · who)

theorem Implies.refl (family : (who : ι) → Source who → IncentiveComparison Outcome) :
    Implies family family :=
  fun _ respected => respected

theorem Implies.trans {first : (who : ι) → Source who → IncentiveComparison Outcome}
    {second : (who : ι) → Middle who → IncentiveComparison Outcome}
    {third : (who : ι) → Target who → IncentiveComparison Outcome}
    (hfirst : Implies first second) (hsecond : Implies second third) :
    Implies first third :=
  fun utility respected => hsecond utility (hfirst utility respected)

/-- On a finite carrier, implication is playerwise cone inclusion. -/
theorem implies_iff_cone [Fintype Outcome] [DecidableEq ι]
    (source : (who : ι) → Source who → IncentiveComparison Outcome)
    (target : (who : ι) → Target who → IncentiveComparison Outcome) :
    Implies source target ↔
      ∀ who deviation, (target who deviation).difference ∈ cone (source who) :=
  forall_holds_imp_iff_cone source target

end Implies

/-! ## Descent and ascent of preservation -/

section Hierarchy

variable {SourceFine SourceCoarse : ι → Type us} {TargetFine TargetCoarse : ι → Type ut}
  {sourceFine : (who : ι) → SourceFine who → IncentiveComparison Outcome}
  {sourceCoarse : (who : ι) → SourceCoarse who → IncentiveComparison Outcome}
  {targetFine : (who : ι) → TargetFine who → IncentiveComparison Outcome}
  {targetCoarse : (who : ι) → TargetCoarse who → IncentiveComparison Outcome}

/-- **Descent.** When the coarse concept already implies the fine one on the
source, preserving the fine concept preserves the coarse one, for any target
on which the fine concept refines the coarse one. -/
theorem Implies.descend (hsource : Implies sourceCoarse sourceFine)
    (htarget : Implies targetFine targetCoarse) (hpreserves : Implies sourceFine targetFine) :
    Implies sourceCoarse targetCoarse :=
  hsource.trans (hpreserves.trans htarget)

/-- **Ascent.** When the coarse concept already implies the fine one on the
target, preserving the coarse concept preserves the fine one, from any source
on which the fine concept refines the coarse one. -/
theorem Implies.ascend (htarget : Implies targetCoarse targetFine)
    (hsource : Implies sourceFine sourceCoarse) (hpreserves : Implies sourceCoarse targetCoarse) :
    Implies sourceFine targetFine :=
  hsource.trans (hpreserves.trans htarget)

/-- Without coincidence on the source, descent fails for some target: the
source's fine family, taken as both concepts of the target, has its fine
concept preserved and its coarse concept not. -/
theorem exists_not_descend (hfails : ¬ Implies sourceCoarse sourceFine) :
    ∃ (targetFine targetCoarse : (who : ι) → SourceFine who → IncentiveComparison Outcome),
      Implies targetFine targetCoarse ∧ Implies sourceFine targetFine ∧
        ¬ Implies sourceCoarse targetCoarse :=
  ⟨sourceFine, sourceFine, .refl _, .refl _, hfails⟩

/-- Without coincidence on the target, ascent fails for some source: the
target's coarse family, taken as both concepts of the source, has its coarse
concept preserved and its fine concept not. -/
theorem exists_not_ascend (hfails : ¬ Implies targetCoarse targetFine) :
    ∃ (sourceFine sourceCoarse : (who : ι) → TargetCoarse who → IncentiveComparison Outcome),
      Implies sourceFine sourceCoarse ∧ Implies sourceCoarse targetCoarse ∧
        ¬ Implies sourceFine targetFine :=
  ⟨targetCoarse, targetCoarse, .refl _, .refl _, hfails⟩

/-- **Characterization of descent.** Preserving the fine concept implies
preserving the coarse one for every target refinement pair exactly when the
two concepts coincide on the source. -/
theorem descend_iff :
    (∀ (targetFine targetCoarse : (who : ι) → SourceFine who → IncentiveComparison Outcome),
      Implies targetFine targetCoarse → Implies sourceFine targetFine →
        Implies sourceCoarse targetCoarse) ↔
      Implies sourceCoarse sourceFine := by
  refine ⟨fun descends => ?_, fun hsource _ _ htarget hpreserves =>
    hsource.descend htarget hpreserves⟩
  by_contra hfails
  obtain ⟨targetFine, targetCoarse, htarget, hpreserves, hnot⟩ := exists_not_descend hfails
  exact hnot (descends targetFine targetCoarse htarget hpreserves)

/-- **Characterization of ascent.** Preserving the coarse concept implies
preserving the fine one from every source refinement pair exactly when the two
concepts coincide on the target. -/
theorem ascend_iff :
    (∀ (sourceFine sourceCoarse : (who : ι) → TargetCoarse who → IncentiveComparison Outcome),
      Implies sourceFine sourceCoarse → Implies sourceCoarse targetCoarse →
        Implies sourceFine targetFine) ↔
      Implies targetCoarse targetFine := by
  refine ⟨fun ascends => ?_, fun htarget _ _ hsource hpreserves =>
    htarget.ascend hsource hpreserves⟩
  by_contra hfails
  obtain ⟨sourceFine, sourceCoarse, hsource, hpreserves, hnot⟩ := exists_not_ascend hfails
  exact hnot (ascends sourceFine sourceCoarse hsource hpreserves)

end Hierarchy

/-! ## Localization -/

section Localization

/-- `fine` is localized in `coarse` with weight `weight`: the coarse incentive
difference is exactly `weight` times the fine one. -/
def IsLocalizedIn (fine coarse : IncentiveComparison Outcome) (weight : ℝ) : Prop :=
  coarse.difference = weight • fine.difference

/-- A comparison localized with positive weight holds exactly when its
localizing comparison does. -/
theorem IsLocalizedIn.holds_iff [Fintype Outcome] {fine coarse : IncentiveComparison Outcome}
    {weight : ℝ}
    (hlocal : fine.IsLocalizedIn coarse weight) (hpositive : 0 < weight)
    (utility : Outcome → ℝ) :
    coarse.Holds utility ↔ fine.Holds utility := by
  rw [holds_iff_inner, holds_iff_inner, hlocal, inner_smul_left]
  simp only [conj_trivial]
  exact ⟨fun h => nonneg_of_mul_nonneg_right (by linarith) hpositive,
    fun h => mul_nonneg hpositive.le h⟩

/-- The mass identity behind a localization, stated without subtraction: the
coarse prescribed mass plus `weight` times the fine alternative mass equals the
coarse alternative mass plus `weight` times the fine prescribed mass. -/
theorem isLocalizedIn_of_mass {fine coarse : IncentiveComparison Outcome} {weight : ℝ}
    (hweight : 0 ≤ weight)
    (hmass : ∀ outcome,
      coarse.prescribed outcome + ENNReal.ofReal weight * fine.alternative outcome =
        coarse.alternative outcome + ENNReal.ofReal weight * fine.prescribed outcome) :
    fine.IsLocalizedIn coarse weight := by
  unfold IsLocalizedIn difference
  ext outcome
  have hreal := congrArg ENNReal.toReal (hmass outcome)
  rw [ENNReal.toReal_add (coarse.prescribed.apply_ne_top outcome)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (fine.alternative.apply_ne_top outcome)),
    ENNReal.toReal_add (coarse.alternative.apply_ne_top outcome)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (fine.prescribed.apply_ne_top outcome)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hweight] at hreal
  simp only [PiLp.smul_apply, smul_eq_mul]
  linarith

variable {Fine : ι → Type us} {Coarse : ι → Type ut}

/-- **Positive localization gives implication.** When every fine comparison is
localized with positive weight in some comparison of the same unit's coarse
family, the coarse family implies the fine one. -/
theorem implies_of_localized [Fintype Outcome]
    (fine : (who : ι) → Fine who → IncentiveComparison Outcome)
    (coarse : (who : ι) → Coarse who → IncentiveComparison Outcome)
    (hlocal : ∀ who deviation, ∃ (localizing : Coarse who) (weight : ℝ), 0 < weight ∧
      (fine who deviation).IsLocalizedIn (coarse who localizing) weight) :
    Implies coarse fine := by
  intro utility respected who deviation
  obtain ⟨localizing, weight, hpositive, hlocalized⟩ := hlocal who deviation
  exact (hlocalized.holds_iff hpositive _).1 (respected who localizing)

end Localization

end IncentiveComparison

end GameTheory
