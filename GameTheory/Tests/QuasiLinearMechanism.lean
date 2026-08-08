/-
Hostile quasilinear direct-mechanism fixture.

The first Boolean player's report changes both allocation and payment.  Truth
strictly beats a deviation, weak monotonicity is strict, and reversing the
allocation rule creates a profitable deviation.  This prevents the ownership
gate from passing through constant allocations, transfers, or utilities.
-/

import GameTheory.Mechanism.QuasiLinear

noncomputable section

namespace GameTheory.Tests.QuasiLinearMechanism

open Languages Mechanism

@[reducible]
def truthful : QuasiLinearMechanism Bool Bool where
  Ty _ := Bool
  value who ownType alternative :=
    if who = false ∧ alternative = ownType then 2 else 0
  choose reports := reports false
  payment reports who :=
    if who = false ∧ reports false = true then 1 else 0

@[reducible]
def reversed : QuasiLinearMechanism Bool Bool where
  Ty _ := Bool
  value who ownType alternative :=
    if who = false ∧ alternative = ownType then 2 else 0
  choose reports := !(reports false)
  payment reports who :=
    if who = false ∧ reports false = true then 1 else 0

def falseReports : truthful.ReportProfile := fun _ => false

theorem allocation_responds_to_report :
    truthful.choose falseReports = false ∧
      truthful.choose (Profile.update falseReports false true) = true := by
  norm_num [falseReports]

theorem payment_responds_to_report :
    truthful.payment falseReports false = 0 ∧
      truthful.payment (Profile.update falseReports false true) false = 1 := by
  norm_num [falseReports]

theorem truth_strictly_beats_deviation :
    truthful.trueUtility falseReports false false = 2 ∧
      truthful.trueUtility
        (Profile.update falseReports false true) false false = -1 := by
  norm_num [QuasiLinearMechanism.trueUtility, falseReports]

theorem truthful_isDSIC : truthful.IsDSIC := by
  intro who types reports misreport
  cases who
  · cases htype : types false <;> cases hreport : reports false <;>
      cases misreport <;>
      simp_all [QuasiLinearMechanism.toBayesianMechanism, truthful] <;>
        norm_num
  · simp_all [QuasiLinearMechanism.toBayesianMechanism, truthful]

theorem truthful_isWeaklyMonotone : truthful.IsWeaklyMonotone :=
  truthful.weaklyMonotone_of_isDSIC truthful_isDSIC

theorem strict_weak_monotonicity_witness :
    truthful.value false false (truthful.choose falseReports) -
          truthful.value false false
            (truthful.choose (Profile.update falseReports false true)) >
      truthful.value false true (truthful.choose falseReports) -
        truthful.value false true
          (truthful.choose (Profile.update falseReports false true)) := by
  norm_num [falseReports]

theorem compiles_to_canonical_ic :
    truthful.toBayesianMechanism.IsIncentiveCompatible :=
  truthful_isDSIC

theorem reversed_not_isDSIC : ¬reversed.IsDSIC := by
  intro hdsic
  have h := hdsic false falseReports falseReports true
  simp [QuasiLinearMechanism.toBayesianMechanism, reversed, falseReports] at h

end GameTheory.Tests.QuasiLinearMechanism
