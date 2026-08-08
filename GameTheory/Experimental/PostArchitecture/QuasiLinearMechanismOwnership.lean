/-
# EXP-066: quasilinear direct-mechanism ownership

Candidate shared data for weak monotonicity, affine maximizers, and Myerson.
The hostile slice also checks transparent specialization from `VCGSetup` and
compilation to the accepted Bayesian direct-mechanism language.
-/

import GameTheory.Languages.BayesianMechanism
import GameTheory.Mechanism.VCG

noncomputable section

namespace GameTheory.Experimental.QuasiLinearMechanismOwnership

open Languages Mechanism.Auction

universe up ua ut

/-- Candidate capability-free quasilinear direct mechanism. -/
structure DirectQuasiLinear (Player : Type up) (Alternative : Type ua) where
  Ty : Player → Type ut
  value : (who : Player) → Ty who → Alternative → ℝ
  choose : (∀ who, Ty who) → Alternative
  payment : (∀ who, Ty who) → Player → ℝ

namespace DirectQuasiLinear

variable {Player : Type up} {Alternative : Type ua}
variable (M : DirectQuasiLinear Player Alternative)

abbrev reportSignature : GameSignature Player where
  Strategy := M.Ty
  Outcome := Alternative

abbrev ReportProfile := Profile M.reportSignature

/-- Quasilinear utility at the true own type and a full report profile. -/
def trueUtility (report : M.ReportProfile) (who : Player)
    (trueType : M.Ty who) : ℝ :=
  M.value who trueType (M.choose report) - M.payment report who

/-- Compile the candidate to the accepted Bayesian direct-mechanism language.
The retained outcome includes reports because payments may depend on them. -/
def toBayesianMechanism [DecidableEq Player] : BayesianMechanism Player where
  Ty := M.Ty
  Report := M.Ty
  Outcome := M.ReportProfile × Alternative
  truth _ ownType := ownType
  choose reports := (reports, M.choose reports)
  utility types outcome who :=
    M.value who (types who) outcome.2 - M.payment outcome.1 who

/-- DSIC is the canonical direct mechanism's pointwise incentive-compatibility
certificate, not a second strategic or equilibrium predicate. -/
abbrev IsDSIC [DecidableEq Player] : Prop :=
  M.toBayesianMechanism.IsIncentiveCompatible

/-- Weak monotonicity of the report-sensitive allocation rule. -/
def IsWeaklyMonotone [DecidableEq Player] : Prop :=
  ∀ who (types : M.ReportProfile) (alternative : M.Ty who),
    M.value who (types who) (M.choose types) -
        M.value who (types who)
          (M.choose (Profile.update types who alternative)) ≥
      M.value who alternative (M.choose types) -
        M.value who alternative
          (M.choose (Profile.update types who alternative))

/-- The two opposite incentive constraints cancel payments and force weak
monotonicity. -/
theorem weaklyMonotone_of_isDSIC [DecidableEq Player]
    (hdsic : M.IsDSIC) : M.IsWeaklyMonotone := by
  intro who types alternative
  have first := hdsic who types types alternative
  have second :=
    hdsic who (Profile.update types who alternative)
      (Profile.update types who alternative) (types who)
  simp only [toBayesianMechanism, Profile.update_same, Profile.update_idem,
    Profile.update_eq_self] at first second
  rw [sub_le_sub_iff] at first second
  apply (sub_le_sub_iff).2
  have combined := add_le_add first second
  have normalized :
      M.value who alternative (M.choose types) +
            M.value who (types who)
              (M.choose (Profile.update types who alternative)) +
          (M.payment types who +
            M.payment (Profile.update types who alternative) who) ≤
        M.value who (types who) (M.choose types) +
            M.value who alternative
              (M.choose (Profile.update types who alternative)) +
          (M.payment types who +
            M.payment (Profile.update types who alternative) who) := by
    calc
      _ =
          (M.value who (types who)
              (M.choose (Profile.update types who alternative)) +
              M.payment types who) +
            (M.value who alternative (M.choose types) +
              M.payment (Profile.update types who alternative) who) := by
            ring
      _ ≤
          (M.value who (types who) (M.choose types) +
              M.payment (Profile.update types who alternative) who) +
            (M.value who alternative
                (M.choose (Profile.update types who alternative)) +
              M.payment types who) := combined
      _ = _ := by ring
  exact (add_le_add_iff_right _).mp normalized

/-- The ownership bridge is definitional: candidate DSIC is canonical IC. -/
theorem toBayesianMechanism_isIncentiveCompatible [DecidableEq Player]
    (hdsic : M.IsDSIC) : M.toBayesianMechanism.IsIncentiveCompatible :=
  hdsic

/-- Every existing Groves setup is an instance of the candidate owner. -/
def ofVCGSetup {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : VCGSetup ι) : DirectQuasiLinear ι V.Outcome where
  Ty := V.Θ
  value := V.val
  choose := V.alloc
  payment := V.vcgPayment

@[simp]
theorem ofVCGSetup_trueUtility {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : VCGSetup ι) (report : V.ReportProfile) (who : ι)
    (trueType : V.Θ who) :
    (ofVCGSetup V).trueUtility report who trueType =
      V.trueUtility who trueType report :=
  rfl

end DirectQuasiLinear

namespace Hostile

@[reducible]
def truthful : DirectQuasiLinear Bool Bool where
  Ty _ := Bool
  value who ownType alternative :=
    if who = false ∧ alternative = ownType then 2 else 0
  choose reports := reports false
  payment reports who :=
    if who = false ∧ reports false = true then 1 else 0

@[reducible]
def reversed : DirectQuasiLinear Bool Bool where
  Ty _ := Bool
  value who ownType alternative :=
    if who = false ∧ alternative = ownType then 2 else 0
  choose reports := !(reports false)
  payment reports who :=
    if who = false ∧ reports false = true then 1 else 0

def falseReports : truthful.ReportProfile := fun _ => false

theorem truthful_allocation_responds_to_report :
    truthful.choose falseReports = false ∧
      truthful.choose (Profile.update falseReports false true) = true := by
  norm_num [falseReports]

theorem truthful_payment_responds_to_report :
    truthful.payment falseReports false = 0 ∧
      truthful.payment (Profile.update falseReports false true) false = 1 := by
  norm_num [falseReports]

theorem truthful_has_strict_deviation_loss :
    truthful.trueUtility falseReports false false = 2 ∧
      truthful.trueUtility
        (Profile.update falseReports false true) false false = -1 := by
  norm_num [DirectQuasiLinear.trueUtility, falseReports]

theorem truthful_isDSIC : truthful.IsDSIC := by
  intro who types reports misreport
  cases who
  · cases htype : types false <;> cases hreport : reports false <;>
      cases misreport <;>
      simp_all [DirectQuasiLinear.toBayesianMechanism, truthful] <;> norm_num
  · simp_all [DirectQuasiLinear.toBayesianMechanism, truthful]

theorem truthful_isWeaklyMonotone : truthful.IsWeaklyMonotone :=
  truthful.weaklyMonotone_of_isDSIC truthful_isDSIC

theorem truthful_strict_weak_monotonicity_witness :
    truthful.value false false (truthful.choose falseReports) -
          truthful.value false false
            (truthful.choose (Profile.update falseReports false true)) >
      truthful.value false true (truthful.choose falseReports) -
        truthful.value false true
          (truthful.choose (Profile.update falseReports false true)) := by
  norm_num [falseReports]

theorem truthful_compiles_to_canonical_ic :
    truthful.toBayesianMechanism.IsIncentiveCompatible :=
  truthful.toBayesianMechanism_isIncentiveCompatible truthful_isDSIC

theorem reversed_not_isDSIC : ¬reversed.IsDSIC := by
  intro hdsic
  have h := hdsic false falseReports falseReports true
  simp [DirectQuasiLinear.toBayesianMechanism, reversed, falseReports] at h

end Hostile

end GameTheory.Experimental.QuasiLinearMechanismOwnership
