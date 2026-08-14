/-
# Quasilinear direct mechanisms

This capability-free owner exposes the allocation and payment structure needed
by weak monotonicity, affine maximizers, and Myerson-style consumers.  It
compiles to the canonical Bayesian direct-mechanism language, so DSIC remains
the library's ordinary dominant-strategy predicate rather than a parallel
solution concept.
-/

import GameTheory.Mechanism.BayesianIncentives

noncomputable section

namespace GameTheory.Mechanism

open Languages

universe up ua ut

/-- A deterministic quasilinear direct mechanism.  The base data stores no
finiteness, prior, topology, or implementability certificate. -/
structure QuasiLinearMechanism (Player : Type up) (Alternative : Type ua) where
  /-- Private type and direct-report space of each player. -/
  Ty : Player → Type ut
  /-- Value of an alternative at a player's true type. -/
  value : (who : Player) → Ty who → Alternative → ℝ
  /-- Alternative selected from a profile of reports. -/
  choose : (∀ who, Ty who) → Alternative
  /-- Payment charged to each player at a profile of reports. -/
  payment : (∀ who, Ty who) → Player → ℝ

namespace QuasiLinearMechanism

variable {Player : Type up} {Alternative : Type ua}
variable (M : QuasiLinearMechanism Player Alternative)

/-- Signature of direct reports. -/
abbrev reportSignature : GameSignature Player where
  Strategy := M.Ty
  Outcome := Alternative

/-- A dependent profile of direct reports. -/
abbrev ReportProfile := Profile M.reportSignature

/-- Quasilinear utility at the true own type and a full report profile. -/
def trueUtility (report : M.ReportProfile) (who : Player)
    (trueType : M.Ty who) : ℝ :=
  M.value who trueType (M.choose report) - M.payment report who

/-- Compile to the canonical Bayesian direct-mechanism language.  The outcome
retains the report profile because payments may depend on every report. -/
@[reducible]
def toBayesianMechanism [DecidableEq Player] : BayesianMechanism Player where
  Ty := M.Ty
  Report := M.Ty
  Outcome := M.ReportProfile × Alternative
  truth _ ownType := ownType
  choose reports := (reports, M.choose reports)
  utility types outcome who :=
    M.value who (types who) outcome.2 - M.payment outcome.1 who

@[simp]
theorem toBayesianMechanism_utility_choose [DecidableEq Player]
    (types : ∀ who, M.Ty who) (reports : M.ReportProfile) (who : Player) :
    M.toBayesianMechanism.utility types
        (M.toBayesianMechanism.choose reports) who =
      M.trueUtility reports who (types who) :=
  rfl

/-- Dominant-strategy incentive compatibility, transparently specialized from
the canonical direct-mechanism incentive predicate. -/
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

/-- Every DSIC quasilinear direct mechanism has a weakly monotone allocation
rule: the two opposite incentive constraints cancel payments. -/
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

end QuasiLinearMechanism

end GameTheory.Mechanism
