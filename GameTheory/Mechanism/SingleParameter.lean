/-
# Single-parameter mechanisms: topology-free algebra

This leaf specializes the canonical quasilinear direct mechanism to real
single-parameter reports and linear values.  It contains the payment sandwich,
allocation monotonicity, zero normalization, and implementability vocabulary
that need no integration, continuity, or measure theory.

Primary reference: R. B. Myerson, “Optimal Auction Design,” *Mathematics of
Operations Research* 6 (1981).
-/

import GameTheory.Mechanism.QuasiLinear

noncomputable section

namespace GameTheory.Mechanism

universe up

/-- Canonical signature for real single-parameter reports. -/
@[reducible]
def singleParameterSignature (Player : Type up) : GameSignature Player where
  Strategy _ := ℝ
  Outcome := Player → ℝ

/-- A real report profile bound to the single-parameter signature. -/
abbrev SingleParameterReportProfile (Player : Type up) :=
  Profile (singleParameterSignature Player)

/-- A direct mechanism with real reports and player-indexed allocated
quantities. -/
structure SingleParameterMechanism (Player : Type up) where
  /-- Quantity assigned to each player at a report profile. -/
  allocation : SingleParameterReportProfile Player → Player → ℝ
  /-- Payment charged to each player at a report profile. -/
  payment : SingleParameterReportProfile Player → Player → ℝ

namespace SingleParameterMechanism

variable {Player : Type up}
variable (M : SingleParameterMechanism Player)

/-- View a single-parameter mechanism through the canonical quasilinear owner. -/
@[reducible]
def toQuasiLinearMechanism : QuasiLinearMechanism Player (Player → ℝ) where
  Ty _ := ℝ
  value who trueType allocation := trueType * allocation who
  choose := M.allocation
  payment := M.payment

/-- Quasilinear utility at a true type and reported profile. -/
def utility (reports : SingleParameterReportProfile Player)
    (who : Player) (trueType : ℝ) : ℝ :=
  trueType * M.allocation reports who - M.payment reports who

/-- Dominant-strategy incentive compatibility through the canonical Bayesian
direct-mechanism predicate. -/
abbrev IsDSIC [DecidableEq Player] : Prop :=
  M.toQuasiLinearMechanism.IsDSIC

@[simp]
theorem toQuasiLinearMechanism_trueUtility
    (reports : SingleParameterReportProfile Player)
    (who : Player) (trueType : ℝ) :
    M.toQuasiLinearMechanism.trueUtility reports who trueType =
      M.utility reports who trueType :=
  rfl

/-- Direct real-report characterization of canonical DSIC.  Quantifying the
base profile already quantifies every fixed profile of opponents' reports. -/
theorem isDSIC_iff [DecidableEq Player] :
    M.IsDSIC ↔ ∀ (who : Player)
      (types : SingleParameterReportProfile Player) (alternative : ℝ),
      M.utility (Profile.update types who alternative) who (types who) ≤
        M.utility types who (types who) := by
  constructor
  · intro h who types alternative
    have hic := h who types types alternative
    simp only [QuasiLinearMechanism.toBayesianMechanism,
      toQuasiLinearMechanism, utility, Profile.update_eq_self] at hic ⊢
    convert hic using 1
    all_goals congr 1
  · intro h who types reports alternative
    have hic := h who (Profile.update reports who (types who)) alternative
    simp only [QuasiLinearMechanism.toBayesianMechanism,
      toQuasiLinearMechanism, utility, Profile.update_same,
      Profile.update_idem] at hic ⊢
    convert hic using 1
    all_goals congr 1

/-- Monotonicity of a single-parameter allocation in each player's own report. -/
def AllocationIsMonotone [DecidableEq Player]
    (allocation : SingleParameterReportProfile Player → Player → ℝ) : Prop :=
  ∀ who reports alternative, reports who ≤ alternative →
    allocation reports who ≤
      allocation (Profile.update reports who alternative) who

/-- Monotonicity of this mechanism's allocation rule. -/
def IsMonotone [DecidableEq Player] : Prop :=
  AllocationIsMonotone M.allocation

/-- Allocation difference from replacing one player's report. -/
abbrev allocationDiff [DecidableEq Player]
    (reports : SingleParameterReportProfile Player)
    (who : Player) (alternative : ℝ) : ℝ :=
  M.allocation reports who -
    M.allocation (Profile.update reports who alternative) who

/-- Payment difference from replacing one player's report. -/
abbrev paymentDiff [DecidableEq Player]
    (reports : SingleParameterReportProfile Player)
    (who : Player) (alternative : ℝ) : ℝ :=
  M.payment reports who -
    M.payment (Profile.update reports who alternative) who

/-- Truthfulness gives the upper payment-difference bound. -/
theorem payment_difference_le_of_isDSIC [DecidableEq Player]
    (hdsic : M.IsDSIC) (who : Player)
    (types : SingleParameterReportProfile Player)
    (alternative : ℝ) :
    M.paymentDiff types who alternative ≤
      types who * M.allocationDiff types who alternative := by
  have hic := (M.isDSIC_iff.mp hdsic) who types alternative
  simp only [utility] at hic
  dsimp [paymentDiff, allocationDiff]
  linarith

/-- Truthfulness gives the lower payment-difference bound. -/
theorem payment_difference_ge_of_isDSIC [DecidableEq Player]
    (hdsic : M.IsDSIC) (who : Player)
    (types : SingleParameterReportProfile Player)
    (alternative : ℝ) :
    alternative * M.allocationDiff types who alternative ≤
      M.paymentDiff types who alternative := by
  have hic := (M.isDSIC_iff.mp hdsic) who
    (Profile.update types who alternative) (types who)
  simp only [utility, Profile.update_same, Profile.update_idem,
    Profile.update_eq_self] at hic
  dsimp [paymentDiff, allocationDiff]
  linarith

/-- The standard DSIC payment sandwich. -/
theorem payment_sandwich [DecidableEq Player]
    (hdsic : M.IsDSIC) (who : Player)
    (types : SingleParameterReportProfile Player)
    (alternative : ℝ) :
    alternative * M.allocationDiff types who alternative ≤
        M.paymentDiff types who alternative ∧
      M.paymentDiff types who alternative ≤
        types who * M.allocationDiff types who alternative :=
  ⟨M.payment_difference_ge_of_isDSIC hdsic who types alternative,
    M.payment_difference_le_of_isDSIC hdsic who types alternative⟩

/-- The payment bounds oriented from `types who` toward the replacement. -/
theorem payment_difference_bound [DecidableEq Player]
    (hdsic : M.IsDSIC) (who : Player)
    (types : SingleParameterReportProfile Player)
    (alternative : ℝ) :
    types who *
        (M.allocation (Profile.update types who alternative) who -
          M.allocation types who) ≤
      M.payment (Profile.update types who alternative) who -
        M.payment types who ∧
    M.payment (Profile.update types who alternative) who -
        M.payment types who ≤
      alternative *
        (M.allocation (Profile.update types who alternative) who -
          M.allocation types who) := by
  have hs := M.payment_sandwich hdsic who
    (Profile.update types who alternative) (types who)
  simp only [Profile.update_same, Profile.update_idem,
    Profile.update_eq_self, allocationDiff, paymentDiff] at hs
  exact hs

/-- DSIC forces monotonicity of a single-parameter allocation rule. -/
theorem isMonotone_of_isDSIC [DecidableEq Player]
    (hdsic : M.IsDSIC) : M.IsMonotone := by
  intro who types alternative hle
  by_cases hlt : types who < alternative
  · have hs := M.payment_sandwich hdsic who types alternative
    have hmul :
        0 ≤ (alternative - types who) *
          (M.allocation (Profile.update types who alternative) who -
            M.allocation types who) := by
      dsimp [allocationDiff, paymentDiff] at hs
      nlinarith
    rw [mul_comm] at hmul
    have hnonneg :
        0 ≤ M.allocation (Profile.update types who alternative) who -
          M.allocation types who :=
      nonneg_of_mul_nonneg_left hmul (sub_pos.mpr hlt)
    linarith
  · have heq : types who = alternative :=
      le_antisymm hle (le_of_not_gt hlt)
    subst heq
    simp

/-- Allocation as a one-variable own-report slice. -/
abbrev OwnAllocation [DecidableEq Player]
    (allocation : SingleParameterReportProfile Player → Player → ℝ)
    (who : Player) (reports : SingleParameterReportProfile Player)
    (replacement : ℝ) : ℝ :=
  allocation (Profile.update reports who replacement) who

/-- Payment normalization at a zero own report. -/
def ZeroNormalized [DecidableEq Player] : Prop :=
  ∀ who reports, M.payment (Profile.update reports who 0) who = 0

/-- An allocation is implementable when some payment rule makes its canonical
single-parameter mechanism DSIC. -/
def IsImplementable [DecidableEq Player]
    (allocation : SingleParameterReportProfile Player → Player → ℝ) : Prop :=
  ∃ payment : SingleParameterReportProfile Player → Player → ℝ,
    (SingleParameterMechanism.mk allocation payment).IsDSIC

/-- DSIC implementability forces allocation monotonicity. -/
theorem allocationIsMonotone_of_isImplementable [DecidableEq Player]
    {allocation : SingleParameterReportProfile Player → Player → ℝ}
    (himpl : IsImplementable allocation) :
    AllocationIsMonotone allocation := by
  rcases himpl with ⟨payment, hdsic⟩
  exact (SingleParameterMechanism.mk allocation payment)
    |>.isMonotone_of_isDSIC hdsic

end SingleParameterMechanism

end GameTheory.Mechanism
