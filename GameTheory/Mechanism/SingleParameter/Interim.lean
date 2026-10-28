module

/-
# Averaging opponents' reports

A fixed law of opponents' reports turns a single-parameter mechanism into
another instance of the same mechanism. The player's own sampled coordinate
is overwritten, so only the law of the other coordinates matters. This is an
interim construction for independent types; correlated conditional beliefs
must be supplied separately and need not stay constant across true types.
-/

public import GameTheory.Mechanism.SingleParameter

@[expose] public section

noncomputable section

namespace GameTheory.Mechanism.SingleParameterMechanism

open GameTheory.Math.Probability

variable {Player : Type*} [DecidableEq Player]
variable (M : SingleParameterMechanism Player)

/-- Average allocation and payment over a fixed opponents' report law. No
integrability is stored; utility decomposition requests it on the actual slices. -/
def averageOpponents (μ : PMF (SingleParameterReportProfile Player)) :
    SingleParameterMechanism Player where
  allocation reports who :=
    expect μ (fun others => M.allocation (Profile.update others who (reports who)) who)
  payment reports who :=
    expect μ (fun others => M.payment (Profile.update others who (reports who)) who)

/-- Averaged quasilinear utility is the expected original utility when the
actual allocation and payment slices are integrable. -/
theorem averageOpponents_utility (μ : PMF (SingleParameterReportProfile Player))
    (who : Player) (reports : SingleParameterReportProfile Player) (r t : ℝ)
    (hq : PayoffIntegrable μ (fun others => M.allocation (Profile.update others who r) who))
    (hp : PayoffIntegrable μ (fun others => M.payment (Profile.update others who r) who)) :
    (M.averageOpponents μ).utility (Profile.update reports who r) who t =
      expect μ (fun others => M.utility (Profile.update others who r) who t) := by
  simp only [utility, averageOpponents, Profile.update_same]
  rw [expect_sub (payoffIntegrable_const_mul hq) hp, expect_const_mul]

end GameTheory.Mechanism.SingleParameterMechanism
