/-
Hostile topology-free single-parameter mechanism fixture.

The quadratic payment makes truthful reporting uniquely optimal for the
identity allocation.  A zero-payment negative control admits a strict upward
deviation, preventing the DSIC and monotonicity results from passing through a
constant allocation or payment rule.
-/

import GameTheory.Mechanism.SingleParameter

noncomputable section

namespace GameTheory.Tests.SingleParameter

open Mechanism

@[reducible]
def quadratic : SingleParameterMechanism Unit where
  allocation reports _ := reports ()
  payment reports _ := (reports ()) ^ 2 / 2

@[reducible]
def zeroPayment : SingleParameterMechanism Unit where
  allocation reports _ := reports ()
  payment _ _ := 0

def typeTwo : Unit → ℝ := fun _ => 2

theorem quadratic_isDSIC : quadratic.IsDSIC := by
  rw [quadratic.isDSIC_iff]
  intro who types alternative
  cases who
  simp only [SingleParameterMechanism.utility, Profile.update_same]
  nlinarith [sq_nonneg (alternative - types ())]

theorem truthful_strictly_beats_zero_report :
    quadratic.utility typeTwo () 2 = 2 ∧
      quadratic.utility (Profile.update typeTwo () 0) () 2 = 0 := by
  norm_num [SingleParameterMechanism.utility, quadratic, typeTwo]

theorem payment_sandwich_at_two_and_zero :
    (0 : ℝ) * quadratic.allocationDiff typeTwo () 0 ≤
        quadratic.paymentDiff typeTwo () 0 ∧
      quadratic.paymentDiff typeTwo () 0 ≤
        typeTwo () * quadratic.allocationDiff typeTwo () 0 :=
  quadratic.payment_sandwich quadratic_isDSIC () typeTwo 0

theorem quadratic_isMonotone : quadratic.IsMonotone :=
  quadratic.isMonotone_of_isDSIC quadratic_isDSIC

theorem identity_allocation_isImplementable :
    SingleParameterMechanism.IsImplementable quadratic.allocation :=
  ⟨quadratic.payment, quadratic_isDSIC⟩

theorem zeroPayment_not_isDSIC : ¬zeroPayment.IsDSIC := by
  intro hdsic
  have h := (zeroPayment.isDSIC_iff.mp hdsic) () typeTwo 3
  norm_num [SingleParameterMechanism.utility, zeroPayment, typeTwo] at h

end GameTheory.Tests.SingleParameter
