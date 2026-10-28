module

/-
# Independent priors and interim expectations

Independent real type laws admit resampling of any own type while keeping a
fixed law of opponents' types. Actual joint payoff integrability supplies
the tower identity and its marginal integrability guard.
-/

public import GameTheory.Mechanism.SingleParameter.Interim
public import GameTheory.Math.Probability.ProductResampling
public import GameTheory.Math.Probability.ExpectationBind

@[expose] public section

noncomputable section

namespace GameTheory.Mechanism.SingleParameterMechanism

open GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- Resampling one own type independently preserves the canonical type-profile law. -/
theorem independentPrior_eq_resample (laws : Player → PMF ℝ) (who : Player) :
    independentProduct laws =
      (laws who).bind (fun t => (independentProduct laws).map
        (fun others : SingleParameterReportProfile Player => Profile.update others who t)) := by
  calc
    _ = (laws who).bind (fun t => (independentProduct laws).map
        (fun others i => if i = who then t else others i)) :=
      independentProduct_resample laws who
    _ = _ := by
      congr 1
      funext t
      congr 1
      funext others i
      by_cases hi : i = who
      · subst i
        simp only [ite_true, Profile.update_same]
      · simp only [hi, ite_false]
        exact (Profile.update_of_ne (sig := singleParameterSignature Player) others t hi).symm

/-- Joint integrability gives the own-type/opponents tower identity for an
independent type prior. -/
theorem expect_independentPrior (laws : Player → PMF ℝ) (who : Player)
    (f : SingleParameterReportProfile Player → ℝ)
    (hf : PayoffIntegrable (independentProduct laws) f) :
    expect (independentProduct laws) f =
      expect (laws who) (fun t => expect (independentProduct laws)
        (fun others => f (Profile.update others who t))) := by
  have hbind := hf
  rw [independentPrior_eq_resample laws who] at hbind
  have h := expect_bind_tower (laws who)
    (fun t => (independentProduct laws).map
      (fun others : SingleParameterReportProfile Player => Profile.update others who t)) f hbind
  rw [← independentPrior_eq_resample laws who] at h
  simpa only [expect_map, Function.comp_def] using h

/-- Actual joint payoff integrability also makes its interim values
integrable under the own-type marginal. -/
theorem integrable_independentPrior_conditional (laws : Player → PMF ℝ) (who : Player)
    (f : SingleParameterReportProfile Player → ℝ)
    (hf : PayoffIntegrable (independentProduct laws) f) :
    PayoffIntegrable (laws who) (fun t => expect (independentProduct laws)
      (fun others => f (Profile.update others who t))) := by
  have hbind := hf
  rw [independentPrior_eq_resample laws who] at hbind
  have h := payoffIntegrable_bind_conditionalExpectation (laws who)
    (fun t => (independentProduct laws).map
      (fun others : SingleParameterReportProfile Player => Profile.update others who t)) f hbind
  simpa only [expect_map, Function.comp_def] using h

end GameTheory.Mechanism.SingleParameterMechanism
