/-
# Interim optimality in Bayesian games

Bayes-Nash is not a second equilibrium predicate: it is ordinary `IsNash` of
the direct type-contingent game form under expected utility. The theorem below
identifies it with prior-weighted interim optimality at every own type.

The interim value is intentionally unnormalised. Zero-probability types then
need no side condition, and conditioning machinery stays out of the static
core.

Primary reference: J. C. Harsanyi, “Games with Incomplete Information Played
by Bayesian Players,” *Management Science* 14 (1967–1968).
-/

import GameTheory.Core.Bayesian
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι ut ua

variable {ι : Type uι}

namespace BayesianGame

/-- The induced real utility on realized type/action outcomes. -/
def utility (B : BayesianGame ι) : Utility B.signature :=
  fun outcome who => B.payoff outcome.1 outcome.2 who

/-- The prior-weighted interim value of taking `respond` at one own type while
all other coordinates use `plan`. No other player's type is an argument. -/
def interimValue (B : BayesianGame ι) [DecidableEq ι] (who : ι)
    [DecidableEq (B.Ty who)] (ownType : B.Ty who)
    (plan : Profile B.signature) (respond : B.Act who) : ℝ :=
  B.prior.expect fun types =>
    if types who = ownType then
      B.payoff types (Profile.update (B.actionsOf plan types) who respond) who
    else 0

/-- A finite own-type carrier partitions prior expectation into the
prior-weighted interim values of its coordinates. -/
theorem prior_expect_eq_sum (B : BayesianGame ι) (who : ι)
    [Fintype (B.Ty who)] [DecidableEq (B.Ty who)]
    (f : (∀ i, B.Ty i) → ℝ) :
    B.prior.expect f =
      ∑ ownType : B.Ty who, B.prior.expect fun types =>
        if types who = ownType then f types else 0 := by
  simp_rw [FinDist.expect_eq_sum_support]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun types _ => ?_
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (types who)
    fun _ => B.prior.prob types * f types]
  simp

/-- An ex-ante deviation to another contingent plan is the sum of its
prior-weighted interim values. -/
theorem expectedUtility_update (B : BayesianGame ι)
    [DecidableEq ι]
    (plan : Profile B.signature) (who : ι)
    [Fintype (B.Ty who)] [DecidableEq (B.Ty who)]
    (deviation : B.Ty who → B.Act who) :
    expectedUtility B.utility who
        (B.toForm.play (Profile.update plan who deviation)) =
      ∑ ownType : B.Ty who,
        B.interimValue who ownType plan (deviation ownType) := by
  have hactions : ∀ types : ∀ i, B.Ty i,
      B.actionsOf (Profile.update plan who deviation) types =
        Profile.update (B.actionsOf plan types) who
          (deviation (types who)) := by
    intro types
    funext i
    by_cases hi : i = who
    · subst hi
      simp [actionsOf]
    · simp [actionsOf, Profile.update_of_ne _ _ hi]
  rw [toForm_play, expectedUtility, FinDist.expect_map]
  simp only [utility, hactions]
  rw [prior_expect_eq_sum B who]
  refine Finset.sum_congr rfl fun ownType _ => ?_
  refine FinDist.expect_congr fun types _ => ?_
  by_cases htype : types who = ownType
  · simp [htype]
  · simp [htype]

/-- Ex-ante Nash of the direct form is exactly interim optimality at every own
type; no `BayesNash` wrapper is introduced. -/
theorem isNash_iff_interim (B : BayesianGame ι)
    [DecidableEq ι]
    [∀ i, Fintype (B.Ty i)] [∀ i, DecidableEq (B.Ty i)]
    (plan : Profile B.signature) :
    IsNash B.toForm (euPreference B.utility) plan ↔
      ∀ (who : ι) (ownType : B.Ty who) (respond : B.Act who),
        B.interimValue who ownType plan respond ≤
          B.interimValue who ownType plan (plan who ownType) := by
  have hstatus : ∀ who : ι,
      expectedUtility B.utility who (B.toForm.play plan) =
        ∑ ownType : B.Ty who,
          B.interimValue who ownType plan (plan who ownType) := by
    intro who
    have h := B.expectedUtility_update plan who (plan who)
    rwa [Profile.update_eq_self] at h
  rw [isNash_iff]
  constructor
  · intro hnash who ownType respond
    classical
    set deviation : B.Ty who → B.Act who :=
      fun t => if t = ownType then respond else plan who t with hdev
    have hle := hnash who deviation
    rw [euPreference_apply, expectedUtility_update, hstatus who] at hle
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ownType),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ ownType)] at hle
    have hrest : ∀ t ∈ Finset.univ.erase ownType,
        B.interimValue who t plan (deviation t) =
          B.interimValue who t plan (plan who t) := by
      intro t ht
      rw [hdev]
      simp [Finset.ne_of_mem_erase ht]
    rw [Finset.sum_congr rfl hrest] at hle
    have hown : deviation ownType = respond := by simp [hdev]
    rw [hown] at hle
    exact le_of_add_le_add_right hle
  · intro hinterim who deviation
    rw [euPreference_apply, expectedUtility_update, hstatus who]
    exact Finset.sum_le_sum fun ownType _ =>
      hinterim who ownType (deviation ownType)

end BayesianGame

end GameTheory
