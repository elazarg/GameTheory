/-
# EXP-008: the Bayesian interim-deviation scope probe

The baseline ex-ante formulation contains no interim deviation: its
`BayesNash` is an `Iff.rfl` wrapper around strategic Nash. Phase 2 therefore
has to produce a genuinely *interim*, type-dependent
deviation test rather than rename the ex-ante theorem.

This is a scope probe, not a public API. It answers one question: does an
interim deviation fit the shared local-deviation interface without exposing
another player's type or recommendation?

The answer recorded by `isNash_iff_interim` below is yes, in the following
precise sense.

* A Bayesian game compiles to an ordinary `GameForm` whose strategies are
  type-contingent plans. Ex-ante Bayes-Nash is then `IsNash` of that form under
  `euPreference` — no new predicate.
* `interimValue` takes the deviator's *own* type and *own* action and nothing
  else. Another player's type appears nowhere in its argument list.
* Ex-ante optimality is equivalent to interim optimality at every own-type.
  That equivalence is a theorem with content, not a definitional unfolding: it
  needs the prior to decompose over the deviator's own type, and it needs the
  ex-ante deviation to be reconstructible from a single-type change.

The probe deliberately uses the prior-weighted (unnormalized) interim value, so
no positive-probability side condition is needed and no conditioning machinery
enters the core.
-/

import GameTheory.Core

noncomputable section

namespace GameTheory.Experimental.Phase2

open GameTheory GameTheory.Math.Probability

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

set_option linter.checkUnivs false in
/-- A finite Bayesian game with a common prior. Type and action universes stay
independent by design. -/
structure BayesianGame (ι : Type u) [Fintype ι] [DecidableEq ι] where
  /-- Each player's type carrier. -/
  Ty : ι → Type v
  /-- Types are enumerable; only the interim decomposition needs this. -/
  tyFintype : ∀ i, Fintype (Ty i)
  /-- Types are comparable; only the interim decomposition needs this. -/
  tyDecEq : ∀ i, DecidableEq (Ty i)
  /-- Each player's action carrier. -/
  Act : ι → Type w
  /-- The common prior over type profiles. -/
  prior : FinDist (∀ i, Ty i)
  /-- Payoffs depend on the realized types and the realized actions. -/
  payoff : (∀ i, Ty i) → (∀ i, Act i) → ι → ℝ

namespace BayesianGame

instance instFintypeTy (B : BayesianGame ι) (i : ι) : Fintype (B.Ty i) := B.tyFintype i

instance instDecidableEqTy (B : BayesianGame ι) (i : ι) : DecidableEq (B.Ty i) := B.tyDecEq i

/-- Actions alone, used only so that `Profile.update` applies to realized
action profiles. -/
abbrev actSig (B : BayesianGame ι) : GameSignature ι where
  Strategy := B.Act
  Outcome := (∀ i, B.Ty i) × (∀ i, B.Act i)

/-- Strategies are type-contingent plans. -/
abbrev sig (B : BayesianGame ι) : GameSignature ι where
  Strategy i := B.Ty i → B.Act i
  Outcome := (∀ i, B.Ty i) × (∀ i, B.Act i)

/-- The realized action profile of a plan at a type profile. -/
def actionsOf (B : BayesianGame ι) (plan : Profile B.sig) (types : ∀ i, B.Ty i) :
    Profile B.actSig :=
  fun i => plan i (types i)

/-- The ex-ante strategic form: draw types from the prior and play the plans. -/
@[reducible]
def toForm (B : BayesianGame ι) : GameForm ι where
  sig := B.sig
  play plan := B.prior.map fun types => (types, B.actionsOf plan types)

/-- The induced real utility. -/
def utility (B : BayesianGame ι) : Utility B.sig :=
  fun outcome who => B.payoff outcome.1 outcome.2 who

/-- The prior-weighted interim value of playing `respond` when the deviator's
own type is `ownType`.

Its arguments are the deviator, the deviator's own type, the status-quo plan,
and the deviator's own action. No other player's type or recommendation is in
scope, which is the locality property the probe is testing. -/
def interimValue (B : BayesianGame ι) (who : ι) (ownType : B.Ty who)
    (plan : Profile B.sig) (respond : B.Act who) : ℝ :=
  B.prior.expect fun types =>
    if types who = ownType then
      B.payoff types (Profile.update (B.actionsOf plan types) who respond) who
    else 0

/-- The prior decomposes over one player's own type. -/
theorem prior_expect_eq_sum (B : BayesianGame ι) (who : ι) (f : (∀ i, B.Ty i) → ℝ) :
    B.prior.expect f =
      ∑ ownType : B.Ty who, B.prior.expect fun types =>
        if types who = ownType then f types else 0 := by
  simp_rw [FinDist.expect_eq_sum_support]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun types _ => ?_
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (types who) fun _ => B.prior.prob types * f types]
  simp

/-- An ex-ante deviation to another plan is the sum of its interim values. -/
theorem expectedUtility_update (B : BayesianGame ι) (plan : Profile B.sig) (who : ι)
    (deviation : B.Ty who → B.Act who) :
    expectedUtility B.utility who (B.toForm.play (Profile.update plan who deviation)) =
      ∑ ownType : B.Ty who, B.interimValue who ownType plan (deviation ownType) := by
  have hactions : ∀ types : ∀ i, B.Ty i,
      B.actionsOf (Profile.update plan who deviation) types =
        Profile.update (B.actionsOf plan types) who (deviation (types who)) := by
    intro types
    funext i
    by_cases hi : i = who
    · subst hi
      simp [actionsOf]
    · simp [actionsOf, Profile.update_of_ne _ _ hi]
  have hplay : B.toForm.play (Profile.update plan who deviation) =
      B.prior.map fun types =>
        (types, B.actionsOf (Profile.update plan who deviation) types) := rfl
  rw [hplay, expectedUtility, FinDist.expect_map]
  simp only [utility, hactions]
  rw [prior_expect_eq_sum B who]
  refine Finset.sum_congr rfl fun ownType _ => ?_
  refine FinDist.expect_congr fun types _ => ?_
  by_cases htype : types who = ownType
  · simp [htype]
  · simp [htype]

/-- **The probe's result.** Ex-ante Bayes-Nash is exactly interim optimality at
every own-type. The interim condition quantifies over the deviator's own type
and own action only; it never mentions another player's type or
recommendation. -/
theorem isNash_iff_interim (B : BayesianGame ι) (plan : Profile B.sig) :
    IsNash B.toForm (euPreference B.utility) plan ↔
      ∀ (who : ι) (ownType : B.Ty who) (respond : B.Act who),
        B.interimValue who ownType plan respond ≤
          B.interimValue who ownType plan (plan who ownType) := by
  have hstatus : ∀ who : ι,
      expectedUtility B.utility who (B.toForm.play plan) =
        ∑ ownType : B.Ty who, B.interimValue who ownType plan (plan who ownType) := by
    intro who
    have := B.expectedUtility_update plan who (plan who)
    rwa [Profile.update_eq_self] at this
  rw [isNash_iff]
  constructor
  · intro hnash who ownType respond
    -- Deviate at `ownType` only; every other type's term is unchanged.
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
    exact Finset.sum_le_sum fun ownType _ => hinterim who ownType (deviation ownType)

end BayesianGame

end GameTheory.Experimental.Phase2
