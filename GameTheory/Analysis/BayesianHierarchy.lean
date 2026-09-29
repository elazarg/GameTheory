/-
# Ex-ante and interim equilibrium as comparison families

An ex-ante deviation in a Bayesian game can condition on the deviator's own
type. Confining a deviation to one own type changes the ex-ante outcome law by
exactly the type's prior probability times the change of the posterior outcome
law given that type. So each interim comparison at a type of positive
probability is localized in an ex-ante comparison, and conversely every ex-ante
comparison is the prior mixture, over own types, of interim comparisons. The two
families imply each other for every utility: Bayes-Nash equilibrium and
posterior interim optimality coincide, with no reachability gap. A gap could
only come from interim constraints at types of probability zero, where no
posterior exists.
-/

import GameTheory.Analysis.IncentiveHierarchy
import GameTheory.Core.BayesianEquilibrium
import GameTheory.Math.Probability.Conditioning
import GameTheory.Math.Probability.Support

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι ut ua uv

namespace BayesianGame

variable {ι : Type uι} [DecidableEq ι] (B : BayesianGame.{uι, ut, ua} ι)
  {Observation : Type uv}

/-- The realized outcome of a plan at a type profile. -/
def outcomeOf (plan : Profile B.signature) (types : ∀ i, B.Ty i) : B.signature.Outcome :=
  (types, B.actionsOf plan types)

/-- An own type with positive prior probability. -/
abbrev PositiveType (who : ι) : Type ut :=
  {ownType : B.Ty who // ownType ∈ (B.prior.map fun types => types who).support}

/-- The posterior over type profiles given one's own type. -/
def ownPosterior (who : ι) (ownType : B.PositiveType who) : PMF (∀ i, B.Ty i) :=
  fiberPosterior B.prior (fun types => types who) ownType.1

/-- The interim comparison of responding with `respond` at one own type, under
the posterior given that type. -/
def interimComparison [∀ i, DecidableEq (B.Ty i)] (observe : B.signature.Outcome → Observation)
    (plan : Profile B.signature) (who : ι)
    (deviation : B.PositiveType who × B.Act who) : IncentiveComparison Observation where
  prescribed := ((B.ownPosterior who deviation.1).map (B.outcomeOf plan)).map observe
  alternative := ((B.ownPosterior who deviation.1).map (B.outcomeOf
    (Profile.update plan who (B.singleTypeDeviation plan who deviation.1.1 deviation.2)))).map
      observe

theorem outcomeOf_singleTypeDeviation_of_ne (plan : Profile B.signature) {who : ι}
    [DecidableEq (B.Ty who)] (ownType : B.Ty who) (respond : B.Act who)
    {types : ∀ i, B.Ty i} (hne : types who ≠ ownType) :
    B.outcomeOf (Profile.update plan who (B.singleTypeDeviation plan who ownType respond))
        types = B.outcomeOf plan types := by
  simp only [outcomeOf, B.actionsOf_update, singleTypeDeviation, hne, ↓reduceIte]
  congr 1
  exact Profile.update_eq_self _ who

omit [DecidableEq ι] in
open Classical in
private theorem map_apply_add_mul (μ ν : PMF (∀ i, B.Ty i)) (first second :
    (∀ i, B.Ty i) → Observation) (weight : ENNReal) (outcome : Observation) :
    μ.map first outcome + weight * ν.map second outcome =
      ∑' types, ((if outcome = first types then μ types else 0) +
        if outcome = second types then weight * ν types else 0) := by
  classical
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun types => ?_
  split_ifs <;> simp

/-- **Localization at an own type.** The interim comparison at a type of
positive probability is localized in the ex-ante comparison of the deviation
confined to that type, with weight the type's prior probability. -/
theorem interimComparison_isLocalizedIn [∀ i, DecidableEq (B.Ty i)]
    (observe : B.signature.Outcome → Observation) (plan : Profile B.signature) (who : ι)
    (ownType : B.PositiveType who) (respond : B.Act who) :
    (B.interimComparison observe plan who (ownType, respond)).IsLocalizedIn
      (equilibriumComparison B.toForm (PMF.pure plan) (DeviationScheme.unilateralConstant _)
        observe who (B.singleTypeDeviation plan who ownType.1 respond))
      ((B.prior.map fun types => types who) ownType.1).toReal := by
  classical
  apply IncentiveComparison.isLocalizedIn_of_mass ENNReal.toReal_nonneg
  intro outcome
  rw [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  let deviated := Profile.update plan who (B.singleTypeDeviation plan who ownType.1 respond)
  have hlaw (profile : Profile B.signature) :
      (B.toForm.outcomeLaw (PMF.pure profile)).map observe =
        B.prior.map (observe ∘ B.outcomeOf profile) := by
    simp only [GameForm.outcomeLaw, PMF.pure_bind, PMF.map_comp]
    rfl
  have hdeviated : (DeviationScheme.unilateralConstant B.toForm.sig).apply (PMF.pure plan) who
      (B.singleTypeDeviation plan who ownType.1 respond) = PMF.pure deviated := by
    simp [deviated, PMF.pure_map]
  simp only [equilibriumComparison, interimComparison, hdeviated, hlaw, PMF.map_comp]
  rw [map_apply_add_mul, map_apply_add_mul]
  refine tsum_congr fun types => ?_
  have hmass := fiberPosterior_disintegrate B.prior (fun types => types who) ownType.1
    ownType.2 types
  simp only [ownPosterior]
  by_cases hfiber : types who = ownType.1
  · have hind : {a : ∀ i, B.Ty i | a who = ownType.1}.indicator B.prior types =
        B.prior types :=
      Set.indicator_of_mem (s := {a : ∀ i, B.Ty i | a who = ownType.1}) hfiber _
    rw [hmass, hind]
    split_ifs <;> simp [add_comm]
  · have hind : {a : ∀ i, B.Ty i | a who = ownType.1}.indicator B.prior types = 0 :=
      Set.indicator_of_notMem (s := {a : ∀ i, B.Ty i | a who = ownType.1}) hfiber _
    have hsame : B.outcomeOf deviated types = B.outcomeOf plan types :=
      B.outcomeOf_singleTypeDeviation_of_ne plan ownType.1 respond hfiber
    rw [hmass, hind]
    simp only [Function.comp_apply, hsame]
    split_ifs <;> simp

/-- Ex-ante optimality implies interim optimality at every own type of positive
probability, for every utility. -/
theorem implies_interimComparison [Fintype Observation]
    [∀ i, DecidableEq (B.Ty i)] (observe : B.signature.Outcome → Observation)
    (plan : Profile B.signature) :
    IncentiveComparison.Implies
      (equilibriumComparison B.toForm (PMF.pure plan) (DeviationScheme.unilateralConstant _)
        observe)
      (B.interimComparison observe plan) :=
  IncentiveComparison.implies_of_localized _ _ fun who deviation =>
    ⟨B.singleTypeDeviation plan who deviation.1.1 deviation.2,
      ((B.prior.map fun types => types who) deviation.1.1).toReal,
      ENNReal.toReal_pos (((B.prior.map fun types => types who).mem_support_iff _).1
        deviation.1.2) (PMF.apply_ne_top _ _),
      B.interimComparison_isLocalizedIn observe plan who deviation.1 deviation.2⟩

private theorem map_congr_on_support {α β : Type*} (μ : PMF α) {f g : α → β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.map f = μ.map g := by
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact bind_congr_on_support μ fun a ha => by simp only [Function.comp_apply, h a ha]

/-- Interim optimality at every own type of positive probability implies ex-ante
optimality, for every utility: an ex-ante comparison is the prior mixture of
interim comparisons. -/
theorem interimComparison_implies [Fintype Observation]
    [∀ i, DecidableEq (B.Ty i)] (observe : B.signature.Outcome → Observation)
    (plan : Profile B.signature) :
    IncentiveComparison.Implies (B.interimComparison observe plan)
      (equilibriumComparison B.toForm (PMF.pure plan) (DeviationScheme.unilateralConstant _)
        observe) := by
  intro utility holds who deviation
  let marginal := B.prior.map fun types => types who
  have hsplit (profile : Profile B.signature) :
      (B.toForm.outcomeLaw (PMF.pure profile)).map observe =
        marginal.bindOnSupport fun ownType hown =>
          ((B.ownPosterior who ⟨ownType, hown⟩).map (B.outcomeOf profile)).map observe := by
    simp only [GameForm.outcomeLaw, PMF.pure_bind, PMF.map_comp]
    conv_lhs => rw [← fiberPosterior_reconstruct B.prior (fun types => types who)]
    rw [PMF.map_bind, ← PMF.bindOnSupport_eq_bind]
    rfl
  have hfiber (ownType : B.Ty who) (hown : ownType ∈ marginal.support) :
      ((B.ownPosterior who ⟨ownType, hown⟩).map
          (B.outcomeOf (Profile.update plan who deviation))).map observe =
        (B.interimComparison observe plan who
          (⟨ownType, hown⟩, deviation ownType)).alternative := by
    simp only [interimComparison]
    congr 1
    apply map_congr_on_support
    intro types htypes
    rw [ownPosterior, fiberPosterior_support _ _ _ hown] at htypes
    have hown' : types who = ownType := htypes.1
    simp only [outcomeOf, B.actionsOf_update, singleTypeDeviation, hown', ↓reduceIte]
    exact congrArg (Prod.mk types) ((B.actionsOf_update plan who deviation types).trans
      (by rw [hown']))
  have hdeviated : (DeviationScheme.unilateralConstant B.toForm.sig).apply (PMF.pure plan) who
      deviation = PMF.pure (Profile.update plan who deviation) := by
    exact (DeviationScheme.unilateralConstant_apply _ _ _ _).trans (PMF.pure_map _ _)
  change euPreference _ () _ _
  simp only [equilibriumComparison, hdeviated, hsplit]
  refine ⟨hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _),
    hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _), ?_⟩
  refine extendedExpect_bindOnSupport_mono (fun ownType hown => ?_)
    (hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _))
  rw [hfiber ownType hown]
  exact (holds who (⟨ownType, hown⟩, deviation ownType)).2.2

end BayesianGame

end GameTheory
