/-
# EXP-117: one regular pure-policy law for infinite-horizon Kuhn

The underlying public-history carrier is countably infinite.  A single product
measure over total pure policies is regular, has the exact finite predraws as
all finite marginals, realizes every finite prefix, continues to do so after an
off-baseline behavioral deviation, and gives the same bounded discounted
payoff series as behavioral play.
-/

import GameTheory.Experimental.PostArchitecture.StochasticKuhn

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.StochasticInfiniteKuhn

open GameTheory.Math.Probability GameTheory.Protocol MeasureTheory
open GameTheory.Stochastic GameTheory.Stochastic.Game

open StochasticKuhn

local instance canonicalHistoryMeasurableSpace :
    MeasurableSpace (offPathGame.toExecution false).History := ⊤

local instance actionNonempty :
    ∀ i, Nonempty (offPathGame.Action i) :=
  fun _ => ⟨false⟩

local instance actionFintype :
    ∀ i, Fintype (offPathGame.Action i) :=
  fun _ => inferInstance

local instance choiceMeasurableSpace :
    ∀ i info, MeasurableSpace
      ((offPathGame.perfectMonitoring false).Choice i info) :=
  fun _ _ => ⊤

local instance choiceDiscreteMeasurableSpace :
    ∀ i info, DiscreteMeasurableSpace
      ((offPathGame.perfectMonitoring false).Choice i info) :=
  fun _ _ => ⟨fun _ => MeasurableSet.of_discrete⟩

local instance choiceFintype :
    ∀ i info, Fintype
      ((offPathGame.perfectMonitoring false).Choice i info) :=
  fun i info => Fintype.ofEquiv Bool
    (offPathGame.actionChoiceEquiv false i info)

local instance choiceTopologicalSpace :
    ∀ i info, TopologicalSpace
      ((offPathGame.perfectMonitoring false).Choice i info) :=
  fun _ _ => ⊥

local instance choiceDiscreteTopology :
    ∀ i info, DiscreteTopology
      ((offPathGame.perfectMonitoring false).Choice i info) :=
  fun _ _ => discreteTopology_bot _

/-- The stage utility is genuinely action-dependent. -/
theorem nonconstant_stageUtility :
    offPathGame.stageUtility false (fun _ => false) () = 0 ∧
      offPathGame.stageUtility false (fun _ => true) () = 1 := by
  norm_num

/-- The one law is an ordinary probability measure. -/
theorem policyMeasure_isProbability :
    IsProbabilityMeasure
      (offPathGame.protocolPureProfileMeasure false (baseline false)) :=
  inferInstance

/-- Countability of the state and finite actions make the total-policy product
law regular even though its public-history coordinate carrier is infinite. -/
theorem policyMeasure_isRegular :
    Measure.Regular
      (offPathGame.protocolPureProfileMeasure false (baseline false)) :=
  offPathGame.protocolPureProfileMeasure_regular false (baseline false)

/-- Every bounded restriction is exactly the executable finite predraw. -/
theorem finite_marginal_consumer (horizon : ℕ) :
    (offPathGame.protocolPureProfileMeasure false (baseline false)).map
        ((offPathGame.perfectMonitoring false).restrictPolicies
          (offPathGame.boundedInformationSites false horizon)) =
      ((offPathGame.perfectMonitoring false).finitePolicyDraws
        (offPathGame.toBehaviorProfile false (baseline false))
        (offPathGame.boundedInformationSites false horizon)).toMeasure := by
  unfold Game.protocolPureProfileMeasure
  exact (offPathGame.perfectMonitoring false).behavioralProfileMeasure_map_restrict
      (offPathGame.toBehaviorProfile false (baseline false))
      (offPathGame.boundedInformationSites false horizon)

/-- The same measure, syntactically outside the quantifier, realizes all
finite prefixes. -/
theorem all_prefixes_consumer :
    ∀ horizon,
      offPathGame.protocolPureRunMeasure false (baseline false) horizon =
        ((offPathGame.publicHorizonForm false horizon).play
          (baseline false)).toMeasure :=
  offPathGame.kuhn_policyMeasure_allFinitePrefixes false (baseline false)

/-- An arbitrary public-history deviation reaches the branch excluded from
the baseline support. -/
def deviation : offPathGame.PublicPolicy () :=
  fun _ => FinDist.pure true

theorem unilateral_all_prefixes_consumer :
    ∀ horizon,
      offPathGame.protocolPureRunMeasure false
          (Profile.update (baseline false) () deviation) horizon =
        ((offPathGame.publicHorizonForm false horizon).play
          (Profile.update (baseline false) () deviation)).toMeasure :=
  offPathGame.kuhn_policyMeasure_update_allFinitePrefixes
    false (baseline false) () deviation

theorem stageUtility_abs_le_one (state : Bool)
    (actions : ∀ _ : Unit, Bool) :
    |offPathGame.stageUtility state actions ()| ≤ 1 := by
  rw [show offPathGame.stageUtility state actions () =
      (if actions () then 1 else 0) by rfl]
  split <;> norm_num

/-- Bounded nonconstant stage utility reaches the discounted consequence, not
merely a family of bounded-prefix witnesses. -/
theorem discounted_consumer :
    Summable (fun time => (2 : ℝ)⁻¹ ^ time *
        offPathGame.policyMeasureStageExpectation false
          (baseline false) () time) ∧
      offPathGame.policyMeasureDiscountedPayoff false (2 : ℝ)⁻¹
          (baseline false) () =
        offPathGame.behavioralDiscountedPayoff false (2 : ℝ)⁻¹
          (baseline false) () := by
  apply offPathGame.kuhn_policyMeasure_discountedPayoff
    false (discount := (2 : ℝ)⁻¹) (bound := 1)
  · norm_num
  · norm_num
  · exact stageUtility_abs_le_one

/-- Discounted equality also survives the off-baseline unilateral deviation. -/
theorem unilateral_discounted_consumer :
    Summable (fun time => (2 : ℝ)⁻¹ ^ time *
        offPathGame.policyMeasureStageExpectation false
          (Profile.update (baseline false) () deviation) () time) ∧
      offPathGame.policyMeasureDiscountedPayoff false (2 : ℝ)⁻¹
          (Profile.update (baseline false) () deviation) () =
        offPathGame.behavioralDiscountedPayoff false (2 : ℝ)⁻¹
          (Profile.update (baseline false) () deviation) () := by
  apply offPathGame.kuhn_policyMeasure_update_discountedPayoff
    false (discount := (2 : ℝ)⁻¹) (bound := 1)
      (behavioral := baseline false) (who := ()) (replacement := deviation)
  · norm_num
  · norm_num
  · exact stageUtility_abs_le_one

end GameTheory.Experimental.PostArchitecture.StochasticInfiniteKuhn
