/-
# Finite Bayes-correlated equilibrium

A direct recommendation law jointly distributes true type profiles and
recommended action profiles. It is Bayes plausible when its type marginal is
the common prior, and obedient when no player gains from a deviation depending
only on that player's own type and recommendation.

The flagship theorem pushes a Bayes-Nash plan from a finite private-signal
information structure to an obedient recommendation law in the original game.
Bayes-Nash remains ordinary `IsNash` of the induced Bayesian game form.
-/

import GameTheory.Core.BayesianEquilibrium

noncomputable section

namespace GameTheory

open Probability

universe uι ut ua usig

variable {ι : Type uι}

namespace BayesianGame

/-- A joint finite law over true type profiles and recommended actions. -/
abbrev RecommendationLaw (B : BayesianGame.{uι, ut, ua} ι) :=
  FinDist ((∀ i, B.Ty i) × Profile B.actionSignature)

/-- The type marginal of a recommendation law is the common prior. -/
def IsBayesPlausible (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) : Prop :=
  recommendation.map Prod.fst = B.prior

/-- An obedience deviation may read only the player's own true type and
recommended action. -/
abbrev ObedienceDeviation (B : BayesianGame.{uι, ut, ua} ι) (who : ι) :=
  B.Ty who → B.Act who → B.Act who

/-- Expected payoff from following the recommendation. -/
def recommendedValue (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι) : ℝ :=
  recommendation.expect fun rec => B.payoff rec.1 rec.2 who

/-- The deterministic recommendation law induced by a contingent plan. -/
def strategyRecommendationLaw (B : BayesianGame.{uι, ut, ua} ι)
    (plan : Profile B.signature) : B.RecommendationLaw :=
  B.prior.map fun types => (types, B.actionsOf plan types)

theorem strategyRecommendationLaw_isBayesPlausible
    (B : BayesianGame.{uι, ut, ua} ι)
    (plan : Profile B.signature) :
    B.IsBayesPlausible (B.strategyRecommendationLaw plan) := by
  unfold IsBayesPlausible strategyRecommendationLaw
  rw [FinDist.map_comp]
  exact FinDist.map_id B.prior

/-- A finite private-signal information structure with the original common
prior as its type marginal. -/
structure InformationStructure (B : BayesianGame.{uι, ut, ua} ι)
    (Signal : ι → Type usig) where
  /-- Joint law of true types and private signal profiles. -/
  law : FinDist ((∀ i, B.Ty i) × (∀ i, Signal i))
  /-- The law preserves the original common prior. -/
  isBayesPlausible : law.map Prod.fst = B.prior

namespace InformationStructure

variable {B : BayesianGame.{uι, ut, ua} ι}
variable {Signal : ι → Type usig}

/-- Bayesian game obtained when each player observes only its own true type and
private signal. -/
@[reducible]
def inducedBayesianGame (S : InformationStructure B Signal) :
    BayesianGame ι where
  Ty i := B.Ty i × Signal i
  Act := B.Act
  prior := S.law.map fun rec i => (rec.1 i, rec.2 i)
  payoff observed actions who :=
    B.payoff (fun i => (observed i).1) actions who

/-- Original-game recommendation law induced by a plan in the expanded
private-signal game. -/
def outcomeLaw (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) :
    B.RecommendationLaw :=
  S.law.map fun rec =>
    (rec.1, fun i => plan i (rec.1 i, rec.2 i))

theorem outcomeLaw_isBayesPlausible (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) :
    B.IsBayesPlausible (S.outcomeLaw plan) := by
  unfold BayesianGame.IsBayesPlausible outcomeLaw
  rw [FinDist.map_comp]
  exact S.isBayesPlausible

end InformationStructure

variable [DecidableEq ι]

/-- Apply one obedience deviation to a recommended action profile. -/
def applyObedienceDeviation (B : BayesianGame.{uι, ut, ua} ι)
    (types : ∀ i, B.Ty i) (actions : Profile B.actionSignature)
    (who : ι) (deviation : B.ObedienceDeviation who) :
    Profile B.actionSignature :=
  Profile.update actions who (deviation (types who) (actions who))

/-- Expected payoff after applying an obedience deviation. -/
def deviatingValue (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι)
    (deviation : B.ObedienceDeviation who) : ℝ :=
  recommendation.expect fun rec =>
    B.payoff rec.1
      (B.applyObedienceDeviation rec.1 rec.2 who deviation) who

/-- A Bayes-correlated equilibrium is Bayes plausible and obedient. -/
def IsBayesCorrelatedEq (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) : Prop :=
  B.IsBayesPlausible recommendation ∧
    ∀ who deviation,
      B.deviatingValue recommendation who deviation ≤
        B.recommendedValue recommendation who

omit [DecidableEq ι] in
/-- Following the deterministic recommendation law has the plan's ex-ante
expected utility. -/
theorem recommendedValue_strategyRecommendationLaw
    (B : BayesianGame.{uι, ut, ua} ι) (plan : Profile B.signature)
    (who : ι) :
    B.recommendedValue (B.strategyRecommendationLaw plan) who =
      expectedUtility B.utility who (B.toForm.play plan) := by
  unfold recommendedValue strategyRecommendationLaw expectedUtility
  rw [FinDist.expect_map, BayesianGame.toForm_play, FinDist.expect_map]
  rfl

/-- An obedience deviation of a deterministic recommendation is exactly the
corresponding contingent-plan deviation. -/
theorem deviatingValue_strategyRecommendationLaw
    (B : BayesianGame.{uι, ut, ua} ι) (plan : Profile B.signature)
    (who : ι) (deviation : B.ObedienceDeviation who) :
    B.deviatingValue (B.strategyRecommendationLaw plan) who deviation =
      expectedUtility B.utility who
        (B.toForm.play
          (Profile.update plan who fun ownType =>
            deviation ownType (plan who ownType))) := by
  unfold deviatingValue strategyRecommendationLaw expectedUtility
  rw [FinDist.expect_map, BayesianGame.toForm_play, FinDist.expect_map]
  apply FinDist.expect_congr
  intro types _
  congr 1
  rw [BayesianGame.actionsOf_update]
  rfl

/-- Ordinary Bayes-Nash induces a deterministic Bayes-correlated
recommendation law. -/
theorem isBayesCorrelatedEq_strategyRecommendationLaw_of_isNash
    (B : BayesianGame.{uι, ut, ua} ι) (plan : Profile B.signature)
    (hNash : IsNash B.toForm (euPreference B.utility) plan) :
    B.IsBayesCorrelatedEq (B.strategyRecommendationLaw plan) := by
  refine ⟨B.strategyRecommendationLaw_isBayesPlausible plan, ?_⟩
  intro who deviation
  rw [B.recommendedValue_strategyRecommendationLaw plan who,
    B.deviatingValue_strategyRecommendationLaw plan who deviation]
  have hdeviation :=
    (isNash_iff
      (F := B.toForm) (weaklyPrefers := euPreference B.utility) plan).1
      hNash who (fun ownType => deviation ownType (plan who ownType))
  simpa only [euPreference_apply] using hdeviation

namespace InformationStructure

variable {B : BayesianGame.{uι, ut, ua} ι}
variable {Signal : ι → Type usig}

omit [DecidableEq ι] in
/-- Following the outcome recommendation has the same expected value as the
induced contingent plan. -/
theorem recommendedValue_outcomeLaw (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) (who : ι) :
    B.recommendedValue (S.outcomeLaw plan) who =
      expectedUtility S.inducedBayesianGame.utility who
        (S.inducedBayesianGame.toForm.play plan) := by
  unfold BayesianGame.recommendedValue outcomeLaw expectedUtility
  rw [FinDist.expect_map, BayesianGame.toForm_play, FinDist.expect_map]
  unfold inducedBayesianGame BayesianGame.utility
  rw [FinDist.expect_map]
  rfl

/-- An obedience deviation of the original recommendation law is exactly a
contingent-plan deviation in the induced private-signal game. -/
theorem deviatingValue_outcomeLaw (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) (who : ι)
    (deviation : B.ObedienceDeviation who) :
    B.deviatingValue (S.outcomeLaw plan) who deviation =
      expectedUtility S.inducedBayesianGame.utility who
        (S.inducedBayesianGame.toForm.play
          (Profile.update plan who fun observed =>
            deviation observed.1 (plan who observed))) := by
  unfold BayesianGame.deviatingValue outcomeLaw expectedUtility
  rw [FinDist.expect_map, BayesianGame.toForm_play, FinDist.expect_map]
  unfold inducedBayesianGame BayesianGame.utility
  rw [FinDist.expect_map]
  apply FinDist.expect_congr
  intro rec _
  congr 1
  rw [BayesianGame.actionsOf_update]
  rfl

/-- **Bayes-Nash outcome laws are Bayes-correlated.** Ordinary Nash in the
Bayesian game induced by a finite private-signal structure yields a Bayes
plausible and obedient recommendation law in the original game. -/
theorem isBayesCorrelatedEq_outcomeLaw_of_isNash
    (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature)
    (hNash :
      IsNash S.inducedBayesianGame.toForm
        (euPreference S.inducedBayesianGame.utility) plan) :
    B.IsBayesCorrelatedEq (S.outcomeLaw plan) := by
  refine ⟨S.outcomeLaw_isBayesPlausible plan, ?_⟩
  intro who deviation
  rw [S.recommendedValue_outcomeLaw plan who,
    S.deviatingValue_outcomeLaw plan who deviation]
  have hdeviation :=
    (isNash_iff
      (F := S.inducedBayesianGame.toForm)
      (weaklyPrefers := euPreference S.inducedBayesianGame.utility)
      plan).1 hNash who
      (fun observed => deviation observed.1 (plan who observed))
  simpa only [euPreference_apply] using hdeviation

end InformationStructure

end BayesianGame

end GameTheory
