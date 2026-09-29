/-
# Bayes-correlated equilibrium

A recommendation law jointly distributes true types and actions. Bayes
plausibility fixes its type marginal; obedience compares the actual law with
every law obtained by a player's type-and-recommendation dependent deviation.
-/

import GameTheory.Core.BayesianEquilibrium

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι ut ua usig

variable {ι : Type uι}

namespace BayesianGame

/-- The joint law of true type profiles and recommended actions. -/
abbrev RecommendationLaw (B : BayesianGame.{uι, ut, ua} ι) :=
  PMF ((∀ i, B.Ty i) × Profile B.actionSignature)

/-- Recommendations preserve the game's prior marginal on true types. -/
def IsBayesPlausible (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) : Prop :=
  recommendation.map Prod.fst = B.prior

/-- A deviation reads only one's true type and recommended action. -/
abbrev ObedienceDeviation (B : BayesianGame.{uι, ut, ua} ι) (who : ι) :=
  B.Ty who → B.Act who → B.Act who

/-- Draw true types from the prior and recommend the contingent plan's actions. -/
def strategyRecommendationLaw (B : BayesianGame.{uι, ut, ua} ι)
    (plan : Profile B.signature) : B.RecommendationLaw :=
  B.prior.map fun types => (types, B.actionsOf plan types)

theorem strategyRecommendationLaw_isBayesPlausible
    (B : BayesianGame.{uι, ut, ua} ι)
    (plan : Profile B.signature) :
    B.IsBayesPlausible (B.strategyRecommendationLaw plan) := by
  unfold IsBayesPlausible strategyRecommendationLaw
  rw [PMF.map_comp]
  exact PMF.map_id B.prior

/-- A private-signal structure with the original type marginal. -/
structure InformationStructure (B : BayesianGame.{uι, ut, ua} ι)
    (Signal : ι → Type usig) where
  /-- Joint law of true types and players' private signals. -/
  law : PMF ((∀ i, B.Ty i) × (∀ i, Signal i))
  isBayesPlausible : law.map Prod.fst = B.prior

namespace InformationStructure

variable {B : BayesianGame.{uι, ut, ua} ι}
variable {Signal : ι → Type usig}

/-- Each player observes its true type together with its private signal. -/
@[reducible]
def inducedBayesianGame (S : InformationStructure B Signal) :
    BayesianGame ι where
  Ty i := B.Ty i × Signal i
  Act := B.Act
  prior := S.law.map fun rec i => (rec.1 i, rec.2 i)
  payoff observed actions who :=
    B.payoff (fun i => (observed i).1) actions who

/-- Joint law of true types and the actions selected from private observations. -/
def outcomeLaw (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) :
    B.RecommendationLaw :=
  S.law.map fun rec =>
    (rec.1, fun i => plan i (rec.1 i, rec.2 i))

theorem outcomeLaw_isBayesPlausible (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) :
    B.IsBayesPlausible (S.outcomeLaw plan) := by
  unfold BayesianGame.IsBayesPlausible outcomeLaw
  rw [PMF.map_comp]
  exact S.isBayesPlausible

end InformationStructure

variable [DecidableEq ι]

/-- Replace one recommended action using only that player's observed type and action. -/
def applyObedienceDeviation (B : BayesianGame.{uι, ut, ua} ι)
    (types : ∀ i, B.Ty i) (actions : Profile B.actionSignature)
    (who : ι) (deviation : B.ObedienceDeviation who) :
    Profile B.actionSignature :=
  Profile.update actions who (deviation (types who) (actions who))

/-- The actual recommendation outcome after one obedience deviation. -/
def recordDeviation (B : BayesianGame.{uι, ut, ua} ι)
    (who : ι) (deviation : B.ObedienceDeviation who)
    (rec : (∀ i, B.Ty i) × Profile B.actionSignature) :
    (∀ i, B.Ty i) × Profile B.actionSignature :=
  (rec.1, B.applyObedienceDeviation rec.1 rec.2 who deviation)

/-- Expected value of following recommendations. -/
def recommendedValue (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι) : ℝ :=
  expectedUtility B.utility who recommendation

/-- Expected value of one entire obedience-deviation law. -/
def deviatingValue (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι)
    (deviation : B.ObedienceDeviation who) : ℝ :=
  expectedUtility B.utility who
    (recommendation.map (B.recordDeviation who deviation))

/-- Bayes plausibility and expected-utility obedience between integrable laws. -/
def IsBayesCorrelatedEq (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) : Prop :=
  B.IsBayesPlausible recommendation ∧
    ∀ who deviation,
      euPreference B.utility who recommendation
        (recommendation.map (B.recordDeviation who deviation))

/-- The observed own-type/recommended-action cell. -/
def obedienceEvent (B : BayesianGame.{uι, ut, ua} ι) (who : ι)
    (ownType : B.Ty who) (recommended : B.Act who) :
    Set ((∀ i, B.Ty i) × Profile B.actionSignature) :=
  (fun rec => (rec.1 who, rec.2 who)) ⁻¹' {(ownType, recommended)}

/-- Extract the true type and recommended action visible to one player. -/
def ownObservation (B : BayesianGame.{uι, ut, ua} ι) (who : ι)
    (rec : (∀ i, B.Ty i) × Profile B.actionSignature) :
    B.Ty who × B.Act who :=
  (rec.1 who, rec.2 who)

omit [DecidableEq ι] in
theorem obedienceEvent_eq_fiber (B : BayesianGame.{uι, ut, ua} ι)
    (who : ι) (ownType : B.Ty who) (recommended : B.Act who) :
    B.obedienceEvent who ownType recommended =
      {rec | B.ownObservation who rec = (ownType, recommended)} := by
  ext rec
  simp only [obedienceEvent, ownObservation, Set.mem_preimage,
    Set.mem_singleton_iff, Set.mem_ofPred_eq]

/-- A fixed action replacement, used when testing one observation cell. -/
def fixedReplacementDeviation (B : BayesianGame.{uι, ut, ua} ι)
    (who : ι) (replacement : B.Act who) : B.ObedienceDeviation who :=
  fun _ _ => replacement

/-- Follow the recommended action at every own type. -/
def identityObedienceDeviation (B : BayesianGame.{uι, ut, ua} ι)
    (who : ι) : B.ObedienceDeviation who :=
  fun _ action => action

theorem recordDeviation_identity (B : BayesianGame.{uι, ut, ua} ι)
    (who : ι)
    (rec : (∀ i, B.Ty i) × Profile B.actionSignature) :
    B.recordDeviation who (B.identityObedienceDeviation who) rec = rec := by
  cases rec
  simp [recordDeviation, applyObedienceDeviation,
    identityObedienceDeviation, Profile.update_eq_self]

theorem recommendation_integrable_of_deviation
    (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι)
    (hdeviation : ∀ deviation : B.ObedienceDeviation who,
      UtilityIntegrable B.utility who
        (recommendation.map (B.recordDeviation who deviation))) :
    UtilityIntegrable B.utility who recommendation := by
  have hfun : B.recordDeviation who (B.identityObedienceDeviation who) = id := by
    funext rec
    exact B.recordDeviation_identity who rec
  have hlaw :
      recommendation.map (B.recordDeviation who
        (B.identityObedienceDeviation who)) = recommendation := by
    rw [hfun, PMF.map_id]
  exact payoffIntegrable_congr_law hlaw
    (hdeviation (B.identityObedienceDeviation who))

/-- Posterior payoff from following a positive-mass cell. -/
def interimRecommendedValue (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι)
    (ownType : B.Ty who) (recommended : B.Act who)
    (hObserved :
      ∃ rec ∈ B.obedienceEvent who ownType recommended,
        rec ∈ recommendation.support) : ℝ :=
  expect (recommendation.filter
      (B.obedienceEvent who ownType recommended) hObserved)
    (fun rec => B.utility rec who)

/-- Posterior payoff from a fixed replacement on one cell. -/
def interimDeviatingValue (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι)
    (ownType : B.Ty who) (recommended replacement : B.Act who)
    (hObserved :
      ∃ rec ∈ B.obedienceEvent who ownType recommended,
        rec ∈ recommendation.support) : ℝ :=
  expect (recommendation.filter
      (B.obedienceEvent who ownType recommended) hObserved)
    (fun rec =>
      B.utility (B.recordDeviation who
        (B.fixedReplacementDeviation who replacement) rec) who)

omit [DecidableEq ι] in
theorem interimRecommended_integrable_of_whole
    (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι)
    (ownType : B.Ty who) (recommended : B.Act who)
    (hObserved :
      ∃ rec ∈ B.obedienceEvent who ownType recommended,
        rec ∈ recommendation.support)
    (hwhole : UtilityIntegrable B.utility who recommendation) :
    PayoffIntegrable
      (recommendation.filter
        (B.obedienceEvent who ownType recommended) hObserved)
      (fun rec => B.utility rec who) :=
  payoffIntegrable_filter recommendation
    (B.obedienceEvent who ownType recommended) hObserved _ hwhole

theorem interimDeviating_integrable_of_whole
    (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι)
    (ownType : B.Ty who) (recommended replacement : B.Act who)
    (hObserved :
      ∃ rec ∈ B.obedienceEvent who ownType recommended,
        rec ∈ recommendation.support)
    (hwhole : UtilityIntegrable B.utility who
      (recommendation.map
        (B.recordDeviation who (B.fixedReplacementDeviation who replacement)))) :
    PayoffIntegrable
      (recommendation.filter
        (B.obedienceEvent who ownType recommended) hObserved)
      (fun rec =>
        B.utility (B.recordDeviation who
          (B.fixedReplacementDeviation who replacement) rec) who) := by
  exact payoffIntegrable_filter recommendation
    (B.obedienceEvent who ownType recommended) hObserved _
    ((payoffIntegrable_map_iff
      (B.recordDeviation who (B.fixedReplacementDeviation who replacement))
      recommendation (fun rec => B.utility rec who)).mp hwhole)

/-- Every whole obedience-deviation law has an integrable payoff for the
deviator. Identity obedience is one of them, so the followed law is integrable
too. -/
def HasIntegrableObedienceDeviations (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) : Prop :=
  ∀ who (deviation : B.ObedienceDeviation who),
    UtilityIntegrable B.utility who
      (recommendation.map (B.recordDeviation who deviation))

/-- Positive-cell tests: after every observable own type and recommendation, no
fixed replacement beats obedience in posterior expected utility. -/
def InterimObedienceTests (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) : Prop :=
  ∀ who ownType recommended replacement
      (hObserved :
        ∃ rec ∈ B.obedienceEvent who ownType recommended,
          rec ∈ recommendation.support),
      B.interimDeviatingValue recommendation who ownType recommended
          replacement hObserved ≤
        B.interimRecommendedValue recommendation who ownType recommended
          hObserved

theorem recordDeviation_strategyRecommendationLaw
    (B : BayesianGame.{uι, ut, ua} ι)
    (plan : Profile B.signature) (who : ι)
    (deviation : B.ObedienceDeviation who) :
    (B.strategyRecommendationLaw plan).map
        (B.recordDeviation who deviation) =
      B.toForm.play (Profile.update plan who
        (fun ownType => deviation ownType (plan who ownType))) := by
  rw [strategyRecommendationLaw, PMF.map_comp, B.toForm_play]
  congr 1
  funext types
  simp only [Function.comp_apply, recordDeviation, applyObedienceDeviation]
  congr 1
  rw [B.actionsOf_update]
  rfl

omit [DecidableEq ι] in
theorem recommendedValue_strategyRecommendationLaw
    (B : BayesianGame.{uι, ut, ua} ι) (plan : Profile B.signature)
    (who : ι) :
    B.recommendedValue (B.strategyRecommendationLaw plan) who =
      expectedUtility B.utility who (B.toForm.play plan) := rfl

theorem deviatingValue_strategyRecommendationLaw
    (B : BayesianGame.{uι, ut, ua} ι) (plan : Profile B.signature)
    (who : ι) (deviation : B.ObedienceDeviation who) :
    B.deviatingValue (B.strategyRecommendationLaw plan) who deviation =
      expectedUtility B.utility who
        (B.toForm.play (Profile.update plan who
          (fun ownType => deviation ownType (plan who ownType)))) := by
  exact expectedUtility_congr_law B.utility who
    (B.recordDeviation_strategyRecommendationLaw plan who deviation)

/-- Nash obedience transports along equality of the actual outcome laws. -/
theorem isBayesCorrelatedEq_strategyRecommendationLaw_of_isNash
    (B : BayesianGame.{uι, ut, ua} ι) (plan : Profile B.signature)
    (hNash : IsNash B.toForm (euPreference B.utility) plan) :
    B.IsBayesCorrelatedEq (B.strategyRecommendationLaw plan) := by
  refine ⟨B.strategyRecommendationLaw_isBayesPlausible plan, ?_⟩
  intro who deviation
  have hdeviation :=
    (isNash_iff
      (F := B.toForm) (weaklyPrefers := euPreference B.utility) plan).1
      hNash who (fun ownType => deviation ownType (plan who ownType))
  rw [B.recordDeviation_strategyRecommendationLaw]
  exact hdeviation

/-- Global obedience with integrable deviations implies every positive-cell
fixed-action test. -/
theorem isBayesCorrelatedEq_implies_interim
    (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw)
    (hintegrable : B.HasIntegrableObedienceDeviations recommendation)
    (hBCE : B.IsBayesCorrelatedEq recommendation) :
    B.IsBayesPlausible recommendation ∧
      B.InterimObedienceTests recommendation := by
  classical
  refine ⟨hBCE.1, ?_⟩
  intro who ownType recommended replacement hObserved
  have hdeviation := hintegrable who
  have hfollow := B.recommendation_integrable_of_deviation recommendation who hdeviation
  let event := B.obedienceEvent who ownType recommended
  let localDeviation : B.ObedienceDeviation who :=
    fun candidateType candidateAction =>
      if candidateType = ownType ∧ candidateAction = recommended
      then replacement else candidateAction
  let f : (∀ i, B.Ty i) × Profile B.actionSignature → ℝ :=
    fun rec => B.utility (B.recordDeviation who localDeviation rec) who
  let fixed : B.ObedienceDeviation who :=
    B.fixedReplacementDeviation who replacement
  let ffixed : (∀ i, B.Ty i) × Profile B.actionSignature → ℝ :=
    fun rec => B.utility (B.recordDeviation who fixed rec) who
  let g : (∀ i, B.Ty i) × Profile B.actionSignature → ℝ :=
    fun rec => B.utility rec who
  have hf : PayoffIntegrable recommendation f :=
    (payoffIntegrable_map_iff (B.recordDeviation who localDeviation)
      recommendation g).mp (hdeviation localDeviation)
  have hle : expect recommendation f ≤
      expect recommendation g := by
    have hglobal := (euPreference_iff B.utility who _ _ hfollow (hdeviation localDeviation)).1
      (hBCE.2 who localDeviation)
    rw [expectedUtility_map] at hglobal
    exact hglobal
  have hoff : ∀ rec ∈ recommendation.support, rec ∉ event → f rec = g rec := by
    intro rec _ hnot
    have hpair :
        ¬(rec.1 who = ownType ∧ rec.2 who = recommended) := by
      simpa only [event, obedienceEvent, Set.mem_preimage,
        Set.mem_singleton_iff, Prod.mk.injEq] using hnot
    simp [f, g, recordDeviation, applyObedienceDeviation,
      localDeviation, hpair, Profile.update_eq_self]
  have hconditional :=
    expect_filter_le_of_expect_le_of_eq_off recommendation event hObserved
      f g hf hfollow hoff hle
  have hpoint :
      ∀ rec ∈ (recommendation.filter event hObserved).support,
        ffixed rec = f rec := by
    intro rec hrec
    have hmem : rec ∈ event := by
      rw [PMF.mem_support_filter_iff] at hrec
      exact hrec.1
    have hpair : rec.1 who = ownType ∧ rec.2 who = recommended := by
      simpa only [event, obedienceEvent, Set.mem_preimage,
        Set.mem_singleton_iff, Prod.mk.injEq] using hmem
    simp [ffixed, f, recordDeviation, applyObedienceDeviation,
      fixedReplacementDeviation, fixed, localDeviation, hpair]
  unfold interimDeviatingValue interimRecommendedValue
  calc
    expect (recommendation.filter event hObserved) ffixed =
      expect (recommendation.filter event hObserved) f :=
      expect_congr_on_support hpoint
    _ ≤ expect (recommendation.filter event hObserved) g :=
      hconditional

/-- Whole-law integrability and all positive-cell tests imply obedience. -/
theorem interim_implies_isBayesCorrelatedEq
    (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw)
    (hintegrable : B.HasIntegrableObedienceDeviations recommendation)
    (hinterim :
      B.IsBayesPlausible recommendation ∧
        B.InterimObedienceTests recommendation) :
    B.IsBayesCorrelatedEq recommendation := by
  classical
  refine ⟨hinterim.1, ?_⟩
  intro who deviation
  have hdeviation := hintegrable who
  have hcond := hinterim.2 who
  let hfollow :=
    B.recommendation_integrable_of_deviation recommendation who hdeviation
  let observation := B.ownObservation who
  let f : (∀ i, B.Ty i) × Profile B.actionSignature → ℝ :=
    fun rec => B.utility (B.recordDeviation who deviation rec) who
  let g : (∀ i, B.Ty i) × Profile B.actionSignature → ℝ :=
    fun rec => B.utility rec who
  have hf : PayoffIntegrable recommendation f :=
    (payoffIntegrable_map_iff (B.recordDeviation who deviation)
      recommendation g).mp (hdeviation deviation)
  have hle : expect recommendation f ≤
      expect recommendation g := by
    apply expect_fiberwise_le recommendation observation f g hf hfollow
    intro observed hb
    let replacement := deviation observed.1 observed.2
    let fixed := B.fixedReplacementDeviation who replacement
    let ffixed : (∀ i, B.Ty i) × Profile B.actionSignature → ℝ :=
      fun rec => B.utility (B.recordDeviation who fixed rec) who
    have hObserved :
        ∃ rec ∈ B.obedienceEvent who observed.1 observed.2,
          rec ∈ recommendation.support := by
      rw [PMF.support_map] at hb
      obtain ⟨rec, hrec, hobs⟩ := hb
      refine ⟨rec, ?_, hrec⟩
      simpa [obedienceEvent, observation, ownObservation] using hobs
    have hevent :
        B.obedienceEvent who observed.1 observed.2 =
          {rec | observation rec = observed} := by
      cases observed with
      | mk ownType recommended =>
          exact B.obedienceEvent_eq_fiber who ownType recommended
    have hposterior :
        fiberPosterior recommendation observation observed hb =
          recommendation.filter
            (B.obedienceEvent who observed.1 observed.2) hObserved := by
      simp only [fiberPosterior, ← hevent]
    have hpoint :
        ∀ rec ∈ (fiberPosterior recommendation observation observed hb).support,
          f rec = ffixed rec := by
      intro rec hrec
      have hcell : observation rec = observed := by
        have hmem := hrec
        rw [fiberPosterior_support] at hmem
        exact hmem.1
      have hpair :
          rec.1 who = observed.1 ∧ rec.2 who = observed.2 := by
        exact ⟨congrArg Prod.fst hcell, congrArg Prod.snd hcell⟩
      simp [f, ffixed, recordDeviation, applyObedienceDeviation,
        fixedReplacementDeviation, fixed, replacement, hpair]
    have hvalueEq :
        expect (fiberPosterior recommendation observation observed hb) f =
          expect (fiberPosterior recommendation observation observed hb)
            ffixed :=
      expect_congr_on_support hpoint
    have hfixedLe :
        expect (fiberPosterior recommendation observation observed hb)
            ffixed ≤
          expect (fiberPosterior recommendation observation observed hb) g := by
      have h := hcond observed.1 observed.2 replacement hObserved
      unfold interimDeviatingValue interimRecommendedValue at h
      simpa only [hposterior] using h
    exact hvalueEq.trans_le hfixedLe
  refine (euPreference_iff B.utility who _ _ hfollow (hdeviation deviation)).2 ?_
  have hmap :=
    expectedUtility_map B.utility who (B.recordDeviation who deviation)
      recommendation
  calc
    expectedUtility B.utility who
        (recommendation.map (B.recordDeviation who deviation)) =
      expect recommendation f := by
        exact hmap
    _ ≤ expect recommendation g := hle
    _ = expectedUtility B.utility who recommendation := rfl

/-- With integrable deviations, Bayes correlated equilibrium is Bayes
plausibility together with every positive-cell obedience test. -/
theorem isBayesCorrelatedEq_iff_interim_obedience
    (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw)
    (hintegrable : B.HasIntegrableObedienceDeviations recommendation) :
    B.IsBayesCorrelatedEq recommendation ↔
      B.IsBayesPlausible recommendation ∧
        B.InterimObedienceTests recommendation := by
  constructor
  · exact B.isBayesCorrelatedEq_implies_interim recommendation hintegrable
  · exact B.interim_implies_isBayesCorrelatedEq recommendation hintegrable

namespace InformationStructure

variable {B : BayesianGame.{uι, ut, ua} ι}
variable {Signal : ι → Type usig}

/-- A plausible law itself is an information structure with action signals. -/
def ofRecommendation (recommendation : B.RecommendationLaw)
    (hplausible : B.IsBayesPlausible recommendation) :
    InformationStructure B B.Act where
  law := recommendation
  isBayesPlausible := hplausible

/-- Interpret the private action signal as the player's selected action. -/
def followActionSignal (S : InformationStructure B B.Act) :
    Profile S.inducedBayesianGame.signature :=
  fun _ observed => observed.2

omit [DecidableEq ι] in
theorem outcomeLaw_followActionSignal
    (recommendation : B.RecommendationLaw)
    (hplausible : B.IsBayesPlausible recommendation) :
    let S := ofRecommendation recommendation hplausible
    S.outcomeLaw S.followActionSignal = recommendation := by
  dsimp [ofRecommendation, outcomeLaw, followActionSignal]
  have hfun :
      (fun rec : (∀ i, B.Ty i) × Profile B.actionSignature =>
        (rec.1, fun i => rec.2 i)) = id := by
    funext rec
    cases rec
    rfl
  rw [hfun, PMF.map_id]

omit [DecidableEq ι] in
theorem recommendedValue_outcomeLaw_integrable_iff
    (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) (who : ι) :
    UtilityIntegrable B.utility who (S.outcomeLaw plan) ↔
      UtilityIntegrable S.inducedBayesianGame.utility who
        (S.inducedBayesianGame.toForm.play plan) := by
  let f : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      B.signature.Outcome :=
    fun rec => (rec.1, fun i => plan i (rec.1 i, rec.2 i))
  let g : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      S.inducedBayesianGame.signature.Outcome :=
    fun rec =>
      ((fun i => (rec.1 i, rec.2 i)),
        S.inducedBayesianGame.actionsOf plan
          (fun i => (rec.1 i, rec.2 i)))
  have hleft : S.outcomeLaw plan = S.law.map f := rfl
  have hright :
      S.inducedBayesianGame.toForm.play plan = S.law.map g := by
    rw [S.inducedBayesianGame.toForm_play, PMF.map_comp]
    rfl
  rw [hleft, hright]
  exact utilityIntegrable_two_maps_iff S.law f g B.utility
    S.inducedBayesianGame.utility who (fun rec => rfl)

omit [DecidableEq ι] in
theorem recommendedValue_outcomeLaw
    (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) (who : ι) :
    B.recommendedValue (S.outcomeLaw plan) who =
      expectedUtility S.inducedBayesianGame.utility who
        (S.inducedBayesianGame.toForm.play plan) := by
  let f : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      B.signature.Outcome :=
    fun rec => (rec.1, fun i => plan i (rec.1 i, rec.2 i))
  let g : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      S.inducedBayesianGame.signature.Outcome :=
    fun rec =>
      ((fun i => (rec.1 i, rec.2 i)),
        S.inducedBayesianGame.actionsOf plan
          (fun i => (rec.1 i, rec.2 i)))
  have hleft : S.outcomeLaw plan = S.law.map f := rfl
  have hright :
      S.inducedBayesianGame.toForm.play plan = S.law.map g := by
    rw [S.inducedBayesianGame.toForm_play, PMF.map_comp]
    rfl
  calc
    B.recommendedValue (S.outcomeLaw plan) who =
        expectedUtility B.utility who (S.law.map f) :=
      expectedUtility_congr_law B.utility who hleft
    _ = expectedUtility S.inducedBayesianGame.utility who (S.law.map g) :=
      expectedUtility_two_maps S.law f g B.utility
        S.inducedBayesianGame.utility who (fun rec => rfl)
    _ = expectedUtility S.inducedBayesianGame.utility who
        (S.inducedBayesianGame.toForm.play plan) :=
      expectedUtility_congr_law S.inducedBayesianGame.utility who
        hright.symm

theorem deviatingValue_outcomeLaw_integrable_iff
    (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) (who : ι)
    (deviation : B.ObedienceDeviation who) :
    UtilityIntegrable B.utility who
        ((S.outcomeLaw plan).map (B.recordDeviation who deviation)) ↔
      UtilityIntegrable S.inducedBayesianGame.utility who
        (S.inducedBayesianGame.toForm.play
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed)))) := by
  let f : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      B.signature.Outcome :=
    fun rec =>
      B.recordDeviation who deviation
        (rec.1, fun i => plan i (rec.1 i, rec.2 i))
  let g : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      S.inducedBayesianGame.signature.Outcome :=
    fun rec =>
      ((fun i => (rec.1 i, rec.2 i)),
        S.inducedBayesianGame.actionsOf
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed)))
          (fun i => (rec.1 i, rec.2 i)))
  have hleft :
      (S.outcomeLaw plan).map (B.recordDeviation who deviation) =
        S.law.map f := by
    rw [outcomeLaw, PMF.map_comp]
    rfl
  have hright :
      S.inducedBayesianGame.toForm.play
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed))) =
        S.law.map g := by
    rw [S.inducedBayesianGame.toForm_play, PMF.map_comp]
    rfl
  rw [hleft, hright]
  apply utilityIntegrable_two_maps_iff S.law f g B.utility
    S.inducedBayesianGame.utility who
  intro rec
  simp only [f, g, BayesianGame.utility,
    inducedBayesianGame, recordDeviation, applyObedienceDeviation,
    BayesianGame.actionsOf_update]
  rfl

theorem deviatingValue_outcomeLaw
    (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) (who : ι)
    (deviation : B.ObedienceDeviation who) :
    B.deviatingValue (S.outcomeLaw plan) who deviation =
      expectedUtility S.inducedBayesianGame.utility who
        (S.inducedBayesianGame.toForm.play
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed)))) := by
  let f : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      B.signature.Outcome :=
    fun rec =>
      B.recordDeviation who deviation
        (rec.1, fun i => plan i (rec.1 i, rec.2 i))
  let g : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      S.inducedBayesianGame.signature.Outcome :=
    fun rec =>
      ((fun i => (rec.1 i, rec.2 i)),
        S.inducedBayesianGame.actionsOf
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed)))
          (fun i => (rec.1 i, rec.2 i)))
  have hleft :
      (S.outcomeLaw plan).map (B.recordDeviation who deviation) =
        S.law.map f := by
    rw [outcomeLaw, PMF.map_comp]
    rfl
  have hright :
      S.inducedBayesianGame.toForm.play
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed))) =
        S.law.map g := by
    rw [S.inducedBayesianGame.toForm_play, PMF.map_comp]
    rfl
  have heq : ∀ rec, B.utility (f rec) who =
      S.inducedBayesianGame.utility (g rec) who := by
    intro rec
    simp only [f, g, BayesianGame.utility,
      inducedBayesianGame, recordDeviation, applyObedienceDeviation,
      BayesianGame.actionsOf_update]
    rfl
  calc
    B.deviatingValue (S.outcomeLaw plan) who deviation =
        expectedUtility B.utility who (S.law.map f) :=
      expectedUtility_congr_law B.utility who hleft
    _ = expectedUtility S.inducedBayesianGame.utility who (S.law.map g) :=
      expectedUtility_two_maps S.law f g B.utility
        S.inducedBayesianGame.utility who heq
    _ = expectedUtility S.inducedBayesianGame.utility who
        (S.inducedBayesianGame.toForm.play
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed)))) :=
      expectedUtility_congr_law S.inducedBayesianGame.utility who
        hright.symm

/-- Obedience in the original recommendation law is exactly the corresponding
contingent-plan comparison in the induced private-signal game. -/
theorem outcomeLaw_preference_iff (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature) (who : ι)
    (deviation : B.ObedienceDeviation who) :
    euPreference B.utility who (S.outcomeLaw plan)
        ((S.outcomeLaw plan).map (B.recordDeviation who deviation)) ↔
      euPreference S.inducedBayesianGame.utility who
        (S.inducedBayesianGame.toForm.play plan)
        (S.inducedBayesianGame.toForm.play
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed)))) := by
  let f₁ : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      B.signature.Outcome :=
    fun rec => (rec.1, fun i => plan i (rec.1 i, rec.2 i))
  let f₂ : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      B.signature.Outcome :=
    fun rec =>
      B.recordDeviation who deviation (f₁ rec)
  let g₁ : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      S.inducedBayesianGame.signature.Outcome :=
    fun rec =>
      ((fun i => (rec.1 i, rec.2 i)),
        S.inducedBayesianGame.actionsOf plan
          (fun i => (rec.1 i, rec.2 i)))
  let g₂ : ((∀ i, B.Ty i) × (∀ i, Signal i)) →
      S.inducedBayesianGame.signature.Outcome :=
    fun rec =>
      ((fun i => (rec.1 i, rec.2 i)),
        S.inducedBayesianGame.actionsOf
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed)))
          (fun i => (rec.1 i, rec.2 i)))
  have hleft : S.outcomeLaw plan = S.law.map f₁ := rfl
  have hleftDev :
      (S.outcomeLaw plan).map (B.recordDeviation who deviation) =
        S.law.map f₂ := by
    rw [hleft, PMF.map_comp]
    rfl
  have hright :
      S.inducedBayesianGame.toForm.play plan = S.law.map g₁ := by
    rw [S.inducedBayesianGame.toForm_play, PMF.map_comp]
    rfl
  have hrightDev :
      S.inducedBayesianGame.toForm.play
          (Profile.update plan who
            (fun observed => deviation observed.1 (plan who observed))) =
        S.law.map g₂ := by
    rw [S.inducedBayesianGame.toForm_play, PMF.map_comp]
    rfl
  rw [hleftDev, hleft, hright, hrightDev]
  apply euPreference_two_maps_iff S.law f₁ f₂ g₁ g₂ B.utility
    S.inducedBayesianGame.utility who
  · intro rec
    rfl
  · intro rec
    simp only [f₂, f₁, g₂, BayesianGame.utility,
      inducedBayesianGame, recordDeviation, applyObedienceDeviation,
      BayesianGame.actionsOf_update]
    rfl

theorem isBayesCorrelatedEq_outcomeLaw_of_isNash
    (S : InformationStructure B Signal)
    (plan : Profile S.inducedBayesianGame.signature)
    (hNash :
      IsNash S.inducedBayesianGame.toForm
        (euPreference S.inducedBayesianGame.utility) plan) :
    B.IsBayesCorrelatedEq (S.outcomeLaw plan) := by
  refine ⟨S.outcomeLaw_isBayesPlausible plan, ?_⟩
  intro who deviation
  apply (S.outcomeLaw_preference_iff plan who deviation).2
  exact
    (isNash_iff
      (F := S.inducedBayesianGame.toForm)
      (weaklyPrefers := euPreference S.inducedBayesianGame.utility)
      plan).1 hNash who
      (fun observed => deviation observed.1 (plan who observed))

theorem followActionSignal_isNash_of_isBayesCorrelatedEq
    {recommendation : B.RecommendationLaw}
    (hBCE : B.IsBayesCorrelatedEq recommendation) :
    let S := ofRecommendation recommendation hBCE.1
    IsNash S.inducedBayesianGame.toForm
      (euPreference S.inducedBayesianGame.utility)
      S.followActionSignal := by
  let S := ofRecommendation recommendation hBCE.1
  show IsNash S.inducedBayesianGame.toForm
    (euPreference S.inducedBayesianGame.utility) S.followActionSignal
  rw [isNash_iff]
  intro who replacement
  let deviation : B.ObedienceDeviation who :=
    fun ownType recommended => replacement (ownType, recommended)
  have hobey := hBCE.2 who deviation
  have houtcome : S.outcomeLaw S.followActionSignal = recommendation :=
    outcomeLaw_followActionSignal recommendation hBCE.1
  have hupdate :
      Profile.update S.followActionSignal who
          (fun observed =>
            deviation observed.1 (S.followActionSignal who observed)) =
        Profile.update S.followActionSignal who replacement := by
    congr 1
  rw [← houtcome] at hobey
  have hinduced :=
    (S.outcomeLaw_preference_iff S.followActionSignal who deviation).1 hobey
  rwa [hupdate] at hinduced

theorem exists_informationStructure_isNash_outcomeLaw
    {recommendation : B.RecommendationLaw}
    (hBCE : B.IsBayesCorrelatedEq recommendation) :
    ∃ S : InformationStructure B B.Act,
      ∃ plan : Profile S.inducedBayesianGame.signature,
        IsNash S.inducedBayesianGame.toForm
            (euPreference S.inducedBayesianGame.utility) plan ∧
          S.outcomeLaw plan = recommendation := by
  let S := ofRecommendation recommendation hBCE.1
  exact ⟨S, S.followActionSignal,
    followActionSignal_isNash_of_isBayesCorrelatedEq hBCE,
    outcomeLaw_followActionSignal recommendation hBCE.1⟩

end InformationStructure

end BayesianGame

end GameTheory
