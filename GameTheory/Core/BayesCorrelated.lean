/-
# Finite Bayes-correlated equilibrium

A direct recommendation law jointly distributes true type profiles and
recommended action profiles. It is Bayes plausible when its type marginal is
the common prior, and obedient when no player gains from a deviation depending
only on that player's own type and recommendation.

The main theorem pushes a Bayes-Nash plan from a finite private-signal
information structure to an obedient recommendation law in the original game.
Bayes-Nash remains ordinary `IsNash` of the induced Bayesian game form.

Primary reference: D. Bergemann and S. Morris, “Bayes Correlated Equilibrium
and the Comparison of Information Structures in Games,” *Theoretical
Economics* 11 (2016).
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

/-- The recommendation records in which a player observes one particular
own-type/recommended-action pair. -/
def obedienceEvent (B : BayesianGame.{uι, ut, ua} ι) (who : ι)
    (ownType : B.Ty who) (recommended : B.Act who) :
    Set ((∀ i, B.Ty i) × Profile B.actionSignature) :=
  (fun rec => (rec.1 who, rec.2 who)) ⁻¹' {(ownType, recommended)}

/-- Interim payoff from obeying on a positive-probability observation cell. -/
def interimRecommendedValue (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι)
    (ownType : B.Ty who) (recommended : B.Act who)
    (hObserved :
      ∃ rec ∈ B.obedienceEvent who ownType recommended,
        rec ∈ recommendation.support) : ℝ :=
  (recommendation.condOn (B.obedienceEvent who ownType recommended) hObserved).expect
    fun rec => B.payoff rec.1 rec.2 who

/-- Interim payoff from replacing one recommendation on a positive-probability
observation cell. -/
def interimDeviatingValue (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) (who : ι)
    (ownType : B.Ty who) (recommended replacement : B.Act who)
    (hObserved :
      ∃ rec ∈ B.obedienceEvent who ownType recommended,
        rec ∈ recommendation.support) : ℝ :=
  (recommendation.condOn (B.obedienceEvent who ownType recommended) hObserved).expect
    fun rec => B.payoff rec.1 (Profile.update rec.2 who replacement) who

/-- **Interim obedience characterizes finite Bayes-correlated equilibrium.**
Bayes plausibility plus every positive own-type/recommendation cell preferring
obedience to a fixed replacement is equivalent to the existing ex-ante
deviation-map definition.

The reverse implication disintegrates the recommendation law by the observed
pair.  Consequently the result needs neither all-player type finiteness nor an
additional posterior representation. -/
theorem isBayesCorrelatedEq_iff_interim_obedience
    (B : BayesianGame.{uι, ut, ua} ι)
    (recommendation : B.RecommendationLaw) :
    B.IsBayesCorrelatedEq recommendation ↔
      B.IsBayesPlausible recommendation ∧
        ∀ who ownType recommended replacement,
          ∀ hObserved :
              ∃ rec ∈ B.obedienceEvent who ownType recommended,
                rec ∈ recommendation.support,
            B.interimDeviatingValue recommendation who ownType recommended
                replacement hObserved ≤
              B.interimRecommendedValue recommendation who ownType recommended
                hObserved := by
  classical
  constructor
  · rintro ⟨hplausible, hobedient⟩
    refine ⟨hplausible, ?_⟩
    intro who ownType recommended replacement hObserved
    let deviation : B.ObedienceDeviation who := fun candidateType candidateAction =>
      if candidateType = ownType ∧ candidateAction = recommended then
        replacement
      else candidateAction
    have hglobal := hobedient who deviation
    unfold deviatingValue recommendedValue at hglobal
    have hconditional := FinDist.expect_condOn_le_of_expect_le_of_eq_off
      recommendation (B.obedienceEvent who ownType recommended) hObserved
      hglobal (by
        intro rec _ hnot
        have hpair : ¬(rec.1 who = ownType ∧ rec.2 who = recommended) := by
          simpa only [obedienceEvent, Set.mem_preimage, Set.mem_singleton_iff,
            Prod.mk.injEq] using hnot
        simp [applyObedienceDeviation, deviation, hpair,
          Profile.update_eq_self])
    unfold interimDeviatingValue interimRecommendedValue
    refine le_trans ?_ hconditional
    apply le_of_eq
    apply FinDist.expect_congr
    intro rec hrec
    have hcell :=
      (FinDist.support_condOn recommendation
        (B.obedienceEvent who ownType recommended) hObserved hrec).1
    have hpair : rec.1 who = ownType ∧ rec.2 who = recommended := by
      simpa only [obedienceEvent, Set.mem_preimage, Set.mem_singleton_iff,
        Prod.mk.injEq] using hcell
    simp [applyObedienceDeviation, deviation, hpair]
  · rintro ⟨hplausible, hinterim⟩
    refine ⟨hplausible, ?_⟩
    intro who deviation
    unfold deviatingValue recommendedValue
    have hdecompose := FinDist.eq_bind_condOnFibre recommendation
      (fun rec => (rec.1 who, rec.2 who))
    conv_lhs => rw [hdecompose, FinDist.expect_bind]
    conv_rhs => rw [hdecompose, FinDist.expect_bind]
    apply FinDist.expect_mono
    intro observed hObservedMap
    rw [FinDist.support_map] at hObservedMap
    obtain ⟨witness, hwitness, rfl⟩ := hObservedMap
    have hObserved :
        ∃ rec ∈ B.obedienceEvent who (witness.1 who) (witness.2 who),
          rec ∈ recommendation.support :=
      ⟨witness, Set.mem_preimage.mpr (Set.mem_singleton _), hwitness⟩
    have hfibre :
        ∃ rec ∈ (fun rec => (rec.1 who, rec.2 who)) ⁻¹'
            {(witness.1 who, witness.2 who)},
          rec ∈ recommendation.support :=
      ⟨witness, Set.mem_preimage.mpr (Set.mem_singleton _), hwitness⟩
    rw [FinDist.condOnFibre, dif_pos hfibre]
    calc
      (recommendation.condOn
          (B.obedienceEvent who (witness.1 who) (witness.2 who))
          hObserved).expect
          (fun rec => B.payoff rec.1
            (B.applyObedienceDeviation rec.1 rec.2 who deviation) who) =
          B.interimDeviatingValue recommendation who (witness.1 who)
            (witness.2 who) (deviation (witness.1 who) (witness.2 who))
            hObserved := by
        unfold interimDeviatingValue
        apply FinDist.expect_congr
        intro rec hrec
        have hcell :=
          (FinDist.support_condOn recommendation
            (B.obedienceEvent who (witness.1 who) (witness.2 who))
            hObserved hrec).1
        have hpair :
            rec.1 who = witness.1 who ∧ rec.2 who = witness.2 who := by
          simpa only [obedienceEvent, Set.mem_preimage, Set.mem_singleton_iff,
            Prod.mk.injEq] using hcell
        simp [applyObedienceDeviation, hpair]
      _ ≤ B.interimRecommendedValue recommendation who (witness.1 who)
            (witness.2 who) hObserved :=
        hinterim who (witness.1 who) (witness.2 who)
          (deviation (witness.1 who) (witness.2 who)) hObserved
      _ = (recommendation.condOn
          (B.obedienceEvent who (witness.1 who) (witness.2 who))
          hObserved).expect (fun rec => B.payoff rec.1 rec.2 who) := rfl

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
