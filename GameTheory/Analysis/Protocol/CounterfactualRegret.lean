/-
# Counterfactual regret and Bayes continuation gain

Counterfactual continuation values reuse canonical Protocol histories,
behavioral continuations, and Bayes beliefs.  Exact scaling and sign theorems
connect their regret to ordinary behavioral-policy deviation gains.  Common
own reach is a named weaker certificate; perfect recall discharges it.
-/

import GameTheory.Analysis.Protocol.CounterfactualReach

noncomputable section

namespace GameTheory.Protocol

open GameTheory Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

/-- Continuation utility from one supplied history after replacing one
player's whole behavioral policy. -/
def behavioralContinuationValue [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) (history : E.History) : ℝ :=
  (M.runBehavioralFrom
    (Profile.update (sig := M.behavioralSignature)
      strategy who alternative) fuel history).expect payoff

/-- A continuation value at an information site weighted by everybody except
the focal player's reach. -/
def counterfactualContinuationValue [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) : ℝ :=
  ∑ history : M.InformationHistory who site.1,
    M.counterfactualReachProbability strategy who history.1.trace *
      behavioralContinuationValue M strategy who alternative payoff fuel history.1

/-- Counterfactual regret of a whole continuation-policy replacement. Positive
values mean that the replacement improves the counterfactual continuation
value at the information site. -/
def counterfactualRegret [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (alternative : M.BehavioralPolicy who) : ℝ :=
  counterfactualContinuationValue M strategy who site alternative payoff fuel -
    counterfactualContinuationValue M strategy who site (strategy who) payoff fuel

/-- Counterfactual regret for committing to one pure choice at the selected
information site while preserving the behavioral policy everywhere else. -/
def counterfactualActionRegret [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1) : ℝ :=
  counterfactualRegret M strategy who site payoff fuel
    ((strategy who).commit site.1 choice)

/-- The ordinary continuation value under the canonical Bayes belief at a
positive-mass information site. -/
def bayesContinuationValue [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) : ℝ :=
  (M.bayesBelief strategy who site hantichain hmass).expect fun history =>
    behavioralContinuationValue M strategy who alternative payoff fuel history.1

/-- Probability of an own-action record under one behavioral policy.  Inactive
steps are absent because their only legal choice has probability one. -/
def ownPlayReachProbability {who : ι} (policy : M.BehavioralPolicy who) :
    List (M.InfoState who × E.Action who) → ℝ
  | [] => 1
  | (info, action) :: prior =>
      (FinDist.map (fun choice => choice.1) (policy info)).prob (some action) *
        ownPlayReachProbability policy prior

private theorem playerStepProb_eq_one_of_none
    (strategy : (player : ι) → M.BehavioralPolicy player) (who : ι)
    {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (hchoice : joint.1 who = none) :
    M.playerStepProb strategy who trace joint = 1 := by
  classical
  have hinactive : ¬ E.active state who := by
    have hlegal := E.legalOption_of_legal joint.2 who
    simpa [hchoice, LegalOption] using hlegal
  letI : Subsingleton (M.Choice who (M.infoOf who trace)) :=
    ⟨fun first second => by
      apply Subtype.ext
      have hfirst := (M.menu_adequate who trace first.1).mp first.2
      have hsecond := (M.menu_adequate who trace second.1).mp second.2
      rw [LegalOption.eq_none_of_inactive first.1 hfirst hinactive,
        LegalOption.eq_none_of_inactive second.1 hsecond hinactive]⟩
  unfold Protocol.InformationModel.playerStepProb
  rw [FinDist.eq_pure_of_subsingleton
    (strategy who (M.infoOf who trace))
    (M.choicesOfLegal trace joint who)]
  exact FinDist.prob_pure_self _

/-- The recursive focal reach is exactly the probability of the canonical
own-action record.  Consequently it ignores chance, opponents, and forced
inactive coordinates. -/
theorem playerReachProbability_eq_ownPlayReachProbability
    (strategy : (player : ι) → M.BehavioralPolicy player) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    M.playerReachProbability strategy who trace =
      ownPlayReachProbability M (strategy who) (M.ownPlay who trace) := by
  classical
  induction trace with
  | start => rfl
  | @extend source target prior joint isLegal realized ih =>
      show
        M.playerReachProbability strategy who prior *
            M.playerStepProb strategy who prior ⟨joint, isLegal⟩ =
          ownPlayReachProbability M (strategy who)
            (M.ownPlay who (prior.extend joint isLegal realized))
      rw [InfoSignals.ownPlay_extend, ih]
      cases hchoice : joint who with
      | none =>
          rw [playerStepProb_eq_one_of_none M strategy who prior
            ⟨joint, isLegal⟩ hchoice, mul_one]
      | some action =>
          rw [ownPlayReachProbability]
          have hstep :
              M.playerStepProb strategy who prior ⟨joint, isLegal⟩ =
                (FinDist.map (fun choice => choice.1)
                  (strategy who (M.infoOf who prior))).prob (some action) := by
            unfold Protocol.InformationModel.playerStepProb
            symm
            have hmap := FinDist.prob_map_of_injective
              (fun choice : M.Choice who (M.infoOf who prior) => choice.1)
              Subtype.val_injective
              (strategy who (M.infoOf who prior))
              (M.choicesOfLegal prior ⟨joint, isLegal⟩ who)
            simpa [Protocol.InformationModel.choicesOfLegal, hchoice] using hmap
          rw [hstep]
          exact mul_comm _ _

/-- Perfect recall discharges the common-own-reach premise used by the
counterfactual/Bayes normalization theorem. -/
theorem playerReachProbability_eq_of_perfectRecall
    (hrecall : M.PerfectRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player) (who : ι)
    {firstState secondState : E.State}
    (first : E.Trace firstState) (second : E.Trace secondState)
    (hinfo : M.infoOf who first = M.infoOf who second) :
    M.playerReachProbability strategy who first =
      M.playerReachProbability strategy who second := by
  rw [playerReachProbability_eq_ownPlayReachProbability M,
    playerReachProbability_eq_ownPlayReachProbability M,
    hrecall who first second hinfo]

/-- Counterfactual reach is nonnegative because every recursive factor is a
finite product of distribution masses. -/
theorem counterfactualReachProbability_nonneg
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    0 ≤ M.counterfactualReachProbability strategy who trace := by
  classical
  induction trace with
  | start => norm_num [Protocol.InformationModel.counterfactualReachProbability]
  | @extend source target prior joint isLegal realized ih =>
      rw [Protocol.InformationModel.counterfactualReachProbability]
      apply mul_nonneg ih
      unfold Protocol.InformationModel.counterfactualStepProb
        Protocol.InformationModel.opponentsStepProb
      apply mul_nonneg
      · exact Finset.prod_nonneg fun other _ => FinDist.prob_nonneg _ _
      · exact FinDist.prob_nonneg _ _

/-- Named certificate that the focal player's own reach is constant on one
information fiber.  Perfect recall implies it, while absent-minded models may
establish it directly at selected sites. -/
def CommonPlayerReachAt
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who) : Prop :=
  ∃ reach : ℝ, ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = reach

/-- Perfect recall supplies common own reach at every decision information
site. -/
theorem commonPlayerReachAt_of_perfectRecall
    (hrecall : M.PerfectRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who) :
    CommonPlayerReachAt M strategy who site := by
  obtain ⟨reference, _hnonterminal, _haction⟩ := site.2
  refine ⟨M.playerReachProbability strategy who reference.1.trace, ?_⟩
  intro history
  exact playerReachProbability_eq_of_perfectRecall M hrecall strategy who
    history.1.trace reference.1.trace (history.2.trans reference.2.symm)

/-- Positive information mass forces the certified common own reach to be
positive; a zero-own-reach fiber cannot have positive actual mass. -/
theorem commonPlayerReach_pos
    [Fintype ι] [DecidableEq ι]
    {strategy : (player : ι) → M.BehavioralPolicy player}
    {who : ι} {site : M.InformationSite who}
    [Fintype (M.InformationHistory who site.1)]
    (reach : ℝ)
    (hcommon : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = reach)
    (hmass : 0 < M.informationMass strategy who site) :
    0 < reach := by
  unfold Protocol.InformationModel.informationMass at hmass
  obtain ⟨history, _hmemory, hhistory⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun history _ => FinDist.prob_nonneg
        (M.runBehavioral strategy history.1.trace.length) history.1)).mp hmass
  rw [M.historyReachProbability_eq_player_mul_counterfactual
    strategy who history.1.trace, hcommon history] at hhistory
  exact pos_of_mul_pos_left hhistory
    (counterfactualReachProbability_nonneg M strategy who history.1.trace)

/-- If the focal player's own reach is common across one information fiber,
the canonical Bayes continuation value and the counterfactual value differ by
exactly the expected normalization factors. -/
theorem informationMass_mul_bayesContinuationValue_eq
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.informationMass strategy who site *
        bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel =
      ownReach *
        counterfactualContinuationValue M strategy who site alternative payoff fuel := by
  classical
  unfold bayesContinuationValue counterfactualContinuationValue
  rw [FinDist.expect_eq_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro history _
  rw [M.bayesBelief_prob strategy who site hantichain hmass history,
    M.historyReachProbability_eq_player_mul_counterfactual
      strategy who history.1.trace,
    hown history]
  field_simp [hmass.ne']

/-- The scaled ordinary behavioral-policy deviation gain is exactly the scaled
counterfactual regret. This is the theorem-level consumer missing from a bare
counterfactual-regret definition. -/
theorem informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.informationMass strategy who site *
        (bayesContinuationValue M strategy who site hantichain hmass
            alternative payoff fuel -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff fuel) =
      ownReach *
        counterfactualRegret M strategy who site payoff fuel alternative := by
  rw [counterfactualRegret, mul_sub, mul_sub,
    informationMass_mul_bayesContinuationValue_eq M strategy who site
      hantichain hmass ownReach hown alternative payoff fuel,
    informationMass_mul_bayesContinuationValue_eq M strategy who site
      hantichain hmass ownReach hown (strategy who) payoff fuel]

/-- Action-local specialization of the exact deviation-gain decomposition. -/
theorem informationMass_mul_bayesActionGain_eq_ownReach_mul_counterfactualActionRegret
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (choice : M.Choice who site.1)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.informationMass strategy who site *
        (bayesContinuationValue M strategy who site hantichain hmass
            ((strategy who).commit site.1 choice) payoff fuel -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff fuel) =
      ownReach *
        counterfactualActionRegret M strategy who site payoff fuel choice := by
  exact informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
    strategy who site hantichain hmass ownReach hown
      ((strategy who).commit site.1 choice) payoff fuel

/-- With positive common own reach, counterfactual regret detects exactly the
same profitable deviations as the ordinary canonical Bayes continuation. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ) (hownpos : 0 < ownReach)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    0 < counterfactualRegret M strategy who site payoff fuel alternative ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel := by
  have hscaled :=
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
      strategy who site hantichain hmass ownReach hown alternative payoff fuel
  constructor
  · intro hregret
    have hpositive : 0 < ownReach *
        counterfactualRegret M strategy who site payoff fuel alternative :=
      mul_pos hownpos hregret
    rw [← hscaled] at hpositive
    exact (mul_pos_iff_of_pos_left hmass).mp hpositive
  · intro hgain
    have hpositive : 0 < M.informationMass strategy who site *
        (bayesContinuationValue M strategy who site hantichain hmass
            alternative payoff fuel -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff fuel) :=
      mul_pos hmass hgain
    rw [hscaled] at hpositive
    exact (mul_pos_iff_of_pos_left hownpos).mp hpositive

/-- Certificate-facing exact deviation-gain decomposition. -/
theorem informationMass_mul_bayesGain_eq_commonReach_mul_counterfactualRegret
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (common : CommonPlayerReachAt M strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    ∃ reach : ℝ,
      M.informationMass strategy who site *
          (bayesContinuationValue M strategy who site hantichain hmass
              alternative payoff fuel -
            bayesContinuationValue M strategy who site hantichain hmass
              (strategy who) payoff fuel) =
        reach *
          counterfactualRegret M strategy who site payoff fuel alternative := by
  rcases common with ⟨reach, hcommon⟩
  exact ⟨reach,
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
      strategy who site hantichain hmass reach hcommon
        alternative payoff fuel⟩

/-- At any positive-mass site carrying common own reach, counterfactual regret
detects exactly the profitable canonical Bayes continuation deviations. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos_of_commonReach
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (common : CommonPlayerReachAt M strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    0 < counterfactualRegret M strategy who site payoff fuel alternative ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel := by
  rcases common with ⟨reach, hcommon⟩
  exact counterfactualRegret_pos_iff_bayesGain_pos M strategy who site
    hantichain hmass reach
      (commonPlayerReach_pos M reach hcommon hmass)
      hcommon alternative payoff fuel

/-- Familiar perfect-recall specialization: no fiberwise reach proof remains
at the call site. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos_of_perfectRecall
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.PerfectRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    0 < counterfactualRegret M strategy who site payoff fuel alternative ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel :=
  counterfactualRegret_pos_iff_bayesGain_pos_of_commonReach M strategy who site
    hantichain hmass
    (commonPlayerReachAt_of_perfectRecall M hrecall strategy who site)
    alternative payoff fuel

/-- Perfect-recall action-local specialization.  Positive counterfactual
action regret is exactly an ordinary profitable pure commitment at the
canonical Bayes continuation game. -/
theorem counterfactualActionRegret_pos_iff_bayesActionGain_pos_of_perfectRecall
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.PerfectRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (choice : M.Choice who site.1)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    0 < counterfactualActionRegret M strategy who site payoff fuel choice ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          ((strategy who).commit site.1 choice) payoff fuel -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel := by
  exact counterfactualRegret_pos_iff_bayesGain_pos_of_perfectRecall M hrecall
    strategy who site hantichain hmass
      ((strategy who).commit site.1 choice) payoff fuel

end InformationModel

end GameTheory.Protocol
