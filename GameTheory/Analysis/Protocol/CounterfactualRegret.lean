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

/-- At a history in the selected information state, installing a local law
commutes with the one-step independent product: equivalently, first draw the
selected player's choice and then use the corresponding pure commitment.

This is a law identity, not merely an expectation calculation, and it needs
only the finite player product already used by behavioral execution. -/
theorem behavioralJoint_update_withLaw_eq_bind
    [Fintype ι] [DecidableEq ι]
    (profile : (i : ι) → M.BehavioralPolicy i) (who : ι)
    (policy : M.BehavioralPolicy who)
    [DecidableEq (M.InfoState who)]
    (info : M.InfoState who) (law : FinDist (M.Choice who info))
    {state : E.State} (trace : E.Trace state) (hterm : ¬ E.terminal state)
    (hinfo : M.infoOf who trace = info) :
    M.behavioralJoint
        (Profile.update (sig := M.behavioralSignature)
          profile who (policy.withLaw info law))
        trace hterm =
      law.bind fun choice =>
        M.behavioralJoint
          (Profile.update (sig := M.behavioralSignature)
            profile who (policy.commit info choice))
          trace hterm := by
  subst info
  let jointOf :
      ((i : ι) → M.Choice i (M.infoOf i trace)) →
        { joint : (i : ι) → Option (E.Action i) // E.Legal state joint } :=
    fun draws => ⟨fun i => (draws i).1,
      ExecutionProtocol.legal_of_legalOption hterm fun i =>
        (M.menu_adequate i trace (draws i).1).mp (draws i).2⟩
  let otherLaws :
      (other : {other : ι // other ≠ who}) →
        FinDist (M.Choice other.1 (M.infoOf other.1 trace)) :=
    fun other => profile other.1 (M.infoOf other.1 trace)
  let split :=
    Equiv.piSplitAt who fun i => M.Choice i (M.infoOf i trace)
  have hwithWho :
      Profile.update (sig := M.behavioralSignature) profile who
          (policy.withLaw (M.infoOf who trace) law) who
            (M.infoOf who trace) = law := by
    rw [Profile.update_same, BehavioralPolicy.withLaw_self]
  have hwithOthers :
      (fun other : {other : ι // other ≠ who} =>
          Profile.update (sig := M.behavioralSignature) profile who
              (policy.withLaw (M.infoOf who trace) law)
            other.1 (M.infoOf other.1 trace)) =
        otherLaws := by
    funext other
    rw [Profile.update_of_ne _ _ other.2]
  have hcommitWho (choice : M.Choice who (M.infoOf who trace)) :
      Profile.update (sig := M.behavioralSignature) profile who
          (policy.commit (M.infoOf who trace) choice) who
            (M.infoOf who trace) = FinDist.pure choice := by
    rw [Profile.update_same, BehavioralPolicy.commit_self]
  have hcommitOthers (choice : M.Choice who (M.infoOf who trace)) :
      (fun other : {other : ι // other ≠ who} =>
          Profile.update (sig := M.behavioralSignature) profile who
              (policy.commit (M.infoOf who trace) choice)
            other.1 (M.infoOf other.1 trace)) =
        otherLaws := by
    funext other
    rw [Profile.update_of_ne _ _ other.2]
  unfold behavioralJoint
  rw [← FinDist.map_bind]
  apply congrArg (FinDist.map jointOf)
  rw [FinDist.pi_eq_map_product who, hwithWho, hwithOthers]
  have hbranches :
      (fun choice : M.Choice who (M.infoOf who trace) =>
          FinDist.pi fun i =>
            Profile.update (sig := M.behavioralSignature) profile who
                (policy.commit (M.infoOf who trace) choice) i
              (M.infoOf i trace)) =
        fun choice =>
          FinDist.map split.symm
            (FinDist.product (FinDist.pure choice)
              (FinDist.pi otherLaws)) := by
    funext choice
    rw [FinDist.pi_eq_map_product who, hcommitWho choice,
      hcommitOthers choice]
  rw [hbranches, FinDist.product, FinDist.map_bind]
  refine FinDist.bind_congr fun choice _ => ?_
  rw [FinDist.product, FinDist.pure_bind, FinDist.map_comp]

/-- After leaving a genuine decision at `info`, a persistent installed law and
one of its pure commitments are observationally identical to the remaining
run when that information state cannot matter twice. -/
theorem withLaw_eq_commit_after_actsOnce
    (hactsOnce : M.ActsOnceWhereItMatters)
    {who : ι}
    (policy : M.BehavioralPolicy who)
    [DecidableEq (M.InfoState who)]
    (info : M.InfoState who) (law : FinDist (M.Choice who info))
    (choice : M.Choice who info)
    {h : E.History} (hinfo : M.infoOf who h.trace = info)
    (hactive : E.active h.state who)
    {joint : ∀ i, Option (E.Action i)} (isLegal : E.Legal h.state joint)
    {target : E.State}
    (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    {fuel : ℕ} (later : E.History)
    (hreach : ExecutionProtocol.ReachesWithin E fuel
      (h.extend isLegal realized) later)
    (hlater : ¬ E.terminal later.state) :
    policy.withLaw info law (M.infoOf who later.trace) =
      policy.commit info choice (M.infoOf who later.trace) := by
  subst info
  by_cases hne : M.infoOf who later.trace ≠ M.infoOf who h.trace
  · rw [BehavioralPolicy.withLaw_of_ne _ _ _ hne,
      BehavioralPolicy.commit_of_ne _ _ _ hne]
  push Not at hne
  by_cases hactiveLater : E.active later.state who
  · have hdisj :
        M.infoOf who later.trace ≠ M.infoOf who h.trace ∨
          Subsingleton (M.Choice who (M.infoOf who h.trace)) := by
      obtain ⟨laterJoint, hlaterJoint⟩ := E.progress later.state hlater
      have hlaterLegal : E.Legal later.state laterJoint :=
        ⟨hlater, hlaterJoint⟩
      obtain ⟨laterTarget, hlaterRealized⟩ :=
        (E.step later.state
          ⟨laterJoint, hlaterLegal⟩).support_nonempty
      obtain ⟨_, hsome⟩ := LegalOption.exists_eq_some_of_active
        (joint who) (ExecutionProtocol.legalOption_of_legal isLegal who)
          hactive
      obtain ⟨_, hlaterSome⟩ := LegalOption.exists_eq_some_of_active
        (laterJoint who)
        (ExecutionProtocol.legalOption_of_legal hlaterLegal who)
          hactiveLater
      exact M.infoOf_ne_or_subsingleton_of_actsOnce hactsOnce who
        isLegal realized (by rw [hsome]; rfl) hreach hlaterLegal
          hlaterRealized (by rw [hlaterSome]; rfl)
    rcases hdisj with hne' | hsubsingleton
    · exact absurd hne hne'
    · rw [hne, BehavioralPolicy.withLaw_self,
        BehavioralPolicy.commit_self]
      exact FinDist.eq_pure_of_subsingleton law choice
  · exact M.behavioral_eq_of_not_active _ _ later.trace hactiveLater

/-- Behavioral continuation from a nonterminal selected decision is affine in
the law installed there.  No global finiteness of information states is used:
the proof factors only the current finite player product, then uses no-revisit
to make the selected coordinate invisible downstream. -/
theorem runBehavioralFrom_update_withLaw_eq_bind
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (profile : (i : ι) → M.BehavioralPolicy i) (who : ι)
    (policy : M.BehavioralPolicy who)
    [DecidableEq (M.InfoState who)]
    (info : M.InfoState who) (law : FinDist (M.Choice who info))
    (h : E.History) (hinfo : M.infoOf who h.trace = info)
    (hterm : ¬ E.terminal h.state) (hactive : E.active h.state who)
    (fuel : ℕ) :
    M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) profile who
          (policy.withLaw info law)) (fuel + 1) h =
      law.bind fun choice =>
        M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) profile who
            (policy.commit info choice)) (fuel + 1) h := by
  rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm,
    M.behavioralJoint_update_withLaw_eq_bind profile who policy info law
      h.trace hterm hinfo,
    FinDist.bind_bind]
  refine FinDist.bind_congr fun choice _ => ?_
  rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm]
  refine FinDist.bind_congr fun draw _ => ?_
  refine FinDist.bindOnSupport_congr fun target realized => ?_
  refine M.runBehavioralFrom_congr fuel _ fun later hreach hlater player => ?_
  by_cases hplayer : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    exact M.withLaw_eq_commit_after_actsOnce hactsOnce policy
      info law choice (h := h) hinfo hactive draw.2 realized later hreach hlater
  · rw [Profile.update_of_ne _ _ hplayer,
      Profile.update_of_ne _ _ hplayer]

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

/-- Changing only the focal player's baseline policy leaves counterfactual
continuation value unchanged when the supplied continuation policy is fixed.
Counterfactual reach omits that baseline coordinate, and the continuation
runner overwrites it. -/
theorem counterfactualContinuationValue_eq_of_eq_off
    [Fintype ι] [DecidableEq ι]
    {first second : (player : ι) → M.BehavioralPolicy player}
    {who : ι}
    (hagree : ∀ other, other ≠ who → first other = second other)
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    counterfactualContinuationValue M first who site
        alternative payoff fuel =
      counterfactualContinuationValue M second who site
        alternative payoff fuel := by
  have hupdated :
      Profile.update (sig := M.behavioralSignature) first who alternative =
        Profile.update (sig := M.behavioralSignature) second who alternative := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Profile.update_same, Profile.update_same]
    · rw [Profile.update_of_ne _ _ hplayer,
        Profile.update_of_ne _ _ hplayer, hagree player hplayer]
  unfold counterfactualContinuationValue
  apply Finset.sum_congr rfl
  intro history _
  rw [M.counterfactualReachProbability_eq_of_eq_off hagree history.1.trace]
  unfold behavioralContinuationValue
  rw [hupdated]

/-- At a nonterminal history in a no-revisit decision fiber, ordinary
continuation value is affine in the selected information-local law. -/
theorem behavioralContinuationValue_withLaw_eq_expect
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (policy : M.BehavioralPolicy who)
    (law : FinDist (M.Choice who site.1))
    (history : M.InformationHistory who site.1)
    (hterm : ¬ E.terminal history.1.state)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    behavioralContinuationValue M strategy who
        (policy.withLaw site.1 law) payoff (fuel + 1) history.1 =
      law.expect fun choice =>
        behavioralContinuationValue M strategy who
          (policy.commit site.1 choice) payoff (fuel + 1) history.1 := by
  unfold behavioralContinuationValue
  rw [M.runBehavioralFrom_update_withLaw_eq_bind hactsOnce strategy who
    policy site.1 law history.1 history.2 hterm
      (InformationSite.active M site history) fuel,
    FinDist.expect_bind]

/-- Counterfactual continuation value is affine in a law installed at a
nonterminal, no-revisit information site.  The reach weights stay canonical;
only the existing behavioral continuation runner is factored. -/
theorem counterfactualContinuationValue_withLaw_eq_expect
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hallNonterminal : InformationSite.AllNonterminal M site)
    (policy : M.BehavioralPolicy who)
    (law : FinDist (M.Choice who site.1))
    (payoff : E.History → ℝ) (fuel : ℕ) :
    counterfactualContinuationValue M strategy who site
        (policy.withLaw site.1 law) payoff (fuel + 1) =
      law.expect fun choice =>
        counterfactualContinuationValue M strategy who site
          (policy.commit site.1 choice) payoff (fuel + 1) := by
  unfold counterfactualContinuationValue
  simp_rw [M.behavioralContinuationValue_withLaw_eq_expect hactsOnce
    strategy who site policy law _ (hallNonterminal _) payoff fuel,
    ← FinDist.expect_smul]
  exact FinDist.expect_sum_comm law
    (fun (history : M.InformationHistory who site.1) choice =>
    M.counterfactualReachProbability strategy who history.1.trace *
      behavioralContinuationValue M strategy who
        (policy.commit site.1 choice) payoff (fuel + 1) history.1)

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

/-- Counterfactual continuation payoff of one pure local commitment.  This is
the ordinary finite-action utility whose external regret is D45 action regret
when the selected information state is not revisited. -/
def counterfactualActionUtility [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1) : ℝ :=
  counterfactualContinuationValue M strategy who site
    ((strategy who).commit site.1 choice) payoff fuel

/-- At a nonterminal no-revisit site, the current counterfactual continuation
value is the expectation of its pure-commitment continuation utilities. -/
theorem counterfactualContinuationValue_eq_expect_actionUtility
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hallNonterminal : InformationSite.AllNonterminal M site)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    counterfactualContinuationValue M strategy who site
        (strategy who) payoff (fuel + 1) =
      (strategy who site.1).expect
        (counterfactualActionUtility M strategy who site payoff (fuel + 1)) := by
  calc
    counterfactualContinuationValue M strategy who site
        (strategy who) payoff (fuel + 1) =
      counterfactualContinuationValue M strategy who site
        ((strategy who).withLaw site.1 (strategy who site.1))
          payoff (fuel + 1) := by
            rw [BehavioralPolicy.withLaw_eq_self]
    _ = _ := by
      exact (show
          counterfactualContinuationValue M strategy who site
              ((strategy who).withLaw site.1 (strategy who site.1))
                payoff (fuel + 1) =
            (strategy who site.1).expect fun choice =>
              counterfactualContinuationValue M strategy who site
                ((strategy who).commit site.1 choice) payoff (fuel + 1)
        from M.counterfactualContinuationValue_withLaw_eq_expect hactsOnce
          strategy who site hallNonterminal (strategy who)
            (strategy who site.1) payoff fuel)

/-- D45 action regret is exactly external regret for the pure-commitment
continuation utility.  This is the generic realization equation D46 had to
assume model by model. -/
theorem counterfactualActionRegret_eq_sub_expect
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hallNonterminal : InformationSite.AllNonterminal M site)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1) :
    counterfactualActionRegret M strategy who site payoff (fuel + 1) choice =
      counterfactualActionUtility M strategy who site payoff (fuel + 1) choice -
        (strategy who site.1).expect
          (counterfactualActionUtility M strategy who site payoff (fuel + 1)) := by
  rw [counterfactualActionRegret, counterfactualRegret,
    counterfactualActionUtility,
    M.counterfactualContinuationValue_eq_expect_actionUtility hactsOnce
      strategy who site hallNonterminal payoff fuel]

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

/-- A normalized counterfactual-reach fiber turns pointwise continuation
payoff bounds into the same bounds on pure-action counterfactual utility. -/
theorem counterfactualActionUtility_mem_Icc
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1) {lo hi : ℝ}
    (hmass : ∑ history : M.InformationHistory who site.1,
      M.counterfactualReachProbability strategy who history.1.trace = 1)
    (hcontinuation : ∀ history : M.InformationHistory who site.1,
      behavioralContinuationValue M strategy who
          ((strategy who).commit site.1 choice) payoff fuel history.1 ∈
        Set.Icc lo hi) :
    counterfactualActionUtility M strategy who site payoff fuel choice ∈
      Set.Icc lo hi := by
  unfold counterfactualActionUtility counterfactualContinuationValue
  constructor
  · calc
      lo = (∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace) * lo := by
            rw [hmass, one_mul]
      _ = ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace * lo := by
            rw [Finset.sum_mul]
      _ ≤ ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace *
            behavioralContinuationValue M strategy who
              ((strategy who).commit site.1 choice) payoff fuel history.1 := by
            apply Finset.sum_le_sum
            intro history _
            exact mul_le_mul_of_nonneg_left (hcontinuation history).1
              (counterfactualReachProbability_nonneg M strategy who
                history.1.trace)
  · calc
      (∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace *
            behavioralContinuationValue M strategy who
              ((strategy who).commit site.1 choice) payoff fuel history.1) ≤
          ∑ history : M.InformationHistory who site.1,
            M.counterfactualReachProbability strategy who history.1.trace * hi := by
              apply Finset.sum_le_sum
              intro history _
              exact mul_le_mul_of_nonneg_left (hcontinuation history).2
                (counterfactualReachProbability_nonneg M strategy who
                  history.1.trace)
      _ = (∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace) * hi := by
            rw [Finset.sum_mul]
      _ = hi := by rw [hmass, one_mul]

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
