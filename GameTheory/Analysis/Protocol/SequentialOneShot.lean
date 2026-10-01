/-
# The one-shot deviation principle for consistent assessments

In a decision-recall protocol with finitely many histories, local choices
control whole continuation policies. At a fully mixed Bayes assessment, a bound
on the gain from changing the law at any single decision site of a player
bounds the gain from any whole continuation policy by the number of that
player's decision sites times the bound. The estimate is uniform in how rarely
a site is reached: splicing the policy after a site, every later site of the
spliced branch is met only through the site's own histories.

The uniformity is what passes the principle to limits. At a Kreps-Wilson
consistent assessment, optimality against single-site law changes implies
optimality against every whole continuation policy, including at sites the
assessment never reaches. Sequential equilibrium is therefore consistency plus
one-shot optimality. Local laws may be restricted to allowed sets; only the
alternative's own laws need be allowed, not the assessment's.
-/

import GameTheory.Analysis.Protocol.InformationLocalization
import GameTheory.Analysis.Protocol.SequentialLimits
import GameTheory.Analysis.Protocol.SequentialRationality
import GameTheory.Protocol.FiniteInformation

noncomputable section

namespace GameTheory.Protocol.InformationModel

open Filter GameTheory.Math.Probability
open scoped ENNReal

universe uι us ua up uq uk

variable {ι : Type uι} [DecidableEq ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [E.FiniteMovers]

omit [E.FiniteMovers] [DecidableEq ι] in
/-- The probability of an own-action record reads the policy only at the
recorded information states. -/
theorem ownPlayReachProbability_congr {who : ι} {first second : M.BehavioralPolicy who} :
    ∀ record : List (M.InfoState who × E.Action who),
      (∀ entry ∈ record, first entry.1 = second entry.1) →
        ownPlayReachProbability M first record = ownPlayReachProbability M second record
  | [], _ => rfl
  | (info, action) :: prior, hagree => by
      have hhead : first info = second info := hagree (info, action) List.mem_cons_self
      rw [ownPlayReachProbability, ownPlayReachProbability, hhead,
        ownPlayReachProbability_congr prior fun entry hentry =>
          hagree entry (List.mem_cons_of_mem _ hentry)]

omit [DecidableEq ι] in
/-- A history's reach weight is a probability, hence finite. -/
theorem historyReachWeight_ne_top (profile : (i : ι) → M.BehavioralPolicy i)
    (history : E.History) : M.historyReachWeight profile history ≠ ⊤ :=
  PMF.apply_ne_top _ _

omit [DecidableEq ι] in
/-- Splicing after a site keeps the policy at every decision recorded on the
way to the site: under decision recall none of those decisions follows it. -/
theorem spliceAfter_eq_of_mem_ownPlay (hrecall : M.DecisionRecall)
    (profile : (i : ι) → M.BehavioralPolicy i) {who : ι}
    (alternative : M.BehavioralPolicy who) (site : M.InformationSite who)
    (history : M.InformationHistory who site.1) {entry : M.InfoState who × E.Action who}
    (hentry : entry ∈ M.ownPlay who history.1.trace) :
    (profile who).spliceAfter M alternative site.1 entry.1 = profile who entry.1 := by
  obtain ⟨witness, hterm, -⟩ := site.2
  have hsame := hrecall who site history witness
  have hnot : site.1 ∉ (M.ownPlay who witness.1.trace).map Prod.fst := by
    have hfresh := M.infoOf_not_mem_actedAt_of_decisionRecall hrecall profile who witness.1 hterm
      (InformationSite.active M site witness)
    rwa [witness.2, M.actedAt_eq_map_ownPlay] at hfresh
  have hmem : entry ∈ M.ownPlay who witness.1.trace := hsame ▸ hentry
  obtain ⟨ancestor, hinfo, hactive, hancestorTerm, fuel, hreach⟩ :=
    M.exists_decision_ancestor_of_mem_ownPlay who witness.1.trace hmem
  have hrecord : M.recordAt who entry.1 = M.ownPlay who ancestor.trace := by
    rw [← hinfo]
    exact hrecall.recordAt_eq_ownPlay_of_active who ancestor hancestorTerm hactive
  have hsuffix := M.ownPlay_isSuffix_of_reachesWithin who hreach
  have hcondition :
      ¬ (entry.1 = site.1 ∨ site.1 ∈ (M.recordAt who entry.1).map Prod.fst) := by
    rintro (hat | hafter)
    · have hacted := List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hat] at hacted
      exact hnot hacted
    · rw [hrecord] at hafter
      obtain ⟨other, hother, hfst⟩ := List.mem_map.1 hafter
      exact hnot (List.mem_map.2 ⟨other, hsuffix.subset hother, hfst⟩)
  simp only [BehavioralPolicy.spliceAfter]
  exact ite_eq_right hcondition

/-- Splicing after a site leaves the reach of the site's histories unchanged. -/
theorem historyReachWeight_spliceAfter (hrecall : M.DecisionRecall)
    (profile : (i : ι) → M.BehavioralPolicy i) (who : ι)
    (site : M.InformationSite who) (alternative : M.BehavioralPolicy who)
    (history : M.InformationHistory who site.1) :
    M.historyReachWeight (Profile.update (sig := M.behavioralSignature) profile who
        ((profile who).spliceAfter M alternative site.1)) history.1 =
      M.historyReachWeight profile history.1 := by
  refine (ENNReal.toReal_eq_toReal_iff' (M.historyReachWeight_ne_top _ _)
    (M.historyReachWeight_ne_top _ _)).1 ?_
  have hcounterfactual := M.counterfactualReachProbability_eq_of_eq_off
    (first := Profile.update (sig := M.behavioralSignature) profile who
      ((profile who).spliceAfter M alternative site.1)) (second := profile)
    (fun other hother => Profile.update_of_ne _ _ hother) history.1.trace
  rw [M.historyReachProbability_eq_player_mul_counterfactual _ who history.1.trace,
    M.historyReachProbability_eq_player_mul_counterfactual profile who history.1.trace,
    hcounterfactual, playerReachProbability_eq_ownPlayReachProbability,
    playerReachProbability_eq_ownPlayReachProbability, Profile.update_same]
  congr 1
  exact M.ownPlayReachProbability_congr _ fun entry hentry =>
    M.spliceAfter_eq_of_mem_ownPlay hrecall profile alternative site history hentry

omit [E.FiniteMovers] [DecidableEq ι] in
/-- Each history of a site on the branch after `site` continues a history of
`site`. -/
theorem exists_site_ancestor_of_branch (hrecall : M.DecisionRecall) {who : ι}
    (site later : M.InformationSite who)
    (hbranch : later.1 = site.1 ∨ site.1 ∈ (M.recordAt who later.1).map Prod.fst)
    (root : E.History) (hroot : M.IsSiteHistory later root) :
    ∃ ancestor, M.IsSiteHistory site ancestor ∧ E.HistoryReaches ancestor root := by
  rcases hbranch with hsame | hafter
  · exact ⟨root, hroot.trans hsame, ExecutionProtocol.HistoryReaches.refl E _⟩
  · rw [hrecall.recordAt_eq_ownPlay who later ⟨root, hroot⟩] at hafter
    obtain ⟨entry, hentry, hfst⟩ := List.mem_map.1 hafter
    obtain ⟨ancestor, hinfo, hreach⟩ := M.exists_ancestor_of_mem_ownPlay who root.trace hentry
    exact ⟨ancestor, hinfo.trans hfst, hreach⟩

/-- At a fully mixed Bayes assessment, a bound on a Bayes continuation gain
bounds counterfactual regret by the same multiple of the site's counterfactual
mass. The continuation runner is arbitrary. -/
theorem BehavioralAssessment.counterfactualRegret_le_of_continuationGain_le
    [Fintype E.History] (hrecall : M.DecisionRecall) (assessment : M.BehavioralAssessment)
    (hfull : assessment.IsFullyMixed)
    (hbayes : BehavioralAssessment.IsBayesConsistent M assessment
      hrecall.decisionInformationAntichain)
    {who : ι} [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    (replacement : M.BehavioralPolicy who) (payoff : E.History → ℝ)
    (run : M.ContinuationRunner) (bound : ℝ)
    (hgain : (assessment.continuationContextWith run site payoff).value replacement -
      (assessment.continuationContextWith run site payoff).value (assessment.strategy who) ≤
        bound) :
    M.counterfactualRegret assessment.strategy who site payoff run replacement ≤
      bound * ∑ history : M.InformationHistory who site.1,
        M.counterfactualReachProbability assessment.strategy who history.1.trace := by
  have hantichain := hrecall.decisionInformationAntichain who site
  have hmass := M.informationMass_pos_of_fullSupport assessment.strategy hfull who site
  obtain ⟨witness, -, -⟩ := site.2
  have hown (history : M.InformationHistory who site.1) :
      M.playerReachProbability assessment.strategy who history.1.trace =
        M.playerReachProbability assessment.strategy who witness.1.trace :=
    M.playerReachProbability_eq_of_decisionRecall hrecall assessment.strategy who site
      history witness
  have hscaled := M.informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
    assessment.strategy who site hantichain hmass _ hown replacement payoff run
    (fun _ _ => payoffIntegrable_of_finite _ _) (fun _ _ => payoffIntegrable_of_finite _ _)
  rw [← assessment.continuationContextWith_value_eq_bayesContinuationValue M who site
      hantichain hmass (hbayes who site hmass) replacement payoff run,
    ← assessment.continuationContextWith_value_eq_bayesContinuationValue M who site
      hantichain hmass (hbayes who site hmass) (assessment.strategy who) payoff run]
    at hscaled
  have hmassEq : (M.informationMass assessment.strategy who site).toReal =
      M.playerReachProbability assessment.strategy who witness.1.trace *
        ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability assessment.strategy who history.1.trace := by
    rw [informationMass, tsum_fintype,
      ENNReal.toReal_sum fun history _ => M.historyReachWeight_ne_top _ history.1,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun history _ => ?_
    rw [M.historyReachProbability_eq_player_mul_counterfactual assessment.strategy who
      history.1.trace, hown]
  have hmassPos : 0 < (M.informationMass assessment.strategy who site).toReal :=
    ENNReal.toReal_pos hmass.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one _ who site hantichain))
  have hownPos : 0 < M.playerReachProbability assessment.strategy who witness.1.trace := by
    rcases (M.playerReachProbability_nonneg assessment.strategy who witness.1.trace).lt_or_eq
      with hpos | hzero
    · exact hpos
    · rw [hmassEq, ← hzero, zero_mul] at hmassPos
      exact absurd hmassPos (lt_irrefl 0)
  refine le_of_mul_le_mul_left ?_ hownPos
  rw [← hscaled]
  calc
    _ ≤ (M.informationMass assessment.strategy who site).toReal * bound :=
      mul_le_mul_of_nonneg_left hgain hmassPos.le
    _ = _ := by
      rw [hmassEq]
      ring

/-- **Quantitative one-shot deviation principle.** At a fully mixed Bayes
assessment of a decision-recall protocol with finitely many histories, suppose
no single-site change to the alternative's own law gains more than `bound`.
Then the whole alternative gains at most the number of the player's decision
sites times `bound`, at every site and however rarely it is reached. -/
theorem BehavioralAssessment.continuationGain_le_of_localGain_le
    [Finite E.History] (hrecall : M.DecisionRecall) (assessment : M.BehavioralAssessment)
    (hfull : assessment.IsFullyMixed)
    (hbayes : BehavioralAssessment.IsBayesConsistent M assessment
      hrecall.decisionInformationAntichain)
    (certificate : E.WellFoundedHistories) (who : ι) [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (alternative : M.BehavioralPolicy who) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hlocal : ∀ later : M.InformationSite who,
      (assessment.continuationContext certificate later payoff).value
          ((assessment.strategy who).withLaw later.1 (alternative later.1)) -
        (assessment.continuationContext certificate later payoff).value
          (assessment.strategy who) ≤ bound)
    (site : M.InformationSite who) :
    (assessment.continuationContext certificate site payoff).value alternative -
        (assessment.continuationContext certificate site payoff).value
          (assessment.strategy who) ≤
      Nat.card (M.InformationSite who) * bound := by
  let _ := Fintype.ofFinite E.History
  let _ := Fintype.ofFinite (M.InformationSite who)
  obtain ⟨horizon, -, hhorizon⟩ := E.exists_pos_boundedHorizon
  simp only [assessment.continuationContext_eq_truncated_of_bounded certificate hhorizon]
    at hlocal ⊢
  let Branch : M.InfoState who → Prop := fun info =>
    info = site.1 ∨ site.1 ∈ (M.recordAt who info).map Prod.fst
  let allowance : M.InfoState who → ℝ := fun info =>
    ∑ later : M.InformationSite who, if later.1 = info ∧ Branch later.1 then bound else 0
  have hallowance (info : M.InfoState who) : 0 ≤ allowance info :=
    Finset.sum_nonneg fun later _ => by
      split
      · exact hbound
      · exact le_rfl
  have hallowanceAt (later : M.InformationSite who) :
      allowance later.1 = if Branch later.1 then bound else 0 := by
    change (∑ other : M.InformationSite who,
      if other.1 = later.1 ∧ Branch other.1 then bound else 0) = _
    rw [Finset.sum_eq_single later]
    · simp
    · intro other _ hother
      exact ite_eq_right fun hsame => hother (Subtype.ext hsame.1)
    · exact fun hnot => absurd (Finset.mem_univ later) hnot
  have hregret (later : M.InformationSite who) :
      M.counterfactualRegret assessment.strategy who later payoff (M.truncatedRunner horizon)
          ((assessment.strategy who).withLaw later.1
            ((assessment.strategy who).spliceAfter M alternative site.1 later.1)) ≤
        allowance later.1 * ∑ history : M.InformationHistory who later.1,
          M.counterfactualReachProbability assessment.strategy who history.1.trace := by
    rw [hallowanceAt]
    by_cases hbranch : Branch later.1
    · have hlaw : (assessment.strategy who).spliceAfter M alternative site.1 later.1 =
          alternative later.1 := by
        simp only [BehavioralPolicy.spliceAfter]
        exact ite_eq_left hbranch
      rw [hlaw, ite_eq_left hbranch]
      exact assessment.counterfactualRegret_le_of_continuationGain_le M hrecall hfull hbayes
        later _ payoff _ bound (hlocal later)
    · have hlaw : (assessment.strategy who).spliceAfter M alternative site.1 later.1 =
          assessment.strategy who later.1 := by
        simp only [BehavioralPolicy.spliceAfter]
        exact ite_eq_right hbranch
      rw [hlaw, ite_eq_right hbranch, zero_mul, BehavioralPolicy.withLaw_eq_self,
        counterfactualRegret, sub_self]
  have hroot := M.behavioralRootGain_le_of_counterfactualLocalGain_le hrecall
    assessment.strategy who ((assessment.strategy who).spliceAfter M alternative site.1)
    payoff hhorizon allowance hallowance hregret
  have hcut := M.rootGain_spliceAfter_eq_sum_informationGain hrecall assessment.strategy
    who site alternative payoff hhorizon
  have hantichain := hrecall.decisionInformationAntichain who site
  have hmass := M.informationMass_pos_of_fullSupport assessment.strategy hfull who site
  have hnormalized := assessment.informationMass_mul_continuationGain_eq_sum M who site
    hantichain hmass (hbayes who site hmass) alternative payoff (M.truncatedRunner horizon)
    (fun _ => payoffIntegrable_of_finite _ _) (fun _ => payoffIntegrable_of_finite _ _)
  have hbranchMass (later : M.InformationSite who) (hbranch : Branch later.1) :
      ∑ history : M.InformationHistory who later.1,
          (M.historyReachWeight (Profile.update (sig := M.behavioralSignature)
            assessment.strategy who ((assessment.strategy who).spliceAfter M alternative
              site.1)) history.1).toReal ≤
        (M.informationMass assessment.strategy who site).toReal := by
    rw [← ENNReal.toReal_sum fun history _ => M.historyReachWeight_ne_top _ history.1,
      ← tsum_fintype (L := SummationFilter.unconditional _)]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one _ who site hantichain)) ?_
    calc
      _ = ∑' root : {root // M.IsSiteHistory later root},
          E.coneMass certificate (M.randomizedChooser (Profile.update
            (sig := M.behavioralSignature) assessment.strategy who
              ((assessment.strategy who).spliceAfter M alternative site.1))) root
            E.initHistory :=
        tsum_congr fun history => (M.coneMass_eq_historyReachWeight certificate _ history.1).symm
      _ ≤ ∑' root : {root // M.IsSiteHistory site root},
          E.coneMass certificate (M.randomizedChooser (Profile.update
            (sig := M.behavioralSignature) assessment.strategy who
              ((assessment.strategy who).spliceAfter M alternative site.1))) root
            E.initHistory :=
        tsum_coneMass_le_of_reaches certificate _ _ _
          (M.siteHistory_antichain (hrecall.decisionInformationAntichain who later))
          (M.siteHistory_antichain hantichain)
          (M.exists_site_ancestor_of_branch hrecall site later hbranch) _
      _ = M.informationMass assessment.strategy who site :=
        tsum_congr fun history => (M.coneMass_eq_historyReachWeight certificate _ history.1).trans
          (M.historyReachWeight_spliceAfter hrecall assessment.strategy who site alternative
            history)
  have hsum : ∑ history : E.History,
      (M.historyReachWeight (Profile.update (sig := M.behavioralSignature) assessment.strategy
        who ((assessment.strategy who).spliceAfter M alternative site.1)) history).toReal *
          allowance (M.infoOf who history.trace) ≤
      Nat.card (M.InformationSite who) * bound *
        (M.informationMass assessment.strategy who site).toReal := by
    simp only [allowance, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _later : M.InformationSite who,
          bound * (M.informationMass assessment.strategy who site).toReal :=
        Finset.sum_le_sum fun later _ => by
          by_cases hbranch : Branch later.1
          · have hfiber :
                (∑ history : E.History,
                  (M.historyReachWeight (Profile.update (sig := M.behavioralSignature)
                    assessment.strategy who ((assessment.strategy who).spliceAfter M
                      alternative site.1)) history).toReal *
                    if later.1 = M.infoOf who history.trace ∧ Branch later.1 then bound
                    else 0) =
                  bound * ∑ history : M.InformationHistory who later.1,
                    (M.historyReachWeight (Profile.update (sig := M.behavioralSignature)
                      assessment.strategy who ((assessment.strategy who).spliceAfter M
                        alternative site.1)) history.1).toReal := by
              simp only [hbranch, and_true, mul_ite, mul_zero]
              rw [← Finset.sum_filter, Finset.sum_subtype
                (p := fun history : E.History => M.infoOf who history.trace = later.1) _
                (fun history => by simp [eq_comm]), Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
            rw [hfiber]
            exact mul_le_mul_of_nonneg_left (hbranchMass later hbranch) hbound
          · simp only [hbranch, and_false, ↓reduceIte, mul_zero, Finset.sum_const_zero]
            exact mul_nonneg hbound ENNReal.toReal_nonneg
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
        ring
  have hmassPos : 0 < (M.informationMass assessment.strategy who site).toReal :=
    ENNReal.toReal_pos hmass.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one _ who site hantichain))
  change (assessment.continuationContextWith (M.truncatedRunner horizon) site payoff).value
      alternative -
    (assessment.continuationContextWith (M.truncatedRunner horizon) site payoff).value
      (assessment.strategy who) ≤ _
  refine le_of_mul_le_mul_left ?_ hmassPos
  calc
    _ = expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
          assessment.strategy who ((assessment.strategy who).spliceAfter M alternative
            site.1)) horizon) payoff -
        expect (M.runBehavioral assessment.strategy horizon) payoff := by
      rw [hnormalized]
      simp only [Profile.update_eq_self]
      rw [← hcut]
    _ ≤ _ := hroot.trans hsum
    _ = _ := by ring

omit [E.FiniteMovers] [DecidableEq ι] in
/-- Splicing a single-site law change after its own site changes nothing. -/
theorem spliceAfter_withLaw {who : ι} [DecidableEq (M.InfoState who)]
    (policy : M.BehavioralPolicy who) (site : M.InformationSite who)
    (law : PMF (M.Choice who site.1)) :
    policy.spliceAfter M (policy.withLaw site.1 law) site.1 = policy.withLaw site.1 law := by
  funext info
  simp only [BehavioralPolicy.spliceAfter]
  split
  · rfl
  · rename_i outside
    exact (BehavioralPolicy.withLaw_of_ne _ _ _ fun same => outside (Or.inl same)).symm

/-- **Local deviations at the root.** At a fully mixed Bayes assessment of a
decision-recall protocol with finitely many histories, changing one site's law
changes the value of terminal play by the site's mass times the change of that
site's continuation value. -/
theorem BehavioralAssessment.rootGain_withLaw_eq_mass_mul
    [Finite E.History] (hrecall : M.DecisionRecall) (assessment : M.BehavioralAssessment)
    (hfull : assessment.IsFullyMixed)
    (hbayes : BehavioralAssessment.IsBayesConsistent M assessment
      hrecall.decisionInformationAntichain)
    (certificate : E.WellFoundedHistories) (who : ι) [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (site : M.InformationSite who) (law : PMF (M.Choice who site.1)) :
    expect (M.runBehavioralTerminalFrom certificate (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who ((assessment.strategy who).withLaw site.1 law))
          E.initHistory) payoff -
      expect (M.runBehavioralTerminalFrom certificate assessment.strategy E.initHistory) payoff =
    (M.informationMass assessment.strategy who site).toReal *
      ((assessment.continuationContext certificate site payoff).value
          ((assessment.strategy who).withLaw site.1 law) -
        (assessment.continuationContext certificate site payoff).value
          (assessment.strategy who)) := by
  let _ := Fintype.ofFinite E.History
  obtain ⟨horizon, -, hhorizon⟩ := E.exists_pos_boundedHorizon
  rw [M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate hhorizon,
    M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate hhorizon]
  simp only [assessment.continuationContext_eq_truncated_of_bounded certificate hhorizon]
  change _ = _ * ((assessment.continuationContextWith (M.truncatedRunner horizon) site
    payoff).value _ - (assessment.continuationContextWith (M.truncatedRunner horizon) site
      payoff).value _)
  have hcut := M.rootGain_spliceAfter_eq_sum_informationGain hrecall assessment.strategy who
    site ((assessment.strategy who).withLaw site.1 law) payoff hhorizon
  rw [M.spliceAfter_withLaw] at hcut
  have hmass := M.informationMass_pos_of_fullSupport assessment.strategy hfull who site
  rw [assessment.informationMass_mul_continuationGain_eq_sum M who site
    (hrecall.decisionInformationAntichain who site) hmass (hbayes who site hmass) _ payoff
    (M.truncatedRunner horizon) (fun _ => payoffIntegrable_of_finite _ _)
    (fun _ => payoffIntegrable_of_finite _ _)]
  simp only [Profile.update_eq_self]
  exact hcut

/-- **One-shot deviation principle for fully mixed Bayes assessments.** In a
decision-recall protocol with finitely many histories, optimality against
every allowed single-site law implies optimality against every whole
continuation policy whose laws are allowed. The allowed sets may vary by player
and site, and the assessment's own laws need not be allowed. -/
theorem BehavioralAssessment.continuation_value_le_of_locallyOptimal
    [Finite E.History] [∀ i, DecidableEq (M.InfoState i)]
    (hrecall : M.DecisionRecall)
    (assessment : M.BehavioralAssessment)
    (hfull : assessment.IsFullyMixed)
    (hbayes : BehavioralAssessment.IsBayesConsistent M assessment
      (hrecall.decisionInformationAntichain))
    (Allowed : (i : ι) → (info : M.InfoState i) → PMF (M.Choice i info) → Prop)
    (payoff : ι → E.History → ℝ) (certificate : E.WellFoundedHistories)
    (hlocal : ∀ (i : ι) (site : M.InformationSite i)
      (law : PMF (M.Choice i site.1)), Allowed i site.1 law →
        (assessment.continuationContext certificate site (payoff i)).value
            ((assessment.strategy i).withLaw site.1 law) ≤
          (assessment.continuationContext certificate site (payoff i)).value
            (assessment.strategy i))
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (halternative : ∀ later : M.InformationSite who,
      Allowed who later.1 (alternative later.1)) :
    (assessment.continuationContext certificate site (payoff who)).value alternative ≤
      (assessment.continuationContext certificate site (payoff who)).value
        (assessment.strategy who) := by
  have hgain := assessment.continuationGain_le_of_localGain_le M hrecall hfull hbayes
    certificate who (payoff who) alternative 0 le_rfl
    (fun later => sub_nonpos.2 (hlocal who later _ (halternative later))) site
  rw [mul_zero] at hgain
  exact sub_nonpos.1 hgain

/-- **One-shot deviation principle for consistent assessments.** In a
decision-recall protocol with finitely many histories, a Kreps-Wilson
consistent assessment that is optimal against every allowed single-site law is
optimal against every whole continuation policy whose laws are allowed, at
every decision site, including sites the assessment does not reach. The
approximating assessments need not be locally optimal themselves. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.continuation_value_le_of_locallyOptimal
    [Finite E.History] [∀ i, DecidableEq (M.InfoState i)]
    (hrecall : M.DecisionRecall) {assessment : M.BehavioralAssessment}
    (hconsistent : assessment.IsSequentiallyConsistent hrecall.decisionInformationAntichain)
    (Allowed : (i : ι) → (info : M.InfoState i) → PMF (M.Choice i info) → Prop)
    (payoff : ι → E.History → ℝ) (certificate : E.WellFoundedHistories)
    (hlocal : ∀ (i : ι) (site : M.InformationSite i)
      (law : PMF (M.Choice i site.1)), Allowed i site.1 law →
        (assessment.continuationContext certificate site (payoff i)).value
            ((assessment.strategy i).withLaw site.1 law) ≤
          (assessment.continuationContext certificate site (payoff i)).value
            (assessment.strategy i))
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (halternative : ∀ later : M.InformationSite who,
      Allowed who later.1 (alternative later.1)) :
    (assessment.continuationContext certificate site (payoff who)).value alternative ≤
      (assessment.continuationContext certificate site (payoff who)).value
        (assessment.strategy who) := by
  obtain ⟨sequence, happrox, hconverges⟩ := hconsistent
  let _ := Fintype.ofFinite E.History
  let _ := Fintype.ofFinite (M.InformationSite who)
  let total : ℝ := ∑ history : E.History, |payoff who history|
  have htotal (history : E.History) : |payoff who history| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff who other)) (Finset.mem_univ history)
  have hvalue (later : M.InformationSite who) (replacement : ℕ → M.BehavioralPolicy who)
      (limit : M.BehavioralPolicy who)
      (hreplacement : ∀ decision : M.InformationSite who,
        PMFConvergesPointwise (fun n => replacement n decision.1) (limit decision.1)) :
      Tendsto (fun n => ((sequence n).continuationContext certificate later (payoff who)).value
          (replacement n)) atTop
        (nhds ((assessment.continuationContext certificate later (payoff who)).value limit)) :=
    M.continuationContext_value_tendsto_of_bounded_terminal certificate
      (fun i decision => hconverges.strategy i decision) who later (hconverges.belief who later)
      hreplacement (payoff who) total ((abs_nonneg _).trans (htotal E.initHistory))
      (fun final _ => htotal final)
  have hwithLaw (later decision : M.InformationSite who) :
      PMFConvergesPointwise
        (fun n => ((sequence n).strategy who).withLaw later.1 (alternative later.1) decision.1)
        ((assessment.strategy who).withLaw later.1 (alternative later.1) decision.1) := by
    by_cases hsame : decision = later
    · subst decision
      simpa only [BehavioralPolicy.withLaw_self] using
        pmfConvergesPointwise_const (alternative later.1)
    · have hdifferent : decision.1 ≠ later.1 := fun hequal => hsame (Subtype.ext hequal)
      simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ hdifferent] using
        hconverges.strategy who decision
  let gain (n : ℕ) (later : M.InformationSite who) : ℝ :=
    ((sequence n).continuationContext certificate later (payoff who)).value
        (((sequence n).strategy who).withLaw later.1 (alternative later.1)) -
      ((sequence n).continuationContext certificate later (payoff who)).value
        ((sequence n).strategy who)
  let error (n : ℕ) : ℝ := ∑ later : M.InformationSite who, max (gain n later) 0
  have herror : Tendsto error atTop (nhds 0) := by
    have heach (later : M.InformationSite who) :
        Tendsto (fun n => max (gain n later) 0) atTop (nhds 0) := by
      have hlimit := sub_nonpos.2 (hlocal who later _ (halternative later))
      simpa only [max_eq_right hlimit] using
        ((hvalue later _ _ (hwithLaw later)).sub
          (hvalue later _ _ (hconverges.strategy who))).max
            (tendsto_const_nhds (x := (0 : ℝ)))
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ fun later _ =>
      heach later
  have hbound (n : ℕ) :
      ((sequence n).continuationContext certificate site (payoff who)).value alternative -
          ((sequence n).continuationContext certificate site (payoff who)).value
            ((sequence n).strategy who) ≤
        Nat.card (M.InformationSite who) * error n :=
    (sequence n).continuationGain_le_of_localGain_le M hrecall (happrox n).1 (happrox n).2
      certificate who (payoff who) alternative (error n)
      (Finset.sum_nonneg fun _ _ => le_max_right _ _)
      (fun later => (le_max_left _ _).trans (Finset.single_le_sum
        (fun other _ => le_max_right (gain n other) 0) (Finset.mem_univ later))) site
  have hdeviation := (hvalue site (fun _ => alternative) alternative
    fun decision => pmfConvergesPointwise_const _).sub
      (hvalue site _ _ (hconverges.strategy who))
  have herrorBound : Tendsto (fun n => (Nat.card (M.InformationSite who) : ℝ) * error n) atTop
      (nhds 0) := by
    simpa only [mul_zero] using herror.const_mul (Nat.card (M.InformationSite who) : ℝ)
  exact sub_nonpos.1 (le_of_tendsto_of_tendsto hdeviation herrorBound
    (Eventually.of_forall hbound))

/-- **Sequential equilibrium is consistency plus one-shot optimality.** In a
decision-recall protocol with finitely many histories, a consistent assessment
is sequentially rational exactly when no player gains by changing the law at a
single decision site. -/
theorem BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal
    [Finite E.History] [∀ i, DecidableEq (M.InfoState i)]
    (hrecall : M.DecisionRecall) (assessment : M.BehavioralAssessment)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) :
    assessment.IsSequentialEquilibrium hrecall.decisionInformationAntichain certificate payoff ↔
      assessment.IsSequentiallyConsistent hrecall.decisionInformationAntichain ∧
        ∀ (i : ι) (site : M.InformationSite i) (law : PMF (M.Choice i site.1)),
          (assessment.continuationContext certificate site (payoff i)).value
              ((assessment.strategy i).withLaw site.1 law) ≤
            (assessment.continuationContext certificate site (payoff i)).value
              (assessment.strategy i) := by
  let _ := Fintype.ofFinite E.History
  have hintegrable (i : ι) (site : M.InformationSite i) (policy : M.BehavioralPolicy i) :=
    assessment.continuationContext_integrable_of_bounded_terminal certificate site (payoff i)
      (∑ history : E.History, |payoff i history|)
      (fun final _ => Finset.single_le_sum (fun other _ => abs_nonneg (payoff i other))
        (Finset.mem_univ final)) policy
  have hoptimal (i : ι) (site : M.InformationSite i) :
      assessment.IsSequentiallyRationalAt site
          (assessment.continuationContext certificate site (payoff i)) ↔
        ∀ alternative : M.BehavioralPolicy i,
          (assessment.continuationContext certificate site (payoff i)).value alternative ≤
            (assessment.continuationContext certificate site (payoff i)).value
              (assessment.strategy i) :=
    (Context.isLocallyOptimal_iff_of_integrable (hintegrable i site _)
      fun alternative _ => hintegrable i site alternative).trans
        ⟨fun h alternative => h alternative (Set.mem_univ _),
          fun h alternative _ => h alternative⟩
  constructor
  · rintro ⟨hrational, hconsistent⟩
    exact ⟨hconsistent, fun i site law => (hoptimal i site).1 (hrational i site) _⟩
  · rintro ⟨hconsistent, hlocal⟩
    refine ⟨fun i site => (hoptimal i site).2 fun alternative => ?_, hconsistent⟩
    exact hconsistent.continuation_value_le_of_locallyOptimal M hrecall (fun _ _ _ => True)
      payoff certificate (fun i site law _ => hlocal i site law) i site alternative
      fun _ => trivial

end GameTheory.Protocol.InformationModel
