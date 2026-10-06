/-
# Transporting Bayes beliefs

Bayes beliefs at an information site are normalized reach weights, so they
move wherever reach weights move. A player's own strategy cancels from its
beliefs at a site of common own reach. Along an approximating sequence reach
weights and site masses converge, so a consistent assessment obeys Bayes' rule
wherever its limit reaches a site. With no clock, a site's mass is the
probability that terminal play passes through it; when a site's histories
share one depth, its belief is the behavioral law at that depth conditioned on
the information event.

Between two protocols, a history map whose reach weights sum over its fibers
transports site masses and beliefs, and so does any readout whose joint law
with the information event agrees. Each transport has a form stated with reach
weights alone and a form at decision depths, which may differ between the two
protocols.
-/

import GameTheory.Analysis.Protocol.BehavioralBayes
import GameTheory.Analysis.Protocol.CounterfactualRegret
import GameTheory.Analysis.Protocol.InformationLocalization
import GameTheory.Analysis.Protocol.Sequential

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter
open scoped ENNReal

section Single

variable {ι : Type*} {E : ExecutionProtocol ι} (M : InformationModel E)
variable [E.FiniteMovers]

/-! ## Own strategy cancels -/

/-- **Own strategy cancels from Bayes beliefs.** Two profiles differing only in
one player's strategy give that player the same Bayes belief at a site of
common own reach, whenever both reach the site. -/
theorem bayesBelief_eq_of_eq_off [DecidableEq ι]
    (first second : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    (antichain : site.IsHistoryAntichain)
    (agree : ∀ other, other ≠ who → first other = second other)
    (firstCommon : M.CommonPlayerReachAt first who site)
    (secondCommon : M.CommonPlayerReachAt second who site)
    (firstPositive : 0 < M.informationMass first who site)
    (secondPositive : 0 < M.informationMass second who site) :
    M.bayesBelief first who site antichain firstPositive =
      M.bayesBelief second who site antichain secondPositive := by
  classical
  obtain ⟨firstReach, firstCommon⟩ := firstCommon
  obtain ⟨secondReach, secondCommon⟩ := secondCommon
  have firstNonzero := (M.commonPlayerReach_pos firstReach firstCommon firstPositive).ne'
  have secondNonzero := (M.commonPlayerReach_pos secondReach secondCommon secondPositive).ne'
  have factor (profile : (i : ι) → M.BehavioralPolicy i) (reach : ℝ)
      (common : ∀ history : M.InformationHistory who site.1,
        M.playerReachProbability profile who history.1.trace = reach) :
      (M.informationMass profile who site).toReal = reach *
        ∑' history : M.InformationHistory who site.1,
          M.counterfactualReachProbability profile who history.1.trace := by
    unfold informationMass
    rw [ENNReal.tsum_toReal_eq (f := fun history : M.InformationHistory who site.1 =>
      M.historyReachWeight profile history.1) fun history => PMF.apply_ne_top _ _,
      ← tsum_mul_left]
    apply tsum_congr
    intro history
    rw [M.historyReachProbability_eq_player_mul_counterfactual profile who history.1.trace,
      common history]
  have firstMass := factor first firstReach firstCommon
  have secondMass := factor second secondReach secondCommon
  simp_rw [← M.counterfactualReachProbability_eq_of_eq_off agree] at secondMass
  apply pmf_ext_toReal
  intro history
  rw [M.bayesBelief_apply first who site antichain firstPositive history,
    M.bayesBelief_apply second who site antichain secondPositive history,
    ENNReal.toReal_div, ENNReal.toReal_div,
    M.historyReachProbability_eq_player_mul_counterfactual first who history.1.trace,
    M.historyReachProbability_eq_player_mul_counterfactual second who history.1.trace,
    firstCommon history, secondCommon history, firstMass, secondMass,
    ← M.counterfactualReachProbability_eq_of_eq_off agree history.1.trace,
    mul_div_mul_left _ _ firstNonzero, mul_div_mul_left _ _ secondNonzero]

/-! ## Limits of Bayes beliefs -/

variable {M} in
/-- Reach weights converge with the behavioral strategies at decision sites.
A reach weight is a finite product along one trace, so no finiteness of menus
or transitions is needed. -/
theorem BehavioralAssessmentConvergesPointwise.historyReachWeight
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (history : E.History) :
    Tendsto (fun n => M.historyReachWeight (sequence n).strategy history) atTop
      (nhds (M.historyReachWeight assessment.strategy history)) := by
  classical
  apply (ENNReal.tendsto_toReal_iff (fun _ => PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  obtain ⟨state, trace⟩ := history
  induction trace with
  | start => exact tendsto_const_nhds
  | @extend source target prior joint legal realized induction =>
      change Tendsto (fun n => (M.historyReachWeight (sequence n).strategy
          ⟨target, prior.extend joint legal realized⟩).toReal) atTop
        (nhds (M.historyReachWeight assessment.strategy
          ⟨target, prior.extend joint legal realized⟩).toReal)
      change Tendsto (fun n => (M.historyReachWeight (sequence n).strategy
          ⟨source, prior⟩).toReal) atTop
        (nhds (M.historyReachWeight assessment.strategy ⟨source, prior⟩).toReal) at induction
      refine Tendsto.congr (fun n => (historyReachProbability_extend M (sequence n).strategy
        prior joint legal realized).symm) ?_
      rw [historyReachProbability_extend M assessment.strategy prior joint legal realized]
      simp only [stepProb]
      apply induction.mul
      apply Tendsto.mul_const
      simp only [behavioralJoint_prob_eq_prod]
      apply tendsto_finsetProd
      intro player _
      by_cases active : E.active source player
      · obtain ⟨⟨info, decision⟩, same⟩ :=
          M.exists_informationSite_of_active player ⟨source, prior⟩ legal.1 active
        change info = M.infoOf player prior at same
        subst same
        exact (converges.strategy player ⟨_, decision⟩).toReal _
      · simp only [M.behavioral_eq_of_not_active ((sequence _).strategy player)
          (assessment.strategy player) prior active]
        exact tendsto_const_nhds

variable {M} in
/-- Site masses converge when the site has finitely many histories. -/
theorem BehavioralAssessmentConvergesPointwise.informationMass
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : ι) (site : M.InformationSite who)
    [Finite (M.InformationHistory who site.1)] :
    Tendsto (fun n => M.informationMass (sequence n).strategy who site) atTop
      (nhds (M.informationMass assessment.strategy who site)) := by
  let _ : Fintype (M.InformationHistory who site.1) := Fintype.ofFinite _
  simp only [InformationModel.informationMass, tsum_fintype]
  exact tendsto_finsetSum Finset.univ fun history _ => converges.historyReachWeight history.1

variable {M} in
/-- **Consistency implies Bayes' rule where possible.** A consistent
assessment obeys Bayes' rule at every site its limit strategy reaches with
positive mass. Off such sites its beliefs are those of the approximating
sequence. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.isBayesConsistent
    {assessment : M.BehavioralAssessment}
    [∀ who (site : M.InformationSite who), Finite (M.InformationHistory who site.1)]
    (antichain : M.DecisionInformationAntichain)
    (consistent : assessment.IsSequentiallyConsistent antichain) :
    BehavioralAssessment.IsBayesConsistent M assessment antichain := by
  obtain ⟨sequence, approximates, converges⟩ := consistent
  intro who site positive history
  have ratios := ENNReal.Tendsto.div
    (converges.historyReachWeight history.1) (Or.inr positive.ne')
    (converges.informationMass who site)
    (Or.inl (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one assessment.strategy who site (antichain who site))))
  have equality (n : ℕ) : (sequence n).belief who site history =
      M.historyReachWeight (sequence n).strategy history.1 /
        M.informationMass (sequence n).strategy who site :=
    (approximates n).2 who site
      (M.informationMass_pos_of_fullSupport _ (approximates n).1 who site) history
  exact tendsto_nhds_unique (converges.belief who site history)
    (ratios.congr' (Eventually.of_forall fun n => (equality n).symm))

/-! ## Site mass as an event -/

/-- **A site's mass is the probability of passing through it.** Terminal play
passes through at most one history of the site, so its mass is the probability
that terminal play has an ancestor in the site. No clock is involved. -/
theorem informationMass_eq_passage (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i) (who : ι) (site : M.InformationSite who)
    (antichain : site.IsHistoryAntichain) :
    M.informationMass strategy who site =
      (M.runBehavioralTerminalFrom certificate strategy E.initHistory).toOuterMeasure
        {final | ∃ history, M.infoOf who history.trace = site.1 ∧
          E.HistoryReaches history final} := by
  classical
  calc
    M.informationMass strategy who site =
        ∑' root : {root // M.IsSiteHistory site root},
          E.coneMass certificate (M.randomizedChooser strategy) root E.initHistory :=
      tsum_congr fun history => (M.coneMass_eq_historyReachWeight certificate _ history.1).symm
    _ = _ := tsum_coneMass_eq certificate _ _ (M.siteHistory_antichain antichain) _

section Depth

variable (strategy : (i : ι) → M.BehavioralPolicy i) (who : ι) (site : M.InformationSite who)
  (depth : ℕ) (sameDepth : InformationSite.CommonDepth M site depth)

include sameDepth in
/-- At a common depth, a site's mass is the probability of its information
event under behavioral play of that length. -/
theorem informationMass_eq_fixedDepth_toOuterMeasure :
    M.informationMass strategy who site =
      (M.runBehavioral strategy depth).toOuterMeasure
        {history | M.infoOf who history.trace = site.1} := by
  unfold informationMass
  rw [PMF.toOuterMeasure_apply]
  rw [← tsum_subtype {history : E.History | M.infoOf who history.trace = site.1}
    (M.runBehavioral strategy depth)]
  exact tsum_congr fun history => by rw [historyReachWeight, sameDepth history]

include sameDepth in
/-- At a common depth, the Bayes belief is behavioral play of that length
conditioned on the information event. -/
theorem bayesBelief_map_eq_filter (antichain : site.IsHistoryAntichain)
    (positive : 0 < M.informationMass strategy who site)
    (meet : ∃ history ∈ {history | M.infoOf who history.trace = site.1},
      history ∈ (M.runBehavioral strategy depth).support) :
    (M.bayesBelief strategy who site antichain positive).map Subtype.val =
      (M.runBehavioral strategy depth).filter
        {history | M.infoOf who history.trace = site.1} meet := by
  classical
  ext history
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    ← M.informationMass_eq_fixedDepth_toOuterMeasure strategy who site depth sameDepth]
  by_cases observed : M.infoOf who history.trace = site.1
  · let compatible : M.InformationHistory who site.1 := ⟨history, observed⟩
    rw [pmf_map_apply_of_injective _ Subtype.val_injective compatible, M.bayesBelief_apply,
      Set.indicator_of_mem (show history ∈ {history | M.infoOf who history.trace = site.1}
        from observed), historyReachWeight, sameDepth compatible, div_eq_mul_inv]
  · rw [Set.indicator_of_notMem (show history ∉ {history | M.infoOf who history.trace = site.1}
      from observed), zero_mul, PMF.apply_eq_zero_iff, PMF.support_map]
    rintro ⟨compatible, _, same⟩
    apply observed
    rw [← same]
    exact compatible.2

end Depth

/-- If every play of a common decision depth reaches a site, a consistent
belief there is the unconditioned behavioral law at that depth. -/
theorem BehavioralAssessment.belief_map_eq_run_of_full_reach
    [∀ player (decision : M.InformationSite player),
      Finite (M.InformationHistory player decision.1)]
    (assessment : M.BehavioralAssessment) (antichain : M.DecisionInformationAntichain)
    (consistent : assessment.IsSequentiallyConsistent antichain)
    (who : ι) (site : M.InformationSite who) (depth : ℕ)
    (sameDepth : InformationSite.CommonDepth M site depth)
    (seen : ∀ history ∈ (M.runBehavioral assessment.strategy depth).support,
      M.infoOf who history.trace = site.1) :
    (assessment.belief who site).map Subtype.val =
      M.runBehavioral assessment.strategy depth := by
  classical
  let law := M.runBehavioral assessment.strategy depth
  let information : Set E.History := {history | M.infoOf who history.trace = site.1}
  have mass : law.toOuterMeasure information = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff law information).mpr fun history supported =>
      seen history supported
  have informationMass : M.informationMass assessment.strategy who site = 1 :=
    (M.informationMass_eq_fixedDepth_toOuterMeasure assessment.strategy who site depth
      sameDepth).trans mass
  have positive : 0 < M.informationMass assessment.strategy who site := by
    rw [informationMass]
    exact one_pos
  obtain ⟨witness, supported⟩ := law.support_nonempty
  have meet : ∃ history ∈ information, history ∈ law.support :=
    ⟨witness, seen witness supported, supported⟩
  have bayes : assessment.belief who site =
      M.bayesBelief assessment.strategy who site (antichain who site) positive := by
    ext history
    rw [M.bayesBelief_apply]
    exact consistent.isBayesConsistent antichain who site positive history
  have conditioned := M.bayesBelief_map_eq_filter assessment.strategy who site depth
    sameDepth (antichain who site) positive meet
  rw [← bayes] at conditioned
  have unchanged : law.filter information meet = law := by
    ext history
    rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, mass, inv_one, mul_one]
    by_cases member : history ∈ information
    · rw [Set.indicator_of_mem member]
    · rw [Set.indicator_of_notMem member]
      exact ((PMF.apply_eq_zero_iff law history).mpr fun supported =>
        member (seen history supported)).symm
  exact conditioned.trans unchanged

end Single

/-! ## Transport between protocols -/

section Transport

variable {ι : Type*} {E T : ExecutionProtocol ι}
  (M : InformationModel E) (N : InformationModel T)
variable [E.FiniteMovers] [T.FiniteMovers]

section Fiber

variable (project : E.History → T.History) (who : ι)
  (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
  (rawWeight : E.History → ℝ≥0∞) (sourceWeight : T.History → ℝ≥0∞)
  (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
    N.infoOf who (project history).trace = sourceSite.1)

omit [E.FiniteMovers] [T.FiniteMovers] in
/-- Restrict a projected weight sum to the chosen raw fiber: histories of
positive weight projecting into the source fiber lie in the raw fiber. -/
private theorem fiber_sum [DecidableEq T.History]
    (projected : ∀ history : T.History,
      sourceWeight history = ∑' original,
          if project original = history then rawWeight original else 0)
    (reflects : ∀ history, rawWeight history ≠ 0 →
      N.infoOf who (project history).trace = sourceSite.1 →
        M.infoOf who history.trace = rawSite.1)
    (history : N.InformationHistory who sourceSite.1) :
    sourceWeight history.1 =
      ∑' original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then rawWeight original.1 else 0 := by
  classical
  rw [projected, ← tsum_subtype_eq_of_support_subset
    (s := {original : E.History | M.infoOf who original.trace = rawSite.1})]
  · rfl
  · intro original present
    by_cases same : project original = history.1
    · rw [Function.mem_support, ite_eq_left same] at present
      exact reflects original present (by rw [same]; exact history.2)
    · exact absurd (ite_eq_right same) present

omit [E.FiniteMovers] [T.FiniteMovers] in
include maps in
private theorem fiber_mass [DecidableEq T.History]
    (fiber : ∀ history : N.InformationHistory who sourceSite.1,
      sourceWeight history.1 =
        ∑' original : M.InformationHistory who rawSite.1,
          if project original.1 = history.1 then rawWeight original.1 else 0) :
    ∑' original : M.InformationHistory who rawSite.1, rawWeight original.1 =
      ∑' history : N.InformationHistory who sourceSite.1, sourceWeight history.1 := by
  classical
  simp_rw [fiber]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro original
  let image : N.InformationHistory who sourceSite.1 :=
    ⟨project original.1, maps original.1 original.2⟩
  have equal (target : N.InformationHistory who sourceSite.1) :
      project original.1 = target.1 ↔ target = image := by
    change image.1 = target.1 ↔ target = image
    exact ⟨fun same => (Subtype.ext same).symm, fun same => by rw [same]⟩
  simp only [equal, tsum_ite_eq]

end Fiber

variable (raw : (i : ι) → M.BehavioralPolicy i) (source : (i : ι) → N.BehavioralPolicy i)
  (project : E.History → T.History)

section Reach

variable [DecidableEq T.History] (who : ι) (rawSite : M.InformationSite who)
  (sourceSite : N.InformationSite who)
  (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
    N.infoOf who (project history).trace = sourceSite.1)
  (fiber : ∀ history : N.InformationHistory who sourceSite.1,
    N.historyReachWeight source history.1 =
      ∑' original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then M.historyReachWeight raw original.1 else 0)

include maps fiber in
/-- A history map whose reach weights sum over its fibers transports the
site's mass. -/
theorem informationMass_projection_of_reach :
    M.informationMass raw who rawSite = N.informationMass source who sourceSite :=
  fiber_mass M N project who rawSite sourceSite (M.historyReachWeight raw)
    (N.historyReachWeight source) maps fiber

include fiber in
/-- **Bayes projection.** A history map whose reach weights sum over its fibers
transports the Bayes belief. -/
theorem bayesBelief_projection_of_reach
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (rawPositive : 0 < M.informationMass raw who rawSite)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief raw who rawSite rawAntichain rawPositive).map
      (fun original : M.InformationHistory who rawSite.1 =>
        (⟨project original.1, maps original.1 original.2⟩ :
          N.InformationHistory who sourceSite.1)) =
      N.bayesBelief source who sourceSite sourceAntichain sourcePositive := by
  classical
  have mass := M.informationMass_projection_of_reach N raw source project who rawSite sourceSite
    maps fiber
  ext history
  rw [PMF.map_apply, N.bayesBelief_apply, fiber history, ← mass, div_eq_mul_inv,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro original
  rw [M.bayesBelief_apply]
  by_cases same : project original.1 = history.1
  · have equal : history = ⟨project original.1, maps original.1 original.2⟩ :=
      Subtype.ext same.symm
    rw [ite_eq_left equal, ite_eq_left same, div_eq_mul_inv]
  · have different : history ≠ ⟨project original.1, maps original.1 original.2⟩ :=
      fun equal => same (congrArg Subtype.val equal).symm
    rw [ite_eq_right different, ite_eq_right same, zero_mul]

end Reach

/-- A length-preserving history map with matching behavioral laws transports
each reach weight to the sum over its fiber. -/
theorem historyReachWeight_projection [DecidableEq T.History]
    (lengths : ∀ history, (project history).trace.length = history.trace.length)
    (laws : ∀ fuel, (M.runBehavioral raw fuel).map project = N.runBehavioral source fuel)
    (history : T.History) :
    N.historyReachWeight source history =
      ∑' original, if project original = history then M.historyReachWeight raw original else 0 := by
  classical
  unfold historyReachWeight
  rw [← laws history.trace.length, PMF.map_apply]
  apply tsum_congr
  intro original
  by_cases same : project original = history
  · rw [ite_eq_left same.symm, ite_eq_left same, ← same, lengths]
  · rw [ite_eq_right (Ne.symm same), ite_eq_right same]

section Aligned

variable (lengths : ∀ history, (project history).trace.length = history.trace.length)
  (laws : ∀ fuel, (M.runBehavioral raw fuel).map project = N.runBehavioral source fuel)
  (who : ι) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
  (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
    N.infoOf who (project history).trace = sourceSite.1)
  (reflects : ∀ history, 0 < (M.historyReachWeight raw history).toReal →
    N.infoOf who (project history).trace = sourceSite.1 →
      M.infoOf who history.trace = rawSite.1)

include lengths laws reflects in
theorem informationHistoryReach_projection [DecidableEq T.History]
    (history : N.InformationHistory who sourceSite.1) :
    N.historyReachWeight source history.1 =
      ∑' original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then M.historyReachWeight raw original.1 else 0 :=
  fiber_sum M N project who rawSite sourceSite (M.historyReachWeight raw)
    (N.historyReachWeight source)
    (M.historyReachWeight_projection N raw source project lengths laws)
    (fun original present => reflects original
      (ENNReal.toReal_pos present (PMF.apply_ne_top _ _))) history

include lengths laws reflects maps in
/-- Length-preserving projections with matching laws transport site masses
whenever the histories of positive reach reflect the raw fiber. -/
theorem informationMass_projection :
    M.informationMass raw who rawSite = N.informationMass source who sourceSite := by
  classical
  exact M.informationMass_projection_of_reach N raw source project who rawSite sourceSite maps
    (M.informationHistoryReach_projection N raw source project lengths laws who rawSite
      sourceSite reflects)

include lengths laws reflects in
/-- Length-preserving projections with matching laws transport Bayes beliefs
whenever the histories of positive reach reflect the raw fiber. -/
theorem bayesBelief_projection
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (rawPositive : 0 < M.informationMass raw who rawSite)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief raw who rawSite rawAntichain rawPositive).map
      (fun original : M.InformationHistory who rawSite.1 =>
        (⟨project original.1, maps original.1 original.2⟩ :
          N.InformationHistory who sourceSite.1)) =
      N.bayesBelief source who sourceSite sourceAntichain sourcePositive := by
  classical
  exact M.bayesBelief_projection_of_reach N raw source project who rawSite sourceSite maps
    (M.informationHistoryReach_projection N raw source project lengths laws who rawSite
      sourceSite reflects) rawAntichain sourceAntichain rawPositive sourcePositive

end Aligned

section AtDepth

variable (who : ι) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
  (rawDepth sourceDepth : ℕ)
  (rawClock : InformationSite.CommonDepth M rawSite rawDepth)
  (sourceClock : InformationSite.CommonDepth N sourceSite sourceDepth)
  (law : (M.runBehavioral raw rawDepth).map project = N.runBehavioral source sourceDepth)
  (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
    N.infoOf who (project history).trace = sourceSite.1)
  (reflects : ∀ history, 0 < ((M.runBehavioral raw rawDepth) history).toReal →
    N.infoOf who (project history).trace = sourceSite.1 →
      M.infoOf who history.trace = rawSite.1)

include rawClock sourceClock law reflects in
/-- Corresponding decision depths may differ between the two protocols. At
those depths the behavioral laws transport reach weights by fiber sums. -/
theorem informationHistoryReach_projection_at_depth [DecidableEq T.History]
    (history : N.InformationHistory who sourceSite.1) :
    N.historyReachWeight source history.1 =
      ∑' original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then M.historyReachWeight raw original.1 else 0 := by
  have fiber := fiber_sum M N project who rawSite sourceSite (M.runBehavioral raw rawDepth)
    (N.runBehavioral source sourceDepth)
    (fun target => by
      rw [← law, PMF.map_apply]
      apply tsum_congr
      intro original
      by_cases same : project original = target
      · rw [ite_eq_left same.symm, ite_eq_left same]
      · rw [ite_eq_right (Ne.symm same), ite_eq_right same])
    (fun original present => reflects original
      (ENNReal.toReal_pos present (PMF.apply_ne_top _ _))) history
  rw [historyReachWeight, sourceClock history, fiber]
  apply tsum_congr
  intro original
  rw [historyReachWeight, rawClock original]

include rawClock sourceClock law maps reflects in
theorem informationMass_projection_at_depth :
    M.informationMass raw who rawSite = N.informationMass source who sourceSite := by
  classical
  exact M.informationMass_projection_of_reach N raw source project who rawSite sourceSite maps
    (M.informationHistoryReach_projection_at_depth N raw source project who rawSite
      sourceSite rawDepth sourceDepth rawClock sourceClock law reflects)

include rawClock sourceClock law reflects in
/-- Bayes conditioning commutes with a projection between decision depths that
may differ. Applied along fully mixed approximants, it transports off-path
limiting beliefs. -/
theorem bayesBelief_projection_at_depth
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (rawPositive : 0 < M.informationMass raw who rawSite)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief raw who rawSite rawAntichain rawPositive).map
      (fun original : M.InformationHistory who rawSite.1 =>
        (⟨project original.1, maps original.1 original.2⟩ :
          N.InformationHistory who sourceSite.1)) =
      N.bayesBelief source who sourceSite sourceAntichain sourcePositive := by
  classical
  exact M.bayesBelief_projection_of_reach N raw source project who rawSite sourceSite maps
    (M.informationHistoryReach_projection_at_depth N raw source project who rawSite
      sourceSite rawDepth sourceDepth rawClock sourceClock law reflects)
    rawAntichain sourceAntichain rawPositive sourcePositive

end AtDepth

/-- A focal selector can single out one private alias history without changing
that player's Bayes belief. Only the selected profile need reflect the raw
fiber; the native profile may mix over many aliases. -/
theorem bayesBelief_projection_at_depth_of_focal_selector [DecidableEq ι]
    (native selected : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
    (rawDepth sourceDepth : ℕ)
    (rawClock : InformationSite.CommonDepth M rawSite rawDepth)
    (sourceClock : InformationSite.CommonDepth N sourceSite sourceDepth)
    (law : (M.runBehavioral selected rawDepth).map project =
      N.runBehavioral source sourceDepth)
    (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
      N.infoOf who (project history).trace = sourceSite.1)
    (reflects : ∀ history, 0 < ((M.runBehavioral selected rawDepth) history).toReal →
      N.infoOf who (project history).trace = sourceSite.1 →
        M.infoOf who history.trace = rawSite.1)
    (agree : ∀ other, other ≠ who → native other = selected other)
    (nativeCommon : M.CommonPlayerReachAt native who rawSite)
    (selectedCommon : M.CommonPlayerReachAt selected who rawSite)
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (nativePositive : 0 < M.informationMass native who rawSite)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief native who rawSite rawAntichain nativePositive).map
      (fun original : M.InformationHistory who rawSite.1 =>
        (⟨project original.1, maps original.1 original.2⟩ :
          N.InformationHistory who sourceSite.1)) =
      N.bayesBelief source who sourceSite sourceAntichain sourcePositive := by
  have mass := M.informationMass_projection_at_depth N selected source project who rawSite
    sourceSite rawDepth sourceDepth rawClock sourceClock law maps reflects
  have selectedPositive : 0 < M.informationMass selected who rawSite := by
    rw [mass]
    exact sourcePositive
  rw [M.bayesBelief_eq_of_eq_off native selected who rawSite rawAntichain agree
    nativeCommon selectedCommon nativePositive selectedPositive]
  exact M.bayesBelief_projection_at_depth N selected source project who rawSite sourceSite
    rawDepth sourceDepth rawClock sourceClock law maps reflects rawAntichain sourceAntichain
      selectedPositive sourcePositive

/-! ## Readouts -/

section Readout

variable {X : Type*} (strategy : (i : ι) → M.BehavioralPolicy i)
  (who : ι) (site : M.InformationSite who) (sourceSite : N.InformationSite who)
  (readout : E.History → X) (sourceReadout : T.History → X)

open Classical in
/-- The reach weight of a site's histories carrying one readout value. -/
def readoutReach (strategy : (i : ι) → M.BehavioralPolicy i) (who : ι)
    (site : M.InformationSite who) (readout : E.History → X) (value : X) : ℝ≥0∞ :=
  ∑' history : M.InformationHistory who site.1,
    if value = readout history.1 then M.historyReachWeight strategy history.1 else 0

/-- Summing a site's readout reaches recovers the site's mass. -/
theorem tsum_readoutReach :
    ∑' value, M.readoutReach strategy who site readout value =
      M.informationMass strategy who site := by
  classical
  unfold readoutReach informationMass
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun history => by simp only [tsum_ite_eq]

/-- The Bayes posterior of a readout value is its reach share of the site. -/
theorem bayesBelief_readout_apply (antichain : site.IsHistoryAntichain)
    (positive : 0 < M.informationMass strategy who site) (value : X) :
    ((M.bayesBelief strategy who site antichain positive).map
      (fun history => readout history.1)) value =
      M.readoutReach strategy who site readout value / M.informationMass strategy who site := by
  classical
  rw [PMF.map_apply, readoutReach, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro history
  by_cases same : value = readout history.1 <;>
    simp [same, M.bayesBelief_apply, div_eq_mul_inv]

include sourceSite in
/-- **Readout transport.** Two sites with equal readout reaches carry equal
masses and equal Bayes posteriors over the readout. Complete histories may
differ, and no clock is involved. -/
theorem bayesBelief_readout_of_reach
    (source : (i : ι) → N.BehavioralPolicy i)
    (same : ∀ value, M.readoutReach strategy who site readout value =
      N.readoutReach source who sourceSite sourceReadout value)
    (rawAntichain : site.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (rawPositive : 0 < M.informationMass strategy who site)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief strategy who site rawAntichain rawPositive).map
        (fun history => readout history.1) =
      (N.bayesBelief source who sourceSite sourceAntichain sourcePositive).map
        (fun history => sourceReadout history.1) := by
  have mass : M.informationMass strategy who site = N.informationMass source who sourceSite := by
    rw [← M.tsum_readoutReach strategy who site readout,
      ← N.tsum_readoutReach source who sourceSite sourceReadout]
    exact tsum_congr same
  ext value
  rw [M.bayesBelief_readout_apply strategy who site readout rawAntichain rawPositive,
    N.bayesBelief_readout_apply source who sourceSite sourceReadout sourceAntichain
      sourcePositive, same, mass]

open Classical in
/-- Keep a readout on one information event and mark all other histories as
outside it. -/
def informationReadout (who : ι) (site : M.InformationSite who)
    (readout : E.History → X) (history : E.History) : Option X :=
  if M.infoOf who history.trace = site.1 then some (readout history) else none

section AtDepth

variable (depth : ℕ) (sameDepth : InformationSite.CommonDepth M site depth)

include sameDepth in
open Classical in
/-- At a common depth, a readout reach is the probability of the marked readout. -/
theorem readoutReach_eq_informationReadout (value : X) :
    M.readoutReach strategy who site readout value =
      ((M.runBehavioral strategy depth).map (M.informationReadout who site readout))
        (some value) := by
  let fiber : Set E.History := {history | M.infoOf who history.trace = site.1}
  let joint (history : E.History) : ℝ≥0∞ :=
    if value = readout history then (M.runBehavioral strategy depth) history else 0
  rw [PMF.map_apply]
  symm
  calc
    _ = ∑' history, fiber.indicator joint history := by
      apply tsum_congr
      intro history
      by_cases observed : M.infoOf who history.trace = site.1 <;>
        simp [informationReadout, observed, fiber, joint]
    _ = ∑' history : fiber, joint history := (tsum_subtype fiber joint).symm
    _ = _ := tsum_congr fun history => by
      simp only [joint, historyReachWeight, sameDepth history]

variable (source : (i : ι) → N.BehavioralPolicy i) (sourceDepth : ℕ)
  (sourceClock : InformationSite.CommonDepth N sourceSite sourceDepth)
  (law : (M.runBehavioral strategy depth).map (M.informationReadout who site readout) =
    (N.runBehavioral source sourceDepth).map
      (N.informationReadout who sourceSite sourceReadout))

include sameDepth sourceClock law in
/-- Matching marked readout laws at decision depths, which may differ, give
equal site masses. -/
theorem informationMass_readout_at_depth :
    M.informationMass strategy who site = N.informationMass source who sourceSite := by
  rw [← M.tsum_readoutReach strategy who site readout,
    ← N.tsum_readoutReach source who sourceSite sourceReadout]
  refine tsum_congr fun value => ?_
  rw [M.readoutReach_eq_informationReadout strategy who site readout depth sameDepth,
    N.readoutReach_eq_informationReadout source who sourceSite sourceReadout sourceDepth
      sourceClock, law]

include sameDepth sourceClock law in
/-- Matching marked readout laws at decision depths transport the Bayes
posterior over the readout. -/
theorem bayesBelief_readout_at_depth
    (rawAntichain : site.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (rawPositive : 0 < M.informationMass strategy who site)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief strategy who site rawAntichain rawPositive).map
        (fun history => readout history.1) =
      (N.bayesBelief source who sourceSite sourceAntichain sourcePositive).map
        (fun history => sourceReadout history.1) :=
  M.bayesBelief_readout_of_reach N strategy who site sourceSite readout sourceReadout source
    (fun value => by
      rw [M.readoutReach_eq_informationReadout strategy who site readout depth sameDepth,
        N.readoutReach_eq_informationReadout source who sourceSite sourceReadout sourceDepth
          sourceClock, law])
    rawAntichain sourceAntichain rawPositive sourcePositive

end AtDepth

/-- An ordinary readout law suffices when one predicate on the readout
characterizes both information events on the supports of play. -/
theorem informationReadout_law_of_fiber (source : (i : ι) → N.BehavioralPolicy i)
    (depth sourceDepth : ℕ) (predicate : X → Prop)
    (unmarked : (M.runBehavioral strategy depth).map readout =
      (N.runBehavioral source sourceDepth).map sourceReadout)
    (rawFiber : ∀ history ∈ (M.runBehavioral strategy depth).support,
      M.infoOf who history.trace = site.1 ↔ predicate (readout history))
    (sourceFiber : ∀ history ∈ (N.runBehavioral source sourceDepth).support,
      N.infoOf who history.trace = sourceSite.1 ↔ predicate (sourceReadout history)) :
    (M.runBehavioral strategy depth).map (M.informationReadout who site readout) =
      (N.runBehavioral source sourceDepth).map
        (N.informationReadout who sourceSite sourceReadout) := by
  classical
  let mark (value : X) := if predicate value then some value else none
  calc
    _ = ((M.runBehavioral strategy depth).map readout).map mark := by
      rw [PMF.map_comp]
      apply map_congr_on_support _
      intro history supported
      simp only [informationReadout, Function.comp_apply, mark, rawFiber history supported]
    _ = ((N.runBehavioral source sourceDepth).map sourceReadout).map mark :=
      congrArg (fun distribution => distribution.map mark) unmarked
    _ = _ := by
      rw [PMF.map_comp]
      apply map_congr_on_support _
      intro history supported
      simp only [informationReadout, Function.comp_apply, mark, sourceFiber history supported]

end Readout

end Transport

end GameTheory.Protocol.InformationModel
