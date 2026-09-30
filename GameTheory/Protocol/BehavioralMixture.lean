/-
# Behavioral mixture laws

Installing one player's local behavioral law is equivalent to drawing a
choice and continuing under its pure commitment. No-revisit makes this
factorization valid throughout a finite-horizon run.
-/

import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.BehavioralAssessment

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel
/-- At a history in the selected information state, installing a local law
commutes with the one-step joint law: equivalently, first draw the selected
player's choice and then use the corresponding pure commitment.

This is a law identity, not merely an expectation calculation, and it needs
only the finitely many movers already used by behavioral execution. -/
theorem behavioralJoint_update_withLaw_eq_bind
    [E.FiniteMovers] [DecidableEq ι]
    (profile : (i : ι) → M.BehavioralPolicy i) (who : ι)
    (policy : M.BehavioralPolicy who)
    [DecidableEq (M.InfoState who)]
    (info : M.InfoState who) (law : PMF (M.Choice who info))
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
  let current : (i : ι) → PMF (M.Choice i (M.infoOf i trace)) :=
    fun i => profile i (M.infoOf i trace)
  have hwithLaw :
      (fun i => Profile.update (sig := M.behavioralSignature) profile who
          (policy.withLaw (M.infoOf who trace) law) i (M.infoOf i trace)) =
        Function.update current who law := by
    funext i
    by_cases hi : i = who
    · subst i
      rw [Profile.update_same, BehavioralPolicy.withLaw_self, Function.update_self]
    · rw [Profile.update_of_ne _ _ hi, Function.update_of_ne hi]
  have hcommit (choice : M.Choice who (M.infoOf who trace)) :
      (fun i => Profile.update (sig := M.behavioralSignature) profile who
          (policy.commit (M.infoOf who trace) choice) i (M.infoOf i trace)) =
        Function.update current who (PMF.pure choice) := by
    funext i
    by_cases hi : i = who
    · subst i
      rw [Profile.update_same, BehavioralPolicy.commit_self, Function.update_self]
    · rw [Profile.update_of_ne _ _ hi, Function.update_of_ne hi]
  have hdrawn : who ∈ E.movers state ∨ IsPointMass law := by
    by_cases hactive : E.active state who
    · exact Or.inl ((E.mem_movers).2 hactive)
    · have := M.subsingleton_choice_of_not_active trace hactive
      exact Or.inr (isPointMass_of_subsingleton law)
  unfold behavioralJoint
  rw [hwithLaw, finitaryProduct_update_bind current law hdrawn, PMF.map_bind]
  simp only [hcommit]

/-- After leaving a genuine decision at `info`, a persistent installed law and
one of its pure commitments are observationally identical to the remaining
run when that information state cannot matter twice. -/
theorem withLaw_eq_commit_after_actsOnce
    (hactsOnce : M.ActsOnceWhereItMatters)
    {who : ι}
    (policy : M.BehavioralPolicy who)
    [DecidableEq (M.InfoState who)]
    (info : M.InfoState who) (law : PMF (M.Choice who info))
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
      exact eq_pure_of_subsingleton law choice
  · exact M.behavioral_eq_of_not_active _ _ later.trace hactiveLater

/-- Behavioral continuation from a nonterminal selected decision is affine in
the law installed there.  No global finiteness of information states is used:
the proof factors only the current finite player product, then uses no-revisit
to make the selected coordinate invisible downstream. -/
theorem runBehavioralFrom_update_withLaw_eq_bind
    [E.FiniteMovers] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (profile : (i : ι) → M.BehavioralPolicy i) (who : ι)
    (policy : M.BehavioralPolicy who)
    [DecidableEq (M.InfoState who)]
    (info : M.InfoState who) (law : PMF (M.Choice who info))
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
    PMF.bind_bind]
  refine bind_congr_on_support law fun choice _ => ?_
  rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm]
  refine bind_congr_on_support _ fun draw _ => ?_
  refine bindOnSupport_congr _ fun target realized => ?_
  refine M.runBehavioralFrom_congr fuel _ fun later hreach hlater player => ?_
  by_cases hplayer : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    exact M.withLaw_eq_commit_after_actsOnce hactsOnce policy
      info law choice (h := h) hinfo hactive draw.2 realized later hreach hlater
  · rw [Profile.update_of_ne _ _ hplayer,
      Profile.update_of_ne _ _ hplayer]

/-- Installing a local law factors the belief-averaged outcome law into a
choice draw followed by the corresponding committed continuation. -/
theorem BehavioralAssessment.truncatedContinuationContext_withLaw_outcome_eq_bind
    [E.FiniteMovers] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (assessment : M.BehavioralAssessment)
    {i : ι} [DecidableEq (M.InfoState i)] (site : M.InformationSite i)
    (policy : M.BehavioralPolicy i) (law : PMF (M.Choice i site.1))
    (payoff : E.History → ℝ) (fuel : ℕ) :
    (assessment.truncatedContinuationContext site payoff (fuel + 1)).outcome
        (policy.withLaw site.1 law) =
      law.bind (fun choice =>
        (assessment.truncatedContinuationContext site payoff (fuel + 1)).outcome
          (policy.commit site.1 choice)) := by
  let belief := assessment.belief i site
  have hkernel (history : M.InformationHistory i site.1) :
      M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) assessment.strategy i
            (policy.withLaw site.1 law)) (fuel + 1) history.1 =
        law.bind fun choice =>
          M.runBehavioralFrom
            (Profile.update (sig := M.behavioralSignature) assessment.strategy i
              (policy.commit site.1 choice)) (fuel + 1) history.1 := by
    by_cases hterminal : E.terminal history.1.state
    · simp only [M.runBehavioralFrom_of_terminal _ _ hterminal,
        PMF.bind_const]
    · exact M.runBehavioralFrom_update_withLaw_eq_bind hactsOnce
        assessment.strategy i policy site.1 law history.1 history.2 hterminal
        (InformationSite.active M site history) fuel
  show belief.bind (fun history =>
      M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy i
          (policy.withLaw site.1 law)) (fuel + 1) history.1) =
    law.bind (fun choice => belief.bind (fun history =>
      M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy i
          (policy.commit site.1 choice)) (fuel + 1) history.1))
  calc
    _ = belief.bind (fun history => law.bind fun choice =>
        M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) assessment.strategy i
            (policy.commit site.1 choice)) (fuel + 1) history.1) := by
      apply congrArg
      funext history
      exact hkernel history
    _ = _ := PMF.bind_comm belief law fun history choice =>
      M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy i
          (policy.commit site.1 choice)) (fuel + 1) history.1

/-- The installed-law guard supplies supported committed continuation guards
after the outcome-law factorization. -/
theorem BehavioralAssessment.truncatedContinuationContext_withLaw_commit_integrable
    [E.FiniteMovers] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (assessment : M.BehavioralAssessment)
    {i : ι} [DecidableEq (M.InfoState i)] (site : M.InformationSite i)
    (policy : M.BehavioralPolicy i) (law : PMF (M.Choice i site.1))
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hbase : (assessment.truncatedContinuationContext site payoff (fuel + 1)).IntegrableAt
      (policy.withLaw site.1 law))
    (choice : M.Choice i site.1) (hchoice : choice ∈ law.support) :
    (assessment.truncatedContinuationContext site payoff (fuel + 1)).IntegrableAt
      (policy.commit site.1 choice) := by
  let q := fun choice : M.Choice i site.1 =>
    (assessment.belief i site).bind fun history =>
      M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy i
          (policy.commit site.1 choice)) (fuel + 1) history.1
  have hlaw := assessment.truncatedContinuationContext_withLaw_outcome_eq_bind
    M hactsOnce site policy law payoff fuel
  have hbind : PayoffIntegrable (law.bind q) payoff := by
    show PayoffIntegrable (law.bind fun choice =>
      (assessment.truncatedContinuationContext site payoff (fuel + 1)).outcome
        (policy.commit site.1 choice)) payoff
    rw [← hlaw]
    exact hbase
  exact payoffIntegrable_bind_conditional_on_support law q payoff hbind
    choice hchoice

/-- Belief averaging preserves local-law affinity when decision information is
not revisited. Supported commit values are integrated from the installed-law
guard; no extra branch-integrability premise is required. -/
theorem BehavioralAssessment.truncatedContinuationContext_withLaw_eq_expect
    [E.FiniteMovers] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (assessment : M.BehavioralAssessment)
    {i : ι} [DecidableEq (M.InfoState i)] (site : M.InformationSite i)
    (policy : M.BehavioralPolicy i) (law : PMF (M.Choice i site.1))
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hbase : (assessment.truncatedContinuationContext site payoff (fuel + 1)).IntegrableAt
      (policy.withLaw site.1 law))
    (value : M.Choice i site.1 → ℝ)
    (hvalue : ∀ choice ∈ law.support,
      value choice = (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
        (policy.commit site.1 choice)) :
    PayoffIntegrable law value ∧
      (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
          (policy.withLaw site.1 law) = expect law value := by
  let belief := assessment.belief i site
  let q := fun choice : M.Choice i site.1 =>
    belief.bind fun history =>
      M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy i
          (policy.commit site.1 choice)) (fuel + 1) history.1
  have hlaw :
      (assessment.truncatedContinuationContext site payoff (fuel + 1)).outcome
          (policy.withLaw site.1 law) = law.bind q := by
    exact assessment.truncatedContinuationContext_withLaw_outcome_eq_bind
      M hactsOnce site policy law payoff fuel
  have hbind : PayoffIntegrable (law.bind q) payoff := by
    rw [← hlaw]
    exact hbase
  have hvalue' : ∀ choice ∈ law.support,
      value choice = expect (q choice) payoff := by
    intro choice hchoice
    rw [hvalue choice hchoice]
    rfl
  have houter := payoffIntegrable_bind_conditionalValue_on_support
    law q payoff hbind value hvalue'
  have htower := expect_bind_tower_on_support law q payoff hbind value hvalue'
  refine ⟨houter, ?_⟩
  show expect _ payoff = expect law value
  exact (expect_congr_law hlaw payoff).trans htower


end InformationModel
end GameTheory.Protocol
