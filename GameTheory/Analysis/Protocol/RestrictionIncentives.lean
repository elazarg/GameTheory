/-
# Incentives at retained sites

An extending profile of the larger protocol has, at a retained site with the
embedded belief, exactly the continuation values of the smaller protocol for
every compliant deviation. The new choices at the site are controlled by a
comparison with a whole continuation policy of the smaller protocol; since a
local law is a mixture of committed choices when decisions are not revisited,
comparisons of single choices cover every local lottery. Play is terminal and
histories are finitely many.
-/

import GameTheory.Protocol.BehavioralMixture
import GameTheory.Protocol.FiniteInformation
import GameTheory.Protocol.RestrictionExecution

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {ι : Type*} [DecidableEq ι]

/-- **Local lotteries are mixtures of committed choices.** With finitely many
histories and no consequential revisit of decisions, a site's continuation
value of a local law is the law's expectation of the values of committing to
each choice. -/
theorem BehavioralAssessment.continuationContext_withLaw_eq_expect {E : ExecutionProtocol ι}
    {M : InformationModel E} [E.FiniteMovers] [Finite E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (assessment : M.BehavioralAssessment) (certificate : E.WellFoundedHistories)
    {who : ι} [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    (policy : M.BehavioralPolicy who) (law : PMF (M.Choice who site.1))
    (payoff : E.History → ℝ) :
    (assessment.continuationContext certificate site payoff).value (policy.withLaw site.1 law) =
      expect law (fun choice => (assessment.continuationContext certificate site payoff).value
        (policy.commit site.1 choice)) := by
  let _ := Fintype.ofFinite E.History
  obtain ⟨bound, positive, bounded⟩ := E.exists_pos_boundedHorizon
  obtain ⟨fuel, rfl⟩ : ∃ fuel, bound = fuel + 1 := ⟨bound - 1, by omega⟩
  simp only [assessment.continuationContext_eq_truncated_of_bounded certificate bounded]
  exact (assessment.truncatedContinuationContext_withLaw_eq_expect M hactsOnce site policy law
    payoff fuel (payoffIntegrable_of_finite _ _) _ fun _ _ => rfl).2

namespace ActionRestriction

variable {E T : ExecutionProtocol ι} {M : InformationModel E} {N : InformationModel T}
  (restriction : M.ActionRestriction N)
variable [E.FiniteMovers] [T.FiniteMovers]

omit [E.FiniteMovers] [T.FiniteMovers] in
/-- Installing corresponding local laws preserves the extension. -/
theorem extends_withLaw (source : (i : ι) → M.BehavioralPolicy i)
    (target : (i : ι) → N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target)
    (who : ι) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who) (law : PMF (M.Choice who site.1)) :
    restriction.ExtendsProfile
      (Profile.update (sig := M.behavioralSignature) source who
        ((source who).withLaw site.1 law))
      (Profile.update (sig := N.behavioralSignature) target who
        ((target who).withLaw (restriction.site who site).1
          (law.map (restriction.choice who site.1)))) := by
  intro other current
  by_cases samePlayer : other = who
  · subst other
    rw [Profile.update_same, Profile.update_same]
    by_cases sameSite : current.1 = site.1
    · have equal : current = site := Subtype.ext sameSite
      subst current
      simp only [site_val, BehavioralPolicy.withLaw_self]
    · rw [BehavioralPolicy.withLaw_of_ne _ _ _ sameSite,
        BehavioralPolicy.withLaw_of_ne _ _ _ (by
          exact fun equal => sameSite ((restriction.information who).injective equal))]
      exact agrees who current
  · rw [Profile.update_of_ne _ _ samePlayer, Profile.update_of_ne _ _ samePlayer]
    exact agrees other current

omit [E.FiniteMovers] [T.FiniteMovers] in
/-- Committing to corresponding choices preserves the extension. -/
theorem extends_commit (source : (i : ι) → M.BehavioralPolicy i)
    (target : (i : ι) → N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target)
    (who : ι) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who) (original : M.Choice who site.1) :
    restriction.ExtendsProfile
      (Profile.update (sig := M.behavioralSignature) source who
        ((source who).commit site.1 original))
      (Profile.update (sig := N.behavioralSignature) target who
        ((target who).commit (restriction.site who site).1
          (restriction.choice who site.1 original))) := by
  intro other current
  by_cases samePlayer : other = who
  · subst other
    rw [Profile.update_same, Profile.update_same]
    by_cases sameSite : current.1 = site.1
    · have equal : current = site := Subtype.ext sameSite
      subst current
      rw [BehavioralPolicy.commit_self, PMF.pure_map]
      exact BehavioralPolicy.commit_self _ _ _
    · rw [BehavioralPolicy.commit_of_ne _ _ _ sameSite]
      have different : restriction.information who current.1 ≠ (restriction.site who site).1 :=
        fun equal => sameSite ((restriction.information who).injective equal)
      exact (BehavioralPolicy.commit_of_ne _ _ _ different).trans (agrees who current)
  · rw [Profile.update_of_ne _ _ samePlayer, Profile.update_of_ne _ _ samePlayer]
    exact agrees other current

variable [Finite T.History] (sourceCertificate : E.WellFoundedHistories)
  (targetCertificate : T.WellFoundedHistories)

/-- Terminal continuation laws correspond at a retained site with the embedded
belief whenever the compared deviations extend each other. -/
theorem context_outcome_eq (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (who : ι) (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (original : M.BehavioralPolicy who) (translated : N.BehavioralPolicy who)
    (agrees : restriction.ExtendsProfile
      (Profile.update (sig := M.behavioralSignature) source.strategy who original)
      (Profile.update (sig := N.behavioralSignature) target.strategy who translated))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ) :
    (target.continuationContext targetCertificate (restriction.site who site)
        targetPayoff).outcome translated =
      ((source.continuationContext sourceCertificate site sourcePayoff).outcome original).map
        restriction.history := by
  change (target.belief who (restriction.site who site)).bind _ =
    ((source.belief who site).bind _).map restriction.history
  rw [belief, PMF.bind_map, PMF.map_bind]
  apply bind_congr_on_support
  intro history _
  simp only [Function.comp_apply, informationHistory_val]
  exact (restriction.terminal_law sourceCertificate targetCertificate _ _ agrees history.1).symm

/-- Corresponding continuation values agree when the payoffs correspond. -/
theorem context_value_eq (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (who : ι) (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (original : M.BehavioralPolicy who) (translated : N.BehavioralPolicy who)
    (agrees : restriction.ExtendsProfile
      (Profile.update (sig := M.behavioralSignature) source.strategy who original)
      (Profile.update (sig := N.behavioralSignature) target.strategy who translated))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (payoff : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history) :
    (target.continuationContext targetCertificate (restriction.site who site)
        targetPayoff).value translated =
      (source.continuationContext sourceCertificate site sourcePayoff).value original := by
  unfold Context.value
  rw [restriction.context_outcome_eq sourceCertificate targetCertificate source target who site
    belief original translated agrees sourcePayoff targetPayoff, expect_map]
  exact expect_congr_on_support fun history _ => payoff history

/-- An embedded local law has exactly its value in the smaller protocol. -/
theorem context_withLaw_value_eq
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (agrees : restriction.ExtendsProfile source.strategy target.strategy)
    (who : ι) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (law : PMF (M.Choice who site.1))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (payoff : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history) :
    (target.continuationContext targetCertificate (restriction.site who site) targetPayoff).value
        ((target.strategy who).withLaw (restriction.site who site).1
          (law.map (restriction.choice who site.1))) =
      (source.continuationContext sourceCertificate site sourcePayoff).value
        ((source.strategy who).withLaw site.1 law) :=
  restriction.context_value_eq sourceCertificate targetCertificate source target who site belief
    _ _ (restriction.extends_withLaw source.strategy target.strategy agrees who site law)
    sourcePayoff targetPayoff payoff

/-- **Retained local optimality from whole-policy comparisons.** At a retained
site, if each new choice is bounded by the value of some whole continuation
policy of the smaller protocol, sequential rationality of the smaller
protocol makes every local law of the larger one unprofitable. -/
theorem retained_localOptimal_of_continuation
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (agrees : restriction.ExtendsProfile source.strategy target.strategy)
    (hactsOnce : N.ActsOnceWhereItMatters)
    (who : ι) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (payoff : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history)
    (rational : source.IsSequentiallyRationalAt site
      (source.continuationContext sourceCertificate site sourcePayoff))
    (comparison : ∀ action : N.Choice who (restriction.site who site).1,
      action ∉ Set.range (restriction.choice who site.1) →
      ∃ alternative : M.BehavioralPolicy who,
        (target.continuationContext targetCertificate (restriction.site who site)
            targetPayoff).value
            ((target.strategy who).commit (restriction.site who site).1 action) ≤
          (source.continuationContext sourceCertificate site sourcePayoff).value alternative)
    (law : PMF (N.Choice who (restriction.site who site).1)) :
    (target.continuationContext targetCertificate (restriction.site who site) targetPayoff).value
        ((target.strategy who).withLaw (restriction.site who site).1 law) ≤
      (target.continuationContext targetCertificate (restriction.site who site)
        targetPayoff).value (target.strategy who) := by
  classical
  have _ : Finite E.History := Finite.of_injective restriction.history restriction.history.injective
  have real := (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    fun _ _ => payoffIntegrable_of_finite _ _).mp rational
  have baseline := restriction.context_value_eq sourceCertificate targetCertificate source target
    who site belief (source.strategy who) (target.strategy who)
    (by simpa only [Profile.update_eq_self] using agrees) sourcePayoff targetPayoff payoff
  have pureOptimal (action : N.Choice who (restriction.site who site).1) :
      (target.continuationContext targetCertificate (restriction.site who site)
          targetPayoff).value
          ((target.strategy who).commit (restriction.site who site).1 action) ≤
        (target.continuationContext targetCertificate (restriction.site who site)
          targetPayoff).value (target.strategy who) := by
    by_cases permitted : action ∈ Set.range (restriction.choice who site.1)
    · obtain ⟨original, rfl⟩ := permitted
      have equality := restriction.context_value_eq sourceCertificate targetCertificate source
        target who site belief ((source.strategy who).commit site.1 original)
        ((target.strategy who).commit (restriction.site who site).1
          (restriction.choice who site.1 original))
        (restriction.extends_commit source.strategy target.strategy agrees who site original)
        sourcePayoff targetPayoff payoff
      rw [equality, baseline]
      exact real ((source.strategy who).commit site.1 original) (Set.mem_univ _)
    · obtain ⟨alternative, bound⟩ := comparison action permitted
      exact bound.trans ((real alternative (Set.mem_univ _)).trans_eq baseline.symm)
  rw [target.continuationContext_withLaw_eq_expect hactsOnce targetCertificate
    (restriction.site who site) (target.strategy who) law targetPayoff]
  exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun action _ => pureOptimal action

/-- **Retained local optimality from comparators.** Each new choice is bounded
by one legal local lottery of the smaller protocol, shared by all hidden
histories of the site, under the same remaining profiles. -/
theorem retained_localOptimal_of_comparator
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (agrees : restriction.ExtendsProfile source.strategy target.strategy)
    (hactsOnce : N.ActsOnceWhereItMatters)
    (who : ι) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (payoff : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history)
    (rational : source.IsSequentiallyRationalAt site
      (source.continuationContext sourceCertificate site sourcePayoff))
    (comparator : N.Choice who (restriction.site who site).1 → PMF (M.Choice who site.1))
    (comparison : ∀ action : N.Choice who (restriction.site who site).1,
      action ∉ Set.range (restriction.choice who site.1) →
      ∀ history : M.InformationHistory who site.1,
        expect (N.runBehavioralTerminalFrom targetCertificate
          (Profile.update (sig := N.behavioralSignature) target.strategy who
            ((target.strategy who).commit (restriction.site who site).1 action))
          (restriction.history history.1)) targetPayoff ≤
        expect (M.runBehavioralTerminalFrom sourceCertificate
          (Profile.update (sig := M.behavioralSignature) source.strategy who
            ((source.strategy who).withLaw site.1 (comparator action)))
          history.1) sourcePayoff)
    (law : PMF (N.Choice who (restriction.site who site).1)) :
    (target.continuationContext targetCertificate (restriction.site who site) targetPayoff).value
        ((target.strategy who).withLaw (restriction.site who site).1 law) ≤
      (target.continuationContext targetCertificate (restriction.site who site)
        targetPayoff).value (target.strategy who) := by
  have _ : Finite E.History := Finite.of_injective restriction.history restriction.history.injective
  apply restriction.retained_localOptimal_of_continuation sourceCertificate targetCertificate
    source target agrees hactsOnce who site belief sourcePayoff targetPayoff payoff rational _ law
  intro action extra
  refine ⟨(source.strategy who).withLaw site.1 (comparator action), ?_⟩
  unfold Context.value
  change expect ((target.belief who (restriction.site who site)).bind _) _ ≤
    expect ((source.belief who site).bind _) _
  rw [belief, PMF.bind_map, expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  exact expect_mono (fun history _ => comparison action extra history)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

end ActionRestriction

end GameTheory.Protocol.InformationModel
