/-
# Bounded counterfactual decomposition

This module starts the global bridge at its semantic cut. A local behavioral
replacement is invisible strictly before a common-depth information site, and
an exact run split expresses the root gain as the expected continuation gain
at that cut. Later theorems reindex the cut law over the information fiber and
identify the result with canonical counterfactual regret.
-/

import GameTheory.Analysis.Protocol.CounterfactualRegret

noncomputable section

namespace GameTheory.Protocol

open GameTheory Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

/-- Runner congruence needs agreement only at histories where another step can
still be taken. In particular, policies may first differ exactly at the end of
the supplied fuel block. -/
theorem runBehavioralFrom_congr_before
    [Fintype ι]
    {first second : (i : ι) → M.BehavioralPolicy i} :
    ∀ (fuel : ℕ) (history : E.History),
      (∀ (later : E.History),
        ExecutionProtocol.ReachesWithin E fuel history later →
        ¬ E.terminal later.state →
        later.trace.length < history.trace.length + fuel →
        ∀ i,
          first i (M.infoOf i later.trace) =
            second i (M.infoOf i later.trace)) →
      M.runBehavioralFrom first fuel history =
        M.runBehavioralFrom second fuel history := by
  intro fuel
  induction fuel with
  | zero =>
      intro history _hagree
      rfl
  | succ fuel ih =>
      intro history hagree
      by_cases hterm : E.terminal history.state
      · rw [M.runBehavioralFrom_of_terminal _ _ hterm,
          M.runBehavioralFrom_of_terminal _ _ hterm]
      · have hhere : M.behavioralJoint first history.trace hterm =
            M.behavioralJoint second history.trace hterm :=
          M.behavioralJoint_congr history.trace hterm fun i =>
            hagree history (.refl _ _) hterm (by omega) i
        rw [M.runBehavioralFrom_succ_of_not_terminal first fuel hterm,
          M.runBehavioralFrom_succ_of_not_terminal second fuel hterm,
          hhere]
        refine FinDist.bind_congr fun draw _ =>
          FinDist.bindOnSupport_congr fun target realized => ?_
        apply ih
        intro later hreach hlater hlength i
        apply hagree later (.step draw.1 draw.2 realized hreach) hlater
        simp [ExecutionProtocol.History.extend,
          ExecutionProtocol.Trace.length] at hlength ⊢
        omega

/-- Every history in this information fiber occurs at one trace depth. This is
a theorem-side bounded-evaluator certificate, not data stored in the model. -/
def InformationSite.CommonDepth {i : ι}
    (site : M.InformationSite i) (depth : ℕ) : Prop :=
  ∀ history : M.InformationHistory i site.1,
    history.1.trace.length = depth

/-- Replacing one information-local policy cannot affect the law strictly
before a common-depth site. The alternative need agree with the baseline only
away from that one information state. -/
theorem runBehavioral_prefix_eq_of_agree_off_site
    [Fintype ι] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who) (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info) :
    M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative) depth =
      M.runBehavioral strategy depth := by
  unfold InformationModel.runBehavioral
  apply M.runBehavioralFrom_congr_before
  intro later _hreach hterm hbefore player
  by_cases hplayer : player = who
  · subst player
    rw [Profile.update_same]
    by_cases hinfo : M.infoOf who later.trace = site.1
    · have hatDepth : later.trace.length = depth := by
        simpa using hdepth ⟨later, hinfo⟩
      have hlt : later.trace.length < depth := by
        simpa [ExecutionProtocol.initHistory,
          ExecutionProtocol.Trace.length] using hbefore
      exact False.elim (by omega)
    · exact hagree hinfo
  · rw [Profile.update_of_ne _ _ hplayer]

/-- If two profiles have the same law at a cut, their root payoff difference
after a common continuation budget is exactly the cut-law expectation of their
pointwise continuation difference. -/
theorem rootGain_eq_prefixExpectation
    [Fintype ι]
    (first second : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) (depth fuel : ℕ)
    (hprefix : M.runBehavioral first depth =
      M.runBehavioral second depth) :
    (M.runBehavioral first (depth + fuel)).expect payoff -
        (M.runBehavioral second (depth + fuel)).expect payoff =
      (M.runBehavioral second depth).expect fun history =>
        (M.runBehavioralFrom first fuel history).expect payoff -
          (M.runBehavioralFrom second fuel history).expect payoff := by
  unfold InformationModel.runBehavioral at hprefix ⊢
  rw [M.runBehavioralFrom_add first depth fuel,
    M.runBehavioralFrom_add second depth fuel, hprefix,
    FinDist.expect_bind, FinDist.expect_bind, ← FinDist.expect_sub]

/-- Reindexing a common-depth cut law over one information fiber exposes the
canonical counterfactual coefficient. Histories outside the fiber need only
have zero gain on the finite support actually reached at the cut. -/
theorem prefixExpectation_eq_ownReach_mul_counterfactualSum
    [Fintype ι] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (depth : ℕ) (hdepth : InformationSite.CommonDepth M site depth)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (gain : E.History → ℝ)
    (hzero : ∀ history ∈ (M.runBehavioral strategy depth).support,
      M.infoOf who history.trace ≠ site.1 → gain history = 0) :
    (M.runBehavioral strategy depth).expect gain =
      ownReach *
        ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace *
            gain history.1 := by
  unfold FinDist.expect
  calc
    (∑' history : E.History,
        (M.runBehavioral strategy depth).prob history * gain history) =
      ∑' history : E.History,
        {history | M.infoOf who history.trace = site.1}.indicator
          (fun current =>
            (M.runBehavioral strategy depth).prob current * gain current)
          history := by
        apply tsum_congr
        intro history
        by_cases hinfo : M.infoOf who history.trace = site.1
        · simp [Set.indicator, hinfo]
        · by_cases hsupport :
              history ∈ (M.runBehavioral strategy depth).support
          · rw [hzero history hsupport hinfo, mul_zero]
            simp [Set.indicator, hinfo]
          · rw [FinDist.prob_eq_zero_iff.mpr hsupport, zero_mul]
            simp [Set.indicator, hinfo]
    _ = ∑' history : M.InformationHistory who site.1,
          (M.runBehavioral strategy depth).prob history.1 *
            gain history.1 := by
      exact (tsum_subtype
        {history | M.infoOf who history.trace = site.1}
        (fun current =>
          (M.runBehavioral strategy depth).prob current * gain current)).symm
    _ = ∑ history : M.InformationHistory who site.1,
          (M.runBehavioral strategy depth).prob history.1 *
            gain history.1 := tsum_fintype _
    _ = ∑ history : M.InformationHistory who site.1,
          ownReach *
            (M.counterfactualReachProbability strategy who history.1.trace *
              gain history.1) := by
      apply Finset.sum_congr rfl
      intro history _
      have hprob : (M.runBehavioral strategy depth).prob history.1 =
          M.historyReachProbability strategy history.1 := by
        unfold InformationModel.historyReachProbability
        rw [hdepth history]
      rw [hprob,
        M.historyReachProbability_eq_player_mul_counterfactual
          strategy who history.1.trace,
        hown history]
      ring
    _ = ownReach *
        ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace *
            gain history.1 := by
      rw [Finset.mul_sum]

/-- Outside a common-depth site, a policy replacement cannot affect any later
continuation: reaching the site later would put two comparable histories at
the same trace depth. -/
theorem runBehavioralFrom_update_eq_of_outside_commonDepth
    [Fintype ι] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info)
    (history : E.History) (hlength : history.trace.length = depth)
    (hinfo : M.infoOf who history.trace ≠ site.1) (fuel : ℕ) :
    M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative) fuel history =
      M.runBehavioralFrom strategy fuel history := by
  apply M.runBehavioralFrom_congr
  intro later hreach _hlater player
  by_cases hplayer : player = who
  · subst player
    rw [Profile.update_same]
    by_cases hlaterInfo : M.infoOf who later.trace = site.1
    · have hlaterDepth : later.trace.length = depth := by
        simpa using hdepth ⟨later, hlaterInfo⟩
      have hequal : later = history :=
        hreach.eq_of_trace_length_eq (by omega)
      subst later
      exact False.elim (hinfo hlaterInfo)
    · exact hagree hlaterInfo
  · rw [Profile.update_of_ne _ _ hplayer]

/-- Policy differences confined to an earlier common-depth information site
are invisible to every continuation that starts strictly after that depth. -/
theorem runBehavioralFrom_eq_of_agree_off_pastSite
    [Fintype ι]
    (first second : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who) (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hothers : ∀ player, player ≠ who → first player = second player)
    (hwho : ∀ {info : M.InfoState who}, info ≠ site.1 →
      first who info = second who info)
    (history : E.History) (hafter : depth < history.trace.length)
    (fuel : ℕ) :
    M.runBehavioralFrom first fuel history =
      M.runBehavioralFrom second fuel history := by
  apply M.runBehavioralFrom_congr
  intro later hreach _hlater player
  by_cases hplayer : player = who
  · subst player
    by_cases hinfo : M.infoOf who later.trace = site.1
    · have hlaterDepth : later.trace.length = depth := by
        simpa using hdepth ⟨later, hinfo⟩
      have hle := hreach.trace_length_le
      exact False.elim (by omega)
    · exact hwho hinfo
  · exact congrFun (hothers player hplayer)
      (M.infoOf player later.trace)

/-- Changes confined to an earlier common-depth information site do not alter
action regret at a strictly later site. Counterfactual reach already omits the
focal player's policy, and the continuation runner cannot revisit the earlier
site. -/
theorem counterfactualActionRegret_eq_of_agree_off_pastSite
    [Fintype ι] [DecidableEq ι]
    (first second : (i : ι) → M.BehavioralPolicy i)
    (who : ι) [DecidableEq (M.InfoState who)]
    (pastSite : M.InformationSite who) (pastDepth : ℕ)
    (hpastDepth : InformationSite.CommonDepth M pastSite pastDepth)
    (hplayers : ∀ other, other ≠ who → first other = second other)
    (hwho : ∀ {info : M.InfoState who}, info ≠ pastSite.1 →
      first who info = second who info)
    (laterSite : M.InformationSite who)
    [Fintype (M.InformationHistory who laterSite.1)]
    (hlater : ∀ history : M.InformationHistory who laterSite.1,
      pastDepth < history.1.trace.length)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who laterSite.1) :
    M.counterfactualActionRegret first who laterSite payoff fuel choice =
      M.counterfactualActionRegret second who laterSite payoff fuel choice := by
  have hcontinuation : ∀
      (firstPolicy secondPolicy : M.BehavioralPolicy who),
      (∀ {info : M.InfoState who}, info ≠ pastSite.1 →
        firstPolicy info = secondPolicy info) →
      M.counterfactualContinuationValue first who laterSite firstPolicy
          payoff fuel =
        M.counterfactualContinuationValue second who laterSite secondPolicy
          payoff fuel := by
    intro firstPolicy secondPolicy hpolicy
    unfold InformationModel.counterfactualContinuationValue
    apply Finset.sum_congr rfl
    intro history _
    rw [M.counterfactualReachProbability_eq_of_eq_off hplayers
      history.1.trace]
    apply congrArg
      (fun value : ℝ =>
        M.counterfactualReachProbability second who history.1.trace * value)
    unfold InformationModel.behavioralContinuationValue
    apply congrArg (fun law : FinDist E.History => law.expect payoff)
    exact M.runBehavioralFrom_eq_of_agree_off_pastSite
      (Profile.update (sig := M.behavioralSignature) first who firstPolicy)
      (Profile.update (sig := M.behavioralSignature) second who secondPolicy)
      who pastSite pastDepth hpastDepth
      (fun other hne => by
        rw [Profile.update_of_ne _ _ hne, Profile.update_of_ne _ _ hne]
        exact hplayers other hne)
      (fun hinfo => by
        rw [Profile.update_same, Profile.update_same]
        exact hpolicy hinfo)
      history.1 (hlater history) fuel
  have hcommitted : ∀ {info : M.InfoState who}, info ≠ pastSite.1 →
      (first who).commit laterSite.1 choice info =
        (second who).commit laterSite.1 choice info := by
    intro info hinfo
    by_cases hlaterInfo : info = laterSite.1
    · subst info
      rw [BehavioralPolicy.commit_self, BehavioralPolicy.commit_self]
    · rw [BehavioralPolicy.commit_of_ne _ _ _ hlaterInfo,
          BehavioralPolicy.commit_of_ne _ _ _ hlaterInfo]
      exact hwho hinfo
  unfold InformationModel.counterfactualActionRegret
    InformationModel.counterfactualRegret
  rw [hcontinuation ((first who).commit laterSite.1 choice)
      ((second who).commit laterSite.1 choice) hcommitted,
    hcontinuation (first who) (second who) hwho]

/-- The bounded cut gain vanishes on every reached history outside the local
replacement site, including histories absorbed before the cut depth. -/
theorem cutGain_eq_zero_of_info_ne
    [Fintype ι] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (depth fuel : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info)
    (payoff : E.History → ℝ)
    (history : E.History)
    (hsupport : history ∈ (M.runBehavioral strategy depth).support)
    (hinfo : M.infoOf who history.trace ≠ site.1) :
    (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative) fuel history).expect payoff -
      (M.runBehavioralFrom strategy fuel history).expect payoff = 0 := by
  let updated := Profile.update (sig := M.behavioralSignature)
    strategy who alternative
  by_cases hterm : E.terminal history.state
  · rw [M.runBehavioralFrom_of_terminal updated fuel hterm,
      M.runBehavioralFrom_of_terminal strategy fuel hterm, sub_self]
  · have hcut :=
      M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
        strategy depth E.initHistory history (by
          simpa [InformationModel.runBehavioral] using hsupport)
    rcases hcut with hterminal | hlength
    · exact False.elim (hterm hterminal)
    · have hlength' : history.trace.length = depth := by
        simpa [ExecutionProtocol.initHistory,
          ExecutionProtocol.Trace.length] using hlength
      have hruns := M.runBehavioralFrom_update_eq_of_outside_commonDepth
        strategy who site alternative depth hdepth hagree history hlength'
          hinfo fuel
      rw [show Profile.update (sig := M.behavioralSignature)
          strategy who alternative = updated by rfl] at hruns
      rw [hruns, sub_self]

/-- D45 whole-policy regret is the counterfactual sum of the corresponding
ordinary behavioral continuation gains. -/
theorem counterfactualRegret_eq_sum_behavioralContinuationGain
    [Fintype ι] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.counterfactualRegret strategy who site payoff fuel alternative =
      ∑ history : M.InformationHistory who site.1,
        M.counterfactualReachProbability strategy who history.1.trace *
          ((M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature)
                strategy who alternative) fuel history.1).expect payoff -
            (M.runBehavioralFrom strategy fuel history.1).expect payoff) := by
  unfold InformationModel.counterfactualRegret
    InformationModel.counterfactualContinuationValue
    InformationModel.behavioralContinuationValue
  rw [Profile.update_eq_self]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- **Single-site root decomposition.** For a local policy replacement at a
common-depth information site, the exact bounded root gain is alternative own
reach times the existing D45 counterfactual regret. Early terminal histories
are absorbed; no separate runner or payoff semantics is introduced. -/
theorem rootGain_eq_ownReach_mul_counterfactualRegret
    [Fintype ι] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (depth fuel : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (payoff : E.History → ℝ) :
    (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative) (depth + fuel)).expect payoff -
      (M.runBehavioral strategy (depth + fuel)).expect payoff =
        ownReach *
          M.counterfactualRegret strategy who site payoff fuel alternative := by
  let updated := Profile.update (sig := M.behavioralSignature)
    strategy who alternative
  have hprefix : M.runBehavioral updated depth =
      M.runBehavioral strategy depth :=
    M.runBehavioral_prefix_eq_of_agree_off_site strategy who site
      alternative depth hdepth hagree
  rw [M.rootGain_eq_prefixExpectation updated strategy payoff depth fuel
    hprefix]
  let gain : E.History → ℝ := fun history =>
    (M.runBehavioralFrom updated fuel history).expect payoff -
      (M.runBehavioralFrom strategy fuel history).expect payoff
  rw [M.prefixExpectation_eq_ownReach_mul_counterfactualSum strategy who
    site depth hdepth ownReach hown gain]
  · rw [M.counterfactualRegret_eq_sum_behavioralContinuationGain strategy
      who site alternative payoff fuel]
  · intro history hsupport hinfo
    exact M.cutGain_eq_zero_of_info_ne strategy who site alternative depth
      fuel hdepth hagree payoff history hsupport hinfo

/-- Perfect recall supplies the common own-reach coefficient in the
single-site root decomposition. The coefficient is read at the decision
history already carried by `InformationSite`. -/
theorem rootGain_eq_representativeReach_mul_counterfactualRegret_of_perfectRecall
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.PerfectRecall)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (depth fuel : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info)
    (payoff : E.History → ℝ) :
    (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative) (depth + fuel)).expect payoff -
      (M.runBehavioral strategy (depth + fuel)).expect payoff =
        M.playerReachProbability strategy who site.2.choose.1.trace *
          M.counterfactualRegret strategy who site payoff fuel alternative := by
  apply M.rootGain_eq_ownReach_mul_counterfactualRegret strategy who site
    alternative depth fuel hdepth hagree
  intro history
  exact M.playerReachProbability_eq_of_perfectRecall hrecall strategy who
    history.1.trace site.2.choose.1.trace
      (history.2.trans site.2.choose.2.symm)

/-- Pure-action specialization of the perfect-recall root bridge. -/
theorem rootGain_eq_representativeReach_mul_counterfactualActionRegret_of_perfectRecall
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.PerfectRecall)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (choice : M.Choice who site.1)
    (depth fuel : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (payoff : E.History → ℝ) :
    (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature) strategy who
          ((strategy who).commit site.1 choice))
        (depth + fuel)).expect payoff -
      (M.runBehavioral strategy (depth + fuel)).expect payoff =
        M.playerReachProbability strategy who site.2.choose.1.trace *
          M.counterfactualActionRegret strategy who site payoff fuel choice := by
  exact M.rootGain_eq_representativeReach_mul_counterfactualRegret_of_perfectRecall
    hrecall strategy who site ((strategy who).commit site.1 choice)
      depth fuel hdepth (fun hne =>
        BehavioralPolicy.commit_of_ne (strategy who) site.1 choice hne)
      payoff

/-- A finite topological chain of single-site root identities telescopes to a
whole-policy root-gain decomposition. Callers obtain each premise from
`rootGain_eq_ownReach_mul_counterfactualRegret`; this lemma performs no second
evaluation and introduces no aggregate regret definition. -/
theorem rootGain_eq_sum_stepCounterfactualTerms
    [Fintype ι]
    (strategies : ℕ → (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) (horizon steps : ℕ)
    (ownReach localRegret : ℕ → ℝ)
    (hstep : ∀ step < steps,
      (M.runBehavioral (strategies (step + 1)) horizon).expect payoff -
          (M.runBehavioral (strategies step) horizon).expect payoff =
        ownReach step * localRegret step) :
    (M.runBehavioral (strategies steps) horizon).expect payoff -
        (M.runBehavioral (strategies 0) horizon).expect payoff =
      ∑ step ∈ Finset.range steps,
        ownReach step * localRegret step := by
  rw [← Finset.sum_range_sub (fun step =>
    (M.runBehavioral (strategies step) horizon).expect payoff) steps]
  apply Finset.sum_congr rfl
  intro step hmem
  exact hstep step (Finset.mem_range.mp hmem)

end InformationModel

end GameTheory.Protocol
