/-
# One-shot optimality at an unreached decision

The incumbent exits at the root and would reward at the decision that exiting
leaves unreached. Trembles toward entering and punishing converge to this
assessment, so it is consistent without being fully mixed. It is optimal
against every single-site law change, and the one-shot deviation principle for
consistent assessments makes it a sequential equilibrium.
-/

import GameTheory.Analysis.Protocol.InformationLocalizationTest
import GameTheory.Analysis.Protocol.SequentialOneShot

noncomputable section

namespace GameTheory.Tests.SequentialOneShot

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open GameTheory.Tests.SubgamePerfect GameTheory.Tests.SubgameLocalization
open GameTheory.Tests.InformationLocalization
open InformationModel

/-- Every legal transition leaves the root by exiting or entering, or leaves
the decision by punishing or rewarding. -/
theorem step_cases {source target : State} {joint : Unit → Option Action}
    (legal : arena.Legal source joint)
    (realized : target ∈ (arena.step source ⟨joint, legal⟩).support) :
    (source = .root ∧ joint () = some .exit ∧ target = .exited) ∨
      (source = .root ∧ joint () = some .enter ∧ target = .decision) ∨
      (source = .decision ∧ joint () = some .punish ∧ target = .punished) ∨
      (source = .decision ∧ joint () = some .reward ∧ target = .rewarded) := by
  have hoption := ExecutionProtocol.legalOption_of_legal legal ()
  cases hchoice : joint () with
  | none =>
      rw [hchoice] at hoption
      exact absurd (legal.1 : ¬ arena.terminal source) fun hrunning => by
        cases source <;> simp_all [LegalOption]
  | some action =>
      rw [hchoice] at hoption
      obtain ⟨hactive, havailable⟩ := hoption
      cases source <;> cases action <;> simp_all [arena]

theorem arena_isTreeShaped : arena.IsTreeShaped := by
  apply ExecutionProtocol.isTreeShaped_of_predecessor_unique
  · intro source joint legal hinit
    rcases step_cases legal hinit with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> cases h
  · intro target firstSource secondSource firstJoint secondJoint firstLegal secondLegal
      hfirst hsecond
    rcases step_cases firstLegal hfirst with
      ⟨hsource, hjoint, htarget⟩ | ⟨hsource, hjoint, htarget⟩ |
        ⟨hsource, hjoint, htarget⟩ | ⟨hsource, hjoint, htarget⟩ <;>
    rcases step_cases secondLegal hsecond with
      ⟨hsource', hjoint', htarget'⟩ | ⟨hsource', hjoint', htarget'⟩ |
        ⟨hsource', hjoint', htarget'⟩ | ⟨hsource', hjoint', htarget'⟩ <;>
    first
      | exact ⟨hsource.trans hsource'.symm, funext fun u => by
          cases u
          exact hjoint.trans hjoint'.symm⟩
      | exact absurd (htarget.symm.trans htarget') (by simp)

instance : Fintype arena.History := arena.historyFintype arena_isTreeShaped

/-- The root information site. -/
def rootSite : model.InformationSite () :=
  ⟨State.root, ⟨⟨arena.initHistory, signals_infoOf_state _⟩, root_not_terminal, .exit,
    by simp [SubgamePerfect.menu]⟩⟩

/-- The player decides only at the root and at the decision. -/
theorem site_cases (site : model.InformationSite ()) :
    site.1 = .root ∨ site.1 = .decision := by
  obtain ⟨info, _, _, action, haction⟩ := site
  change some action ∈ SubgamePerfect.menu info at haction
  cases info <;>
    first | exact Or.inl rfl | exact Or.inr rfl | simp [SubgamePerfect.menu] at haction

/-- A positive tremble weight that tends to zero. -/
def weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  positivity

theorem weight_lt_one (n : ℕ) : weight n < 1 := by
  unfold weight
  rw [div_lt_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem weight_tendsto_zero : Tendsto weight atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  simp only [weight, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  ring

/-- Tremble toward entering and punishing; otherwise exit and reward. -/
def tremblePolicy (n : ℕ) : model.BehavioralPolicy ()
  | .root => mix (weight n) (weight_pos n).le (weight_lt_one n).le
      (PMF.pure ⟨some .enter, by simp [SubgamePerfect.menu]⟩)
      (PMF.pure ⟨some .exit, by simp [SubgamePerfect.menu]⟩)
  | .decision => mix (weight n) (weight_pos n).le (weight_lt_one n).le
      (PMF.pure ⟨some .punish, by simp [SubgamePerfect.menu]⟩)
      (PMF.pure ⟨some .reward, by simp [SubgamePerfect.menu]⟩)
  | .exited => PMF.pure ⟨none, by simp [SubgamePerfect.menu]⟩
  | .punished => PMF.pure ⟨none, by simp [SubgamePerfect.menu]⟩
  | .rewarded => PMF.pure ⟨none, by simp [SubgamePerfect.menu]⟩

/-- Exit at the root and reward at the decision. -/
def rewardingProfile : Profile model.strategicSignature :=
  Profile.update incumbentProfile () rewardingPolicy

def rewardingAssessment : model.BehavioralAssessment :=
  BehavioralAssessment.ofStrategy fun who => (rewardingProfile who).toBehavioral

def trembleAssessment (n : ℕ) : model.BehavioralAssessment :=
  BehavioralAssessment.ofStrategy fun _ => tremblePolicy n

theorem trembleAssessment_fullyMixed (n : ℕ) : (trembleAssessment n).IsFullyMixed := by
  rintro ⟨⟩ ⟨info, hinfo⟩ ⟨choice, hchoice⟩
  rcases site_cases ⟨info, hinfo⟩ with hinfo' | hinfo' <;> change info = _ at hinfo' <;>
    subst hinfo'
  · change choice ∈ SubgamePerfect.menu State.root at hchoice
    have hcases : choice = some .exit ∨ choice = some .enter := by
      simpa [SubgamePerfect.menu] using hchoice
    rcases hcases with rfl | rfl
    · exact mem_support_mix_right (weight n) (weight_pos n).le (weight_lt_one n).le
        (weight_lt_one n) (by simp)
    · exact mem_support_mix_left (weight n) (weight_pos n).le (weight_lt_one n).le
        (weight_pos n) (by simp)
  · change choice ∈ SubgamePerfect.menu State.decision at hchoice
    have hcases : choice = some .punish ∨ choice = some .reward := by
      simpa [SubgamePerfect.menu] using hchoice
    rcases hcases with rfl | rfl
    · exact mem_support_mix_left (weight n) (weight_pos n).le (weight_lt_one n).le
        (weight_pos n) (by simp)
    · exact mem_support_mix_right (weight n) (weight_pos n).le (weight_lt_one n).le
        (weight_lt_one n) (by simp)

theorem trembleAssessment_converges :
    BehavioralAssessmentConvergesPointwise trembleAssessment rewardingAssessment := by
  refine ⟨fun who site => ?_, fun who site => pmfConvergesPointwise_const _⟩
  cases who
  rcases site with ⟨info, hinfo⟩
  rcases site_cases ⟨info, hinfo⟩ with hroot | hdecision
  · change info = .root at hroot
    subst hroot
    exact pmfConvergesPointwise_mix_zero weight (fun n => (weight_pos n).le)
      (fun n => (weight_lt_one n).le) weight_tendsto_zero _ _
  · change info = .decision at hdecision
    subst hdecision
    exact pmfConvergesPointwise_mix_zero weight (fun n => (weight_pos n).le)
      (fun n => (weight_lt_one n).le) weight_tendsto_zero _ _

/-- Rewarding off path is Kreps-Wilson consistent. -/
theorem rewardingAssessment_consistent :
    rewardingAssessment.IsSequentiallyConsistent decisionRecall.decisionInformationAntichain :=
  ⟨trembleAssessment, fun n => ⟨trembleAssessment_fullyMixed n, bayes_ofStrategy _⟩,
    trembleAssessment_converges⟩

/-- The assessment never enters, so it is not fully mixed. -/
theorem rewardingAssessment_not_fullyMixed : ¬ rewardingAssessment.IsFullyMixed := by
  intro hfull
  have henter := hfull () rootSite ⟨some .enter, by simp [SubgamePerfect.menu, rootSite]⟩
  simp only [rewardingAssessment, BehavioralAssessment.ofStrategy_strategy, rewardingProfile,
    Profile.update_same, Policy.toBehavioral, PMF.mem_support_pure_iff] at henter
  exact absurd (congrArg Subtype.val henter) (by simp [rewardingPolicy, rootSite])

/-- The payoff read by assessments. -/
def sePayoff (who : Unit) (history : arena.History) : ℝ := payoff history who

/-- Each site has one history, so a continuation value is the value from it. -/
theorem value_eq (strategy : (who : Unit) → model.BehavioralPolicy who)
    (site : model.InformationSite ()) (history : model.InformationHistory () site.1)
    (policy : model.BehavioralPolicy ()) :
    ((BehavioralAssessment.ofStrategy strategy).continuationContext arena_wellFoundedHistories
        site (sePayoff ())).value policy =
      expect (model.runBehavioralTerminalFrom arena_wellFoundedHistories
        (Profile.update (sig := model.behavioralSignature) strategy () policy) history.1)
        (fun final => payoff final ()) := by
  rw [BehavioralAssessment.continuationContext_value]
  change expect ((PMF.pure (Classical.choose site.2)).bind _) _ = _
  rw [PMF.pure_bind, site_history_unique site (Classical.choose site.2) history]
  rfl

/-- Exiting earns `2` at the root. -/
theorem rewarding_value_root :
    arena.historyBackwardValue arena_wellFoundedHistories
        (model.historyChooser rewardingProfile) (fun history => payoff history ())
        arena.initHistory = 2 := by
  have hinit : ¬ arena.terminal arena.initHistory.state := by
    simpa only [ExecutionProtocol.initHistory_state] using root_not_terminal
  apply backwardValue_of_constant_successors _ _ hinit 2
  intro target realized _
  have hstep : arena.step arena.initHistory.state
      (model.historyChooser rewardingProfile arena.initHistory hinit) = PMF.pure .exited := rfl
  rw [hstep, PMF.mem_support_pure_iff] at realized
  subst target
  rw [arena.historyBackwardValue_of_terminal terminal_exited]
  rfl

/-- Play from the decision ends by punishing or rewarding, so no policy earns
more than `1` there. -/
theorem decision_continuation_le_one (profile : (who : Unit) → model.BehavioralPolicy who) :
    expect (model.runBehavioralTerminalFrom arena_wellFoundedHistories profile decisionHistory)
      (fun final => payoff final ()) ≤ 1 := by
  calc
    _ ≤ expect (model.runBehavioralTerminalFrom arena_wellFoundedHistories profile
          decisionHistory) (fun _ => (1 : ℝ)) := by
      refine expect_mono (fun final hfinal => ?_) (payoff_integrable _)
        (payoffIntegrable_constant _ _)
      have hterm := model.runBehavioralTerminalFrom_support_terminal arena_wellFoundedHistories
        profile decisionHistory final hfinal
      obtain ⟨fuel, hreach⟩ :=
        arena.randomizedBackwardLaw_support_reaches decisionHistory final hfinal
      rcases hreach.eq_or_step with hsame | ⟨joint, legal, reached, realized, rest, hrest⟩
      · subst hsame
        exact absurd hterm decision_not_terminal
      · have hfinal : final = decisionHistory.extend legal realized :=
          hrest.eq_of_terminal (by
            rcases step_cases legal realized with
              ⟨h, -, rfl⟩ | ⟨h, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
              first | cases h | simp)
        subst hfinal
        rcases step_cases legal realized with
          ⟨h, -, rfl⟩ | ⟨h, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
          first | cases h | simp [payoff, ExecutionProtocol.History.extend]
    _ = 1 := expect_constant _ _

/-- No single-site law change improves on exiting and rewarding. -/
theorem rewardingAssessment_locallyOptimal (who : Unit) (site : model.InformationSite who)
    (law : PMF (model.Choice who site.1)) :
    (rewardingAssessment.continuationContext arena_wellFoundedHistories site
        (sePayoff who)).value ((rewardingAssessment.strategy who).withLaw site.1 law) ≤
      (rewardingAssessment.continuationContext arena_wellFoundedHistories site
        (sePayoff who)).value (rewardingAssessment.strategy who) := by
  cases who
  unfold rewardingAssessment
  rcases site_cases site with hroot | hdecision
  · let history : model.InformationHistory () site.1 :=
      ⟨arena.initHistory, (signals_infoOf_state _).trans hroot.symm⟩
    rw [value_eq _ site history, value_eq _ site history]
    simp only [BehavioralAssessment.ofStrategy_strategy, Profile.update_eq_self]
    change _ ≤ expect (model.runBehavioralTerminalFrom arena_wellFoundedHistories
      (fun who => (rewardingProfile who).toBehavioral) arena.initHistory) _
    rw [terminal_eq]
    have hvalue := rewarding_value_root
    unfold ExecutionProtocol.historyBackwardValue at hvalue
    rw [hvalue]
    exact expect_le_two _
  · let history : model.InformationHistory () site.1 :=
      ⟨decisionHistory, (signals_infoOf_state decisionTrace).trans hdecision.symm⟩
    rw [value_eq _ site history, value_eq _ site history]
    simp only [BehavioralAssessment.ofStrategy_strategy, Profile.update_eq_self]
    change _ ≤ expect (model.runBehavioralTerminalFrom arena_wellFoundedHistories
      (fun who => (rewardingProfile who).toBehavioral) decisionHistory) _
    rw [terminal_eq]
    have hvalue := rewarding_value_decision
    unfold ExecutionProtocol.historyBackwardValue at hvalue
    rw [show model.historyChooser rewardingProfile =
      model.historyChooser (Profile.update incumbentProfile () rewardingPolicy) from rfl, hvalue]
    exact decision_continuation_le_one _

/-- **Rewarding off path is a sequential equilibrium.** The assessment is
consistent but not fully mixed and its decision is unreached; one-shot
optimality suffices. -/
theorem rewardingAssessment_isSequentialEquilibrium :
    rewardingAssessment.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
      arena_wellFoundedHistories sePayoff :=
  (BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal model decisionRecall
    rewardingAssessment arena_wellFoundedHistories sePayoff).2
      ⟨rewardingAssessment_consistent, rewardingAssessment_locallyOptimal⟩

end GameTheory.Tests.SequentialOneShot
