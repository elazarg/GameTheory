/-
# Well-founded continuation optimality and subgame perfection

Historywise continuation optimality asks every player to prefer the profile to
every whole replacement policy after every history, including histories the
profile does not reach.  In imperfect-information games that is stronger than
subgame perfection: a proper subgame may start only where its continuation is
closed under every decision information set.

This module defines that closure directly over canonical protocol histories,
without adding an EFG evaluator. `WellFoundedPlay` lifts from states to
histories, and the resulting recursion evaluates the same protocol step law
while retaining the history an information-local policy may observe. Under
`ActsOnceWhereItMatters`, a persistent policy replacement at the current
information state is observationally a one-shot change, which characterizes
the stronger historywise predicate. Whole-policy replacement is essential in
the proper-subgame predicate: when the initial history is the only proper
root, complementary changes at several information states can be profitable
even though no single-information-state replacement is.
-/

import GameTheory.Protocol.HistoryBackward
import GameTheory.Protocol.InformationOneShot

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}


namespace InformationModel

variable (M : InformationModel E)

/-- A history starts a proper subgame when every decision information set met
below it is wholly contained below it.  Inactive and terminal histories do not
belong to decision information sets and therefore impose no closure demand. -/
def IsSubgameRoot (root : E.History) : Prop :=
  ∀ (who : ι) (inside outside : E.History),
    E.HistoryReaches root inside →
    ¬ E.terminal inside.state → E.active inside.state who →
    ¬ E.terminal outside.state → E.active outside.state who →
    M.infoOf who inside.trace = M.infoOf who outside.trace →
    E.HistoryReaches root outside

/-- The initial history always starts a subgame: every complete history is a
continuation of it. -/
theorem initHistory_isSubgameRoot : M.IsSubgameRoot E.initHistory := by
  intro who inside outside hinside hinsTerm hinsActive houtTerm houtActive hinfo
  exact ⟨outside.trace.length, E.reachesWithin_from_init outside⟩

/-- A replacement at the current information state becomes invisible after the
first step when that information state cannot recur with a genuine choice. -/
theorem Policy.replaceAt_act_eq_of_actsOnce
    {i : ι} [DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : M.Policy i) {history : E.History}
    (choice : M.Choice i (M.infoOf i history.trace))
    {joint : ∀ j, Option (E.Action j)}
    (isLegal : E.Legal history.state joint)
    {target : E.State}
    (realized :
      target ∈ (E.step history.state ⟨joint, isLegal⟩).support)
    {fuel : ℕ} (later : E.History)
    (hreach :
      E.ReachesWithin fuel
        (history.extend isLegal realized) later)
    (hlater : ¬ E.terminal later.state) :
    (policy.replaceAt (M.infoOf i history.trace) choice).act
        (M.infoOf i later.trace) =
      policy.act (M.infoOf i later.trace) := by
  by_cases hne :
      M.infoOf i later.trace ≠ M.infoOf i history.trace
  · exact congrArg Subtype.val
      (policy.replaceAt_of_ne
        (M.infoOf i history.trace) choice hne)
  push Not at hne
  by_cases hactiveLater : E.active later.state i
  · by_cases hactiveHere : E.active history.state i
    · obtain ⟨laterJoint, hlaterJoint⟩ :=
        E.progress later.state hlater
      have hlaterLegal : E.Legal later.state laterJoint :=
        ⟨hlater, hlaterJoint⟩
      obtain ⟨laterTarget, hlaterRealized⟩ :=
        (E.step later.state
          ⟨laterJoint, hlaterLegal⟩).support_nonempty
      obtain ⟨_action, hsome⟩ :=
        LegalOption.exists_eq_some_of_active (joint i)
          (ExecutionProtocol.legalOption_of_legal isLegal i)
          hactiveHere
      obtain ⟨_laterAction, hlaterSome⟩ :=
        LegalOption.exists_eq_some_of_active (laterJoint i)
          (ExecutionProtocol.legalOption_of_legal hlaterLegal i)
          hactiveLater
      have hdisj :=
        M.infoOf_ne_or_subsingleton_of_actsOnce hactsOnce i
          isLegal realized (by rw [hsome]; rfl) hreach
          hlaterLegal hlaterRealized (by rw [hlaterSome]; rfl)
      rcases hdisj with hne' | hsubsingleton
      · exact absurd hne hne'
      · rw [hne]
        simp only [Policy.act, Policy.replaceAt_self]
        exact congrArg Subtype.val
          (hsubsingleton.elim choice
            (policy (M.infoOf i history.trace)))
    · have hsubsingleton :=
        M.subsingleton_choice_of_not_active history.trace hactiveHere
      rw [hne]
      simp only [Policy.act, Policy.replaceAt_self]
      exact congrArg Subtype.val
        (hsubsingleton.elim choice
          (policy (M.infoOf i history.trace)))
  · have hsubsingleton :=
      M.subsingleton_choice_of_not_active later.trace hactiveLater
    exact congrArg Subtype.val (hsubsingleton.elim _ _)

/-- After the first step, the one-shot profile and the original profile induce
the same chooser at every reachable later history. -/
theorem historyChooser_oneShotProfile_eq_of_actsOnce
    [DecidableEq ι] {who : ι}
    [DecidableEq (M.InfoState who)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (profile : Profile M.strategicSignature)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (choice : M.Choice who (M.infoOf who history.trace))
    {target : E.State}
    (realized :
      target ∈
        (E.step history.state
          (M.historyChooser
            (M.oneShotProfile profile history who choice)
            history hterm)).support)
    {fuel : ℕ} (later : E.History)
    (hreach :
      E.ReachesWithin fuel
        (history.extend
          (M.historyChooser
            (M.oneShotProfile profile history who choice)
            history hterm).2
          realized)
        later)
    (hlater : ¬ E.terminal later.state) :
    M.historyChooser (M.oneShotProfile profile history who choice)
        later hlater =
      M.historyChooser profile later hlater := by
  apply Subtype.ext
  funext i
  by_cases hi : i = who
  · subst i
    simp only [InformationModel.historyChooser,
      InformationModel.jointAt, M.oneShotProfile_same]
    exact Policy.replaceAt_act_eq_of_actsOnce (M := M) hactsOnce
      (profile who) choice
      (M.historyChooser
        (M.oneShotProfile profile history who choice)
        history hterm).2
      realized later hreach hlater
  · simp [InformationModel.historyChooser, InformationModel.jointAt,
      M.oneShotProfile_of_ne profile history who choice hi]

/-- A changed current choice followed by the original profile's complete
history-preserving terminal law. -/
def oneShotHistoryLaw [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (choice : M.Choice who (M.infoOf who history.trace)) : PMF E.History :=
  let changed := M.oneShotProfile profile history who choice
  let chosen := M.historyChooser changed history hterm
  (E.step history.state chosen).bindOnSupport fun _target realized =>
    E.historyBackwardLaw certificate (M.historyChooser profile)
      (history.extend chosen.2 realized)

/-- The actual one-choice history context uses the same continuation
comparison as the generic protocol context. -/
def oneShotHistoryContext [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) (who : ι)
    [DecidableEq (M.InfoState who)]
    (history : E.History) (hterm : ¬ E.terminal history.state) :
    GameTheory.Protocol.Context
      (M.Choice who (M.infoOf who history.trace)) E.History where
  outcome choice := M.oneShotHistoryLaw certificate profile who history hterm choice
  continuation outcome := utility outcome who

theorem oneShotHistoryLaw_self [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (history : E.History) (hterm : ¬ E.terminal history.state) :
    M.oneShotHistoryLaw certificate profile who history hterm
        (profile who (M.infoOf who history.trace)) =
      E.historyBackwardLaw certificate (M.historyChooser profile) history := by
  let continuation := fun
      (chosen : { joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint }) =>
    (E.step history.state chosen).bindOnSupport fun _target realized =>
      E.historyBackwardLaw certificate (M.historyChooser profile)
        (history.extend chosen.2 realized)
  have hchosen :=
    (M.historyChooser_oneShotProfile_self profile history hterm who).symm
  calc
    M.oneShotHistoryLaw certificate profile who history hterm
        (profile who (M.infoOf who history.trace)) =
      continuation (M.historyChooser
        (M.oneShotProfile profile history who
          (profile who (M.infoOf who history.trace))) history hterm) := rfl
    _ = continuation (M.historyChooser profile history hterm) :=
      congrArg continuation hchosen
    _ = E.historyBackwardLaw certificate (M.historyChooser profile) history :=
      (E.historyBackwardLaw_of_not_terminal hterm).symm

/-- The incumbent and every legal one-choice continuation have expected
payoffs, and no one-choice change improves the incumbent. -/
def HasNoProfitableOneShotDeviation [DecidableEq ι]
    [∀ i, DecidableEq (M.InfoState i)]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  ∀ (who : ι) (history : E.History)
    (hterm : ¬ E.terminal history.state),
      (M.oneShotHistoryContext certificate profile utility who history hterm).IsLocallyOptimal
        Set.univ (profile who (M.infoOf who history.trace))

/-- Whole-policy optimality after every history, including off-path histories.
Each comparison requires both payoff laws to have expectations and compares
their extended values. -/
def IsHistorywiseOptimal [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  ∀ (who : ι) (alternative : M.Policy who) (history : E.History),
    HasExpectation
        (E.historyBackwardLaw certificate
          (M.historyChooser (Profile.update profile who alternative)) history)
        (fun outcome => utility outcome who) ∧
      HasExpectation
          (E.historyBackwardLaw certificate (M.historyChooser profile) history)
          (fun outcome => utility outcome who) ∧
        E.historyBackwardExtendedValue certificate
            (M.historyChooser (Profile.update profile who alternative))
            (fun outcome => utility outcome who) history ≤
          E.historyBackwardExtendedValue certificate (M.historyChooser profile)
            (fun outcome => utility outcome who) history

/-- Whole-policy optimality at every information-set-closed subgame root. -/
def IsSubgamePerfect [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  ∀ (history : E.History), M.IsSubgameRoot history →
    ∀ (who : ι) (alternative : M.Policy who),
      HasExpectation
          (E.historyBackwardLaw certificate
            (M.historyChooser (Profile.update profile who alternative)) history)
          (fun outcome => utility outcome who) ∧
        HasExpectation
            (E.historyBackwardLaw certificate (M.historyChooser profile) history)
            (fun outcome => utility outcome who) ∧
          E.historyBackwardExtendedValue certificate
              (M.historyChooser (Profile.update profile who alternative))
              (fun outcome => utility outcome who) history ≤
            E.historyBackwardExtendedValue certificate (M.historyChooser profile)
              (fun outcome => utility outcome who) history

theorem IsHistorywiseOptimal.isSubgamePerfect [DecidableEq ι]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hoptimal : M.IsHistorywiseOptimal certificate profile utility) :
    M.IsSubgamePerfect certificate profile utility := by
  intro history _ who alternative
  exact hoptimal who alternative history

/-- Local optimality gives the incumbent terminal law an expectation at every
history, including terminal and off-path histories. -/
theorem historyBackwardLaw_hasExpectation_of_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hopt : M.HasNoProfitableOneShotDeviation certificate profile utility)
    (who : ι) (history : E.History) :
    HasExpectation
      (E.historyBackwardLaw certificate (M.historyChooser profile) history)
      (fun outcome => utility outcome who) := by
  by_cases hterm : E.terminal history.state
  · rw [E.historyBackwardLaw_of_terminal hterm]
    exact hasExpectation_of_payoffIntegrable (payoffIntegrable_pure history _)
  · have hlocal := (hopt who history hterm).1
    rw [← M.oneShotHistoryLaw_self certificate profile who history hterm]
    exact hlocal

/-- A local one-choice condition defeats every whole-policy replacement at every
history: no replacement has a larger extended value. -/
theorem historyBackwardExtendedValue_update_le_of_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hopt : M.HasNoProfitableOneShotDeviation certificate profile utility)
    (who : ι) (alternative : M.Policy who) (history : E.History) :
    E.historyBackwardExtendedValue certificate
        (M.historyChooser (Profile.update profile who alternative))
        (fun outcome => utility outcome who) history ≤
      E.historyBackwardExtendedValue certificate (M.historyChooser profile)
        (fun outcome => utility outcome who) history := by
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ current ih =>
      by_cases hterm : E.terminal current.state
      · unfold ExecutionProtocol.historyBackwardExtendedValue
        rw [E.historyBackwardLaw_of_terminal hterm,
          E.historyBackwardLaw_of_terminal hterm]
      · let choice := alternative (M.infoOf who current.trace)
        let changed := M.oneShotProfile profile current who choice
        let chosen := M.historyChooser changed current hterm
        let stepLaw := E.step current.state chosen
        have hchosen :
            M.historyChooser (Profile.update profile who alternative)
                current hterm = chosen := by
          dsimp only [chosen, changed, choice]
          exact M.historyChooser_update_eq_oneShotProfile
            profile current hterm who alternative
        have hleftLaw :
            E.historyBackwardLaw certificate
                (M.historyChooser (Profile.update profile who alternative)) current =
              stepLaw.bindOnSupport fun _target realized =>
                E.historyBackwardLaw certificate
                  (M.historyChooser (Profile.update profile who alternative))
                  (current.extend chosen.2 realized) :=
          E.historyBackwardLaw_of_not_terminal_of_chooser_eq hterm chosen hchosen
        have hrightLaw :
            M.oneShotHistoryLaw certificate profile who current hterm choice =
              stepLaw.bindOnSupport fun _target realized =>
                E.historyBackwardLaw certificate (M.historyChooser profile)
                  (current.extend chosen.2 realized) := rfl
        have hlocal := hopt who current hterm
        have hright : HasExpectation
            (stepLaw.bindOnSupport fun _target realized =>
              E.historyBackwardLaw certificate (M.historyChooser profile)
                (current.extend chosen.2 realized))
            (fun outcome => utility outcome who) := by
          rw [← hrightLaw]
          exact hlocal.2.1 choice (Set.mem_univ _)
        have hbound := hlocal.2.2 choice (Set.mem_univ _)
        unfold ExecutionProtocol.historyBackwardExtendedValue
        calc
          extendedExpect (E.historyBackwardLaw certificate
              (M.historyChooser (Profile.update profile who alternative)) current)
              (fun outcome => utility outcome who) =
            extendedExpect (stepLaw.bindOnSupport fun _target realized =>
              E.historyBackwardLaw certificate
                (M.historyChooser (Profile.update profile who alternative))
                (current.extend chosen.2 realized))
              (fun outcome => utility outcome who) := by
                rw [hleftLaw]
          _ ≤ extendedExpect (stepLaw.bindOnSupport fun _target realized =>
                E.historyBackwardLaw certificate (M.historyChooser profile)
                  (current.extend chosen.2 realized))
                (fun outcome => utility outcome who) :=
              extendedExpect_bindOnSupport_mono (fun target realized =>
                ih (current.extend chosen.2 realized) ⟨chosen.1, chosen.2, realized⟩) hright
          _ ≤ extendedExpect (E.historyBackwardLaw certificate
                (M.historyChooser profile) current)
                (fun outcome => utility outcome who) := by
              unfold GameTheory.Protocol.Context.extendedValue at hbound
              simpa only [oneShotHistoryContext, hrightLaw,
                M.oneShotHistoryLaw_self] using hbound

/-- Local optimality implies historywise optimality when each whole replacement
policy being compared has an expectation. -/
theorem isHistorywiseOptimal_of_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hopt : M.HasNoProfitableOneShotDeviation certificate profile utility)
    (hcandidate : ∀ (who : ι) (alternative : M.Policy who)
      (history : E.History), HasExpectation
        (E.historyBackwardLaw certificate
          (M.historyChooser (Profile.update profile who alternative)) history)
        (fun outcome => utility outcome who)) :
    M.IsHistorywiseOptimal certificate profile utility := by
  intro who alternative history
  exact ⟨hcandidate who alternative history,
    M.historyBackwardLaw_hasExpectation_of_hasNoProfitableOneShotDeviation hopt who history,
    M.historyBackwardExtendedValue_update_le_of_hasNoProfitableOneShotDeviation
      hopt who alternative history⟩

/-- If an information state never matters again after one action, the
one-choice continuation law is the law of the persistent replacement policy. -/
theorem oneShotHistoryLaw_eq_changed_of_actsOnce
    [DecidableEq ι] {who : ι} [DecidableEq (M.InfoState who)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (choice : M.Choice who (M.infoOf who history.trace)) :
    M.oneShotHistoryLaw certificate profile who history hterm choice =
      E.historyBackwardLaw certificate
        (M.historyChooser (M.oneShotProfile profile history who choice)) history := by
  let changed := M.oneShotProfile profile history who choice
  let chosen := M.historyChooser changed history hterm
  rw [E.historyBackwardLaw_of_not_terminal hterm]
  dsimp only [oneShotHistoryLaw]
  apply bindOnSupport_congr
  intro target realized
  apply E.historyBackwardLaw_congr_of_reaches
    (history.extend chosen.2 realized)
  intro later hreach hlater
  symm
  rcases hreach with ⟨fuel, hwithin⟩
  exact M.historyChooser_oneShotProfile_eq_of_actsOnce
    hactsOnce profile history hterm choice realized later hwithin hlater

/-- Whole-policy optimality rules out every local choice when the current
information state cannot be revisited with a genuine choice. -/
theorem hasNoProfitableOneShotDeviation_of_isHistorywiseOptimal
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hoptimal : M.IsHistorywiseOptimal certificate profile utility) :
    M.HasNoProfitableOneShotDeviation certificate profile utility := by
  intro who history hterm
  let ctx := M.oneShotHistoryContext certificate profile utility who history hterm
  let own := profile who (M.infoOf who history.trace)
  have hownLaw := M.oneShotHistoryLaw_self certificate profile who history hterm
  obtain ⟨_, hinc, _⟩ := hoptimal who (profile who) history
  have hincCtx : ctx.HasValueAt own := by
    show HasExpectation
      (M.oneShotHistoryLaw certificate profile who history hterm own)
      (fun outcome => utility outcome who)
    rw [hownLaw]
    exact hinc
  refine ⟨hincCtx, ?_, ?_⟩
  · intro choice _
    let replacement := (profile who).replaceAt
      (M.infoOf who history.trace) choice
    obtain ⟨hchanged, _, _⟩ := hoptimal who replacement history
    have hLaw := M.oneShotHistoryLaw_eq_changed_of_actsOnce
      hactsOnce certificate profile history hterm choice
    show HasExpectation
      (M.oneShotHistoryLaw certificate profile who history hterm choice)
      (fun outcome => utility outcome who)
    rw [hLaw]
    exact hchanged
  · intro choice _
    let replacement := (profile who).replaceAt
      (M.infoOf who history.trace) choice
    obtain ⟨-, -, hle⟩ := hoptimal who replacement history
    have hLaw := M.oneShotHistoryLaw_eq_changed_of_actsOnce
      hactsOnce certificate profile history hterm choice
    show extendedExpect
        (M.oneShotHistoryLaw certificate profile who history hterm choice)
        (fun outcome => utility outcome who) ≤
      extendedExpect
        (M.oneShotHistoryLaw certificate profile who history hterm own)
        (fun outcome => utility outcome who)
    unfold ExecutionProtocol.historyBackwardExtendedValue at hle
    rw [hLaw, hownLaw]
    exact hle

/-- Under no revisits, the historywise one-shot principle is an equivalence
provided every whole-policy candidate law in the comparison has an
expectation. -/
theorem isHistorywiseOptimal_iff_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ)
    (hcandidate : ∀ (who : ι) (alternative : M.Policy who)
      (history : E.History), HasExpectation
        (E.historyBackwardLaw certificate
          (M.historyChooser (Profile.update profile who alternative)) history)
        (fun outcome => utility outcome who)) :
    M.IsHistorywiseOptimal certificate profile utility ↔
      M.HasNoProfitableOneShotDeviation certificate profile utility :=
  ⟨M.hasNoProfitableOneShotDeviation_of_isHistorywiseOptimal hactsOnce,
    fun hlocal => M.isHistorywiseOptimal_of_hasNoProfitableOneShotDeviation
      hlocal hcandidate⟩

end InformationModel

end GameTheory.Protocol
