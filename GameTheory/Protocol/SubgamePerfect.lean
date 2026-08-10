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
the stronger historywise predicate.
-/

import GameTheory.Protocol.Assessment

noncomputable section

namespace GameTheory.Protocol

open Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E)

/-- History extension inherits the successor order of the state it reaches.
The relation may compare two histories reaching related states even when one is
not literally an extension of the other; recursion only follows realized
extensions, while this coarser inverse image supplies well-foundedness. -/
def HistorySuccessor (later earlier : E.History) : Prop :=
  E.Successor later.state earlier.state

/-- A well-founded state protocol is also well-founded on complete histories. -/
theorem wellFounded_historySuccessor
    (certificate : E.WellFoundedPlay) :
    WellFounded E.HistorySuccessor :=
  certificate.onFun

/-- Well-founded recursion whose argument retains the complete history. -/
def historyBackwardRec {motive : E.History → Sort*}
    (certificate : E.WellFoundedPlay)
    (rule : ∀ history : E.History,
      (∀ later : E.History,
        E.HistorySuccessor later history → motive later) →
      motive history)
    (history : E.History) : motive history :=
  WellFounded.fix (E.wellFounded_historySuccessor certificate) rule history

/-- The unfolding equation for history-indexed backward recursion. -/
theorem historyBackwardRec_eq {motive : E.History → Sort*}
    (certificate : E.WellFoundedPlay)
    (rule : ∀ history : E.History,
      (∀ later : E.History,
        E.HistorySuccessor later history → motive later) →
      motive history)
    (history : E.History) :
    E.historyBackwardRec certificate rule history =
      rule history fun later _relation =>
        E.historyBackwardRec certificate rule later :=
  WellFounded.fix_eq
    (E.wellFounded_historySuccessor certificate) rule history

/-- Expected value after one realized legal step, retaining the support proof
needed to extend the current history. -/
def historyStepValue (history : E.History)
    (chosen :
      { joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint })
    (continuation :
      ∀ target : E.State,
        target ∈ (E.step history.state chosen).support → ℝ) : ℝ :=
  ((E.step history.state chosen).bindOnSupport fun target realized =>
    FinDist.pure (continuation target realized)).expect id

/-- Pointwise larger successor values give a larger one-step value. -/
theorem historyStepValue_mono
    {history : E.History}
    {chosen :
      { joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint }}
    {first second :
      ∀ target : E.State,
        target ∈ (E.step history.state chosen).support → ℝ}
    (hle : ∀ target realized, first target realized ≤ second target realized) :
    E.historyStepValue history chosen first ≤
      E.historyStepValue history chosen second := by
  apply FinDist.expect_bindOnSupport_mono
  intro target realized
  simp [hle target realized]

/-- Pointwise equal successor values give the same one-step value. -/
theorem historyStepValue_congr
    {history : E.History}
    {chosen :
      { joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint }}
    {first second :
      ∀ target : E.State,
        target ∈ (E.step history.state chosen).support → ℝ}
    (heq : ∀ target realized, first target realized = second target realized) :
    E.historyStepValue history chosen first =
      E.historyStepValue history chosen second := by
  apply FinDist.expect_bindOnSupport_congr
  intro target realized
  simp [heq target realized]

open Classical in
/-- Terminal payoff induced by a fixed history-dependent chooser. This is the
history-preserving analogue of `backwardValue`, using the same transition law
and the same `WellFoundedPlay` certificate. -/
def historyBackwardValue (certificate : E.WellFoundedPlay)
    (chooser : E.HistoryChooser) (payoff : E.History → ℝ) :
    E.History → ℝ :=
  E.historyBackwardRec certificate fun history recurse =>
    if hterm : E.terminal history.state then payoff history
    else
      let chosen := chooser history hterm
      E.historyStepValue history chosen fun _target realized =>
        recurse (history.extend chosen.2 realized)
          ⟨chosen.1, chosen.2, realized⟩

open Classical in
/-- Unfold history-preserving backward value once. -/
theorem historyBackwardValue_eq
    (certificate : E.WellFoundedPlay)
    (chooser : E.HistoryChooser) (payoff : E.History → ℝ)
    (history : E.History) :
    E.historyBackwardValue certificate chooser payoff history =
      if hterm : E.terminal history.state then payoff history
      else
        let chosen := chooser history hterm
        E.historyStepValue history chosen fun _target realized =>
          E.historyBackwardValue certificate chooser payoff
            (history.extend chosen.2 realized) := by
  rw [historyBackwardValue, historyBackwardRec_eq]

/-- At a terminal history, backward value is the supplied payoff. -/
theorem historyBackwardValue_of_terminal
    {certificate : E.WellFoundedPlay}
    {chooser : E.HistoryChooser} {payoff : E.History → ℝ}
    {history : E.History} (_hterm : E.terminal history.state) :
    E.historyBackwardValue certificate chooser payoff history =
      payoff history := by
  rw [historyBackwardValue_eq, dif_pos _hterm]

/-- At a nonterminal history, backward value is the expected value of its
realized successor histories. -/
theorem historyBackwardValue_of_not_terminal
    {certificate : E.WellFoundedPlay}
    {chooser : E.HistoryChooser} {payoff : E.History → ℝ}
    {history : E.History} (hterm : ¬ E.terminal history.state) :
    E.historyBackwardValue certificate chooser payoff history =
      let chosen := chooser history hterm
      E.historyStepValue history chosen fun _target realized =>
        E.historyBackwardValue certificate chooser payoff
          (history.extend chosen.2 realized) := by
  rw [historyBackwardValue_eq, dif_neg hterm]

/-- A history-dependent chooser has stopped within `horizon` when every history
in the forward runner's support at that fuel is terminal. -/
def StopsHistoryWithin (chooser : E.HistoryChooser)
    (horizon : ℕ) (history : E.History) : Prop :=
  ∀ final ∈ (E.runHistoryFor chooser horizon history).support,
    E.terminal final.state

/-- Wherever the forward history runner has stopped, history-indexed backward
value computes its expected terminal payoff. -/
theorem historyBackwardValue_eq_expect_runHistoryFor
    {certificate : E.WellFoundedPlay}
    {chooser : E.HistoryChooser} {payoff : E.History → ℝ}
    {horizon : ℕ} {history : E.History}
    (hstop : E.StopsHistoryWithin chooser horizon history) :
    E.historyBackwardValue certificate chooser payoff history =
      (E.runHistoryFor chooser horizon history).expect payoff := by
  induction horizon generalizing history with
  | zero =>
      have hterm : E.terminal history.state :=
        hstop history (by
          rw [ExecutionProtocol.runHistoryFor_zero]
          exact FinDist.mem_support_pure.mpr rfl)
      rw [E.historyBackwardValue_of_terminal hterm,
        ExecutionProtocol.runHistoryFor_zero, FinDist.expect_pure]
  | succ horizon ih =>
      by_cases hterm : E.terminal history.state
      · rw [E.historyBackwardValue_of_terminal hterm,
          ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm,
          FinDist.expect_pure]
      · rw [E.historyBackwardValue_of_not_terminal hterm,
          ExecutionProtocol.runHistoryFor_succ_of_not_terminal
            chooser horizon hterm,
          historyStepValue]
        apply FinDist.expect_bindOnSupport_congr
        intro target realized
        rw [FinDist.expect_pure]
        apply ih
        intro final hfinal
        apply hstop final
        rw [ExecutionProtocol.runHistoryFor_succ_of_not_terminal
          chooser horizon hterm, FinDist.support_bindOnSupport]
        exact Set.mem_iUnion.mpr
          ⟨target, Set.mem_iUnion.mpr ⟨realized, hfinal⟩⟩

/-- Unbounded reachability between histories, expressed through the existing
finite path witness rather than a second transition relation. -/
def HistoryReaches (start target : E.History) : Prop :=
  ∃ fuel, E.ReachesWithin fuel start target

theorem HistoryReaches.refl (history : E.History) :
    E.HistoryReaches history history :=
  ⟨0, .refl 0 history⟩

theorem HistoryReaches.step {start target : E.History}
    {joint : ∀ i, Option (E.Action i)}
    (isLegal : E.Legal start.state joint)
    {reached : E.State}
    (realized :
      reached ∈ (E.step start.state ⟨joint, isLegal⟩).support)
    (rest : E.HistoryReaches (start.extend isLegal realized) target) :
    E.HistoryReaches start target := by
  rcases rest with ⟨fuel, hrest⟩
  exact ⟨fuel + 1, .step joint isLegal realized hrest⟩

/-- Choosers agreeing at every history reachable from `start` have equal
history-preserving backward value there. -/
theorem historyBackwardValue_congr_of_reaches
    {certificate : E.WellFoundedPlay}
    {first second : E.HistoryChooser}
    {payoff : E.History → ℝ} :
    ∀ start : E.History,
      (∀ later, E.HistoryReaches start later →
        ∀ hterm : ¬ E.terminal later.state,
          first later hterm = second later hterm) →
      E.historyBackwardValue certificate first payoff start =
        E.historyBackwardValue certificate second payoff start := by
  intro start
  induction start using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ history ih =>
      intro hagree
      by_cases hterm : E.terminal history.state
      · rw [E.historyBackwardValue_of_terminal hterm,
          E.historyBackwardValue_of_terminal hterm]
      · rw [E.historyBackwardValue_of_not_terminal hterm,
          E.historyBackwardValue_of_not_terminal hterm,
          hagree history (HistoryReaches.refl E history) hterm]
        apply historyStepValue_congr
        intro target realized
        let chosen := second history hterm
        exact ih (history.extend chosen.2 realized)
          ⟨chosen.1, chosen.2, realized⟩
          (fun later hreach =>
            hagree later
              (HistoryReaches.step E chosen.2 realized hreach))

end ExecutionProtocol

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

/-- Expected payoff from changing one current information-local choice and then
returning to the original profile. -/
def oneShotHistoryValue [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (payoff : E.History → ℝ) (who : ι)
    [DecidableEq (M.InfoState who)]
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (choice : M.Choice who (M.infoOf who history.trace)) : ℝ :=
  let changed := M.oneShotProfile profile history who choice
  let chosen := M.historyChooser changed history hterm
  E.historyStepValue history chosen fun _target realized =>
    E.historyBackwardValue certificate (M.historyChooser profile) payoff
      (history.extend chosen.2 realized)

/-- No player has a profitable typed one-choice deviation after any history. -/
def HasNoProfitableOneShotDeviation [DecidableEq ι]
    [∀ i, DecidableEq (M.InfoState i)]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  ∀ (who : ι) (history : E.History)
    (hterm : ¬ E.terminal history.state)
    (choice : M.Choice who (M.infoOf who history.trace)),
      M.oneShotHistoryValue certificate profile
          (fun outcome => utility outcome who)
          who history hterm choice ≤
        E.historyBackwardValue certificate
          (M.historyChooser profile)
          (fun outcome => utility outcome who) history

/-- A pure profile is historywise optimal when no whole replacement policy
improves any player's payoff after any complete history.  This stronger notion
is useful in perfect-information backward induction and has the clean
history-local one-shot characterization below. -/
def IsHistorywiseOptimal [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  ∀ (who : ι) (alternative : M.Policy who)
    (history : E.History),
      E.historyBackwardValue certificate
          (M.historyChooser
            (Profile.update profile who alternative))
          (fun outcome => utility outcome who) history ≤
        E.historyBackwardValue certificate
          (M.historyChooser profile)
          (fun outcome => utility outcome who) history

/-- A pure profile is subgame perfect when no player benefits from a whole
replacement policy in any information-set-closed subgame, reached or off path.
The initial history is always included. -/
def IsSubgamePerfect [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  ∀ (history : E.History), M.IsSubgameRoot history →
    ∀ (who : ι) (alternative : M.Policy who),
      E.historyBackwardValue certificate
          (M.historyChooser
            (Profile.update profile who alternative))
          (fun outcome => utility outcome who) history ≤
        E.historyBackwardValue certificate
          (M.historyChooser profile)
          (fun outcome => utility outcome who) history

/-- Historywise optimality implies subgame perfection by restriction to the
certified subgame roots. -/
theorem IsHistorywiseOptimal.isSubgamePerfect [DecidableEq ι]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hoptimal : M.IsHistorywiseOptimal certificate profile utility) :
    M.IsSubgamePerfect certificate profile utility := by
  intro history hroot who alternative
  exact hoptimal who alternative history

/-- One-shot optimality at every history defeats every whole replacement
information-local policy after every history. -/
theorem isHistorywiseOptimal_of_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hopt :
      M.HasNoProfitableOneShotDeviation
        certificate profile utility) :
    M.IsHistorywiseOptimal certificate profile utility := by
  intro who alternative history
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ current ih =>
      by_cases hterm : E.terminal current.state
      · rw [E.historyBackwardValue_of_terminal hterm,
          E.historyBackwardValue_of_terminal hterm]
      · let choice := alternative (M.infoOf who current.trace)
        let changed := M.oneShotProfile profile current who choice
        let chosen := M.historyChooser changed current hterm
        have hchosen :
            M.historyChooser
                (Profile.update profile who alternative)
                current hterm =
              chosen := by
          dsimp only [chosen, changed, choice]
          exact M.historyChooser_update_eq_oneShotProfile
            profile current hterm who alternative
        rw [E.historyBackwardValue_of_not_terminal
              (chooser := M.historyChooser
                (Profile.update profile who alternative)) hterm,
          hchosen]
        calc
          E.historyStepValue current chosen
              (fun target realized =>
                E.historyBackwardValue certificate
                  (M.historyChooser
                    (Profile.update profile who alternative))
                  (fun outcome => utility outcome who)
                  (current.extend chosen.2 realized)) ≤
            E.historyStepValue current chosen
              (fun target realized =>
                E.historyBackwardValue certificate
                  (M.historyChooser profile)
                  (fun outcome => utility outcome who)
                  (current.extend chosen.2 realized)) := by
              apply ExecutionProtocol.historyStepValue_mono
              intro target realized
              exact ih (current.extend chosen.2 realized)
                ⟨chosen.1, chosen.2, realized⟩
          _ = M.oneShotHistoryValue certificate profile
              (fun outcome => utility outcome who)
              who current hterm choice := by
                rfl
          _ ≤ E.historyBackwardValue certificate
              (M.historyChooser profile)
              (fun outcome => utility outcome who) current :=
                hopt who current hterm choice

/-- Under the same no-revisit condition used by the behavioral/mixed
representation theorem, historywise optimality rules out every one-shot
deviation. -/
theorem hasNoProfitableOneShotDeviation_of_isHistorywiseOptimal
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hoptimal : M.IsHistorywiseOptimal certificate profile utility) :
    M.HasNoProfitableOneShotDeviation
      certificate profile utility := by
  intro who history hterm choice
  let alternative :=
    (profile who).replaceAt (M.infoOf who history.trace) choice
  let changed := M.oneShotProfile profile history who choice
  let chosen := M.historyChooser changed history hterm
  have hprofile :
      Profile.update profile who alternative = changed := by
    rfl
  have hbest := hoptimal who alternative history
  rw [hprofile,
    E.historyBackwardValue_of_not_terminal
      (chooser := M.historyChooser changed) hterm] at hbest
  calc
    M.oneShotHistoryValue certificate profile
        (fun outcome => utility outcome who)
        who history hterm choice =
      E.historyStepValue history chosen
        (fun target realized =>
          E.historyBackwardValue certificate
            (M.historyChooser changed)
            (fun outcome => utility outcome who)
            (history.extend chosen.2 realized)) := by
              apply ExecutionProtocol.historyStepValue_congr
              intro target realized
              symm
              apply
                ExecutionProtocol.historyBackwardValue_congr_of_reaches
              intro later hreach hlater
              rcases hreach with ⟨fuel, hreach⟩
              exact
                M.historyChooser_oneShotProfile_eq_of_actsOnce
                  hactsOnce profile history hterm choice
                  realized later hreach hlater
    _ ≤ E.historyBackwardValue certificate
        (M.historyChooser profile)
        (fun outcome => utility outcome who) history := hbest

/-- **Well-founded historywise one-shot deviation principle.** On an
information model where genuine choices do not recur at one information state,
a profile is optimal after every history exactly when no player has a
profitable one-shot deviation after any history. -/
theorem isHistorywiseOptimal_iff_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) :
    M.IsHistorywiseOptimal certificate profile utility ↔
      M.HasNoProfitableOneShotDeviation
        certificate profile utility :=
  ⟨M.hasNoProfitableOneShotDeviation_of_isHistorywiseOptimal
      hactsOnce,
    M.isHistorywiseOptimal_of_hasNoProfitableOneShotDeviation⟩

end InformationModel

end GameTheory.Protocol
