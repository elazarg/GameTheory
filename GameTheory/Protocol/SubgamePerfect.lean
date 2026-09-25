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

import GameTheory.Protocol.Backward
import GameTheory.Protocol.InformationOneShot

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

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

open Classical in
/-- A history-preserving terminal law, recursing through realized successors. -/
def historyBackwardLaw (certificate : E.WellFoundedPlay)
    (chooser : E.HistoryChooser) : E.History → PMF E.History :=
  E.historyBackwardRec certificate fun history recurse =>
    if hterm : E.terminal history.state then PMF.pure history
    else
      let chosen := chooser history hterm
      (E.step history.state chosen).bindOnSupport fun _target realized =>
        recurse (history.extend chosen.2 realized)
          ⟨chosen.1, chosen.2, realized⟩

open Classical in
theorem historyBackwardLaw_eq (certificate : E.WellFoundedPlay)
    (chooser : E.HistoryChooser) (history : E.History) :
    E.historyBackwardLaw certificate chooser history =
      if hterm : E.terminal history.state then PMF.pure history
      else
        let chosen := chooser history hterm
        (E.step history.state chosen).bindOnSupport fun _target realized =>
          E.historyBackwardLaw certificate chooser
            (history.extend chosen.2 realized) := by
  rw [historyBackwardLaw, historyBackwardRec_eq]

theorem historyBackwardLaw_of_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {history : E.History} (hterm : E.terminal history.state) :
    E.historyBackwardLaw certificate chooser history = PMF.pure history := by
  rw [historyBackwardLaw_eq, dite_eq_left hterm]

theorem historyBackwardLaw_of_not_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {history : E.History} (hterm : ¬ E.terminal history.state) :
    E.historyBackwardLaw certificate chooser history =
      (E.step history.state (chooser history hterm)).bindOnSupport
        fun _target realized =>
          E.historyBackwardLaw certificate chooser
            (history.extend (chooser history hterm).2 realized) := by
  rw [historyBackwardLaw_eq, dite_eq_right hterm]

/-- Rewrite the nonterminal law using an equal chosen joint action without
exposing dependent legality proofs at callers. -/
theorem historyBackwardLaw_of_not_terminal_of_chooser_eq
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {history : E.History} (hterm : ¬ E.terminal history.state)
    (chosen : { joint : ∀ i, Option (E.Action i) //
      E.Legal history.state joint })
    (hchosen : chooser history hterm = chosen) :
    E.historyBackwardLaw certificate chooser history =
      (E.step history.state chosen).bindOnSupport fun _target realized =>
        E.historyBackwardLaw certificate chooser
          (history.extend chosen.2 realized) := by
  calc
    E.historyBackwardLaw certificate chooser history =
        (E.step history.state (chooser history hterm)).bindOnSupport
          fun _target realized => E.historyBackwardLaw certificate chooser
            (history.extend (chooser history hterm).2 realized) :=
      E.historyBackwardLaw_of_not_terminal hterm
    _ = (E.step history.state chosen).bindOnSupport
          fun _target realized => E.historyBackwardLaw certificate chooser
            (history.extend chosen.2 realized) :=
      congrArg (fun selected : { joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint } =>
        (E.step history.state selected).bindOnSupport fun _target realized =>
          E.historyBackwardLaw certificate chooser
            (history.extend selected.2 realized)) hchosen

/-- Every supported outcome of the well-founded history law is terminal. -/
theorem historyBackwardLaw_support_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    (history : E.History) :
    ∀ final ∈ (E.historyBackwardLaw certificate chooser history).support,
      E.terminal final.state := by
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ current ih =>
      intro final hfinal
      by_cases hterm : E.terminal current.state
      · rw [E.historyBackwardLaw_of_terminal hterm,
          PMF.mem_support_pure_iff] at hfinal
        subst final
        exact hterm
      · rw [E.historyBackwardLaw_of_not_terminal hterm,
          PMF.mem_support_bindOnSupport_iff] at hfinal
        obtain ⟨target, realized, hcontinue⟩ := hfinal
        exact ih (current.extend (chooser current hterm).2 realized)
          ⟨(chooser current hterm).1, (chooser current hterm).2, realized⟩
          final hcontinue

/-- Boundedness only on terminal histories is sufficient for any well-founded
history chooser's real payoff to be defined. -/
theorem payoffIntegrable_historyBackwardLaw_of_bounded_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {C : ℝ}
    (hbound : ∀ final, E.terminal final.state → |payoff final| ≤ C)
    (history : E.History) :
    PayoffIntegrable (E.historyBackwardLaw certificate chooser history) payoff := by
  apply payoffIntegrable_of_bounded_on_support
  intro final hfinal
  exact hbound final (E.historyBackwardLaw_support_terminal history final hfinal)

/-- Finite support at each legal transition also makes every well-founded
terminal payoff integrable, without any bound on the payoff itself. -/
theorem payoffIntegrable_historyBackwardLaw_of_finite_step_support
    {certificate : E.WellFoundedPlay}
    (hfinite : ∀ (history : E.History) (_hterm : ¬ E.terminal history.state)
      (chosen : {joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint}),
      (E.step history.state chosen).support.Finite)
    (chooser : E.HistoryChooser) (payoff : E.History → ℝ)
    (history : E.History) :
    PayoffIntegrable (E.historyBackwardLaw certificate chooser history) payoff := by
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ current ih =>
      by_cases hterm : E.terminal current.state
      · rw [E.historyBackwardLaw_of_terminal hterm]
        exact payoffIntegrable_pure current payoff
      · rw [E.historyBackwardLaw_of_not_terminal hterm]
        exact payoffIntegrable_bindOnSupport_of_finite_support
          (E.step current.state (chooser current hterm))
          (fun _target realized => E.historyBackwardLaw certificate chooser
            (current.extend (chooser current hterm).2 realized)) payoff
          (hfinite current hterm (chooser current hterm))
          (fun _target realized =>
            ih (current.extend (chooser current hterm).2 realized)
              ⟨(chooser current hterm).1,
                (chooser current hterm).2, realized⟩)

/-- A history chooser has stopped at this fuel when the forward law contains
only terminal histories. -/
def StopsHistoryWithin (chooser : E.HistoryChooser)
    (horizon : ℕ) (history : E.History) : Prop :=
  ∀ final ∈ (E.runHistoryFor chooser horizon history).support,
    E.terminal final.state

theorem stopsHistoryWithin_of_bound {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (chooser : E.HistoryChooser) (history : E.History) :
    E.StopsHistoryWithin chooser bound history := by
  intro final reached
  have randomized := reached
  rw [← E.runRandomizedFor_toRandomized] at randomized
  rcases E.runRandomizedFor_terminal_or_length _ _ _ _ randomized with stopped | consumed
  · exact stopped
  · exact bounded final.state final.trace (by omega)

/-- The well-founded history law agrees with any forward run that has stopped. -/
theorem historyBackwardLaw_eq_runHistoryFor
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {horizon : ℕ} {history : E.History}
    (hstop : E.StopsHistoryWithin chooser horizon history) :
    E.historyBackwardLaw certificate chooser history =
      E.runHistoryFor chooser horizon history := by
  induction horizon generalizing history with
  | zero =>
      have hterm : E.terminal history.state :=
        hstop history (by
          rw [ExecutionProtocol.runHistoryFor_zero]
          simp)
      rw [E.historyBackwardLaw_of_terminal hterm,
        ExecutionProtocol.runHistoryFor_zero]
  | succ horizon ih =>
      by_cases hterm : E.terminal history.state
      · rw [E.historyBackwardLaw_of_terminal hterm,
          ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
      · rw [E.historyBackwardLaw_of_not_terminal hterm,
          ExecutionProtocol.runHistoryFor_succ_of_not_terminal
            chooser horizon hterm]
        apply bindOnSupport_congr
        intro target realized
        apply ih
        intro final hfinal
        apply hstop final
        rw [ExecutionProtocol.runHistoryFor_succ_of_not_terminal
          chooser horizon hterm, PMF.mem_support_bindOnSupport_iff]
        exact ⟨target, realized, hfinal⟩

/-- A real history value requires finite integrability under its terminal law. -/
def historyBackwardValue (certificate : E.WellFoundedPlay)
    (chooser : E.HistoryChooser) (payoff : E.History → ℝ)
    (history : E.History)
    (hintegrable : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff) : ℝ :=
  expect (E.historyBackwardLaw certificate chooser history) payoff hintegrable

theorem historyBackwardValue_of_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {history : E.History}
    (hterm : E.terminal history.state)
    (hintegrable : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff) :
    E.historyBackwardValue certificate chooser payoff history hintegrable =
      payoff history := by
  have hpure : PayoffIntegrable (PMF.pure history) payoff := by
    rw [← E.historyBackwardLaw_of_terminal hterm]
    exact hintegrable
  unfold historyBackwardValue expect
  rw [E.historyBackwardLaw_of_terminal hterm]
  exact expect_pure history payoff hpure

/-- Numerical history Bellman equation on supported realized successors.
The source law guard supplies the conditional and outer guards. -/
theorem historyBackwardValue_of_not_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {history : E.History}
    (hterm : ¬ E.terminal history.state)
    (hsource : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff)
    (successorValue : E.State → ℝ)
    (hvalue : ∀ target, ∀ realized :
      target ∈ (E.step history.state (chooser history hterm)).support,
      ∀ hchild : PayoffIntegrable
        (E.historyBackwardLaw certificate chooser
          (history.extend (chooser history hterm).2 realized)) payoff,
        successorValue target =
          E.historyBackwardValue certificate chooser payoff
            (history.extend (chooser history hterm).2 realized) hchild) :
    ∃ houter : PayoffIntegrable
        (E.step history.state (chooser history hterm)) successorValue,
      E.historyBackwardValue certificate chooser payoff history hsource =
        expect (E.step history.state (chooser history hterm))
          successorValue houter := by
  let chosen := chooser history hterm
  let p := E.step history.state chosen
  let q : ∀ target, target ∈ p.support → PMF E.History :=
    fun _target realized =>
      E.historyBackwardLaw certificate chooser (history.extend chosen.2 realized)
  have hbind : PayoffIntegrable (p.bindOnSupport q) payoff := by
    rw [← E.historyBackwardLaw_of_not_terminal hterm]
    exact hsource
  have hcond : ∀ target, ∀ realized : target ∈ p.support,
      successorValue target = expect (q target realized) payoff
        (payoffIntegrable_bindOnSupport_conditional_on_support
          p q payoff hbind target realized) := by
    intro target realized
    exact hvalue target realized _
  let houter := payoffIntegrable_bindOnSupport_conditionalValue_on_support
    p q payoff hbind successorValue hcond
  refine ⟨houter, ?_⟩
  have htower := expect_bindOnSupport_tower_on_support
    p q payoff hbind successorValue hcond
  unfold historyBackwardValue expect at htower ⊢
  rw [E.historyBackwardLaw_of_not_terminal hterm]
  exact htower

theorem historyBackwardValue_eq_expect_runHistoryFor
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {horizon : ℕ} {history : E.History}
    (hstop : E.StopsHistoryWithin chooser horizon history)
    (hback : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff)
    (hrun : PayoffIntegrable (E.runHistoryFor chooser horizon history) payoff) :
    E.historyBackwardValue certificate chooser payoff history hback =
      expect (E.runHistoryFor chooser horizon history) payoff hrun := by
  unfold historyBackwardValue expect
  rw [E.historyBackwardLaw_eq_runHistoryFor hstop]

theorem historyBackwardValue_eq_expect_runHistoryFor_guarded
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {horizon : ℕ} {history : E.History}
    (hstop : E.StopsHistoryWithin chooser horizon history)
    (hback : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff) :
    ∃ hrun : PayoffIntegrable (E.runHistoryFor chooser horizon history) payoff,
      E.historyBackwardValue certificate chooser payoff history hback =
        expect (E.runHistoryFor chooser horizon history) payoff hrun := by
  let hrun : PayoffIntegrable (E.runHistoryFor chooser horizon history) payoff := by
    rw [← E.historyBackwardLaw_eq_runHistoryFor hstop]
    exact hback
  exact ⟨hrun, E.historyBackwardValue_eq_expect_runHistoryFor hstop hback hrun⟩

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

/-- Choosers agreeing on the reachable history cone have the same terminal law. -/
theorem historyBackwardLaw_congr_of_reaches
    {certificate : E.WellFoundedPlay}
    {first second : E.HistoryChooser} :
    ∀ start : E.History,
      (∀ later, E.HistoryReaches start later →
        ∀ hterm : ¬ E.terminal later.state,
          first later hterm = second later hterm) →
      E.historyBackwardLaw certificate first start =
        E.historyBackwardLaw certificate second start := by
  intro start
  induction start using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ history ih =>
      intro hagree
      by_cases hterm : E.terminal history.state
      · rw [E.historyBackwardLaw_of_terminal hterm,
          E.historyBackwardLaw_of_terminal hterm]
      · rw [E.historyBackwardLaw_of_not_terminal hterm,
          E.historyBackwardLaw_of_not_terminal hterm,
          hagree history (HistoryReaches.refl E history) hterm]
        apply bindOnSupport_congr
        intro target realized
        let chosen := second history hterm
        exact ih (history.extend chosen.2 realized)
          ⟨chosen.1, chosen.2, realized⟩
          (fun later hreach =>
            hagree later (HistoryReaches.step E chosen.2 realized hreach))

theorem historyBackwardValue_congr_of_reaches
    {certificate : E.WellFoundedPlay}
    {first second : E.HistoryChooser}
    {payoff : E.History → ℝ} (start : E.History)
    (hagree : ∀ later, E.HistoryReaches start later →
      ∀ hterm : ¬ E.terminal later.state,
        first later hterm = second later hterm)
    (hfirst : PayoffIntegrable (E.historyBackwardLaw certificate first start) payoff)
    (hsecond : PayoffIntegrable (E.historyBackwardLaw certificate second start) payoff) :
    E.historyBackwardValue certificate first payoff start hfirst =
      E.historyBackwardValue certificate second payoff start hsecond := by
  unfold historyBackwardValue expect
  rw [E.historyBackwardLaw_congr_of_reaches start hagree]

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

/-- The actual one-choice history context uses the same guarded continuation
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

/-- The incumbent and every legal one-choice continuation have finite real
values, and no one-choice change improves the incumbent. -/
def HasNoProfitableOneShotDeviation [DecidableEq ι]
    [∀ i, DecidableEq (M.InfoState i)]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  ∀ (who : ι) (history : E.History)
    (hterm : ¬ E.terminal history.state),
      (M.oneShotHistoryContext certificate profile utility who history hterm).IsLocallyOptimal
        Set.univ (profile who (M.infoOf who history.trace))

/-- Whole-policy optimality after every history. Each comparison carries both
finite-real integrability witnesses, including off-path histories. -/
def IsHistorywiseOptimal [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  ∀ (who : ι) (alternative : M.Policy who) (history : E.History),
    ∃ hother : PayoffIntegrable
        (E.historyBackwardLaw certificate
          (M.historyChooser (Profile.update profile who alternative)) history)
        (fun outcome => utility outcome who),
      ∃ hinc : PayoffIntegrable
          (E.historyBackwardLaw certificate (M.historyChooser profile) history)
          (fun outcome => utility outcome who),
        E.historyBackwardValue certificate
            (M.historyChooser (Profile.update profile who alternative))
            (fun outcome => utility outcome who) history hother ≤
          E.historyBackwardValue certificate (M.historyChooser profile)
            (fun outcome => utility outcome who) history hinc

/-- Whole-policy optimality at every information-set-closed subgame root. -/
def IsSubgamePerfect [DecidableEq ι]
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  ∀ (history : E.History), M.IsSubgameRoot history →
    ∀ (who : ι) (alternative : M.Policy who),
      ∃ hother : PayoffIntegrable
          (E.historyBackwardLaw certificate
            (M.historyChooser (Profile.update profile who alternative)) history)
          (fun outcome => utility outcome who),
        ∃ hinc : PayoffIntegrable
            (E.historyBackwardLaw certificate (M.historyChooser profile) history)
            (fun outcome => utility outcome who),
          E.historyBackwardValue certificate
              (M.historyChooser (Profile.update profile who alternative))
              (fun outcome => utility outcome who) history hother ≤
            E.historyBackwardValue certificate (M.historyChooser profile)
              (fun outcome => utility outcome who) history hinc

theorem IsHistorywiseOptimal.isSubgamePerfect [DecidableEq ι]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hoptimal : M.IsHistorywiseOptimal certificate profile utility) :
    M.IsSubgamePerfect certificate profile utility := by
  intro history _ who alternative
  exact hoptimal who alternative history

/-- Guarded local optimality certifies the incumbent terminal law at every
history, including terminal and off-path histories. -/
theorem historyBackwardLaw_integrable_of_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hopt : M.HasNoProfitableOneShotDeviation certificate profile utility)
    (who : ι) (history : E.History) :
    PayoffIntegrable
      (E.historyBackwardLaw certificate (M.historyChooser profile) history)
      (fun outcome => utility outcome who) := by
  by_cases hterm : E.terminal history.state
  · rw [E.historyBackwardLaw_of_terminal hterm]
    exact payoffIntegrable_pure history _
  · have hlocal := (hopt who history hterm).1
    rw [← M.oneShotHistoryLaw_self certificate profile who history hterm]
    exact hlocal

/-- A guarded local one-choice condition defeats an arbitrary whole-policy
replacement at a queried history once that candidate's terminal law is finite. -/
theorem historyBackwardValue_update_le_of_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hopt : M.HasNoProfitableOneShotDeviation certificate profile utility)
    (who : ι) (alternative : M.Policy who) (history : E.History)
    (hcandidate : PayoffIntegrable
      (E.historyBackwardLaw certificate
        (M.historyChooser (Profile.update profile who alternative)) history)
      (fun outcome => utility outcome who)) :
    E.historyBackwardValue certificate
        (M.historyChooser (Profile.update profile who alternative))
        (fun outcome => utility outcome who) history hcandidate ≤
      E.historyBackwardValue certificate (M.historyChooser profile)
        (fun outcome => utility outcome who) history
        (M.historyBackwardLaw_integrable_of_hasNoProfitableOneShotDeviation
          hopt who history) := by
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ current ih =>
      by_cases hterm : E.terminal current.state
      · unfold ExecutionProtocol.historyBackwardValue expect
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
        have hleft : PayoffIntegrable
            (stepLaw.bindOnSupport fun _target realized =>
              E.historyBackwardLaw certificate
                (M.historyChooser (Profile.update profile who alternative))
                (current.extend chosen.2 realized))
            (fun outcome => utility outcome who) := by
          rw [← hleftLaw]
          exact hcandidate
        have hlocal := hopt who current hterm
        have hright : PayoffIntegrable
            (stepLaw.bindOnSupport fun _target realized =>
              E.historyBackwardLaw certificate (M.historyChooser profile)
                (current.extend chosen.2 realized))
            (fun outcome => utility outcome who) := by
          rw [← hrightLaw]
          exact hlocal.2.1 choice (Set.mem_univ _)
        have hbound := hlocal.2.2 choice (Set.mem_univ _)
          hlocal.1 (hlocal.2.1 choice (Set.mem_univ _))
        unfold ExecutionProtocol.historyBackwardValue
        calc
          expect (E.historyBackwardLaw certificate
              (M.historyChooser (Profile.update profile who alternative)) current)
              (fun outcome => utility outcome who) hcandidate =
            expect (stepLaw.bindOnSupport fun _target realized =>
              E.historyBackwardLaw certificate
                (M.historyChooser (Profile.update profile who alternative))
                (current.extend chosen.2 realized))
              (fun outcome => utility outcome who) hleft := by
                unfold expect
                rw [hleftLaw]
          _ ≤ expect (stepLaw.bindOnSupport fun _target realized =>
                E.historyBackwardLaw certificate (M.historyChooser profile)
                  (current.extend chosen.2 realized))
                (fun outcome => utility outcome who) hright := by
              apply expect_bindOnSupport_mono_on_support
              intro target realized hconditional _
              simpa only [ExecutionProtocol.historyBackwardValue] using
                ih (current.extend chosen.2 realized)
                  ⟨chosen.1, chosen.2, realized⟩ hconditional
          _ ≤ expect (E.historyBackwardLaw certificate
                (M.historyChooser profile) current)
                (fun outcome => utility outcome who)
                (M.historyBackwardLaw_integrable_of_hasNoProfitableOneShotDeviation
                  hopt who current) := by
              unfold GameTheory.Protocol.Context.value at hbound
              unfold expect at hbound ⊢
              simpa only [oneShotHistoryContext, hrightLaw,
                M.oneShotHistoryLaw_self] using hbound

/-- Local optimality implies guarded historywise optimality when each whole
replacement policy being compared has a defined finite terminal value. -/
theorem isHistorywiseOptimal_of_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    {certificate : E.WellFoundedPlay}
    {profile : Profile M.strategicSignature}
    {utility : E.History → ι → ℝ}
    (hopt : M.HasNoProfitableOneShotDeviation certificate profile utility)
    (hcandidate : ∀ (who : ι) (alternative : M.Policy who)
      (history : E.History), PayoffIntegrable
        (E.historyBackwardLaw certificate
          (M.historyChooser (Profile.update profile who alternative)) history)
        (fun outcome => utility outcome who)) :
    M.IsHistorywiseOptimal certificate profile utility := by
  intro who alternative history
  let hother := hcandidate who alternative history
  let hinc := M.historyBackwardLaw_integrable_of_hasNoProfitableOneShotDeviation
    hopt who history
  exact ⟨hother, hinc,
    M.historyBackwardValue_update_le_of_hasNoProfitableOneShotDeviation
      hopt who alternative history hother⟩

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

/-- Guarded whole-policy optimality rules out every local choice when the
current information state cannot be revisited with a genuine choice. -/
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
  have hincCtx : ctx.IntegrableAt own := by
    show PayoffIntegrable
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
    show PayoffIntegrable
      (M.oneShotHistoryLaw certificate profile who history hterm choice)
      (fun outcome => utility outcome who)
    rw [hLaw]
    exact hchanged
  · intro choice _ hinc' halt
    let replacement := (profile who).replaceAt
      (M.infoOf who history.trace) choice
    obtain ⟨hchanged, hincOther, hle⟩ := hoptimal who replacement history
    have hLaw := M.oneShotHistoryLaw_eq_changed_of_actsOnce
      hactsOnce certificate profile history hterm choice
    show expect
        (M.oneShotHistoryLaw certificate profile who history hterm choice)
        (fun outcome => utility outcome who) halt ≤
      expect
        (M.oneShotHistoryLaw certificate profile who history hterm own)
        (fun outcome => utility outcome who) hinc'
    unfold ExecutionProtocol.historyBackwardValue expect at hle
    unfold expect
    rw [hLaw, hownLaw]
    exact hle

/-- Under no revisits, the historywise one-shot principle is an equivalence
provided every whole-policy candidate law in the comparison has a finite value. -/
theorem isHistorywiseOptimal_iff_hasNoProfitableOneShotDeviation
    [DecidableEq ι] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ)
    (hcandidate : ∀ (who : ι) (alternative : M.Policy who)
      (history : E.History), PayoffIntegrable
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
