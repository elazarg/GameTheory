module

/-
# Conditional-probability consistency rejects a dogmatic off-path chance belief

The weak-PBE control exits before a fair hidden bit is drawn. Its off-path
guessing belief assigns probability one to false, although nature assigns each
bit probability one half. A common conditional system respecting nature cannot
represent that belief even though the whole guessing site is unreached.
-/

public import GameTheory.Tests.WeakPBESeparation
public import GameTheory.Protocol.ConditionalPBE

@[expose] public section

noncomputable section

namespace GameTheory.Tests.ConditionalPBESeparation

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability
open GameTheory.Tests.WeakPBESeparation
open scoped ENNReal

/-- The rejected assessment belongs to the predicate's explicit-chance domain. -/
theorem arena_hasExplicitChance : arena.HasExplicitChance := by
  intro history active joint
  rcases history with ⟨state, _trace⟩
  cases state with
  | root => exact ⟨_, rfl⟩
  | chance => obtain ⟨_, active⟩ := active; exact False.elim active
  | guess latent => exact ⟨_, rfl⟩
  | exited => exact ⟨_, rfl⟩
  | done latent chosen => exact ⟨_, rfl⟩

def guessingSite : model.InformationSite () :=
  ⟨.guess, ⟨⟨guessHistory false, rfl⟩, by simp [State.terminal],
    false, by simp [menu]⟩⟩

def guessingHistory (bit : Bool) : model.InformationHistory () guessingSite.1 :=
  ⟨guessHistory bit, rfl⟩

theorem guessing_passage_eq_chance_cone :
    model.terminalPassage () guessingSite = arena.terminalCone chanceHistory := by
  ext final
  rcases final with ⟨final, terminal⟩
  constructor
  · rintro ⟨history, fuel, reached⟩
    have stage : history.1.state.stage = .guess :=
      (infoOf_stage history.1.trace).symm.trans history.2
    obtain ⟨first, initial⟩ := guess_reaches_from_chance history.1 stage
    exact ⟨first + fuel, initial.trans reached⟩
  · rintro ⟨fuel, reached⟩
    cases reached with
    | refl => exact False.elim terminal
    | @step restFuel _ _ joint legal target realized rest =>
        have jointEq : joint = arena.noop := by
          funext who
          cases who
          exact LegalOption.eq_none_of_inactive (joint ())
            (ExecutionProtocol.legalOption_of_legal legal ()) (by change ¬ False; exact not_false)
        subst joint
        change target ∈ (coin.map State.guess).support at realized
        rw [PMF.support_map] at realized
        obtain ⟨bit, _, rfl⟩ := realized
        refine ⟨guessingHistory bit, restFuel, ?_⟩
        exact rest

theorem guess_move_legal (bit chosen : Bool) :
    arena.Legal (.guess bit) (move chosen) :=
  ⟨by simp [State.terminal], fun _ => ⟨trivial, Set.mem_univ _⟩⟩

def doneHistory (bit chosen : Bool) : arena.History :=
  (guessHistory bit).extend (guess_move_legal bit chosen)
    (show State.done bit chosen ∈ (arena.step (.guess bit)
      ⟨move chosen, guess_move_legal bit chosen⟩).support from by
        simp [arena, action, move])

def doneTerminal (bit chosen : Bool) : arena.TerminalHistory :=
  ⟨doneHistory bit chosen, by trivial⟩

theorem guess_reaches_done (bit chosen : Bool) :
    arena.HistoryReaches (guessHistory bit) (doneHistory bit chosen) :=
  ⟨1, .step (move chosen) (guess_move_legal bit chosen) _ (.refl _ _)⟩

theorem guess_reaches_done_same_bit (bit : Bool) (final : arena.TerminalHistory)
    (reached : arena.HistoryReaches (guessHistory bit) final.1) :
    ∃ chosen, final.1.state = .done bit chosen := by
  obtain ⟨fuel, reached⟩ := reached
  rcases final with ⟨final, terminal⟩
  cases reached with
  | refl => exact False.elim terminal
  | @step restFuel _ _ joint legal target realized rest =>
      have targetEq : target = State.done bit (action joint) := by
        change _ ∈ (PMF.pure (State.done bit (action joint))).support at realized
        exact (PMF.mem_support_pure_iff _ _).mp realized
      have stopped : arena.terminal ((guessHistory bit).extend legal realized).state := by
        change arena.terminal target
        rw [targetEq]
        trivial
      have equal := rest.eq_of_terminal stopped
      exact ⟨action joint, (congrArg History.state equal).trans targetEq⟩

theorem false_done_mem_false_cone :
    doneTerminal false false ∈ arena.terminalCone (guessHistory false) :=
  guess_reaches_done false false

theorem true_done_not_mem_false_cone :
    doneTerminal true false ∉ arena.terminalCone (guessHistory false) := by
  intro reached
  obtain ⟨chosen, equal⟩ := guess_reaches_done_same_bit false _ reached
  change State.done true false = State.done false chosen at equal
  cases equal

set_option backward.isDefEq.respectTransparency false in
theorem backwardLaw_guess (bit : Bool) :
    arena.historyBackwardLaw wellFoundedHistories (model.historyChooser profile)
      (guessHistory bit) = PMF.pure (doneHistory bit false) := by
  rw [arena.historyBackwardLaw_of_not_terminal_of_chooser_eq
    (show ¬ arena.terminal (guessHistory bit).state by simp [State.terminal])
    ⟨move false, guess_move_legal bit false⟩ rfl]
  change (PMF.pure (State.done bit false)).bindOnSupport _ = _
  rw [PMF.pure_bindOnSupport]
  exact arena.historyBackwardLaw_of_terminal (by trivial)

theorem backwardLaw_chance :
    arena.historyBackwardLaw wellFoundedHistories (model.historyChooser profile)
      chanceHistory = coin.map (fun bit => doneHistory bit false) := by
  rw [arena.historyBackwardLaw_of_not_terminal_of_chooser_eq
    (show ¬ arena.terminal chanceHistory.state by simp [State.terminal])
    ⟨arena.noop, chance_noop_legal⟩ rfl]
  change (coin.map State.guess).bindOnSupport _ = _
  let kernel : State → PMF arena.History := fun state => match state with
    | .guess bit => PMF.pure (doneHistory bit false)
    | _ => PMF.pure (doneHistory false false)
  calc
    _ = (coin.map State.guess).bind kernel := by
      apply bindOnSupport_eq_bind_of_eq_on_support
      intro target realized
      rw [PMF.support_map] at realized
      obtain ⟨bit, _, rfl⟩ := realized
      exact backwardLaw_guess bit
    _ = coin.map (fun bit => doneHistory bit false) := by
      rw [PMF.bind_map]
      exact PMF.bind_pure_comp _ _

theorem terminalLaw_chance :
    model.terminalLaw wellFoundedHistories assessment.strategy chanceHistory =
      coin.map (fun bit => doneTerminal bit false) := by
  apply pmf_map_injective Subtype.val_injective
  rw [model.terminalLaw_map_val]
  change model.runBehavioralTerminalFrom wellFoundedHistories
    (fun who => (profile who).toBehavioral) chanceHistory = _
  rw [model.runBehavioralTerminalFrom_toBehavioral wellFoundedHistories profile]
  change arena.historyBackwardLaw wellFoundedHistories (model.historyChooser profile)
    chanceHistory = _
  rw [backwardLaw_chance, PMF.map_comp]
  rfl

theorem chance_false_cone_probability :
    (model.terminalLaw wellFoundedHistories assessment.strategy chanceHistory).toOuterMeasure
      (arena.terminalCone (guessHistory false)) = 1 / 2 := by
  classical
  rw [terminalLaw_chance, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_fintype]
  simp only [Fintype.sum_bool, Set.indicator_apply, Set.mem_preimage,
    false_done_mem_false_cone, true_done_not_mem_false_cone, ite_true, ite_false, zero_add]
  norm_num [coin, mix_apply, PMF.pure_apply, ENNReal.ofReal_div_of_pos]

/-- A common conditional system cannot simultaneously represent the dogmatic
guessing belief and the off-path fair chance continuation. -/
theorem assessment_not_conditionalProbabilityConsistent :
    ¬ assessment.IsConditionalProbabilityConsistent model wellFoundedHistories := by
  rintro ⟨C, compatible⟩
  have represented := compatible.represents () guessingSite (guessingHistory false)
  have dogmatic : C.prob (arena.terminalCone (guessHistory false))
      (model.terminalPassage () guessingSite)
        (model.terminalPassage_nonempty wellFoundedHistories assessment.strategy () guessingSite) =
      1 := by
    have same : selectedHistory guessingSite = guessingHistory false := by
      apply Subtype.ext
      simp [selectedHistory, guessingSite, guessingHistory]
    have mass : assessment.belief () guessingSite (guessingHistory false) = 1 := by
      change (PMF.pure (selectedHistory guessingSite)) (guessingHistory false) = 1
      rw [same]
      exact PMF.pure_apply_self _
    exact represented.symm.trans mass
  have nature := compatible.nature chanceHistory (by simp [State.terminal])
    (by intro who; simp [State.active])
    (guessHistory false) (guess_reaches_from_chance (guessHistory false) rfl)
  have contradictory : (1 : ℝ≥0∞) = 1 / 2 := by
    calc
      1 = C.prob (arena.terminalCone (guessHistory false))
          (arena.terminalCone chanceHistory)
            (model.terminalCone_nonempty wellFoundedHistories
              assessment.strategy chanceHistory) := by
        simpa only [guessing_passage_eq_chance_cone] using dogmatic.symm
      _ = _ := nature.trans chance_false_cone_probability
  have real := congrArg ENNReal.toReal contradictory
  norm_num at real

theorem assessment_not_conditionalPBE :
    ¬ assessment.IsConditionalPBE model arena_hasExplicitChance wellFoundedHistories payoff :=
  fun equilibrium => assessment_not_conditionalProbabilityConsistent equilibrium.2

/-- The explicit weak PBE is rejected by conditional-probability PBE. -/
theorem weakPBE_not_conditionalPBE :
    assessment.IsWeakPBE information_antichain wellFoundedHistories payoff ∧
      ¬ assessment.IsConditionalPBE model arena_hasExplicitChance wellFoundedHistories payoff :=
  ⟨assessment_isWeakPBE, assessment_not_conditionalPBE⟩

end GameTheory.Tests.ConditionalPBESeparation
