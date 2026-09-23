/-
# State sufficiency and completed readout controls

History-dependent actions can induce a state-only transition law. Conversely,
the branch-merging fixture rejects the claim when history changes that law.
A separate stochastic countdown checks completed readout from a retained prefix.
-/

import GameTheory.Protocol.StateKernel
import GameTheory.Protocol.ContinuationLaw
import GameTheory.Tests.History
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Tests.ExecutionLaws

open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def coin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

@[reducible] def loop : ExecutionProtocol Unit where
  State := Unit
  Action _ := Bool
  init := ()
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  step _ _ := FinDist.pure ()
  progress _ _ := ⟨fun _ => some false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

def counterChooser : loop.RandomizedChooser := fun history _ =>
  (if history.trace.length = 0 then coin else FinDist.pure false).map fun action =>
    ⟨fun _ => some action,
      by exact ⟨not_false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩⟩

def loopOnce : loop.History :=
  loop.initHistory.extend
    (show loop.Legal () (fun _ => some false) from
      ⟨not_false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩)
    (FinDist.mem_support_pure.mpr rfl)

theorem loop_same_state : loop.initHistory.state = loopOnce.state := rfl

/-- The action laws distinguish two histories at the same state. -/
theorem counter_actions_differ :
    (counterChooser loop.initHistory not_false).map (fun joint => joint.1 ()) ≠
      (counterChooser loopOnce not_false).map (fun joint => joint.1 ()) := by
  intro equal
  have := congrArg (fun law => law.prob (some true)) equal
  simp only [counterChooser, FinDist.map_comp] at this
  have mass : (coin.map some).prob (some true) =
      ((FinDist.pure false).map some).prob (some true) := this
  rw [FinDist.prob_map_of_injective some (Option.some_injective Bool),
    FinDist.prob_map_of_injective some (Option.some_injective Bool)] at mass
  norm_num [coin, FinDist.prob_pure_eq_ite] at mass

/-- Nevertheless the state-kernel premise holds for this history chooser. -/
theorem counter_state_law (fuel : ℕ) (history : loop.History) :
    (loop.runRandomizedFor counterChooser fuel history).map History.state =
      (fun law : FinDist Unit => law.bind FinDist.pure)^[fuel]
        (FinDist.pure history.state) := by
  apply loop.runRandomizedFor_map_state counterChooser FinDist.pure
  · intro state terminal
    exact terminal.elim
  · intro current _
    simp [counterChooser, FinDist.bind_const]

/-- The existing merging-history example cannot satisfy state sufficiency. -/
theorem merging_history_has_no_state_kernel :
    ¬ ∃ kernel : merge.State → FinDist merge.State,
      ∀ (history : merge.History) (running : ¬ merge.terminal history.state),
        ((model.historyChooser (fun _ => follow)).toRandomized history running).bind
          (merge.step history.state) = kernel history.state := by
  rintro ⟨kernel, step⟩
  have left := step viaLeft not_terminal_mid
  have right := step viaRight not_terminal_mid
  have equal := left.trans right.symm
  have := congrArg (fun law => law.prob Stage.endL) equal
  simp only [HistoryChooser.toRandomized, FinDist.pure_bind] at this
  have mass : (FinDist.pure Stage.endL).prob Stage.endL =
      (FinDist.pure Stage.endR).prob Stage.endL := this
  norm_num [FinDist.prob_pure_eq_ite] at mass

@[reducible] def countdown : ExecutionProtocol Unit where
  State := ℕ × Bool
  Action _ := Unit
  init := (3, false)
  active _ _ := False
  available _ _ := Set.univ
  terminal state := state.1 = 0
  step state _ :=
    if state.1 = 2 then coin.map (fun toss => (1, toss))
    else FinDist.pure (state.1 - 1, state.2)
  progress _ _ := ⟨fun _ => none, fun _ => not_false⟩

def countdownChooser : countdown.RandomizedChooser := fun _history running =>
  FinDist.pure ⟨fun _ => none, running, fun _ => not_false⟩

def readout (state : countdown.State) : Bool := if state.1 = 0 then state.2 else false

def completionLaw (state : countdown.State) : FinDist Bool :=
  if state.1 < 2 then FinDist.pure state.2 else coin

theorem countdown_decreases (history : countdown.History)
    (joint : {actions // countdown.Legal history.state actions})
    (after : countdown.State) (realized : after ∈ (countdown.step history.state joint).support) :
    after.1 < history.state.1 := by
  have running := joint.2.1
  by_cases two : history.state.1 = 2
  · simp only [countdown, two, ↓reduceIte, FinDist.support_map, Set.mem_image] at realized
    obtain ⟨toss, _, rfl⟩ := realized
    omega
  · simp only [countdown, two, ↓reduceIte, FinDist.mem_support_pure] at realized
    subst after
    have nonzero : history.state.1 ≠ 0 := running
    exact Nat.sub_lt (Nat.pos_of_ne_zero nonzero) (by omega)

theorem countdown_step_law (history : countdown.History)
    (running : ¬ countdown.terminal history.state) :
    (countdownChooser history running).bind
        (fun joint => (countdown.step history.state joint).bind completionLaw) =
      completionLaw history.state := by
  simp only [countdownChooser, FinDist.pure_bind]
  rcases history with ⟨⟨steps, toss⟩, trace⟩
  match steps with
  | 0 => exact (running rfl).elim
  | 1 => simp [completionLaw]
  | 2 => simp [completionLaw, FinDist.bind_map, FinDist.bind_pure]
  | n + 3 =>
      have ne : n + 3 ≠ 2 := by omega
      have large : ¬ n + 3 < 2 := by omega
      have later : ¬ n + 2 < 2 := by omega
      simp [completionLaw, ne, large, later]

def retainedPrefix : countdown.History :=
  countdown.initHistory.extend
    (show countdown.Legal (3, false) (fun _ => none) from
      ⟨by decide, fun _ => not_false⟩)
    (show (2, false) ∈ (countdown.step (3, false)
      ⟨fun _ => none, by exact ⟨by decide, fun _ => not_false⟩⟩).support from
      FinDist.mem_support_pure.mpr rfl)

/-- The supplied prefix is already one legal step, and is retained by execution. -/
theorem retainedPrefix_length : retainedPrefix.trace.length = 1 := rfl

theorem completed_run_retains_prefix (final : countdown.History)
    (realized : final ∈ (countdown.runRandomizedFor countdownChooser 2 retainedPrefix).support) :
    countdown.ReachesWithin 2 retainedPrefix final ∧ 1 ≤ final.trace.length := by
  have reachable := countdown.runRandomizedFor_reachesWithin countdownChooser 2
    retainedPrefix final realized
  exact ⟨reachable, reachable.trace_length_le⟩

theorem completed_from_retained_prefix :
    (countdown.runRandomizedFor countdownChooser 2 retainedPrefix).map
        (fun history => readout history.state) = coin := by
  apply countdown.runRandomizedFor_readout_eq countdownChooser Prod.fst
    (fun _ zero => zero) countdown_decreases readout completionLaw
  · intro state terminal
    simp [completionLaw, readout, show state.1 = 0 from terminal]
  · exact countdown_step_law
  · exact le_refl 2

/-- One step leaves the sampled coin hidden in a nonterminal state. -/
theorem insufficient_fuel :
    (countdown.runRandomizedFor countdownChooser 1 retainedPrefix).map
        (fun history => readout history.state) = FinDist.pure false := by
  rw [runRandomizedFor_succ_of_not_terminal _ 0 (by decide)]
  simp only [countdownChooser, FinDist.pure_bind]
  apply FinDist.map_bindOnSupport_const
  intro target realized
  simp only [runRandomizedFor_zero, FinDist.map_pure, History.extend_state]
  have first : target.1 = 1 := by
    have supported : target ∈ (coin.map (fun toss => (1, toss))).support := realized
    rw [FinDist.support_map] at supported
    obtain ⟨toss, _, rfl⟩ := supported
    rfl
  simp [readout, first]

theorem insufficient_fuel_not_completed :
    (countdown.runRandomizedFor countdownChooser 1 retainedPrefix).map
        (fun history => readout history.state) ≠ coin := by
  rw [insufficient_fuel]
  intro equal
  have := congrArg (fun law => law.prob true) equal
  norm_num [coin, FinDist.prob_pure_eq_ite] at this

example (chooser : Randomized.twice.RandomizedChooser) (history : Randomized.twice.History) :
    Randomized.twice.runRandomizedFor chooser 5 history =
      Randomized.twice.runRandomizedFor chooser 2 history :=
  Randomized.twice.runRandomizedFor_eq_of_bound Randomized.twice_bounded chooser history 5
    (by omega)

end GameTheory.Tests.ExecutionLaws
