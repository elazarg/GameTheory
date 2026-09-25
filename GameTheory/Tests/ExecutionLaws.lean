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

def coin : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

@[reducible] def loop : ExecutionProtocol Unit where
  State := Unit
  Action _ := Bool
  init := ()
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  step _ _ := PMF.pure ()
  progress _ _ := ⟨fun _ => some false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

def counterChooser : loop.RandomizedChooser := fun history _ =>
  (if history.trace.length = 0 then coin else PMF.pure false).map fun action =>
    ⟨fun _ => some action,
      by exact ⟨not_false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩⟩

def loopOnce : loop.History :=
  loop.initHistory.extend
    (show loop.Legal () (fun _ => some false) from
      ⟨not_false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩)
    ((PMF.mem_support_pure_iff _ _).mpr rfl)

theorem loop_same_state : loop.initHistory.state = loopOnce.state := rfl

/-- The action laws distinguish two histories at the same state. -/
theorem counter_actions_differ :
    (counterChooser loop.initHistory not_false).map (fun joint => joint.1 ()) ≠
      (counterChooser loopOnce not_false).map (fun joint => joint.1 ()) := by
  intro equal
  have hmass := congrArg (fun law : PMF (Option Bool) => law (some true)) equal
  simp only [counterChooser, PMF.map_comp, Function.comp_def] at hmass
  have hcoin := pmf_map_apply_of_injective coin (Option.some_injective Bool) true
  have hpure := pmf_map_apply_of_injective (PMF.pure false)
    (Option.some_injective Bool) true
  have hmass' : (coin.map Option.some) (some true) =
      ((PMF.pure false).map Option.some) (some true) := hmass
  rw [hcoin, hpure] at hmass'
  norm_num [coin, mix_apply, PMF.pure_apply] at hmass'

/-- Nevertheless the state-kernel premise holds for this history chooser. -/
theorem counter_state_law (fuel : ℕ) (history : loop.History) :
    (loop.runRandomizedFor counterChooser fuel history).map History.state =
      (fun law : PMF Unit => law.bind PMF.pure)^[fuel]
        (PMF.pure history.state) := by
  apply loop.runRandomizedFor_map_state counterChooser PMF.pure
  · intro state terminal
    exact terminal.elim
  · intro current _
    simp [counterChooser]

/-- The existing merging-history example cannot satisfy state sufficiency. -/
theorem merging_history_has_no_state_kernel :
    ¬ ∃ kernel : merge.State → PMF merge.State,
      ∀ (history : merge.History) (running : ¬ merge.terminal history.state),
        ((model.historyChooser (fun _ => follow)).toRandomized history running).bind
          (merge.step history.state) = kernel history.state := by
  rintro ⟨kernel, step⟩
  have left := step viaLeft not_terminal_mid
  have right := step viaRight not_terminal_mid
  dsimp [HistoryChooser.toRandomized] at left right
  rw [PMF.pure_bind] at left right
  have hleft : PMF.pure Stage.endL = kernel Stage.mid := by
    simpa [viaLeft_state, follow_after_left, merge] using left
  have hright : PMF.pure Stage.endR = kernel Stage.mid := by
    simpa [viaRight_state, follow_after_right, merge] using right
  have equal := hleft.trans hright.symm
  have hmass := congrArg (fun law : PMF Stage => law Stage.endL) equal
  norm_num [PMF.pure_apply] at hmass

@[reducible] def countdown : ExecutionProtocol Unit where
  State := ℕ × Bool
  Action _ := Unit
  init := (3, false)
  active _ _ := False
  available _ _ := Set.univ
  terminal state := state.1 = 0
  step state _ :=
    if state.1 = 2 then coin.map (fun toss => (1, toss))
    else PMF.pure (state.1 - 1, state.2)
  progress _ _ := ⟨fun _ => none, fun _ => not_false⟩

def countdownChooser : countdown.RandomizedChooser := fun _history running =>
  PMF.pure ⟨fun _ => none, running, fun _ => not_false⟩

def readout (state : countdown.State) : Bool := if state.1 = 0 then state.2 else false

def completionLaw (state : countdown.State) : PMF Bool :=
  if state.1 < 2 then PMF.pure state.2 else coin

theorem countdown_decreases (history : countdown.History)
    (joint : {actions // countdown.Legal history.state actions})
    (after : countdown.State) (realized : after ∈ (countdown.step history.state joint).support) :
    after.1 < history.state.1 := by
  have running := joint.2.1
  by_cases two : history.state.1 = 2
  · simp only [countdown, two, ↓reduceIte, PMF.support_map, Set.mem_image] at realized
    obtain ⟨toss, _, rfl⟩ := realized
    omega
  · simp only [countdown, two, ↓reduceIte, PMF.mem_support_pure_iff] at realized
    subst after
    have nonzero : history.state.1 ≠ 0 := running
    exact Nat.sub_lt (Nat.pos_of_ne_zero nonzero) (by omega)

theorem countdown_step_law (history : countdown.History)
    (running : ¬ countdown.terminal history.state) :
    (countdownChooser history running).bind
        (fun joint => (countdown.step history.state joint).bind completionLaw) =
      completionLaw history.state := by
  simp only [countdownChooser, PMF.pure_bind]
  rcases history with ⟨⟨steps, toss⟩, trace⟩
  match steps with
  | 0 => exact (running rfl).elim
  | 1 => simp [completionLaw]
  | 2 =>
      simp only [ite_true]
      rw [PMF.bind_map]
      have hfun : completionLaw ∘ (fun toss : Bool => (1, toss)) = PMF.pure := by
        funext toss
        simp [completionLaw]
      rw [hfun, PMF.bind_pure]
      simp [completionLaw]
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
      (PMF.mem_support_pure_iff _ _).mpr rfl)

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
        (fun history => readout history.state) = PMF.pure false := by
  rw [runRandomizedFor_succ_of_not_terminal _ 0 (by decide)]
  simp only [countdownChooser, PMF.pure_bind]
  apply map_bindOnSupport_const
  intro target realized
  simp only [runRandomizedFor_zero, PMF.pure_map, History.extend_state]
  have first : target.1 = 1 := by
    have supported : target ∈ (coin.map (fun toss => (1, toss))).support := realized
    rw [PMF.support_map] at supported
    obtain ⟨toss, _, rfl⟩ := supported
    rfl
  simp [readout, first]

theorem insufficient_fuel_not_completed :
    (countdown.runRandomizedFor countdownChooser 1 retainedPrefix).map
        (fun history => readout history.state) ≠ coin := by
  rw [insufficient_fuel]
  intro equal
  have hmass := congrArg (fun law : PMF Bool => law true) equal
  norm_num [coin, mix_apply, PMF.pure_apply] at hmass

example (chooser : Randomized.twice.RandomizedChooser) (history : Randomized.twice.History) :
    Randomized.twice.runRandomizedFor chooser 5 history =
      Randomized.twice.runRandomizedFor chooser 2 history :=
  Randomized.twice.runRandomizedFor_eq_of_bound Randomized.twice_bounded chooser history 5
    (by omega)

end GameTheory.Tests.ExecutionLaws
