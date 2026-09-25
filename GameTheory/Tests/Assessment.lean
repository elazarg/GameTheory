/-
# Probes for the one-shot-deviation interface

`GameTheory.Protocol.Assessment` reduces the open-game context to two fields and
*derives* local optimality from them. These probes check that the reduction did
not throw away the content.

The failure mode to rule out is a context whose `value` ignores one of its two
fields. Such a `Context` would still satisfy every theorem in the module —
`isLocallyOptimal_iff_no_profitable_deviation` is a tautology about `value`, and
would hold just as well if `value` were constant. So each probe below fixes one
field and varies the other.
-/

import GameTheory.Protocol.Assessment
import GameTheory.Tests.EFGZermelo
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol (Context)

/-- Two hidden states and a stopping state. -/
inductive Room | left | right | done
  deriving DecidableEq, Repr

instance : Fintype Room :=
  ⟨{.left, .right, .done}, by intro room; cases room <;> simp⟩

/-- The deviator's two calls. -/
inductive Call | up | down
  deriving DecidableEq, Repr

/-- A protocol just rich enough to carry a context: one mover, two rooms. -/
@[reducible]
def rooms : ExecutionProtocol Unit where
  State := Room
  Action _ := Call
  init := .left
  active state _ := state ≠ .done
  available _ _ := Set.univ
  terminal state := state = .done
  step _ _ := PMF.pure .done
  progress := by
    rintro state hterm
    exact ⟨fun _ => some .up, fun _ => ⟨hterm, Set.mem_univ _⟩⟩

/-- A context whose choice matters: `up` leads to `left`, `down` to `right`. -/
def splitContext (continuation : Room → ℝ) : rooms.Context () where
  outcome choice :=
    match choice with
    | some .up => PMF.pure .left
    | some .down => PMF.pure .right
    | none => PMF.pure .done
  continuation := continuation

/-- A continuation that prefers `left`. -/
def prefersLeft : Room → ℝ
  | .left => 1
  | .right => 0
  | .done => 0

/-- A continuation that prefers `right`. -/
def prefersRight : Room → ℝ
  | .left => 0
  | .right => 1
  | .done => 0

theorem value_up (continuation : Room → ℝ) :
    (splitContext continuation).value (some .up)
      (payoffIntegrable_of_finite _ _) = continuation .left := by
  exact expect_pure _ _ _

theorem value_down (continuation : Room → ℝ) :
    (splitContext continuation).value (some .down)
      (payoffIntegrable_of_finite _ _) = continuation .right := by
  exact expect_pure _ _ _

/-- Both calls are on the table. -/
def bothCalls : Set (Option Call) := {some .up, some .down}

/-! ## Probe 1: the value depends on the continuation

Fixing the outcome map and varying only the continuation flips which call is
optimal. This kills any `value` that ignores the continuation — which is
precisely the field the open-game context contributes and a static equilibrium
lacks. -/

theorem up_optimal_under_prefersLeft :
    (splitContext prefersLeft).IsLocallyOptimal bothCalls (some .up) := by
  refine ⟨payoffIntegrable_of_finite _ _,
    (fun _ _ => payoffIntegrable_of_finite _ _), ?_⟩
  rintro alternative (rfl | rfl) hchoice halt
  · exact le_rfl
  · rw [value_down, value_up]
    norm_num [prefersLeft]

theorem up_not_optimal_under_prefersRight :
    ¬ (splitContext prefersRight).IsLocallyOptimal bothCalls (some .up) := by
  intro hopt
  have hdown := hopt.2.2 (some .down) (by simp [bothCalls])
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  rw [value_down, value_up] at hdown
  norm_num [prefersRight] at hdown

/-! ## Probe 2: the value depends on the outcome map

Fixing the continuation and varying only where the calls lead flips the optimum
back. This kills any `value` that ignores the outcome map. -/

/-- The same continuation, but the calls lead the other way. -/
def swappedContext (continuation : Room → ℝ) : rooms.Context () where
  outcome choice :=
    match choice with
    | some .up => PMF.pure .right
    | some .down => PMF.pure .left
    | none => PMF.pure .done
  continuation := continuation

theorem up_optimal_under_swapped :
    (swappedContext prefersRight).IsLocallyOptimal bothCalls (some .up) := by
  refine ⟨payoffIntegrable_of_finite _ _,
    (fun _ _ => payoffIntegrable_of_finite _ _), ?_⟩
  rintro alternative (rfl | rfl) hchoice halt <;>
    simp [Context.value, swappedContext, prefersRight, expect_pure]

/-- Same continuation as `up_not_optimal_under_prefersRight`, opposite verdict:
only the outcome map changed. -/
theorem outcome_map_matters :
    ¬ (splitContext prefersRight).IsLocallyOptimal bothCalls (some .up) ∧
      (swappedContext prefersRight).IsLocallyOptimal bothCalls (some .up) :=
  ⟨up_not_optimal_under_prefersRight, up_optimal_under_swapped⟩

/-! ## Probe 3: a profitable one-shot deviation is exhibited, not just denied

`isLocallyOptimal_iff_no_profitable_deviation` would be vacuously useful if no
profitable deviation ever existed. Here is one. -/

theorem down_is_profitable_under_prefersRight :
    (splitContext prefersRight).IsProfitableDeviation bothCalls (some .up) (some .down) := by
  refine ⟨by simp [bothCalls], payoffIntegrable_of_finite _ _,
    payoffIntegrable_of_finite _ _, ?_⟩
  rw [value_up, value_down]
  norm_num [prefersRight]

/-- And the interface theorem converts the exhibited deviation into a refutation
of optimality, rather than the refutation being assumed. -/
theorem no_optimality_from_profitable_deviation :
    ¬ (splitContext prefersRight).IsLocallyOptimal bothCalls (some .up) := by
  rw [Context.isLocallyOptimal_iff_no_profitable_deviation]
  intro hopt
  exact hopt.2.2 ⟨some .down, down_is_profitable_under_prefersRight⟩

/-! ## Probe 4: `ofBelief` really averages over the belief

The belief-built context must depend on the belief, not just on one state. -/

/-- A branch that reports where it was. -/
def roomBranch (state : Room) (_choice : Option Call) : PMF Room := PMF.pure state

theorem ofBelief_value_pure (state : Room) (continuation : Room → ℝ)
    (choice : Option Call) :
    (Context.ofBelief (E := rooms) (i := ()) (PMF.pure state) roomBranch
      continuation).value choice (payoffIntegrable_of_finite _ _) =
      continuation state := by
  dsimp only [GameTheory.Protocol.Context.value,
    GameTheory.Protocol.Context.IntegrableAt,
    ExecutionProtocol.Context.ofBelief,
    GameTheory.Protocol.Context.ofBelief]
  simp only [PMF.pure_bind, roomBranch, expect_pure]

/-- Two different point beliefs give two different values, so the belief is not
being discarded. -/
theorem belief_matters :
    (Context.ofBelief (E := rooms) (i := ()) (PMF.pure .left) roomBranch
        prefersLeft).value (some .up) (payoffIntegrable_of_finite _ _) ≠
      (Context.ofBelief (E := rooms) (i := ()) (PMF.pure .right) roomBranch
        prefersLeft).value (some .up) (payoffIntegrable_of_finite _ _) := by
  rw [ofBelief_value_pure, ofBelief_value_pure]
  simp [prefersLeft]

/-! ## Probe 5: remaining fuel is coupled to realized depth

The chance-rooted Zermelo fixture contains both a two-decision continuation
and branches that stop early.  At horizon three, its first decision has one
continuation step left, its second decision has none, and an early exit is
absorbing for the unused final unit of fuel.  This is the stopping shape that
the former depth-independent one-shot premise failed to distinguish. -/

namespace StoppingDepth

open EFGZermelo

variable (profile : Profile information.strategicSignature)
  (payoff : execution.History → ℝ)

/-- The first decision is evaluated with exactly two total steps remaining. -/
theorem first_decision_bound
    (hopt : information.IsOneShotOptimalWithin profile () payoff 3)
    (choice : information.Choice ()
      (information.infoOf () leftHistory.trace))
    (hchoice : PayoffIntegrable
      (information.oneShotLaw profile 1 leftHistory left_not_terminal () choice) payoff)
    (hbase : PayoffIntegrable (information.runFrom profile 2 leftHistory) payoff) :
    expect (information.oneShotLaw profile 1 leftHistory left_not_terminal () choice)
        payoff hchoice ≤
      expect (information.runFrom profile 2 leftHistory) payoff hbase := by
  have hlocal := hopt 1 leftHistory (by rfl) left_not_terminal
  have hbase' :
      (information.historyContext profile () payoff 1 leftHistory
        left_not_terminal).IntegrableAt
          (profile () (information.infoOf () leftHistory.trace)) := by
    dsimp only [Context.IntegrableAt, InformationModel.historyContext]
    rw [information.oneShotLaw_self]
    exact hbase
  have hle := hlocal.2.2 choice (Set.mem_univ _) hbase' hchoice
  simpa only [Context.value, InformationModel.historyContext,
    information.oneShotLaw_self] using hle

/-- The later decision is evaluated with exactly one total step remaining. -/
theorem second_decision_bound
    (hopt : information.IsOneShotOptimalWithin profile () payoff 3)
    (choice : information.Choice ()
      (information.infoOf () secondHistory.trace))
    (hchoice : PayoffIntegrable
      (information.oneShotLaw profile 0 secondHistory second_not_terminal () choice) payoff)
    (hbase : PayoffIntegrable (information.runFrom profile 1 secondHistory) payoff) :
    expect (information.oneShotLaw profile 0 secondHistory second_not_terminal () choice)
        payoff hchoice ≤
      expect (information.runFrom profile 1 secondHistory) payoff hbase := by
  have hlocal := hopt 0 secondHistory (by rfl) second_not_terminal
  have hbase' :
      (information.historyContext profile () payoff 0 secondHistory
        second_not_terminal).IntegrableAt
          (profile () (information.infoOf () secondHistory.trace)) := by
    dsimp only [Context.IntegrableAt, InformationModel.historyContext]
    rw [information.oneShotLaw_self]
    exact hbase
  have hle := hlocal.2.2 choice (Set.mem_univ _) hbase' hchoice
  simpa only [Context.value, InformationModel.historyContext,
    information.oneShotLaw_self] using hle

/-- The depth equation rejects evaluating the first decision with the later
decision's continuation fuel. -/
theorem first_decision_wrong_fuel_rejected :
    ¬ leftHistory.trace.length + 0 + 1 = 3 := by
  have hlength : leftHistory.trace.length = 1 := rfl
  omega

/-- The depth equation likewise rejects giving the second decision an extra
continuation step. -/
theorem second_decision_wrong_fuel_rejected :
    ¬ secondHistory.trace.length + 1 + 1 = 3 := by
  have hlength : secondHistory.trace.length = 2 := rfl
  omega

def exitJoint : Unit → Option Action := fun _ => some .exit

theorem exitLegal : execution.Legal leftHistory.state exitJoint := by
  apply execution.legal_of_legalOption left_not_terminal
  intro who
  cases who
  exact ⟨left_active, by simp [execution]⟩

theorem exited_mem_exit_step :
    State.exited ∈
      (execution.step leftHistory.state ⟨exitJoint, exitLegal⟩).support := by
  simp [exitJoint, execution, next]

def exitedHistory : execution.History :=
  leftHistory.extend exitLegal exited_mem_exit_step

theorem exitedHistory_terminal : execution.terminal exitedHistory.state := by
  simp [exitedHistory, execution]

/-- Stopping before the nominal horizon consumes no fictitious decision: the
history runner is already absorbing. -/
theorem early_exit_absorbing :
    information.runFrom profile 1 exitedHistory =
      PMF.pure exitedHistory := by
  exact ExecutionProtocol.runHistoryFor_of_terminal _ _ exitedHistory_terminal

end StoppingDepth

/-! ## Probe 6: information-local one-shot optimality reaches compiled Nash

The repeated-vote information model is hostile to a merely initial-history
argument: the same player can be at either of two nonterminal histories, and
the one-shot premise must cover both. At horizon one, always voting up is
locally optimal at every such history when utility rewards the vote just made.
The generic bridge then controls every replacement policy and proves ordinary
Nash in the compiled `GameForm`.
-/

namespace AssessmentBridge

open Randomized
open GameTheory.Protocol.ExecutionProtocol (History)

/-- Vote up at the continuing information state and do nothing after play
stops. -/
def upPolicy : model.Policy () := fun info =>
  match info with
  | false => ⟨some .up, by simp [menuAt]⟩
  | true => ⟨none, by simp [menuAt]⟩

/-- The one-player profile using `upPolicy`. -/
def upProfile : Profile model.strategicSignature := fun _ => upPolicy

/-- The comparison profile that votes down. -/
def downPolicy : model.Policy () := fun info =>
  match info with
  | false => ⟨some .down, by simp [menuAt]⟩
  | true => ⟨none, by simp [menuAt]⟩

/-- The one-player profile using `downPolicy`. -/
def downProfile : Profile model.strategicSignature := fun _ => downPolicy

/-- Reward an up vote when it is the most recent vote in the reached state. -/
def upStateUtility : Round → ℝ
  | .after .up => 1
  | .done _ .up => 1
  | _ => 0

theorem upStateUtility_bound (state : Round) :
    |upStateUtility state| ≤ 1 := by
  cases state with
  | start => norm_num [upStateUtility]
  | after vote => cases vote <;> norm_num [upStateUtility]
  | done first second =>
      cases second <;> norm_num [upStateUtility]

/-- The corresponding utility on compiled history outcomes. -/
def upUtility (h : History twice) (_ : Unit) : ℝ :=
  upStateUtility h.state

theorem upUtility_bound (h : History twice) :
    |upUtility h ()| ≤ 1 := by
  rcases h with ⟨state, trace⟩
  cases state with
  | start => norm_num [upUtility, upStateUtility]
  | after vote => cases vote <;> norm_num [upUtility, upStateUtility]
  | done first second =>
      cases second <;> norm_num [upUtility, upStateUtility]

theorem upUtility_integrable (law : PMF (History twice)) :
    PayoffIntegrable law (fun h => upUtility h ()) :=
  payoffIntegrable_of_bounded law _ upUtility_bound

/-- At every nonterminal history, the typed up choice is locally optimal in
the actual history context. The payoff bound handles every typed alternative;
the existing one-step run theorem computes the baseline value. -/
theorem up_sequentiallyRationalAt_historyContext :
    ∀ fuel (h : History twice), h.trace.length + fuel + 1 = 1 →
      ∀ (hterm : ¬ twice.terminal h.state),
        model.IsSequentiallyRationalAt
          (upProfile ()) (model.infoOf () h.trace)
          (model.historyContext upProfile ()
            (fun outcome => upUtility outcome ()) fuel h hterm) := by
  intro fuel h hdepth hterm
  have hfuel0 : fuel = 0 := by omega
  subst fuel
  have hstopped : h.state.stopped = false := by
    cases hstopped : h.state.stopped
    · rfl
    · exact absurd hstopped hterm
  have hup : (upProfile () false).1 = some Vote.up := rfl
  refine ⟨upUtility_integrable _, (fun _ _ => upUtility_integrable _), ?_⟩
  intro alternative _ hbase halt
  dsimp only [Context.value, InformationModel.historyContext] at hbase halt ⊢
  dsimp only [Context.IntegrableAt, InformationModel.historyContext] at hbase
  calc
    expect (model.oneShotLaw upProfile 0 h hterm () alternative)
          (fun outcome => upUtility outcome ()) halt ≤
        expect (model.oneShotLaw upProfile 0 h hterm () alternative)
            (fun _ => 1) (payoffIntegrable_constant _ 1) := by
              apply expect_mono
              intro outcome _
              rcases outcome with ⟨state, outcomeTrace⟩
              cases state with
              | start => norm_num [upUtility, upStateUtility]
              | after vote =>
                  cases vote <;> norm_num [upUtility, upStateUtility]
              | done first second =>
                  cases second <;> norm_num [upUtility, upStateUtility]
    _ = 1 := expect_constant _ _ _
    _ = expect (model.oneShotLaw upProfile 0 h hterm ()
          (upProfile () (model.infoOf () h.trace)))
          (fun outcome => upUtility outcome ()) hbase := by
      have hvalue : upStateUtility (stepTo h.state Vote.up) = 1 := by
        cases hstate : h.state with
        | start => rfl
        | after first => rfl
        | done first second =>
            simp [hstate, Round.stopped] at hstopped
      calc
        1 = expect (PMF.pure (stepTo h.state Vote.up)) upStateUtility
            (payoffIntegrable_of_bounded _ _ upStateUtility_bound) := by
              rw [expect_pure]
              exact hvalue.symm
        _ = expect (PMF.map History.state (model.runFrom upProfile 1 h))
              upStateUtility (payoffIntegrable_of_bounded _ _ upStateUtility_bound) := by
                rw [map_state_runFrom_one upProfile Vote.up hup h hstopped]
        _ = expect (model.runFrom upProfile 1 h)
            (fun outcome => upUtility outcome ()) (upUtility_integrable _) := by
              rw [expect_map History.state]
              rfl
        _ = _ := (expect_congr_law
          (model.oneShotLaw_self upProfile 0 h hterm ())
          (fun outcome => upUtility outcome ()) hbase
          (upUtility_integrable _)).symm

/-- The history-context characterization packages the concrete local proof as
finite-horizon one-shot optimality. -/
theorem up_isOneShotOptimalWithin :
    model.IsOneShotOptimalWithin upProfile ()
      (fun outcome => upUtility outcome ()) 1 := by
  rw [InformationModel.isOneShotOptimalWithin_iff_sequentiallyRationalAt_historyContext]
  exact up_sequentiallyRationalAt_historyContext

/-- The generic global bridge now controls an arbitrary replacement policy,
including policies that reach a different continuation history. -/
theorem arbitrary_policy_update_no_better (alternative : model.Policy ()) :
    expect (model.runFrom (Profile.update upProfile () alternative) 1
        twice.initHistory) (fun outcome => upUtility outcome ())
        (upUtility_integrable _) ≤
      expect (model.runFrom upProfile 1 twice.initHistory)
        (fun outcome => upUtility outcome ()) (upUtility_integrable _) := by
  simpa only [expect_proof_irrel] using
  model.expect_runFrom_update_le_of_isOneShotOptimalWithin
    upProfile () (fun outcome => upUtility outcome ()) 1
    up_isOneShotOptimalWithin alternative twice.initHistory (by
      simp [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length])
    (upUtility_integrable _)

/-- The optimal profile has value one in the compiled form. -/
theorem up_expectedUtility :
    expectedUtility upUtility ()
      ((model.toGameForm 1).play upProfile) (upUtility_integrable _) = 1 := by
  rw [InformationModel.toGameForm_play]
  unfold expectedUtility InformationModel.run
  calc
    expect (model.runFrom upProfile 1 twice.initHistory)
        (fun outcome => upUtility outcome ()) (upUtility_integrable _) =
      expect (PMF.map History.state
        (model.runFrom upProfile 1 twice.initHistory)) upStateUtility
          (payoffIntegrable_of_bounded _ _ upStateUtility_bound) := by
            rw [expect_map History.state]
            rfl
    _ = 1 := by
      rw [map_state_runFrom_one upProfile Vote.up rfl
        twice.initHistory rfl]
      norm_num [stepTo, upStateUtility, expect_pure]

/-- The down profile has value zero, so optimality is not vacuous. -/
theorem down_expectedUtility :
    expectedUtility upUtility ()
      ((model.toGameForm 1).play downProfile) (upUtility_integrable _) = 0 := by
  rw [InformationModel.toGameForm_play]
  unfold expectedUtility InformationModel.run
  calc
    expect (model.runFrom downProfile 1 twice.initHistory)
        (fun outcome => upUtility outcome ()) (upUtility_integrable _) =
      expect (PMF.map History.state
        (model.runFrom downProfile 1 twice.initHistory)) upStateUtility
          (payoffIntegrable_of_bounded _ _ upStateUtility_bound) := by
            rw [expect_map History.state]
            rfl
    _ = 0 := by
      rw [map_state_runFrom_one downProfile Vote.down rfl
        twice.initHistory rfl]
      norm_num [stepTo, upStateUtility, expect_pure]

/-- The concrete alternative is strictly worse. -/
theorem up_strictly_better_than_down :
    expectedUtility upUtility ()
        ((model.toGameForm 1).play downProfile) (upUtility_integrable _) <
      expectedUtility upUtility ()
        ((model.toGameForm 1).play upProfile) (upUtility_integrable _) := by
  rw [down_expectedUtility, up_expectedUtility]
  norm_num

/-- **Hostile endpoint.** Concrete local rationality at every history implies
ordinary Nash for the information-local compiled game. -/
theorem up_isNash :
    IsNash (model.toGameForm 1) (euPreference upUtility) upProfile := by
  exact model.isNash_toGameForm_of_isOneShotOptimalWithin
    upProfile upUtility 1
    (fun who => by cases who; exact up_isOneShotOptimalWithin)
    (fun who _ => by cases who; exact upUtility_integrable _)

end AssessmentBridge

end GameTheory.Tests
