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
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Probability
open GameTheory.Protocol.ExecutionProtocol (Context)

/-- Two hidden states and a stopping state. -/
inductive Room | left | right | done
  deriving DecidableEq, Repr

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
  step _ _ := FinDist.pure .done
  progress := by
    rintro state hterm
    exact ⟨fun _ => some .up, fun _ => ⟨hterm, Set.mem_univ _⟩⟩

/-- A context whose choice matters: `up` leads to `left`, `down` to `right`. -/
def splitContext (continuation : Room → ℝ) : rooms.Context () where
  outcome choice :=
    match choice with
    | some .up => FinDist.pure .left
    | some .down => FinDist.pure .right
    | none => FinDist.pure .done
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
    (splitContext continuation).value (some .up) = continuation .left :=
  FinDist.expect_pure ..

theorem value_down (continuation : Room → ℝ) :
    (splitContext continuation).value (some .down) = continuation .right :=
  FinDist.expect_pure ..

/-- Both calls are on the table. -/
def bothCalls : Set (Option Call) := {some .up, some .down}

/-! ## Probe 1: the value depends on the continuation

Fixing the outcome map and varying only the continuation flips which call is
optimal. This kills any `value` that ignores the continuation — which is
precisely the field the open-game context contributes and a static equilibrium
lacks. -/

theorem up_optimal_under_prefersLeft :
    (splitContext prefersLeft).IsLocallyOptimal bothCalls (some .up) := by
  rintro alternative (rfl | rfl)
  · rw [value_up]
  · rw [value_down, value_up]
    norm_num [prefersLeft]

theorem up_not_optimal_under_prefersRight :
    ¬ (splitContext prefersRight).IsLocallyOptimal bothCalls (some .up) := by
  intro hopt
  have hdown := hopt (some .down) (by simp [bothCalls])
  rw [value_down, value_up] at hdown
  norm_num [prefersRight] at hdown

/-! ## Probe 2: the value depends on the outcome map

Fixing the continuation and varying only where the calls lead flips the optimum
back. This kills any `value` that ignores the outcome map. -/

/-- The same continuation, but the calls lead the other way. -/
def swappedContext (continuation : Room → ℝ) : rooms.Context () where
  outcome choice :=
    match choice with
    | some .up => FinDist.pure .right
    | some .down => FinDist.pure .left
    | none => FinDist.pure .done
  continuation := continuation

theorem up_optimal_under_swapped :
    (swappedContext prefersRight).IsLocallyOptimal bothCalls (some .up) := by
  rintro alternative (rfl | rfl) <;>
    simp [Context.value, swappedContext, prefersRight, FinDist.expect_pure]

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
  refine ⟨by simp [bothCalls], ?_⟩
  rw [value_up, value_down]
  norm_num [prefersRight]

/-- And the interface theorem converts the exhibited deviation into a refutation
of optimality, rather than the refutation being assumed. -/
theorem no_optimality_from_profitable_deviation :
    ¬ (splitContext prefersRight).IsLocallyOptimal bothCalls (some .up) := by
  rw [Context.isLocallyOptimal_iff_no_profitable_deviation]
  intro hnone
  exact hnone ⟨some .down, down_is_profitable_under_prefersRight⟩

/-! ## Probe 4: `ofBelief` really averages over the belief

The belief-built context must depend on the belief, not just on one state. -/

/-- A branch that reports where it was. -/
def roomBranch (state : Room) (_choice : Option Call) : FinDist Room := FinDist.pure state

theorem ofBelief_value_pure (state : Room) (continuation : Room → ℝ)
    (choice : Option Call) :
    (Context.ofBelief (E := rooms) (i := ()) (FinDist.pure state) roomBranch
      continuation).value choice = continuation state := by
  rw [Context.ofBelief_value]
  simp [roomBranch]

/-- Two different point beliefs give two different values, so the belief is not
being discarded. -/
theorem belief_matters :
    (Context.ofBelief (E := rooms) (i := ()) (FinDist.pure .left) roomBranch
        prefersLeft).value (some .up) ≠
      (Context.ofBelief (E := rooms) (i := ()) (FinDist.pure .right) roomBranch
        prefersLeft).value (some .up) := by
  rw [ofBelief_value_pure, ofBelief_value_pure]
  simp [prefersLeft]

/-! ## Probe 5: information-local one-shot optimality reaches compiled Nash

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

/-- The corresponding utility on compiled history outcomes. -/
def upUtility (h : History twice) (_ : Unit) : ℝ :=
  upStateUtility h.state

/-- At every nonterminal history, the typed up choice is locally optimal in
the actual history context. The payoff bound handles every typed alternative;
the existing one-step run theorem computes the baseline value. -/
theorem up_sequentiallyRationalAt_historyContext :
    ∀ fuel, fuel < 1 → ∀ (h : History twice)
      (hterm : ¬ twice.terminal h.state),
        model.IsSequentiallyRationalAt
          (upProfile ()) (model.infoOf () h.trace)
          (model.historyContext upProfile ()
            (fun outcome => upUtility outcome ()) fuel h hterm) := by
  intro fuel hfuel h hterm
  have hfuel0 : fuel = 0 := by omega
  subst fuel
  have hstopped : h.state.stopped = false := by
    cases hstopped : h.state.stopped
    · rfl
    · exact absurd hstopped hterm
  have hup : (upProfile () false).1 = some Vote.up := rfl
  intro alternative _
  rw [InformationModel.historyContext_value,
    InformationModel.historyContext_value,
    InformationModel.oneShotLaw_self]
  calc
    (model.oneShotLaw upProfile 0 h hterm () alternative).expect
          (fun outcome => upUtility outcome ()) ≤
        (model.oneShotLaw upProfile 0 h hterm () alternative).expect
            (fun _ => 1) := by
              apply FinDist.expect_mono
              intro outcome _
              rcases outcome with ⟨state, outcomeTrace⟩
              cases state with
              | start => norm_num [upUtility, upStateUtility]
              | after vote =>
                  cases vote <;> norm_num [upUtility, upStateUtility]
              | done first second =>
                  cases second <;> norm_num [upUtility, upStateUtility]
    _ = 1 := FinDist.expect_const ..
    _ = (model.runFrom upProfile 1 h).expect
          (fun outcome => upUtility outcome ()) := by
      have hvalue : upStateUtility (stepTo h.state Vote.up) = 1 := by
        cases hstate : h.state with
        | start => rfl
        | after first => rfl
        | done first second =>
            simp [hstate, Round.stopped] at hstopped
      calc
        1 = (FinDist.pure (stepTo h.state Vote.up)).expect
            upStateUtility := by
              simp [hvalue]
        _ = (FinDist.map History.state
              (model.runFrom upProfile 1 h)).expect upStateUtility := by
                rw [map_state_runFrom_one upProfile Vote.up hup h hstopped]
        _ = (model.runFrom upProfile 1 h).expect
            (fun outcome => upUtility outcome ()) := by
              rw [FinDist.expect_map]
              rfl

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
    (model.runFrom (Profile.update upProfile () alternative) 1
        twice.initHistory).expect (fun outcome => upUtility outcome ()) ≤
      (model.runFrom upProfile 1 twice.initHistory).expect
        (fun outcome => upUtility outcome ()) :=
  model.expect_runFrom_update_le_of_isOneShotOptimalWithin
    upProfile () (fun outcome => upUtility outcome ()) 1
    up_isOneShotOptimalWithin alternative (le_refl 1) twice.initHistory

/-- The optimal profile has value one in the compiled form. -/
theorem up_expectedUtility :
    expectedUtility upUtility ()
      ((model.toGameForm 1).play upProfile) = 1 := by
  rw [InformationModel.toGameForm_play]
  unfold expectedUtility InformationModel.run
  calc
    (model.runFrom upProfile 1 twice.initHistory).expect
        (fun outcome => upUtility outcome ()) =
      (FinDist.map History.state
        (model.runFrom upProfile 1 twice.initHistory)).expect
          upStateUtility := by
            rw [FinDist.expect_map]
            rfl
    _ = 1 := by
      rw [map_state_runFrom_one upProfile Vote.up rfl
        twice.initHistory rfl]
      norm_num [stepTo, upStateUtility]

/-- The down profile has value zero, so optimality is not vacuous. -/
theorem down_expectedUtility :
    expectedUtility upUtility ()
      ((model.toGameForm 1).play downProfile) = 0 := by
  rw [InformationModel.toGameForm_play]
  unfold expectedUtility InformationModel.run
  calc
    (model.runFrom downProfile 1 twice.initHistory).expect
        (fun outcome => upUtility outcome ()) =
      (FinDist.map History.state
        (model.runFrom downProfile 1 twice.initHistory)).expect
          upStateUtility := by
            rw [FinDist.expect_map]
            rfl
    _ = 0 := by
      rw [map_state_runFrom_one downProfile Vote.down rfl
        twice.initHistory rfl]
      norm_num [stepTo, upStateUtility]

/-- The concrete alternative is strictly worse. -/
theorem up_strictly_better_than_down :
    expectedUtility upUtility ()
        ((model.toGameForm 1).play downProfile) <
      expectedUtility upUtility ()
        ((model.toGameForm 1).play upProfile) := by
  rw [down_expectedUtility, up_expectedUtility]
  norm_num

/-- **Hostile endpoint.** Concrete local rationality at every history implies
ordinary Nash for the information-local compiled game. -/
theorem up_isNash :
    IsNash (model.toGameForm 1) (euPreference upUtility) upProfile := by
  apply model.isNash_toGameForm_of_isOneShotOptimalWithin
  intro who
  cases who
  exact up_isOneShotOptimalWithin

end AssessmentBridge

end GameTheory.Tests
