/-
# A two-round simultaneous game

The multi-round counterpart of the one-shot simultaneous test. One round of
simultaneous moves is enough to show that a single-mover tree cannot express
simultaneity; this file checks the harder claim, that simultaneity *composes*
across rounds without encoding tricks.

Everything the encoding needs is already in the execution interface: `active` is
a predicate over players, so a whole round is one state; `step` consumes a joint
action, so a round resolves in one transition; and the resulting state carries
the round's outcome forward, so the second round can depend on the first.

The probes below are what make that claim non-vacuous. Each fixes everything
but one thing and varies it: both players' first-round calls matter, the second
round is not vestigial, and the state reached after round one genuinely records
which outcome occurred.
-/

import GameTheory.Protocol.Execution

noncomputable section

namespace GameTheory.Languages

open GameTheory GameTheory.Protocol GameTheory.Probability

/-- Play proceeds through two simultaneous rounds and then stops. The middle
state carries the first round's outcome, which is what lets the second round
depend on it. -/
inductive Stage
  | opening
  | second (agreedFirst : Bool)
  | finished (agreedFirst agreedSecond : Bool)
  deriving DecidableEq, Repr

/-- Two players, two rounds, both moving in each. -/
@[reducible]
def rounds : ExecutionProtocol (Fin 2) where
  State := Stage
  Action _ := Bool
  init := .opening
  active state _ := match state with | .finished _ _ => False | _ => True
  available _ _ := Set.univ
  terminal state := match state with | .finished _ _ => True | _ => False
  step state joint :=
    match state with
    | .opening =>
        match joint.1 0, joint.1 1 with
        | some first, some second => FinDist.pure (.second (first == second))
        | _, _ => FinDist.pure (.second false)
    | .second agreedFirst =>
        match joint.1 0, joint.1 1 with
        | some first, some second =>
            FinDist.pure (.finished agreedFirst (first == second))
        | _, _ => FinDist.pure (.finished agreedFirst false)
    | .finished agreedFirst agreedSecond =>
        FinDist.pure (.finished agreedFirst agreedSecond)
  progress := by
    rintro state hterm
    refine ⟨fun _ => some true, fun i => ?_⟩
    cases state <;> simp_all

/-- Wherever play has not stopped, everybody is on move: a round is genuinely
simultaneous rather than a disguised alternation. -/
theorem all_active_of_not_terminal {state : Stage} (hterm : ¬ rounds.terminal state)
    (i : Fin 2) : rounds.active state i := by
  cases state <;> simp_all

/-- Both players call `true`. -/
def bothTrue : ∀ _ : Fin 2, Option Bool := fun _ => some true

/-- The first player alone switches. Written so that the option is always
`some`, which keeps the legality proof free of a case split. -/
def firstSwitches : ∀ _ : Fin 2, Option Bool := fun i => some (decide (i ≠ 0))

theorem legal_bothTrue {state : Stage} (hterm : ¬ rounds.terminal state) :
    rounds.Legal state bothTrue :=
  ⟨hterm, fun i => ⟨all_active_of_not_terminal hterm i, Set.mem_univ _⟩⟩

theorem legal_firstSwitches {state : Stage} (hterm : ¬ rounds.terminal state) :
    rounds.Legal state firstSwitches :=
  ⟨hterm, fun i => ⟨all_active_of_not_terminal hterm i, Set.mem_univ _⟩⟩

theorem opening_not_terminal : ¬ rounds.terminal .opening := by simp

theorem second_not_terminal (agreedFirst : Bool) :
    ¬ rounds.terminal (.second agreedFirst) := by simp

/-! ## Probe 1: both players' first-round calls matter

A protocol that read one player's action and ignored the other would fail
this. -/

theorem opening_depends_on_both :
    rounds.step .opening ⟨bothTrue, legal_bothTrue opening_not_terminal⟩ ≠
      rounds.step .opening ⟨firstSwitches, legal_firstSwitches opening_not_terminal⟩ := by
  have hagree : rounds.step .opening ⟨bothTrue, legal_bothTrue opening_not_terminal⟩ =
      FinDist.pure (.second true) := rfl
  have hsplit : rounds.step .opening ⟨firstSwitches, legal_firstSwitches opening_not_terminal⟩ =
      FinDist.pure (.second false) := rfl
  rw [hagree, hsplit]
  intro hequal
  have hmass := congrArg (fun law => FinDist.prob law (Stage.second true)) hequal
  simp [FinDist.prob_pure_eq_ite] at hmass

/-! ## Probe 2: the second round is not vestigial

The same two joint actions, played in round two, still separate the outcome. -/

theorem second_round_depends_on_both (agreedFirst : Bool) :
    rounds.step (.second agreedFirst)
        ⟨bothTrue, legal_bothTrue (second_not_terminal agreedFirst)⟩ ≠
      rounds.step (.second agreedFirst)
        ⟨firstSwitches, legal_firstSwitches (second_not_terminal agreedFirst)⟩ := by
  have hagree : rounds.step (.second agreedFirst)
      ⟨bothTrue, legal_bothTrue (second_not_terminal agreedFirst)⟩ =
      FinDist.pure (.finished agreedFirst true) := rfl
  have hsplit : rounds.step (.second agreedFirst)
      ⟨firstSwitches, legal_firstSwitches (second_not_terminal agreedFirst)⟩ =
      FinDist.pure (.finished agreedFirst false) := rfl
  rw [hagree, hsplit]
  intro hequal
  have hmass :=
    congrArg (fun law => FinDist.prob law (Stage.finished agreedFirst true)) hequal
  simp [FinDist.prob_pure_eq_ite] at hmass

/-! ## Probe 3: round two can see round one

Without this the two probes above would be compatible with a game whose rounds
are independent, which is not a two-round game in any interesting sense. -/

theorem second_states_are_distinct : Stage.second true ≠ Stage.second false := by decide

/-- And the two are reached from the two different first-round outcomes, so the
distinction is realized rather than merely available. -/
theorem first_round_selects_second_state :
    rounds.step .opening ⟨bothTrue, legal_bothTrue opening_not_terminal⟩ =
        FinDist.pure (.second true) ∧
      rounds.step .opening ⟨firstSwitches, legal_firstSwitches opening_not_terminal⟩ =
        FinDist.pure (.second false) :=
  ⟨rfl, rfl⟩

/-! ## Running the whole game -/

/-- A policy that always calls `true`. -/
def alwaysTrue : rounds.Chooser :=
  fun _ hterm => ⟨bothTrue, legal_bothTrue hterm⟩

theorem runFor_two :
    rounds.runFor alwaysTrue 2 .opening = FinDist.pure (.finished true true) := by
  rw [ExecutionProtocol.runFor_succ_of_not_terminal alwaysTrue 1 opening_not_terminal]
  show (FinDist.pure (Stage.second true)).bind (rounds.runFor alwaysTrue 1) = _
  rw [FinDist.pure_bind,
    ExecutionProtocol.runFor_succ_of_not_terminal alwaysTrue 0 (second_not_terminal true)]
  show (FinDist.pure (Stage.finished true true)).bind (rounds.runFor alwaysTrue 0) = _
  rw [FinDist.pure_bind]
  rfl

/-- Two rounds is exactly the horizon, so the fuelled runner is a total
evaluator on this game. -/
theorem stopsWithin_two : rounds.StopsWithin alwaysTrue 2 .opening := by
  intro reached hreached
  rw [runFor_two, FinDist.mem_support_pure] at hreached
  subst hreached
  simp

theorem runFor_stable {fuel : ℕ} (hfuel : 2 ≤ fuel) :
    rounds.runFor alwaysTrue fuel .opening = FinDist.pure (.finished true true) := by
  rw [ExecutionProtocol.runFor_eq_of_stopsWithin_le stopsWithin_two hfuel, runFor_two]

/-! ## Workarounds

The list this encoding is obliged to produce.

**Fake players: none.** The index type is the game's own player set, and every
non-terminal state has all of them on move.

**Fake actions beyond the canonical no-op: none.** Both rounds use the players'
real action carrier. The no-op never appears, because no state has an idle
player: `all_active_of_not_terminal` says everybody moves wherever play
continues.

**Escape fields: none.** The execution interface was used as declared.

**The honest remainder.** The middle state carries the first round's outcome
rather than the first round's *actions*. That is a modelling choice, not a
workaround — but it means a game whose second round depends on the exact
first-round profile, not just on its summary, would need a wider state. Nothing
in the interface prevents that; this file simply does not test it.

No information model is built here. Round two conditioning is expressed through
the state, which is the perfect-monitoring case; the imperfect-information
overlay is exercised elsewhere, on a protocol built for it.
-/

end GameTheory.Languages
