/-
# Randomizing along the history

A `HistoryChooser` commits to one joint action at each history. A player that
randomizes locally does not: it draws from a law over its own options, and the
draws it makes at different histories are independent of one another. This
module runs a protocol under a chooser that answers each history with a *law*
over legal joint actions.

Two laws are composed at every step, and they are composed in the order play
happens: first the draw, then the transition it induces. The deterministic
runner is the special case in which every answer is a point mass, and that is a
theorem here rather than a convention — so this is not a third notion of play
sitting beside the other two.
-/

import GameTheory.Protocol.History

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E) in
/-- A chooser that answers each history with a law over legal joint actions.
Legality stays a typing constraint: no law can put mass on an illegal move. -/
def RandomizedChooser : Type _ :=
  (h : E.History) → ¬ E.terminal h.state →
    FinDist { joint : ∀ i, Option (E.Action i) // E.Legal h.state joint }

/-- A deterministic chooser is one whose every answer is a point mass. -/
def HistoryChooser.toRandomized (chooser : E.HistoryChooser) : E.RandomizedChooser :=
  fun h hterm => FinDist.pure (chooser h hterm)

open Classical in
/-- Run for at most `fuel` steps, drawing a joint action at each history and
then stepping through the transition law it selects. -/
def runRandomizedFor (chooser : E.RandomizedChooser) : ℕ → E.History → FinDist E.History
  | 0, h => FinDist.pure h
  | fuel + 1, h =>
    if hterm : E.terminal h.state then FinDist.pure h
    else
      (chooser h hterm).bind fun draw =>
        (E.step h.state draw).bindOnSupport fun _ realized =>
          runRandomizedFor chooser fuel (h.extend draw.2 realized)

@[simp]
theorem runRandomizedFor_zero (chooser : E.RandomizedChooser) (h : E.History) :
    E.runRandomizedFor chooser 0 h = FinDist.pure h := rfl

@[simp]
theorem runRandomizedFor_of_terminal (chooser : E.RandomizedChooser) (fuel : ℕ) {h : E.History}
    (hterm : E.terminal h.state) : E.runRandomizedFor chooser fuel h = FinDist.pure h := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [runRandomizedFor, dif_pos hterm]

theorem runRandomizedFor_succ_of_not_terminal (chooser : E.RandomizedChooser) (fuel : ℕ)
    {h : E.History} (hterm : ¬ E.terminal h.state) :
    E.runRandomizedFor chooser (fuel + 1) h =
      (chooser h hterm).bind fun draw =>
        (E.step h.state draw).bindOnSupport fun _ realized =>
          E.runRandomizedFor chooser fuel (h.extend draw.2 realized) := by
  rw [runRandomizedFor, dif_neg hterm]

/-- Running for `m + n` randomized history steps is running for `m` steps
and then independently continuing for `n` more. -/
theorem runRandomizedFor_add (chooser : E.RandomizedChooser)
    (firstFuel secondFuel : ℕ) (history : E.History) :
    E.runRandomizedFor chooser (firstFuel + secondFuel) history =
      (E.runRandomizedFor chooser firstFuel history).bind
        (E.runRandomizedFor chooser secondFuel) := by
  induction firstFuel generalizing history with
  | zero => simp [FinDist.pure_bind]
  | succ firstFuel ih =>
      by_cases hterm : E.terminal history.state
      · rw [runRandomizedFor_of_terminal _ _ hterm,
          runRandomizedFor_of_terminal _ _ hterm,
          FinDist.pure_bind,
          runRandomizedFor_of_terminal _ _ hterm]
      · rw [show firstFuel + 1 + secondFuel =
            (firstFuel + secondFuel) + 1 by omega,
          runRandomizedFor_succ_of_not_terminal chooser _ hterm,
          runRandomizedFor_succ_of_not_terminal chooser _ hterm,
          FinDist.bind_bind]
        apply FinDist.bind_congr
        intro draw _
        rw [FinDist.bind_bindOnSupport]
        exact FinDist.bindOnSupport_congr fun reached realized =>
          ih (history.extend draw.2 realized)

/-- In a protocol that never terminates, every history in a `fuel`-step run
has gained exactly `fuel` transitions.  This is the support invariant used by
fixed-horizon proof views; it does not define another runner. -/
theorem trace_length_eq_of_mem_support_runRandomizedFor
    (chooser : E.RandomizedChooser)
    (neverTerminal : ∀ state : E.State, ¬ E.terminal state) :
    ∀ (fuel : ℕ) (start result : E.History),
      result ∈ (E.runRandomizedFor chooser fuel start).support →
        result.trace.length = start.trace.length + fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro start result hresult
      rw [runRandomizedFor_zero, FinDist.mem_support_pure] at hresult
      subst result
      simp
  | succ fuel ih =>
      intro start result hresult
      rw [runRandomizedFor_succ_of_not_terminal chooser fuel
          (neverTerminal start.state), FinDist.support_bind] at hresult
      obtain ⟨draw, hdraw, hresult⟩ := Set.mem_iUnion₂.mp hresult
      rw [FinDist.support_bindOnSupport] at hresult
      obtain ⟨target, realized, hresult⟩ := Set.mem_iUnion₂.mp hresult
      have hlength := ih (start.extend draw.2 realized) result hresult
      simpa only [History.extend, Trace.length, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hlength

/-- **Deterministic play is the degenerate case.** A chooser that answers with
point masses induces exactly the law the deterministic runner induces, so
randomizing is an extension of committing rather than a rival account of it. -/
theorem runRandomizedFor_toRandomized (chooser : E.HistoryChooser) :
    ∀ (fuel : ℕ) (h : E.History),
      E.runRandomizedFor chooser.toRandomized fuel h = E.runHistoryFor chooser fuel h := by
  intro fuel
  induction fuel with
  | zero => intro h; rfl
  | succ fuel ih =>
    intro h
    by_cases hterm : E.terminal h.state
    · rw [runRandomizedFor_of_terminal _ _ hterm, runHistoryFor_of_terminal _ _ hterm]
    · rw [runRandomizedFor_succ_of_not_terminal _ fuel hterm,
        runHistoryFor_succ_of_not_terminal _ fuel hterm,
        HistoryChooser.toRandomized, FinDist.pure_bind]
      exact FinDist.bindOnSupport_congr fun _ _ => ih _

/-- And therefore the state law is still recovered by forgetting the history,
for a chooser that reads neither the history nor a coin. -/
theorem map_state_runRandomizedFor (chooser : E.Chooser) (fuel : ℕ) (h : E.History) :
    FinDist.map History.state
        (E.runRandomizedFor chooser.toHistoryChooser.toRandomized fuel h) =
      E.runFor chooser fuel h.state := by
  rw [runRandomizedFor_toRandomized, map_state_runHistoryFor]

/-- Choosers that answer every history with the same law induce the same run
law. -/
theorem runRandomizedFor_congr {first second : E.RandomizedChooser}
    (hagree : ∀ (h : E.History) (hterm : ¬ E.terminal h.state), first h hterm = second h hterm) :
    ∀ (fuel : ℕ) (h : E.History),
      E.runRandomizedFor first fuel h = E.runRandomizedFor second fuel h := by
  intro fuel
  induction fuel with
  | zero => intro h; rfl
  | succ fuel ih =>
    intro h
    by_cases hterm : E.terminal h.state
    · rw [runRandomizedFor_of_terminal _ _ hterm, runRandomizedFor_of_terminal _ _ hterm]
    · rw [runRandomizedFor_succ_of_not_terminal first fuel hterm,
        runRandomizedFor_succ_of_not_terminal second fuel hterm, hagree h hterm]
      exact FinDist.bind_congr fun _ _ => FinDist.bindOnSupport_congr fun _ _ => ih _

end ExecutionProtocol

end GameTheory.Protocol
