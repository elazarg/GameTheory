/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCircuitProgressTotal

/-!
# Constructing finite executable essential-APS runs

The fixed-point trichotomy gives a local disjunction: terminal absorption,
zero-mass propagation to the displayed successor fiber, or a proper
positive-mass segment into that fiber.  This file composes those local choices.

On a finite owner path with a unique live successor at every step, every point
of the greatest APS family either reaches a terminal point before the requested
horizon or admits a concrete finite singleton-flow run through the horizon.
The run records one continuation value and one mass in `[0,1)` per edge.  This
closes the gap between a pointwise progress disjunction and an actual finite
sequence of executable arc witnesses.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- A concrete singleton-flow run of `horizon` edges.  Values are required to
remain in the supplied owner-indexed family through the terminal vertex, and
each displayed edge carries a mass in `[0,1)` and satisfies the exact arc
equation. -/
def IsQuittingEssentialAPSFiniteRun
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (owner : ℕ → ι) (initial : Payoff ι) (horizon : ℕ)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι) : Prop :=
  value 0 = initial ∧
    (∀ time, time ≤ horizon → value time ∈ family (owner time)) ∧
      ∀ time, time < horizon →
        mass time ∈ Set.Ico (0 : ℝ) 1 ∧
          value time = quittingSingletonArcPayoff (mass time)
            (quittingSoloReward reward (owner time))
            (value (time + 1))

/-- Append one exact singleton-flow edge to a finite run. -/
theorem IsQuittingEssentialAPSFiniteRun.extend
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {family : ι → Set (Payoff ι)}
    {owner : ℕ → ι} {initial : Payoff ι} {horizon : ℕ}
    {mass : ℕ → ℝ} {value : ℕ → Payoff ι}
    {p : ℝ} {next : Payoff ι}
    (hrun : IsQuittingEssentialAPSFiniteRun reward family owner initial
      horizon mass value)
    (hp : p ∈ Set.Ico (0 : ℝ) 1)
    (hnext : next ∈ family (owner (horizon + 1)))
    (harc : value horizon = quittingSingletonArcPayoff p
      (quittingSoloReward reward (owner horizon)) next) :
    ∃ mass' value',
      IsQuittingEssentialAPSFiniteRun reward family owner initial
        (horizon + 1) mass' value' := by
  classical
  refine ⟨Function.update mass horizon p,
    Function.update value (horizon + 1) next, ?_⟩
  rcases hrun with ⟨hinitial, hmem, hstep⟩
  refine ⟨?_, ?_, ?_⟩
  · have hne : (0 : ℕ) ≠ horizon + 1 := by omega
    simpa [hne] using hinitial
  · intro time htime
    by_cases heq : time = horizon + 1
    · subst time
      simpa using hnext
    · have hle : time ≤ horizon := by omega
      simpa [heq] using hmem time hle
  · intro time htime
    by_cases heq : time = horizon
    · subst time
      have hne : horizon ≠ horizon + 1 := by omega
      constructor
      · simpa using hp
      · simpa [hne] using harc
    · have hlt : time < horizon := by omega
      rcases hstep time hlt with ⟨hmass, harcOld⟩
      have hvalueNe : time ≠ horizon + 1 := by omega
      have hnextNe : time + 1 ≠ horizon + 1 := by omega
      constructor
      · simpa [heq] using hmass
      · simpa [heq, hvalueNe, hnextNe] using harcOld

/-- Every vertex of a finite run inside the greatest family lies on the active
hyperplane of its current owner. -/
theorem IsQuittingEssentialAPSFiniteRun.active_of_greatest
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {carrier : ι → Set (Payoff ι)}
    {owner : ℕ → ι} {initial : Payoff ι} {horizon : ℕ}
    {mass : ℕ → ℝ} {value : ℕ → Payoff ι}
    (hrun : IsQuittingEssentialAPSFiniteRun reward
      (quittingEssentialAPSGreatestFamily reward carrier)
      owner initial horizon mass value)
    {time : ℕ} (htime : time ≤ horizon) :
    value time (owner time) =
      quittingSoloReward reward (owner time) (owner time) :=
  quittingEssentialAPSGreatestFamily_active reward carrier
    (owner time) (hrun.2.1 time htime)

/-- **Finite APS run construction under unique live successors.**  Starting
from any greatest-family point, either a terminal point is reached before the
requested horizon, together with the concrete run leading to it, or a concrete
run of the full requested length exists. -/
theorem exists_quittingEssentialAPSFiniteRun_or_terminal_of_unique_live
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ player, Convex ℝ (carrier player))
    (owner : ℕ → ι)
    (hedge : ∀ time,
      QuittingFleschSuccessor reward (owner time) (owner (time + 1)))
    (huniqueLive : ∀ time candidate,
      QuittingFleschSuccessor reward (owner time) candidate →
        candidate ≠ owner (time + 1) →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅)
    {current : Payoff ι}
    (hcurrent : current ∈
      quittingEssentialAPSGreatestFamily reward carrier (owner 0))
    (horizon : ℕ) :
    (∃ stop, stop < horizon ∧
      ∃ mass value,
        IsQuittingEssentialAPSFiniteRun reward
          (quittingEssentialAPSGreatestFamily reward carrier)
          owner current stop mass value ∧
        value stop ∈ quittingEssentialAPSTerminal reward (owner stop)) ∨
      ∃ mass value,
        IsQuittingEssentialAPSFiniteRun reward
          (quittingEssentialAPSGreatestFamily reward carrier)
          owner current horizon mass value := by
  induction horizon with
  | zero =>
      right
      refine ⟨fun _ ↦ 0, fun _ ↦ current, ?_⟩
      refine ⟨rfl, ?_, ?_⟩
      · intro time htime
        have htimeZero : time = 0 := Nat.eq_zero_of_le_zero htime
        subst time
        exact hcurrent
      · intro time htime
        omega
  | succ horizon ih =>
      rcases ih with hterminal | hrun
      · left
        rcases hterminal with
          ⟨stop, hstop, mass, value, hrun, hterminal⟩
        exact ⟨stop, hstop.trans (Nat.lt_succ_self horizon),
          mass, value, hrun, hterminal⟩
      · rcases hrun with ⟨mass, value, hrun⟩
        have hlast : value horizon ∈
            quittingEssentialAPSGreatestFamily reward carrier
              (owner horizon) :=
          hrun.2.1 horizon le_rfl
        rcases
            quittingEssentialAPSGreatestFamily_terminal_or_successor_or_proper_of_unique_live_total
              reward carrier hcarrier (hedge horizon)
              (huniqueLive horizon) hlast with
          hterminal | hsuccessor | hproper
        · left
          exact ⟨horizon, Nat.lt_succ_self horizon,
            mass, value, hrun, hterminal⟩
        · right
          have harcZero : value horizon =
              quittingSingletonArcPayoff 0
                (quittingSoloReward reward (owner horizon))
                (value horizon) := by
            funext who
            simp [quittingSingletonArcPayoff]
          exact hrun.extend ⟨le_rfl, zero_lt_one⟩
            hsuccessor harcZero
        · rcases hproper with
            ⟨_hviable, p, hp, next, hnext, harc, _hactive⟩
          right
          exact hrun.extend ⟨hp.1.le, hp.2⟩ hnext harc

/-- Graph-theoretic uniqueness is a special case of finite-run construction
under unique live successors. -/
theorem exists_quittingEssentialAPSFiniteRun_or_terminal_of_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ player, Convex ℝ (carrier player))
    (owner : ℕ → ι)
    (hedge : ∀ time,
      QuittingFleschSuccessor reward (owner time) (owner (time + 1)))
    (hunique : ∀ time candidate,
      QuittingFleschSuccessor reward (owner time) candidate →
        candidate = owner (time + 1))
    {current : Payoff ι}
    (hcurrent : current ∈
      quittingEssentialAPSGreatestFamily reward carrier (owner 0))
    (horizon : ℕ) :
    (∃ stop, stop < horizon ∧
      ∃ mass value,
        IsQuittingEssentialAPSFiniteRun reward
          (quittingEssentialAPSGreatestFamily reward carrier)
          owner current stop mass value ∧
        value stop ∈ quittingEssentialAPSTerminal reward (owner stop)) ∨
      ∃ mass value,
        IsQuittingEssentialAPSFiniteRun reward
          (quittingEssentialAPSGreatestFamily reward carrier)
          owner current horizon mass value := by
  exact exists_quittingEssentialAPSFiniteRun_or_terminal_of_unique_live
    reward carrier hcarrier owner hedge
      (fun time candidate hcandidate hne ↦
        (hne (hunique time candidate hcandidate)).elim)
      hcurrent horizon

end GameTheory
