/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.EssentialAPS.FiniteRun
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.EssentialAPS.PathContraction

/-!
# Constructing coherent infinite essential-APS runs

The finite-run theorem constructs a run for every requested horizon, but those
runs need not be definitionally compatible as the horizon varies.  When no
point of the visited greatest-family fibers is terminal, the total local
trichotomy supplies a continuation at every stage.  Classical dependent choice
therefore produces one coherent infinite sequence of values and masses.

The resulting run stays inside the greatest APS family, uses masses in
`[0,1)`, and satisfies the exact singleton-arc equation at every stage.  It is
therefore the path object consumed by the opponent-contraction theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- One chosen executable continuation edge at a specified time. -/
structure QuittingEssentialAPSContinuationStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (owner : ℕ → ι) (time : ℕ) (current : Payoff ι) where
  mass : ℝ
  next : Payoff ι
  mass_mem : mass ∈ Set.Ico (0 : ℝ) 1
  next_mem : next ∈ family (owner (time + 1))
  arc : current = quittingSingletonArcPayoff mass
    (quittingSoloReward reward (owner time)) next

/-- An infinite executable APS run. -/
def IsQuittingEssentialAPSInfiniteRun
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (owner : ℕ → ι) (initial : Payoff ι)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι) : Prop :=
  value 0 = initial ∧
    (∀ time, value time ∈ family (owner time)) ∧
      ∀ time,
        mass time ∈ Set.Ico (0 : ℝ) 1 ∧
          value time = quittingSingletonArcPayoff (mass time)
            (quittingSoloReward reward (owner time))
            (value (time + 1))

/-- A nonterminal greatest-family point has an executable continuation at a
unique live successor.  The zero-mass successor case is retained as an exact
edge; the proper case contributes its positive mass witness. -/
theorem
    nonempty_quittingEssentialAPSContinuationStep_of_unique_live_of_not_terminal
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
    (time : ℕ) (current : Payoff ι)
    (hcurrent : current ∈
      quittingEssentialAPSGreatestFamily reward carrier (owner time))
    (hnotTerminal : current ∉
      quittingEssentialAPSTerminal reward (owner time)) :
    Nonempty (QuittingEssentialAPSContinuationStep reward
      (quittingEssentialAPSGreatestFamily reward carrier)
      owner time current) := by
  rcases
      quittingEssentialAPSGreatestFamily_terminal_or_successor_or_proper_of_unique_live_total
        reward carrier hcarrier (hedge time) (huniqueLive time) hcurrent with
    hterminal | hsuccessor | hproper
  · exact False.elim (hnotTerminal hterminal)
  · refine ⟨{
      mass := 0
      next := current
      mass_mem := ⟨le_rfl, zero_lt_one⟩
      next_mem := hsuccessor
      arc := ?_ }⟩
    funext who
    simp [quittingSingletonArcPayoff]
  · rcases hproper with
      ⟨_hviable, p, hp, next, hnext, harc, _hactive⟩
    exact ⟨{
      mass := p
      next := next
      mass_mem := ⟨hp.1.le, hp.2⟩
      next_mem := hnext
      arc := harc }⟩

/-- **Coherent infinite APS run under terminal-freeness.**  If every visited
greatest-family point is nonterminal, local unique-live progress can be chosen
recursively forever. -/
theorem exists_quittingEssentialAPSInfiniteRun_of_unique_live_of_terminalFree
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
    (hterminalFree : ∀ time current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier
        (owner time) →
      current ∉ quittingEssentialAPSTerminal reward (owner time))
    {initial : Payoff ι}
    (hinitial : initial ∈
      quittingEssentialAPSGreatestFamily reward carrier (owner 0)) :
    ∃ mass value,
      IsQuittingEssentialAPSInfiniteRun reward
        (quittingEssentialAPSGreatestFamily reward carrier)
        owner initial mass value := by
  classical
  let State : ℕ → Type := fun time ↦
    {current : Payoff ι // current ∈
      quittingEssentialAPSGreatestFamily reward carrier (owner time)}
  have hstep : ∀ time (current : State time),
      Nonempty (QuittingEssentialAPSContinuationStep reward
        (quittingEssentialAPSGreatestFamily reward carrier)
        owner time current.1) := by
    intro time current
    exact
      nonempty_quittingEssentialAPSContinuationStep_of_unique_live_of_not_terminal
        reward carrier hcarrier owner hedge huniqueLive time current.1
          current.2 (hterminalFree time current.1 current.2)
  let chooseStep : ∀ time (current : State time),
      QuittingEssentialAPSContinuationStep reward
        (quittingEssentialAPSGreatestFamily reward carrier)
        owner time current.1 :=
    fun time current ↦ Classical.choice (hstep time current)
  let state : ∀ time, State time := fun time ↦
    Nat.rec (motive := fun time ↦ State time)
      ⟨initial, hinitial⟩
      (fun time current ↦
        ⟨(chooseStep time current).next,
          (chooseStep time current).next_mem⟩)
      time
  let mass : ℕ → ℝ := fun time ↦ (chooseStep time (state time)).mass
  let value : ℕ → Payoff ι := fun time ↦ (state time).1
  refine ⟨mass, value, ?_, ?_, ?_⟩
  · rfl
  · intro time
    exact (state time).2
  · intro time
    constructor
    · exact (chooseStep time (state time)).mass_mem
    · change (state time).1 =
        quittingSingletonArcPayoff (chooseStep time (state time)).mass
          (quittingSoloReward reward (owner time)) (state (time + 1)).1
      have hnext : state (time + 1) =
          ⟨(chooseStep time (state time)).next,
            (chooseStep time (state time)).next_mem⟩ := rfl
      rw [hnext]
      exact (chooseStep time (state time)).arc

/-- Infinite greatest-family runs are active at every visited owner. -/
theorem IsQuittingEssentialAPSInfiniteRun.active_of_greatest
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {carrier : ι → Set (Payoff ι)}
    {owner : ℕ → ι} {initial : Payoff ι}
    {mass : ℕ → ℝ} {value : ℕ → Payoff ι}
    (hrun : IsQuittingEssentialAPSInfiniteRun reward
      (quittingEssentialAPSGreatestFamily reward carrier)
      owner initial mass value)
    (time : ℕ) :
    value time (owner time) =
      quittingSoloReward reward (owner time) (owner time) :=
  quittingEssentialAPSGreatestFamily_active reward carrier
    (owner time) (hrun.2.1 time)

end GameTheory
