/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCircuitProgress

/-!
# Total finite-path progress for essential APS

The first finite-path progress theorem assumes every displayed successor fiber
is nonempty.  That hypothesis is convenient for applying the convex-join
representation directly, but it is not logically necessary.

At a unique successor, an empty successor fiber collapses the full prefix to
the convex hull of a singleton.  Hence every greatest-family point at the
current owner is the viable solo endpoint and is terminal.  Combining this
empty-fiber case with the nonempty convex-fiber trichotomy yields a total local
recursion and removes all nonemptiness assumptions from the finite path and
active-face exclusion theorems.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- **Total local progress at a unique successor.**  No nonemptiness hypothesis
is needed: an empty successor fiber forces the current point to be terminal. -/
theorem
    quittingEssentialAPSGreatestFamily_terminal_or_successor_or_proper_of_unique_total
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ player, Convex ℝ (carrier player))
    {owner successor : ι}
    (hedge : QuittingFleschSuccessor reward owner successor)
    (hunique : ∀ candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate = successor)
    {current : Payoff ι}
    (hcurrent : current ∈
      quittingEssentialAPSGreatestFamily reward carrier owner) :
    current ∈ quittingEssentialAPSTerminal reward owner ∨
      current ∈ quittingEssentialAPSGreatestFamily reward carrier successor ∨
      current ∈ quittingProperEssentialAPSPrefix reward owner
        (quittingEssentialAPSGreatestFamily reward carrier successor) := by
  by_cases hnonempty :
      (quittingEssentialAPSGreatestFamily reward carrier successor).Nonempty
  · exact
      quittingEssentialAPSGreatestFamily_terminal_or_successor_or_proper_of_unique
        reward carrier hcarrier hedge hunique hnonempty hcurrent
  · have hfixedOwner := congrFun
      (quittingEssentialAPSGreatestFamily_fixed reward carrier) owner
    have hrestricted : current ∈
        quittingEssentialAPSRestrictedOperator reward carrier
          (quittingEssentialAPSGreatestFamily reward carrier) owner := by
      rw [hfixedOwner]
      exact hcurrent
    have hprefix := hrestricted.2
    change current ∈
      quittingEssentialAPSOwnerStep reward
        (quittingEssentialAPSGreatestFamily reward carrier) owner at hprefix
    rw [quittingEssentialAPSOwnerStep_eq_prefix] at hprefix
    rw [quittingEssentialAPSSuccessorSet_eq_of_unique reward
      (quittingEssentialAPSGreatestFamily reward carrier) hedge hunique] at hprefix
    have hsuccessorEmpty :
        quittingEssentialAPSGreatestFamily reward carrier successor = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hsuccessorEmpty] at hprefix
    left
    refine ⟨?_, hprefix.1⟩
    simpa using hprefix.2.1

/-- **Total finite zero-mass propagation dichotomy.**  Along a unique-successor
path, either terminal/proper progress occurs before `horizon`, or the same
payoff belongs to every greatest-family fiber through that horizon. -/
theorem
    quittingEssentialAPSGreatestFamily_path_progress_or_all_memberships_total
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
    (∃ time, time < horizon ∧
      QuittingEssentialAPSPathProgress reward
        (quittingEssentialAPSGreatestFamily reward carrier)
        owner current time) ∨
      ∀ time, time ≤ horizon →
        current ∈ quittingEssentialAPSGreatestFamily reward carrier
          (owner time) := by
  induction horizon with
  | zero =>
      right
      intro time htime
      have htimeZero : time = 0 := Nat.eq_zero_of_le_zero htime
      subst time
      exact hcurrent
  | succ horizon ih =>
      rcases ih with hprogress | hall
      · left
        rcases hprogress with ⟨time, htime, hprogress⟩
        exact ⟨time, htime.trans (Nat.lt_succ_self horizon), hprogress⟩
      · have hhere : current ∈
            quittingEssentialAPSGreatestFamily reward carrier
              (owner horizon) := hall horizon le_rfl
        rcases
            quittingEssentialAPSGreatestFamily_terminal_or_successor_or_proper_of_unique_total
              reward carrier hcarrier (hedge horizon) (hunique horizon)
              hhere with
          hterminal | hsuccessor | hproper
        · left
          exact ⟨horizon, Nat.lt_succ_self horizon, Or.inl hterminal⟩
        · right
          intro time htime
          by_cases hle : time ≤ horizon
          · exact hall time hle
          · have heq : time = horizon + 1 := by omega
            rw [heq]
            exact hsuccessor
        · left
          exact ⟨horizon, Nat.lt_succ_self horizon, Or.inr hproper⟩

/-- Total active-face form: failure of progress carries one unchanged payoff
through every active hyperplane in the finite window. -/
theorem quittingEssentialAPSGreatestFamily_path_progress_or_all_active_total
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
    (∃ time, time < horizon ∧
      QuittingEssentialAPSPathProgress reward
        (quittingEssentialAPSGreatestFamily reward carrier)
        owner current time) ∨
      IsQuittingEssentialAPSActiveAlong reward owner current horizon := by
  rcases
      quittingEssentialAPSGreatestFamily_path_progress_or_all_memberships_total
        reward carrier hcarrier owner hedge hunique hcurrent horizon with
    hprogress | hall
  · exact Or.inl hprogress
  · right
    intro time htime
    exact quittingEssentialAPSGreatestFamily_active reward carrier
      (owner time) (hall time htime)

/-- Total bounded-window progress from active-face exclusion. -/
theorem
    quittingEssentialAPSGreatestFamily_exists_path_progress_of_not_all_active_total
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
    (horizon : ℕ)
    (hnotAllActive :
      ¬ IsQuittingEssentialAPSActiveAlong reward owner current horizon) :
    ∃ time, time < horizon ∧
      QuittingEssentialAPSPathProgress reward
        (quittingEssentialAPSGreatestFamily reward carrier)
        owner current time := by
  rcases quittingEssentialAPSGreatestFamily_path_progress_or_all_active_total
      reward carrier hcarrier owner hedge hunique hcurrent horizon with
    hprogress | hall
  · exact hprogress
  · exact False.elim (hnotAllActive hall)

/-- Carrier-level face avoidance forces terminal or proper progress in the
finite window, with no successor-fiber nonemptiness assumptions. -/
theorem
    quittingEssentialAPSGreatestFamily_exists_path_progress_of_carrier_faceAvoidance_total
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ player, Convex ℝ (carrier player))
    (owner : ℕ → ι)
    (hedge : ∀ time,
      QuittingFleschSuccessor reward (owner time) (owner (time + 1)))
    (hunique : ∀ time candidate,
      QuittingFleschSuccessor reward (owner time) candidate →
        candidate = owner (time + 1))
    (horizon : ℕ)
    (hfaceAvoidance : ∀ value, value ∈ carrier (owner 0) →
      ¬ IsQuittingEssentialAPSActiveAlong reward owner value horizon)
    {current : Payoff ι}
    (hcurrent : current ∈
      quittingEssentialAPSGreatestFamily reward carrier (owner 0)) :
    ∃ time, time < horizon ∧
      QuittingEssentialAPSPathProgress reward
        (quittingEssentialAPSGreatestFamily reward carrier)
        owner current time := by
  have hwithin :=
    quittingEssentialAPSGreatestFamily_subinvariant reward carrier
      (owner 0) hcurrent
  exact
    quittingEssentialAPSGreatestFamily_exists_path_progress_of_not_all_active_total
      reward carrier hcarrier owner hedge hunique hcurrent horizon
      (hfaceAvoidance current hwithin.1)

end GameTheory
