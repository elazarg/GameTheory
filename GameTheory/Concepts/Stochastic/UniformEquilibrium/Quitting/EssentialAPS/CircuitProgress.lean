/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.EssentialAPS.ConvexFixedPoint

/-!
# Finite-path progress from essential APS

The convex fixed-point layer reduces a unique-successor APS step to three
possibilities: terminal absorption, zero-mass propagation into the successor
fiber, or a proper segment with mass in `(0,1)`.

This file iterates that local trichotomy over a finite successor path.  If no
terminal or proper step occurs in the first `horizon` edges, the same payoff
belongs to every greatest-family fiber visited by the path and therefore lies
on every corresponding active hyperplane.  Consequently, excluding the
common active face on the carrier forces progress in a bounded window.

This is the finite combinatorial core of the simple-circuit argument: a chain
of zero-mass APS edges can persist only by carrying one payoff unchanged
through all active faces on the circuit.  Compactness is still needed to turn
pointwise bounded-window progress into a uniform positive lower bound on the
sum of masses, but the zero-mass obstruction itself is now eliminated by an
exact theorem rather than an informal argument.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- Terminal absorption or a proper positive-mass segment at one edge of an
owner path. -/
def QuittingEssentialAPSPathProgress
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (owner : ℕ → ι) (current : Payoff ι) (time : ℕ) : Prop :=
  current ∈ quittingEssentialAPSTerminal reward (owner time) ∨
    current ∈ quittingProperEssentialAPSPrefix reward (owner time)
      (family (owner (time + 1)))

/-- A payoff lies on every active hyperplane visited through `horizon`. -/
def IsQuittingEssentialAPSActiveAlong
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (current : Payoff ι) (horizon : ℕ) : Prop :=
  ∀ time, time ≤ horizon →
    current (owner time) =
      quittingSoloReward reward (owner time) (owner time)

/-- Every point of the carrier-restricted greatest family lies on the active
hyperplane of its owner. -/
theorem quittingEssentialAPSGreatestFamily_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι)) (owner : ι)
    {current : Payoff ι}
    (hcurrent : current ∈
      quittingEssentialAPSGreatestFamily reward carrier owner) :
    current owner = quittingSoloReward reward owner owner := by
  have hfixedOwner := congrFun
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
  exact hprefix.2.2

/-- At a unique successor, the greatest fixed-point equation is an exact
one-fiber recursion. -/
theorem quittingEssentialAPSGreatestFamily_eq_carrier_inter_prefix_of_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι)) {owner successor : ι}
    (hedge : QuittingFleschSuccessor reward owner successor)
    (hunique : ∀ candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate = successor) :
    quittingEssentialAPSGreatestFamily reward carrier owner =
      carrier owner ∩
        quittingEssentialAPSPrefix reward owner
          (quittingEssentialAPSGreatestFamily reward carrier successor) := by
  calc
    quittingEssentialAPSGreatestFamily reward carrier owner =
        quittingEssentialAPSRestrictedOperator reward carrier
          (quittingEssentialAPSGreatestFamily reward carrier) owner :=
      (congrFun
        (quittingEssentialAPSGreatestFamily_fixed reward carrier) owner).symm
    _ = carrier owner ∩
        quittingEssentialAPSOwnerStep reward
          (quittingEssentialAPSGreatestFamily reward carrier) owner := rfl
    _ = carrier owner ∩
        quittingEssentialAPSPrefix reward owner
          (quittingEssentialAPSSuccessorSet reward
            (quittingEssentialAPSGreatestFamily reward carrier) owner) := by
      rw [quittingEssentialAPSOwnerStep_eq_prefix]
    _ = carrier owner ∩
        quittingEssentialAPSPrefix reward owner
          (quittingEssentialAPSGreatestFamily reward carrier successor) := by
      rw [quittingEssentialAPSSuccessorSet_eq_of_unique reward
        (quittingEssentialAPSGreatestFamily reward carrier) hedge hunique]

/-- **Finite zero-mass propagation dichotomy.**  Along a path on which every
owner has the displayed unique successor and every successor fiber is
nonempty, either terminal/proper progress occurs before `horizon`, or the same
payoff belongs to every greatest-family fiber up to that horizon. -/
theorem
    quittingEssentialAPSGreatestFamily_path_progress_or_all_memberships
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ player, Convex ℝ (carrier player))
    (owner : ℕ → ι)
    (hedge : ∀ time,
      QuittingFleschSuccessor reward (owner time) (owner (time + 1)))
    (hunique : ∀ time candidate,
      QuittingFleschSuccessor reward (owner time) candidate →
        candidate = owner (time + 1))
    (hnonempty : ∀ time,
      (quittingEssentialAPSGreatestFamily reward carrier
        (owner (time + 1))).Nonempty)
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
            quittingEssentialAPSGreatestFamily_terminal_or_successor_or_proper_of_unique
              reward carrier hcarrier (hedge horizon) (hunique horizon)
              (hnonempty horizon) hhere with
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

/-- If no progress occurs on a finite unique-successor path, the unchanged
payoff lies on every active hyperplane encountered by the path. -/
theorem quittingEssentialAPSGreatestFamily_path_progress_or_all_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ player, Convex ℝ (carrier player))
    (owner : ℕ → ι)
    (hedge : ∀ time,
      QuittingFleschSuccessor reward (owner time) (owner (time + 1)))
    (hunique : ∀ time candidate,
      QuittingFleschSuccessor reward (owner time) candidate →
        candidate = owner (time + 1))
    (hnonempty : ∀ time,
      (quittingEssentialAPSGreatestFamily reward carrier
        (owner (time + 1))).Nonempty)
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
      quittingEssentialAPSGreatestFamily_path_progress_or_all_memberships
        reward carrier hcarrier owner hedge hunique hnonempty
        hcurrent horizon with
    hprogress | hall
  · exact Or.inl hprogress
  · right
    intro time htime
    exact quittingEssentialAPSGreatestFamily_active reward carrier
      (owner time) (hall time htime)

/-- **Bounded-window progress from active-face exclusion.**  If the selected
payoff is not simultaneously active for all owners in the finite window, some
edge in that window is terminal or carries strictly positive absorption mass. -/
theorem quittingEssentialAPSGreatestFamily_exists_path_progress_of_not_all_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ player, Convex ℝ (carrier player))
    (owner : ℕ → ι)
    (hedge : ∀ time,
      QuittingFleschSuccessor reward (owner time) (owner (time + 1)))
    (hunique : ∀ time candidate,
      QuittingFleschSuccessor reward (owner time) candidate →
        candidate = owner (time + 1))
    (hnonempty : ∀ time,
      (quittingEssentialAPSGreatestFamily reward carrier
        (owner (time + 1))).Nonempty)
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
  rcases quittingEssentialAPSGreatestFamily_path_progress_or_all_active
      reward carrier hcarrier owner hedge hunique hnonempty
      hcurrent horizon with hprogress | hall
  · exact hprogress
  · exact False.elim (hnotAllActive hall)

/-- Carrier-level form matching a simple-circuit exclusion hypothesis: if no
point of the initial carrier fiber lies on every active face in the window,
every greatest-family point makes terminal or proper progress in that window. -/
theorem
    quittingEssentialAPSGreatestFamily_exists_path_progress_of_carrier_faceAvoidance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ player, Convex ℝ (carrier player))
    (owner : ℕ → ι)
    (hedge : ∀ time,
      QuittingFleschSuccessor reward (owner time) (owner (time + 1)))
    (hunique : ∀ time candidate,
      QuittingFleschSuccessor reward (owner time) candidate →
        candidate = owner (time + 1))
    (hnonempty : ∀ time,
      (quittingEssentialAPSGreatestFamily reward carrier
        (owner (time + 1))).Nonempty)
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
    quittingEssentialAPSGreatestFamily_exists_path_progress_of_not_all_active
      reward carrier hcarrier owner hedge hunique hnonempty
      hcurrent horizon (hfaceAvoidance current hwithin.1)

end GameTheory
