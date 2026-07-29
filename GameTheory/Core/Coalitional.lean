/-
# Coalitional games and the core

A coalitional game says what each group can guarantee itself and says nothing
about how. There are no strategies, no play, and no outcome carrier, so this is
deliberately *not* a `GameForm`: forcing it into one would require inventing a
strategy space nobody uses and an outcome nobody observes.

What is shared is the vocabulary of groups. A coalition is a `Finset Agent`
here for the same reason it is one in a strong equilibrium's deviation, and the
core's condition has the same shape as that deviation's — a group objects when
it can do better by itself.

The two theorems below are a possibility and an impossibility. Core allocations
are individually rational, which follows from the definition with nothing
assumed; and the three-player majority game has no core allocation at all,
which is why cooperative solution concepts other than the core exist.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace GameTheory

universe ua

/-- What each coalition can guarantee itself, with the empty coalition
guaranteeing nothing. -/
structure CoalitionalGame (Agent : Type ua) where
  /-- The worth of a coalition. -/
  value : Finset Agent → ℝ
  /-- Nobody together achieves nothing. -/
  value_empty : value ∅ = 0

/-- A division of the proceeds among the agents. -/
abbrev Allocation (Agent : Type ua) := Agent → ℝ

variable {Agent : Type ua} [Fintype Agent] [DecidableEq Agent]

/-- What a coalition collects under an allocation. -/
def payout (allocation : Allocation Agent) (coalition : Finset Agent) : ℝ :=
  ∑ member ∈ coalition, allocation member

variable (G : CoalitionalGame Agent) in
/-- An allocation is in the core when it divides exactly what everyone together
is worth and no coalition can beat its share by walking away. -/
def IsInCore (allocation : Allocation Agent) : Prop :=
  payout allocation Finset.univ = G.value Finset.univ ∧
    ∀ coalition : Finset Agent, G.value coalition ≤ payout allocation coalition

omit [DecidableEq Agent] in
/-- **A core allocation is individually rational.** Each agent gets at least
what they are worth alone, because a lone agent is a coalition. -/
theorem IsInCore.individually_rational {G : CoalitionalGame Agent}
    {allocation : Allocation Agent} (hcore : IsInCore G allocation) (agent : Agent) :
    G.value {agent} ≤ allocation agent := by
  simpa [payout] using hcore.2 {agent}

/-! ## A game with no core

Three agents, and any two of them can take everything. Every pair objects to
being given less than the whole, and there is not enough to satisfy all three
pairs at once. -/

/-- Any majority of three takes the whole prize. -/
def majorityGame : CoalitionalGame (Fin 3) where
  value coalition := if 2 ≤ coalition.card then 1 else 0
  value_empty := by norm_num

/-- **The three-player majority game has an empty core.** Each of the three
pairs must receive the whole prize, which costs twice what there is to give. -/
theorem majorityGame_core_empty (allocation : Allocation (Fin 3)) :
    ¬ IsInCore majorityGame allocation := by
  rintro ⟨htotal, hobject⟩
  have hpair : ∀ pair : Finset (Fin 3), pair.card = 2 → 1 ≤ payout allocation pair := by
    intro pair hcard
    simpa [majorityGame, hcard] using hobject pair
  have h01 := hpair {0, 1} (by decide)
  have h02 := hpair {0, 2} (by decide)
  have h12 := hpair {1, 2} (by decide)
  rw [show payout allocation {0, 1} = allocation 0 + allocation 1 from
      Finset.sum_pair (by decide)] at h01
  rw [show payout allocation {0, 2} = allocation 0 + allocation 2 from
      Finset.sum_pair (by decide)] at h02
  rw [show payout allocation {1, 2} = allocation 1 + allocation 2 from
      Finset.sum_pair (by decide)] at h12
  rw [show payout allocation Finset.univ = allocation 0 + allocation 1 + allocation 2 from
      Fin.sum_univ_three allocation,
    show majorityGame.value Finset.univ = 1 from by norm_num [majorityGame]] at htotal
  linarith

end GameTheory
