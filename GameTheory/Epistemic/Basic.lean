/-
# Finite epistemic partitions

The epistemic branch models knowledge directly on a state space. It deliberately
does not reuse Protocol information states: those are history-local and need
not partition execution states.
-/

import GameTheory.Probability.FinDist

noncomputable section

namespace GameTheory.Epistemic

open GameTheory.Probability

universe uΩ

variable {Ω : Type uΩ}

/-- A finite-cell information partition. The state carrier itself need not
carry a stored finiteness capability. -/
structure InfoPartition (Ω : Type uΩ) where
  /-- The states considered possible at the current state. -/
  cell : Ω → Finset Ω
  /-- Truth lies in its own information cell. -/
  reflexive : ∀ state, state ∈ cell state
  /-- Membership in a cell determines that same cell. -/
  coherent :
    ∀ state other, other ∈ cell state → cell other = cell state

/-- Posterior probability of a finite event conditional on the current cell. -/
def posterior [DecidableEq Ω] (prior : FinDist Ω)
    (partition : InfoPartition Ω) (event : Finset Ω) (state : Ω) : ℝ :=
  (∑ other ∈ partition.cell state ∩ event, prior.prob other) /
    ∑ other ∈ partition.cell state, prior.prob other

/-- States in one cell have the same posterior. -/
theorem posterior_eq_of_mem_cell [DecidableEq Ω] (prior : FinDist Ω)
    (partition : InfoPartition Ω) (event : Finset Ω)
    (state other : Ω) (hother : other ∈ partition.cell state) :
    posterior prior partition event state =
      posterior prior partition event other := by
  simp only [posterior, partition.coherent state other hother]

/-- An event is self-evident when every cell meeting it is contained in it. -/
def IsSelfEvident (partition : InfoPartition Ω) (event : Finset Ω) : Prop :=
  ∀ state ∈ event, partition.cell state ⊆ event

end GameTheory.Epistemic
