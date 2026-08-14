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

/-- The raw finite-cell posterior is exactly `FinDist.condOn` probability when
the current information cell has positive prior mass. -/
theorem posterior_eq_probOf_condOn [DecidableEq Ω]
    (prior : FinDist Ω) (partition : InfoPartition Ω)
    (event : Finset Ω) (state : Ω)
    (hcell :
      ∃ other ∈ (partition.cell state : Set Ω), other ∈ prior.support) :
    posterior prior partition event state =
      (prior.condOn (partition.cell state : Set Ω) hcell).probOf
        (event : Set Ω) := by
  unfold posterior
  rw [FinDist.probOf_condOn_eq_inter hcell]
  rw [← Finset.coe_inter, FinDist.probOf_finset_eq_sum,
    FinDist.probOf_finset_eq_sum]

/-- Under full support, reflexivity supplies the positive-cell witness needed
by the conditioning bridge. -/
theorem posterior_eq_probOf_condOn_of_fullSupport [DecidableEq Ω]
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (partition : InfoPartition Ω) (event : Finset Ω) (state : Ω) :
    posterior prior partition event state =
      (prior.condOn (partition.cell state : Set Ω)
        ⟨state, partition.reflexive state, hfull state⟩).probOf
          (event : Set Ω) :=
  posterior_eq_probOf_condOn prior partition event state
    ⟨state, partition.reflexive state, hfull state⟩

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

/-- A self-evident event has posterior one at each of its states under a
full-support prior. -/
theorem posterior_eq_one_of_selfEvident [DecidableEq Ω]
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (partition : InfoPartition Ω) (event : Finset Ω)
    (state : Ω) (hstate : state ∈ event)
    (hself : IsSelfEvident partition event) :
    posterior prior partition event state = 1 := by
  unfold posterior
  rw [Finset.inter_eq_left.mpr (hself state hstate), div_self]
  exact ne_of_gt <|
    Finset.sum_pos
      (fun other _ => FinDist.prob_pos_iff.mpr (hfull other))
      ⟨state, partition.reflexive state⟩

/-- A cell outside a self-evident event has empty intersection with it. -/
theorem cell_inter_eq_empty_of_not_mem_selfEvident [DecidableEq Ω]
    (partition : InfoPartition Ω) (event : Finset Ω)
    (state : Ω) (hstate : state ∉ event)
    (hself : IsSelfEvident partition event) :
    partition.cell state ∩ event = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨other, hother⟩
  rw [Finset.mem_inter] at hother
  have hsubset := hself other hother.2
  rw [partition.coherent state other hother.1] at hsubset
  exact hstate (hsubset (partition.reflexive state))

/-- Outside a self-evident event, its posterior is zero. -/
theorem posterior_eq_zero_of_not_mem_selfEvident [DecidableEq Ω]
    (prior : FinDist Ω) (partition : InfoPartition Ω)
    (event : Finset Ω) (state : Ω) (hstate : state ∉ event)
    (hself : IsSelfEvident partition event) :
    posterior prior partition event state = 0 := by
  unfold posterior
  rw [cell_inter_eq_empty_of_not_mem_selfEvident
    partition event state hstate hself, Finset.sum_empty, zero_div]

end GameTheory.Epistemic
