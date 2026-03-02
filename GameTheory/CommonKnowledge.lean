import GameTheory.Probability

/-!
# Common Knowledge and Agreeing to Disagree

Formalizes information partitions and the "Agreeing to Disagree"
theorem (Aumann, 1976): agents sharing the same information partition
cell and prior must agree on posteriors.

## Main definitions

* `InfoPartition` — an agent's information partition over a state space
* `posterior` — posterior probability of an event given a partition cell
* `IsSelfEvident` — an event that is known whenever true

## Main results

* `posterior_eq_of_same_cell` — same cell implies same posterior
* `agree_to_disagree` — same cell and prior implies same posteriors
* `posterior_self_evident` — self-evident events have posterior 1
-/

namespace GameTheory

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- An information partition: for each state, the set of states the agent
    considers possible. -/
structure InfoPartition (Ω : Type) [Fintype Ω] where
  /-- The cell of states considered possible at state `s`. -/
  cell : Ω → Finset Ω
  /-- The true state is in its own cell. -/
  reflexive : ∀ s, s ∈ cell s
  /-- If `t` is in `s`'s cell, their cells coincide (partition property). -/
  coherent : ∀ s t, t ∈ cell s → cell t = cell s

/-- Posterior probability of event `E` given the partition cell at `s`. -/
noncomputable def posterior (μ : Ω → ℝ) (P : InfoPartition Ω) (E : Finset Ω)
    (s : Ω) : ℝ :=
  (∑ t ∈ P.cell s ∩ E, μ t) / ∑ t ∈ P.cell s, μ t

/-- If `t` is in the cell of `s`, they have the same posterior. -/
theorem posterior_eq_of_same_cell (μ : Ω → ℝ) (P : InfoPartition Ω)
    (E : Finset Ω) (s t : Ω) (ht : t ∈ P.cell s) :
    posterior μ P E s = posterior μ P E t := by
  simp only [posterior, P.coherent s t ht]

/-- **Agreeing to Disagree**: agents with the same cell and prior agree
    on the posterior for any event. -/
theorem agree_to_disagree (μ : Ω → ℝ) (P₁ P₂ : InfoPartition Ω)
    (E : Finset Ω) (s : Ω) (hcell : P₁.cell s = P₂.cell s) :
    posterior μ P₁ E s = posterior μ P₂ E s := by
  simp only [posterior, hcell]

/-- An event is self-evident for an agent if being at any state in the event
    implies all states the agent considers possible are in the event. -/
def IsSelfEvident (P : InfoPartition Ω) (E : Finset Ω) : Prop :=
  ∀ s ∈ E, P.cell s ⊆ E

/-- Self-evident events have posterior 1 (given positive prior). -/
theorem posterior_self_evident (μ : Ω → ℝ) (hμ : ∀ s, μ s > 0)
    (P : InfoPartition Ω) (E : Finset Ω) (s : Ω) (hs : s ∈ E)
    (hse : IsSelfEvident P E) :
    posterior μ P E s = 1 := by
  unfold posterior
  rw [Finset.inter_eq_left.mpr (hse s hs), div_self]
  exact ne_of_gt (Finset.sum_pos (fun t _ => hμ t) ⟨s, P.reflexive s⟩)

/-- At states outside a self-evident event, the cell has no overlap
    with the event (given the partition property). -/
theorem cell_disjoint_of_not_in_self_evident
    (P : InfoPartition Ω) (E : Finset Ω) (s : Ω) (hs : s ∉ E)
    (hse : IsSelfEvident P E) :
    P.cell s ∩ E = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  intro ⟨t, ht⟩
  rw [Finset.mem_inter] at ht
  have hsub := hse t ht.2
  rw [P.coherent s t ht.1] at hsub
  exact hs (hsub (P.reflexive s))

/-- Outside a self-evident event, the posterior is 0. -/
theorem posterior_zero_outside_self_evident (μ : Ω → ℝ) (_hμ : ∀ s, μ s > 0)
    (P : InfoPartition Ω) (E : Finset Ω) (s : Ω) (hs : s ∉ E)
    (hse : IsSelfEvident P E) :
    posterior μ P E s = 0 := by
  unfold posterior
  rw [cell_disjoint_of_not_in_self_evident P E s hs hse, Finset.sum_empty, zero_div]

end GameTheory
