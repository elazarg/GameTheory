import Math.Probability

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

open Math.Probability

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

/-! ### The knowledge operator

For a partition-based information structure, the *knowledge operator*
`Knows P E` returns the event "the agent knows `E`": the set of states at
which the agent's information cell is contained in `E`. The operator
satisfies the S5 axioms of partition-based knowledge: veridicality (T),
positive introspection (4), and negative introspection (5). -/

/-- The set of states at which an agent with partition `P` knows event `E`. -/
def Knows (P : InfoPartition Ω) (E : Finset Ω) : Finset Ω :=
  Finset.univ.filter (fun s => P.cell s ⊆ E)

@[simp]
theorem mem_Knows_iff (P : InfoPartition Ω) (E : Finset Ω) (s : Ω) :
    s ∈ Knows P E ↔ P.cell s ⊆ E := by
  simp [Knows]

/-- **Veridicality (Axiom T)**: knowing implies truth. -/
theorem Knows_subset (P : InfoPartition Ω) (E : Finset Ω) : Knows P E ⊆ E := by
  intro s hs
  rw [mem_Knows_iff] at hs
  exact hs (P.reflexive s)

/-- **Positive introspection (Axiom 4)**: knowing implies knowing that you
know. The fixed-point form `Knows (Knows P E) = Knows P E` follows since
the converse direction is just veridicality applied to `Knows P E`. -/
theorem Knows_idem (P : InfoPartition Ω) (E : Finset Ω) :
    Knows P (Knows P E) = Knows P E := by
  apply Finset.Subset.antisymm
  · exact Knows_subset P (Knows P E)
  · intro s hs
    rw [mem_Knows_iff] at hs ⊢
    intro t ht
    rw [mem_Knows_iff, P.coherent s t ht]
    exact hs

/-- **Negative introspection (Axiom 5)**: not knowing implies knowing that
you don't know. Stated as: the complement of `Knows P E` is itself known
at every point of that complement. -/
theorem Knows_not_Knows (P : InfoPartition Ω) (E : Finset Ω) :
    (Finset.univ \ Knows P E) ⊆ Knows P (Finset.univ \ Knows P E) := by
  intro s hs
  rw [mem_Knows_iff]
  rw [Finset.mem_sdiff, mem_Knows_iff] at hs
  intro t ht
  rw [Finset.mem_sdiff, mem_Knows_iff]
  refine ⟨Finset.mem_univ t, ?_⟩
  rw [P.coherent s t ht]
  exact hs.2

/-- Knowledge is *monotone*: knowing a larger event follows from knowing a
smaller one. -/
theorem Knows_mono (P : InfoPartition Ω) {E F : Finset Ω} (hEF : E ⊆ F) :
    Knows P E ⊆ Knows P F := by
  intro s hs
  rw [mem_Knows_iff] at hs ⊢
  exact hs.trans hEF

/-- Knowledge distributes over intersection (the *conjunction axiom*). -/
theorem Knows_inter (P : InfoPartition Ω) (E F : Finset Ω) :
    Knows P (E ∩ F) = Knows P E ∩ Knows P F := by
  ext s
  simp only [Finset.mem_inter, mem_Knows_iff, Finset.subset_inter_iff]

/-- An event is self-evident iff it equals "the event is known". -/
theorem isSelfEvident_iff_subset_Knows (P : InfoPartition Ω) (E : Finset Ω) :
    IsSelfEvident P E ↔ E ⊆ Knows P E := by
  constructor
  · intro hse s hs
    rw [mem_Knows_iff]
    exact hse s hs
  · intro h s hs
    have := h hs
    rw [mem_Knows_iff] at this
    exact this

/-- Self-evident events are exactly the fixed points of the knowledge
operator: `IsSelfEvident P E ↔ Knows P E = E`. -/
theorem isSelfEvident_iff_Knows_eq (P : InfoPartition Ω) (E : Finset Ω) :
    IsSelfEvident P E ↔ Knows P E = E := by
  rw [isSelfEvident_iff_subset_Knows]
  exact ⟨fun h => Finset.Subset.antisymm (Knows_subset P E) h,
    fun h => h.ge⟩

end GameTheory

