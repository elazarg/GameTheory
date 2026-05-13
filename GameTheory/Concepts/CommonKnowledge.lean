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

/-! ### Mutual knowledge and common knowledge -/

/-- *Mutual knowledge*: every agent in the family knows `E`. -/
def mutualKnowledge {ι : Type} [Fintype ι] (P : ι → InfoPartition Ω)
    (E : Finset Ω) : Finset Ω :=
  Finset.univ.filter (fun s => ∀ i : ι, s ∈ Knows (P i) E)

@[simp]
theorem mem_mutualKnowledge_iff {ι : Type} [Fintype ι]
    (P : ι → InfoPartition Ω) (E : Finset Ω) (s : Ω) :
    s ∈ mutualKnowledge P E ↔ ∀ i, s ∈ Knows (P i) E := by
  simp [mutualKnowledge]

/-- Mutual knowledge implies truth (veridicality lifted to families). -/
theorem mutualKnowledge_subset {ι : Type} [Fintype ι]
    [Nonempty ι] (P : ι → InfoPartition Ω) (E : Finset Ω) :
    mutualKnowledge P E ⊆ E := by
  intro s hs
  rw [mem_mutualKnowledge_iff] at hs
  exact Knows_subset (P (Classical.arbitrary ι)) E (hs (Classical.arbitrary ι))

/-- An event `E` is *common knowledge* at state `s` (under the family `P`)
if there exists a "public event" `F`: a self-evident-for-everyone event
that contains `s` and is contained in `E`. This is Aumann's (1976) standard
characterization, which is equivalent to iterated mutual knowledge in the
finite setting. -/
def CommonKnowledgeAt {ι : Type} (P : ι → InfoPartition Ω) (E : Finset Ω)
    (s : Ω) : Prop :=
  ∃ F : Finset Ω, F ⊆ E ∧ s ∈ F ∧ ∀ i, IsSelfEvident (P i) F

/-- The set of states at which `E` is common knowledge. -/
noncomputable def CommonKnowledge {ι : Type} (P : ι → InfoPartition Ω)
    (E : Finset Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun s => CommonKnowledgeAt P E s)

omit [DecidableEq Ω] in
theorem mem_CommonKnowledge_iff {ι : Type} (P : ι → InfoPartition Ω)
    (E : Finset Ω) (s : Ω) :
    s ∈ CommonKnowledge P E ↔ CommonKnowledgeAt P E s := by
  classical
  simp [CommonKnowledge]

omit [DecidableEq Ω] in
/-- Common knowledge implies truth: if `E` is common knowledge at `s`, then
`s ∈ E`. -/
theorem CommonKnowledgeAt.implies_mem {ι : Type} {P : ι → InfoPartition Ω}
    {E : Finset Ω} {s : Ω} (h : CommonKnowledgeAt P E s) : s ∈ E := by
  obtain ⟨F, hFE, hsF, _⟩ := h
  exact hFE hsF

/-- Common knowledge implies mutual knowledge: if `E` is common knowledge,
then every agent knows `E`. -/
theorem CommonKnowledgeAt.implies_Knows {ι : Type} {P : ι → InfoPartition Ω}
    {E : Finset Ω} {s : Ω} (h : CommonKnowledgeAt P E s) (i : ι) :
    s ∈ Knows (P i) E := by
  obtain ⟨F, hFE, hsF, hse⟩ := h
  rw [mem_Knows_iff]
  exact ((hse i) s hsF).trans hFE

omit [DecidableEq Ω] in
/-- Common knowledge is itself common knowledge (positive introspection at
the group level): if `E` is CK at `s`, then "`E` is CK" is CK at `s`. The
witness is the same public event `F`. -/
theorem CommonKnowledgeAt.idem {ι : Type} {P : ι → InfoPartition Ω}
    {E : Finset Ω} {s : Ω} (h : CommonKnowledgeAt P E s) :
    CommonKnowledgeAt P (CommonKnowledge P E) s := by
  classical
  obtain ⟨F, hFE, hsF, hse⟩ := h
  refine ⟨F, ?_, hsF, hse⟩
  intro t htF
  rw [mem_CommonKnowledge_iff]
  exact ⟨F, hFE, htF, hse⟩

/-! ### Cell decomposition and Aumann's full agreement theorem

For a self-evident event `F`, the partition `P` decomposes `F` into
disjoint cells (the equivalence classes induced by `cell`). Summing any
function over `F` therefore equals the sum over the distinct cells of
sums-over-each-cell, which is the technical ingredient for Aumann's
full agreement: if two agents with the same prior have constant
posteriors on a common self-evident event `F`, those constants must
both equal the marginal conditional probability `P(E | F)` and hence
each other. -/

omit [DecidableEq Ω] in
/-- Cells of a partition are pairwise disjoint: if `cell s ≠ cell t`,
the two cells share no element. -/
theorem cells_disjoint (P : InfoPartition Ω) {s t : Ω}
    (hne : P.cell s ≠ P.cell t) :
    Disjoint (P.cell s) (P.cell t) := by
  rw [Finset.disjoint_left]
  intro x hxs hxt
  apply hne
  rw [← P.coherent s x hxs, P.coherent t x hxt]

/-- A self-evident event decomposes as the disjoint union of its
contained cells: every state in `F` lives in `cell s` for some `s ∈ F`,
and every such cell is fully contained in `F`. -/
theorem selfEvident_eq_biUnion_cells (P : InfoPartition Ω)
    {F : Finset Ω} (hF : IsSelfEvident P F) :
    F = (F.image P.cell).biUnion id := by
  ext t
  simp only [Finset.mem_biUnion, Finset.mem_image, id]
  refine ⟨fun htF => ?_, ?_⟩
  · refine ⟨P.cell t, ⟨t, htF, rfl⟩, P.reflexive t⟩
  · rintro ⟨C, ⟨s, hsF, rfl⟩, htC⟩
    exact hF s hsF htC

/-- Sum decomposition over the cells of a self-evident event:\ summing
any real-valued function over `F` equals the sum over distinct cells of
the sum over each cell. -/
theorem selfEvident_sum_decomp (P : InfoPartition Ω)
    {F : Finset Ω} (hF : IsSelfEvident P F) (f : Ω → ℝ) :
    ∑ t ∈ F, f t = ∑ C ∈ F.image P.cell, ∑ t ∈ C, f t := by
  -- Establish disjointness of distinct cells in `F.image P.cell`.
  have hdisj : (F.image P.cell : Set (Finset Ω)).PairwiseDisjoint id := by
    intro C₁ hC₁ C₂ hC₂ hne
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hC₁ hC₂
    obtain ⟨s₁, _, rfl⟩ := hC₁
    obtain ⟨s₂, _, rfl⟩ := hC₂
    exact cells_disjoint P (fun h => hne h)
  conv_lhs => rw [selfEvident_eq_biUnion_cells P hF]
  rw [Finset.sum_biUnion hdisj]
  rfl

/-- **Aumann (1976) full agreement, on a public self-evident event**:\
if two agents share the same prior, both have a self-evident event `F`,
and each agent's posterior of `E` is constant on `F`, then the two
constant posteriors are equal.

This is the operationally-useful form of Aumann's theorem: in a
common-knowledge situation about posteriors (which would force them to
be constant on the public event), agents cannot agree to disagree. -/
theorem aumann_full_agreement
    (μ : Ω → ℝ) (hμ_pos : ∀ s, μ s > 0)
    (P₁ P₂ : InfoPartition Ω) (E : Finset Ω) {F : Finset Ω}
    (hFne : F.Nonempty)
    (hF1 : IsSelfEvident P₁ F) (hF2 : IsSelfEvident P₂ F)
    {p₁ p₂ : ℝ}
    (hp1 : ∀ s ∈ F, posterior μ P₁ E s = p₁)
    (hp2 : ∀ s ∈ F, posterior μ P₂ E s = p₂) :
    p₁ = p₂ := by
  -- For each agent, show p_i = (∑_{F ∩ E} μ) / (∑_F μ).
  have hF_pos : 0 < ∑ t ∈ F, μ t :=
    Finset.sum_pos (fun t _ => hμ_pos t) hFne
  -- Per-cell: posterior = p_i implies the per-cell sum identity.
  have h_cell : ∀ {P : InfoPartition Ω} {p : ℝ}
      (hF : IsSelfEvident P F)
      (hp : ∀ s ∈ F, posterior μ P E s = p)
      {C : Finset Ω}, C ∈ F.image P.cell →
      ∑ t ∈ C ∩ E, μ t = p * ∑ t ∈ C, μ t := by
    intro P p hF hp C hC
    rw [Finset.mem_image] at hC
    obtain ⟨s, hsF, hCs⟩ := hC
    have hpost_s := hp s hsF
    -- posterior at s = (∑_{cell s ∩ E} μ) / (∑_{cell s} μ) = p
    -- So ∑_{cell s ∩ E} μ = p · ∑_{cell s} μ.
    have hcell_pos : 0 < ∑ t ∈ P.cell s, μ t :=
      Finset.sum_pos (fun t _ => hμ_pos t) ⟨s, P.reflexive s⟩
    have : (∑ t ∈ P.cell s ∩ E, μ t) / ∑ t ∈ P.cell s, μ t = p := hpost_s
    field_simp at this
    rw [← hCs]; linarith
  -- Sum over cells in F: ∑_{F ∩ E} μ = p_i · ∑_F μ for each i.
  have h_total : ∀ {P : InfoPartition Ω} {p : ℝ}
      (hF : IsSelfEvident P F)
      (hp : ∀ s ∈ F, posterior μ P E s = p),
      ∑ t ∈ F ∩ E, μ t = p * ∑ t ∈ F, μ t := by
    intro P p hF hp
    -- Decompose ∑_F μ via cells.
    rw [selfEvident_sum_decomp P hF μ, Finset.mul_sum]
    -- Decompose ∑_{F ∩ E} μ via cells.
    have hFE : F ∩ E = (F.image P.cell).biUnion (fun C => C ∩ E) := by
      conv_lhs => rw [selfEvident_eq_biUnion_cells P hF]
      rw [Finset.biUnion_inter]
      rfl
    rw [hFE]
    have hdisj : (F.image P.cell : Set (Finset Ω)).PairwiseDisjoint
        (fun C => C ∩ E) := by
      intro C₁ hC₁ C₂ hC₂ hne
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hC₁ hC₂
      obtain ⟨s₁, _, rfl⟩ := hC₁
      obtain ⟨s₂, _, rfl⟩ := hC₂
      exact (cells_disjoint P (fun h => hne h)).mono
        Finset.inter_subset_left Finset.inter_subset_left
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl (fun C hC => ?_)
    exact h_cell hF hp hC
  have h1 := h_total hF1 hp1
  have h2 := h_total hF2 hp2
  -- Both p_i · (∑ F μ) equal ∑_{F ∩ E} μ; divide.
  have : p₁ * ∑ t ∈ F, μ t = p₂ * ∑ t ∈ F, μ t := by
    rw [← h1, ← h2]
  exact mul_right_cancel₀ hF_pos.ne' this

end GameTheory

