/-
# Approximate common knowledge

Finite Monderer--Samet `p`-belief operators over the canonical finite prior.
The quantitative approximate-agreement bound is developed separately from this
operator and exact-bridge layer.

Primary reference: D. Monderer and D. Samet, “Approximating Common Knowledge
with Common Beliefs,” *Games and Economic Behavior* 1 (1989).
-/

import GameTheory.Epistemic.Knowledge

noncomputable section

namespace GameTheory.Epistemic

open GameTheory.Probability

universe uι uΩ

variable {Ω : Type uΩ} [Fintype Ω] [DecidableEq Ω]

/-- The event where the current posterior of `event` is at least `threshold`. -/
def PBelief (prior : FinDist Ω) (partition : InfoPartition Ω)
    (threshold : ℝ) (event : Finset Ω) : Finset Ω :=
  Finset.univ.filter fun state =>
    posterior prior partition event state ≥ threshold

@[simp]
theorem mem_PBelief_iff (prior : FinDist Ω)
    (partition : InfoPartition Ω) (threshold : ℝ)
    (event : Finset Ω) (state : Ω) :
    state ∈ PBelief prior partition threshold event ↔
      posterior prior partition event state ≥ threshold := by
  simp [PBelief]

/-- Lowering the threshold enlarges a `p`-belief event. -/
theorem PBelief_mono_threshold (prior : FinDist Ω)
    (partition : InfoPartition Ω) {lower upper : ℝ}
    (hthreshold : lower ≤ upper) (event : Finset Ω) :
    PBelief prior partition upper event ⊆
      PBelief prior partition lower event := by
  intro state hstate
  rw [mem_PBelief_iff] at hstate ⊢
  exact le_trans hthreshold hstate

/-- Mutual `p`-belief: every agent assigns probability at least `threshold`
to the event. -/
def mutualPBelief {ι : Type uι} [Fintype ι]
    (prior : FinDist Ω) (partition : ι → InfoPartition Ω)
    (threshold : ℝ) (event : Finset Ω) : Finset Ω :=
  Finset.univ.filter fun state =>
    ∀ agent : ι,
      state ∈ PBelief prior (partition agent) threshold event

@[simp]
theorem mem_mutualPBelief_iff {ι : Type uι} [Fintype ι]
    (prior : FinDist Ω) (partition : ι → InfoPartition Ω)
    (threshold : ℝ) (event : Finset Ω) (state : Ω) :
    state ∈ mutualPBelief prior partition threshold event ↔
      ∀ agent : ι,
        posterior prior (partition agent) event state ≥ threshold := by
  simp [mutualPBelief]

/-- Lowering the threshold enlarges mutual `p`-belief. -/
theorem mutualPBelief_mono_threshold {ι : Type uι} [Fintype ι]
    (prior : FinDist Ω) (partition : ι → InfoPartition Ω)
    {lower upper : ℝ} (hthreshold : lower ≤ upper)
    (event : Finset Ω) :
    mutualPBelief prior partition upper event ⊆
      mutualPBelief prior partition lower event := by
  intro state hstate
  rw [mem_mutualPBelief_iff] at hstate ⊢
  intro agent
  exact le_trans hthreshold (hstate agent)

/-- A `p`-evident event: whenever it occurs, every agent assigns probability
at least `threshold` to it. -/
def IsPEvident {ι : Type uι} [Fintype ι]
    (prior : FinDist Ω) (partition : ι → InfoPartition Ω)
    (threshold : ℝ) (event : Finset Ω) : Prop :=
  ∀ agent : ι,
    event ⊆ PBelief prior (partition agent) threshold event

/-- Lowering the threshold preserves `p`-evidence. -/
theorem IsPEvident.mono_threshold {ι : Type uι} [Fintype ι]
    {prior : FinDist Ω} {partition : ι → InfoPartition Ω}
    {lower upper : ℝ} (hthreshold : lower ≤ upper)
    {event : Finset Ω}
    (hself : IsPEvident prior partition upper event) :
    IsPEvident prior partition lower event := by
  intro agent state hstate
  exact PBelief_mono_threshold prior (partition agent) hthreshold event
    (hself agent hstate)

/-- Common `p`-belief at a state, in finite witness form. -/
def CommonPBeliefAt {ι : Type uι} [Fintype ι]
    (prior : FinDist Ω) (partition : ι → InfoPartition Ω)
    (threshold : ℝ) (event : Finset Ω) (state : Ω) : Prop :=
  ∃ witness : Finset Ω,
    state ∈ witness ∧
      IsPEvident prior partition threshold witness ∧
        witness ⊆ mutualPBelief prior partition threshold event

/-- States at which `event` is common `p`-belief. -/
def CommonPBelief {ι : Type uι} [Fintype ι]
    (prior : FinDist Ω) (partition : ι → InfoPartition Ω)
    (threshold : ℝ) (event : Finset Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter fun state =>
    CommonPBeliefAt prior partition threshold event state

theorem mem_CommonPBelief_iff {ι : Type uι} [Fintype ι]
    (prior : FinDist Ω) (partition : ι → InfoPartition Ω)
    (threshold : ℝ) (event : Finset Ω) (state : Ω) :
    state ∈ CommonPBelief prior partition threshold event ↔
      CommonPBeliefAt prior partition threshold event state := by
  classical
  simp [CommonPBelief]

/-- Common `p`-belief implies mutual `p`-belief at the current state. -/
theorem CommonPBeliefAt.implies_mutualPBelief
    {ι : Type uι} [Fintype ι]
    {prior : FinDist Ω} {partition : ι → InfoPartition Ω}
    {threshold : ℝ} {event : Finset Ω} {state : Ω}
    (h : CommonPBeliefAt prior partition threshold event state) :
    state ∈ mutualPBelief prior partition threshold event := by
  obtain ⟨witness, hstate, _, hbelief⟩ := h
  exact hbelief hstate

/-- Lowering the threshold preserves common `p`-belief. -/
theorem CommonPBeliefAt.mono_threshold
    {ι : Type uι} [Fintype ι]
    {prior : FinDist Ω} {partition : ι → InfoPartition Ω}
    {lower upper : ℝ} (hthreshold : lower ≤ upper)
    {event : Finset Ω} {state : Ω}
    (h : CommonPBeliefAt prior partition upper event state) :
    CommonPBeliefAt prior partition lower event state := by
  obtain ⟨witness, hstate, hevident, hbelief⟩ := h
  refine ⟨witness, hstate, hevident.mono_threshold hthreshold, ?_⟩
  exact hbelief.trans <|
    mutualPBelief_mono_threshold prior partition hthreshold event

/-! ## Exact-to-approximate bridges -/

omit [Fintype Ω] in
/-- A cell contained in an event assigns it posterior one under full support. -/
theorem posterior_eq_one_of_cell_subset
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (partition : InfoPartition Ω) {event : Finset Ω} {state : Ω}
    (hcell : partition.cell state ⊆ event) :
    posterior prior partition event state = 1 := by
  unfold posterior
  rw [Finset.inter_eq_left.mpr hcell, div_self]
  exact ne_of_gt <|
    Finset.sum_pos
      (fun other _ => FinDist.prob_pos_iff.mpr (hfull other))
      ⟨state, partition.reflexive state⟩

/-- An event self-evident for every agent is `p`-evident for every threshold
at most one. -/
theorem IsSelfEvident.isPEvident {ι : Type uι} [Fintype ι]
    {prior : FinDist Ω} (hfull : prior.FullSupport)
    {partition : ι → InfoPartition Ω} {threshold : ℝ}
    (hthreshold : threshold ≤ 1) {event : Finset Ω}
    (hself : ∀ agent, IsSelfEvident (partition agent) event) :
    IsPEvident prior partition threshold event := by
  intro agent state hstate
  rw [mem_PBelief_iff]
  rw [posterior_eq_one_of_selfEvident
    prior hfull (partition agent) event state hstate (hself agent)]
  exact hthreshold

/-- Exact common knowledge implies common `p`-belief for every threshold at
most one under a full-support prior. -/
theorem CommonKnowledgeAt.commonPBeliefAt
    {ι : Type uι} [Fintype ι]
    {prior : FinDist Ω} (hfull : prior.FullSupport)
    {partition : ι → InfoPartition Ω} {event : Finset Ω} {state : Ω}
    {threshold : ℝ} (hthreshold : threshold ≤ 1)
    (h : CommonKnowledgeAt partition event state) :
    CommonPBeliefAt prior partition threshold event state := by
  obtain ⟨witness, hsubset, hstate, hself⟩ := h
  refine ⟨witness, hstate,
    IsSelfEvident.isPEvident hfull hthreshold hself, ?_⟩
  intro other hother
  rw [mem_mutualPBelief_iff]
  intro agent
  have hcellWitness : (partition agent).cell other ⊆ witness :=
    hself agent other hother
  have hcellEvent : (partition agent).cell other ⊆ event :=
    hcellWitness.trans hsubset
  rw [posterior_eq_one_of_cell_subset
    prior hfull (partition agent) hcellEvent]
  exact hthreshold

end GameTheory.Epistemic
