/-
# Approximate common knowledge

The p-belief operators are set-valued and work on arbitrary state spaces and
events. Probability enters through the Bayesian posterior in `Basic`.

Primary reference: D. Monderer and M. Samet, “Approximating Common Knowledge
with Common Beliefs,” *Games and Economic Behavior* 1 (1989).
-/

import GameTheory.Epistemic.Basic

noncomputable section

namespace GameTheory.Epistemic

open GameTheory.Math.Probability

universe uι uΩ

variable {Ω : Type uΩ}

/-- The event where the current posterior of `event` is at least `threshold`. -/
def PBelief (prior : PMF Ω) (partition : Setoid Ω)
    (threshold : ℝ) (event : Set Ω) : Set Ω :=
  {state | posterior prior partition event state ≥ threshold}

@[simp]
theorem mem_PBelief_iff (prior : PMF Ω)
    (partition : Setoid Ω) (threshold : ℝ)
    (event : Set Ω) (state : Ω) :
    state ∈ PBelief prior partition threshold event ↔
      posterior prior partition event state ≥ threshold := Iff.rfl

/-- Lowering the threshold enlarges a `p`-belief event. -/
theorem PBelief_mono_threshold (prior : PMF Ω)
    (partition : Setoid Ω) {lower upper : ℝ}
    (hthreshold : lower ≤ upper) (event : Set Ω) :
    PBelief prior partition upper event ⊆
      PBelief prior partition lower event := by
  intro state hstate
  exact le_trans hthreshold hstate

/-- Mutual `p`-belief: every agent assigns probability at least `threshold`
to the event. -/
def mutualPBelief {ι : Type uι}
    (prior : PMF Ω) (partition : ι → Setoid Ω)
    (threshold : ℝ) (event : Set Ω) : Set Ω :=
  {state | ∀ agent : ι,
    state ∈ PBelief prior (partition agent) threshold event}

@[simp]
theorem mem_mutualPBelief_iff {ι : Type uι}
    (prior : PMF Ω) (partition : ι → Setoid Ω)
    (threshold : ℝ) (event : Set Ω) (state : Ω) :
    state ∈ mutualPBelief prior partition threshold event ↔
      ∀ agent : ι,
        posterior prior (partition agent) event state ≥ threshold := by
  rfl

/-- Lowering the threshold enlarges mutual `p`-belief. -/
theorem mutualPBelief_mono_threshold {ι : Type uι}
    (prior : PMF Ω) (partition : ι → Setoid Ω)
    {lower upper : ℝ} (hthreshold : lower ≤ upper)
    (event : Set Ω) :
    mutualPBelief prior partition upper event ⊆
      mutualPBelief prior partition lower event := by
  intro state hstate agent
  exact le_trans hthreshold (hstate agent)

/-- A `p`-evident event: whenever it occurs, every agent assigns probability
at least `threshold` to it. -/
def IsPEvident {ι : Type uι}
    (prior : PMF Ω) (partition : ι → Setoid Ω)
    (threshold : ℝ) (event : Set Ω) : Prop :=
  ∀ agent : ι, event ⊆ PBelief prior (partition agent) threshold event

/-- Lowering the threshold preserves `p`-evidence. -/
theorem IsPEvident.mono_threshold {ι : Type uι}
    {prior : PMF Ω} {partition : ι → Setoid Ω}
    {lower upper : ℝ} (hthreshold : lower ≤ upper)
    {event : Set Ω}
    (hself : IsPEvident prior partition upper event) :
    IsPEvident prior partition lower event := by
  intro agent state hstate
  exact PBelief_mono_threshold prior (partition agent) hthreshold event
    (hself agent hstate)

/-- Common `p`-belief at a state, in public-event witness form. -/
def CommonPBeliefAt {ι : Type uι}
    (prior : PMF Ω) (partition : ι → Setoid Ω)
    (threshold : ℝ) (event : Set Ω) (state : Ω) : Prop :=
  ∃ witness : Set Ω,
    state ∈ witness ∧ IsPEvident prior partition threshold witness ∧
      witness ⊆ mutualPBelief prior partition threshold event

/-- States at which `event` is common `p`-belief. -/
def CommonPBelief {ι : Type uι}
    (prior : PMF Ω) (partition : ι → Setoid Ω)
    (threshold : ℝ) (event : Set Ω) : Set Ω :=
  {state | CommonPBeliefAt prior partition threshold event state}

@[simp]
theorem mem_CommonPBelief_iff {ι : Type uι}
    (prior : PMF Ω) (partition : ι → Setoid Ω)
    (threshold : ℝ) (event : Set Ω) (state : Ω) :
    state ∈ CommonPBelief prior partition threshold event ↔
      CommonPBeliefAt prior partition threshold event state := Iff.rfl

/-- Common `p`-belief implies mutual `p`-belief at the current state. -/
theorem CommonPBeliefAt.implies_mutualPBelief {ι : Type uι}
    {prior : PMF Ω} {partition : ι → Setoid Ω}
    {threshold : ℝ} {event : Set Ω} {state : Ω}
    (h : CommonPBeliefAt prior partition threshold event state) :
    state ∈ mutualPBelief prior partition threshold event := by
  obtain ⟨witness, hstate, _, hbelief⟩ := h
  exact hbelief hstate

/-- Lowering the threshold preserves common `p`-belief. -/
theorem CommonPBeliefAt.mono_threshold {ι : Type uι}
    {prior : PMF Ω} {partition : ι → Setoid Ω}
    {lower upper : ℝ} (hthreshold : lower ≤ upper)
    {event : Set Ω} {state : Ω}
    (h : CommonPBeliefAt prior partition upper event state) :
    CommonPBeliefAt prior partition lower event state := by
  obtain ⟨witness, hstate, hevident, hbelief⟩ := h
  refine ⟨witness, hstate, hevident.mono_threshold hthreshold, ?_⟩
  exact hbelief.trans <| mutualPBelief_mono_threshold prior partition
    hthreshold event

/-! ## Exact-to-approximate bridges -/

/-- An event self-evident for every agent is `p`-evident for every threshold
at most one under a full-support prior. -/
theorem IsSelfEvident.isPEvident {ι : Type uι}
    {prior : PMF Ω} (hfull : FullSupport prior)
    {partition : ι → Setoid Ω} {threshold : ℝ}
    (hthreshold : threshold ≤ 1) {event : Set Ω}
    (hself : ∀ agent, IsSelfEvident (partition agent) event) :
    IsPEvident prior partition threshold event := by
  intro agent state hstate
  rw [mem_PBelief_iff]
  rw [posterior_eq_one_of_selfEvident prior hfull
    (partition agent) event state hstate (hself agent)]
  exact hthreshold

/-- Exact common knowledge implies common `p`-belief for every threshold at
most one under a full-support prior. -/
theorem CommonKnowledgeAt.commonPBeliefAt {ι : Type uι}
    {prior : PMF Ω} (hfull : FullSupport prior)
    {partition : ι → Setoid Ω} {event : Set Ω} {state : Ω}
    {threshold : ℝ} (hthreshold : threshold ≤ 1)
    (h : CommonKnowledgeAt partition event state) :
    CommonPBeliefAt prior partition threshold event state := by
  obtain ⟨witness, hsubset, hstate, hself⟩ := h
  refine ⟨witness, hstate,
    IsSelfEvident.isPEvident hfull hthreshold hself, ?_⟩
  intro other hother agent
  rw [mem_PBelief_iff]
  have hcellWitness : cell (partition agent) other ⊆ witness :=
    hself agent other hother
  have hcellEvent : cell (partition agent) other ⊆ event :=
    hcellWitness.trans hsubset
  rw [posterior_eq_one_of_cell_subset prior hfull
    (partition agent) hcellEvent]
  exact hthreshold

end GameTheory.Epistemic
